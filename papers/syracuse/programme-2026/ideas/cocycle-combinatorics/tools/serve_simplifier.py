#!/usr/bin/env python3
"""serve_simplifier.py -- a tiny web UI for word_simplifier.

Input a gap word, run the simplification engine (roll -> word set -> reduce the
differences), and display the simplifying graph inline (Graphviz SVG) plus the
floor comparison (simplest representative vs 1 - chi = |D|) and a reduction table.

  python3 serve_simplifier.py [--port 8765]
  then open  http://localhost:8765

Pure standard library; shells out to `dot` for SVG rendering.
"""
from __future__ import annotations

import os
import sys
import html
import random
import argparse
import subprocess
import urllib.parse
from math import log10
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, _HERE)
from word_simplifier import (roll, simplify_set, reduction_dot,  # noqa: E402
                             compare_to_floor, decomposition_dot, decompose,
                             decomp_leaves, lattice_simplify, lattice_dot,
                             critical_bounds, random_critical_word,
                             character_bracket)

_RNG = random.Random()


def log10_int(n):
    """log10 of a (possibly huge) integer, robust past the float range."""
    n = abs(int(n))
    if n == 0:
        return float("-inf")
    if n < 10 ** 300:
        return log10(n)
    d = len(str(n))
    return (d - 15) + log10(int(str(n)[:15]))


def mag(n):
    """Compact display for possibly-huge integers."""
    n = int(n)
    if abs(n) < 10_000_000:
        return f"{n:,}"
    return f'&asymp;10<sup>{log10_int(n):.1f}</sup> ({len(str(abs(n)))} digits)'


# --------------------------------------------------------------------------- #
def parse_word(s: str):
    parts = s.replace(",", " ").split()
    if not parts:
        raise ValueError("enter a word, e.g. 1,2,1,3")
    try:
        w = tuple(int(x) for x in parts)
    except ValueError:
        raise ValueError("a word is a list of positive integers, e.g. 1,2,1,3")
    if any(d <= 0 for d in w):
        raise ValueError("gaps must be positive integers")
    return w


MODES = [("anchored", "anchored basis + combine"), ("all", "all pairs (redundant)"),
         ("star", "star (w0 vs all)"), ("adjacent", "adjacent (roll steps)")]
VALID_MODES = {v for v, _ in MODES}


def default_mode(word):
    """all-pairs is O(n^2) edges -> only readable for short words."""
    return "all" if len(word) <= 8 else "star"


def mode_select(current):
    opts = "".join(
        f'<option value="{v}"{" selected" if v == current else ""}>{lab}</option>'
        for v, lab in MODES)
    return f'<select name="mode">{opts}</select>'


def render_svg(dot: str) -> str:
    p = subprocess.run(["dot", "-Tsvg"], input=dot,
                       capture_output=True, text=True)
    if p.returncode != 0:
        raise RuntimeError("graphviz error: " + p.stderr)
    svg = p.stdout
    i = svg.find("<svg")              # drop the XML/doctype header -> inline
    return svg[i:] if i >= 0 else svg


CSS = """
 :root{font-family:Helvetica,Arial,sans-serif}
 body{margin:0;background:#f7f9fb;color:#1c2733}
 header{background:#1c2733;color:#fff;padding:16px 24px}
 header h1{margin:0;font-size:19px;font-weight:600}
 header p{margin:4px 0 0;font-size:13px;color:#9fb3c8}
 main{max-width:1100px;margin:0 auto;padding:22px}
 form{display:flex;gap:10px;align-items:center;margin-bottom:18px}
 input[type=text]{font-size:16px;padding:9px 12px;border:1px solid #c3ced9;
   border-radius:7px;width:300px;font-family:monospace}
 button{font-size:15px;padding:9px 18px;border:0;border-radius:7px;
   background:#2f6fb0;color:#fff;cursor:pointer}
 button:hover{background:#255a90}
 .ex{font-size:13px;color:#5a6b7b}.ex a{color:#2f6fb0;text-decoration:none}
 .err{background:#fdecea;color:#a3261c;padding:10px 14px;border-radius:7px}
 .card{background:#fff;border:1px solid #e1e8ee;border-radius:10px;
   padding:16px 20px;margin-bottom:18px}
 .card h2{margin:0 0 10px;font-size:15px;color:#2f6fb0}
 table{border-collapse:collapse;font-size:13px}
 td,th{padding:4px 12px 4px 0;text-align:left;vertical-align:top}
 th{color:#5a6b7b;font-weight:600}
 .mono{font-family:monospace}
 .big{font-size:17px;font-weight:600}
 .good{color:#1a7f37}.warn{color:#9a6700}
 .graph{overflow:auto;text-align:center}
 .graph svg{max-width:100%;height:auto}
 .rtab td{border-top:1px solid #eef2f6}
"""

FORM = """
<form method="get" action="/">
  <input type="text" name="word" value="{val}" placeholder="1,2,1,3" autofocus>
  {mode_sel}
  <button type="submit">simplify</button>
  <span class="ex">try:
    <a href="/?word=1,2,1,3">1,2,1,3</a> &middot;
    <a href="/?word=1,3,1,3,2">1,3,1,3,2</a> &middot;
    <a href="/?word=2,3,2,3,2,3,1">2,3,2,3,2,3,1</a> &middot;
    <a href="/?word=1,2,1,2,1,2,1,2,1,2,3&mode=star">big (star)</a>
  </span>
</form>
"""

RANDFORM = """
<form method="get" action="/" style="margin-top:-6px">
  <span class="ex">&hellip; or generate a random <b>critical</b> word
    (2<sup>E</sup>&asymp;3<sup>o</sup>, cycle-shaped) of length</span>
  <input type="number" name="rand" min="2" max="200" value="12"
    style="width:72px;font-size:15px;padding:6px 8px;border:1px solid #c3ced9;border-radius:6px">
  <button type="submit">random</button>
</form>
"""


GRAPH_EDGE_LIMIT = 500     # above this, an all-pairs graph is unreadable
GRAPH_MAX_LEN = 30         # above this, skip ALL graph rendering (heavy / slow)
TABLE_ROWS = 60
_NOGRAPH = (f'<p class="ex">graphs hidden for |w| &gt; {GRAPH_MAX_LEN} '
            '(rendering is heavy) &mdash; stats and tables below are still computed.</p>')


def _floor_rows(cf, bc):
    cyc = cf["is_cycle(|D|==gcd)"]
    cyc_html = ('<span class="good">yes &mdash; the squeeze is a real exclusion</span>'
                if cyc else
                f'<span class="warn">no (gcd={cf["gcd_rotations"]}) &mdash; this small '
                'rep is a <b>pattern-seed</b>, not yet an exclusion</span>')
    cb = critical_bounds(cf["E_gapsum"], cf["o_len"])
    c6 = bc.core_sixfree()
    Dval = cf["floor_|D|"]
    lr_D = (log10_int(c6) - log10_int(Dval))   # log10(6-free / |D|): <0 = below the floor
    rb = character_bracket(cf["word"])         # AM-GM estimator on chi(w_<k) = 2^{e_k}/3^k
    lG, lA, lC, lCG, gap = (rb["log10_G"], rb["log10_A"], rb["log10_C"],
                            rb["log10_CG"], rb["amgm_gap"])
    amgm_ok = ('<span class="good">yes</span>'
               if (lG <= lA + 1e-9 and lA <= lCG + 1e-9)
               else '<span class="warn">no</span>')
    ctrl = cb["controlled"]
    conj = cb["three_o"]                       # ~3^o : conjectural (mu(log2 3)=2) target
    r_rig = (c6 / ctrl) if ctrl else float("inf")
    r_conj = (c6 / conj) if conj else float("inf")
    rig_cls = "good" if r_rig < 1 else "warn"
    conj_cls = "good" if r_conj < 1 else "warn"
    reg = ('<span class="warn">critical &mdash; near-coincidence cycle regime '
           '(2<sup>E</sup>&asymp;3<sup>o</sup>)</span>' if cb["critical"]
           else 'not critical (2<sup>E</sup> far from 3<sup>o</sup>)')
    if r_rig < 1:
        verdict = ('<span class="good">rep beats the <b>rigorous</b> bound &mdash; a '
                   'genuine-cycle family here is excluded unconditionally.</span>')
    elif r_conj < 1:
        verdict = ('<span class="warn">rep beats the <b>conjectural</b> &asymp;3<sup>o</sup> '
                   'target but not the (weak, proven) bound &mdash; excludable if '
                   '&mu;(log<sub>2</sub>3)=2, or rigorously once o is large enough '
                   '(for a constant ceiling, o&nbsp;&gtrsim;&nbsp;60).</span>')
    else:
        verdict = '<span class="warn">rep is above both bounds &mdash; no exclusion.</span>'
    return (f'<tr><th>6-free part of core</th><td class="mono big">{c6:,}</td></tr>'
            f'<tr><th>value at (2,3)</th><td class="mono">{bc.core_value()}</td></tr>'
            f'<tr><th>floor |1&minus;&chi;| = |D| = |2<sup>{cf["E_gapsum"]}</sup>'
            f'&minus;3<sup>{cf["o_len"]}</sup>|</th><td class="mono">{mag(cf["floor_|D|"])}</td></tr>'
            f'<tr><th><b>log<sub>10</sub>(6-free / |D|)</b> '
            f'<span class="ex">&lt;0 = below the floor</span></th>'
            f'<td class="mono big">{lr_D:+.3f}</td></tr>'
            f'<tr><th>regime</th><td>{reg}</td></tr>'
            f'<tr><th><b>controlled bound</b> &mdash; rigorous<br>'
            f'<span class="ex">{cb["controlled_name"]}: |2<sup>E</sup>&minus;3<sup>o</sup>| '
            f'&gtrsim; 0.002&middot;3<sup>o</sup>/o<sup>13.3</sup></span></th>'
            f'<td class="mono">{mag(ctrl)}</td></tr>'
            f'<tr><th>conjectural target &mdash; if &mu;(log<sub>2</sub>3)=2<br>'
            f'<span class="ex">|2<sup>E</sup>&minus;3<sup>o</sup>| &gtrsim; 3<sup>o(1&minus;&epsilon;)</sup>'
            f' &asymp; 3<sup>o</sup></span></th><td class="mono">{mag(conj)}</td></tr>'
            f'<tr><th><b>rep / rigorous bound</b></th>'
            f'<td class="mono big {rig_cls}">{r_rig:.3g}</td></tr>'
            f'<tr><th>rep / conjectural &asymp;3<sup>o</sup></th>'
            f'<td class="mono {conj_cls}">{r_conj:.3g}</td></tr>'
            f'<tr><th></th><td>{verdict}</td></tr>'
            f'<tr><th colspan="2" style="padding-top:12px;color:#2f6fb0;'
            f'border-top:1px solid #e1e8ee"><b>abelian estimator</b> &mdash; partial '
            f'characters &chi;(w<sub>&lt;k</sub>) = 2<sup>e<sub>k</sub></sup>/3<sup>k</sup>, '
            f'AM&ndash;GM &nbsp;G(w) &le; A(w) &le; C(w)&middot;G(w) '
            f'<span class="ex">(all log<sub>10</sub>)</span></th></tr>'
            f'<tr><th>G(w) = geometric mean '
            f'<span class="ex">almost abelian: 2<sup>&#772;e</sup>/3<sup>(n&minus;1)/2</sup></span></th>'
            f'<td class="mono">{lG:+.3f}</td></tr>'
            f'<tr><th>A(w) = arithmetic mean '
            f'<span class="ex">= S(w)/(n&middot;3<sup>n&minus;1</sup>)</span></th>'
            f'<td class="mono">{lA:+.3f}</td></tr>'
            f'<tr><th>C(w) = stark ratio '
            f'<span class="ex">max<sub>k</sub>&chi; / min<sub>k</sub>&chi;</span></th>'
            f'<td class="mono">{lC:.3f}</td></tr>'
            f'<tr><th>upper bound C(w)&middot;G(w)</th><td class="mono">{lCG:+.3f}</td></tr>'
            f'<tr><th>AM/GM gap = log<sub>10</sub>(A/G) '
            f'<span class="ex">Jensen / non-abelian spread</span></th>'
            f'<td class="mono big">{gap:.3f}</td></tr>'
            f'<tr><th>G &le; A &le; C&middot;G ?</th><td>{amgm_ok}</td></tr>'
            f'<tr><th>genuine cycle (gcd = |D|)?</th><td>{cyc_html}</td></tr>')


def lattice_html(word, seed) -> str:
    res = lattice_simplify(seed, group_by="first")
    bc = res["best"]
    if bc is None:
        return ('<p class="err">no anchored differences &mdash; every rotation has a '
                'distinct first gap, so no two share an anchor. Try <b>star</b> mode '
                '(anchor everything at w0).</p>')
    cf = compare_to_floor(word, r=bc)
    nw = len(res["words"])
    free = (f'<b>{res["rank"]}</b> free anchored generators in {res["n_groups"]} group(s) '
            f'(by shared first gap) &mdash; vs <b>{res["n_allpairs"]}</b> redundant '
            f'all-pairs differences (only rank &le; {nw - 1} are independent).')

    def row(tag, label, r, extra=""):
        mark = ' &#9733;' if (not r.is_null and r.core_pair == bc.core_pair) else ''
        tgt = ('<b>0 (relation)</b>' if r.is_null else
               f'{html.escape(str(r.u))} | {html.escape(str(r.v))} &nbsp; '
               f'6-free=<b>{r.core_sixfree()}</b>{mark}')
        return (f'<tr class="rtab"><td>{tag}</td><td class="mono">{label}</td>'
                f'<td class="mono">{extra}</td><td class="mono">{tgt}</td></tr>')

    g_rows = "".join(row("round 1", f'w{g["j"]} &minus; w{g["a"]}', g["r"])
                     for g in res["gens"])
    c_rows = "".join(row("round 2", f'w{c["j1"]} &minus; w{c["j2"]}', c["r"],
                         f'= g(w{c["j1"]}) &minus; g(w{c["j2"]})')
                     for c in res["combos"])
    if len(word) > GRAPH_MAX_LEN:
        graph = dsvg = _NOGRAPH
    else:
        graph = render_svg(lattice_dot(seed, "first"))
        dsvg = render_svg(decomposition_dot(bc.u0, bc.v0))
    return f"""
<div class="card">
  <h2>simplest representative &nbsp;<span style="font-weight:400;color:#5a6b7b;font-size:13px">
    anchored basis + combination round, |w|={len(word)}</span></h2>
  <div class="big mono">{html.escape(str(bc.u))} &nbsp;&minus;&nbsp; {html.escape(str(bc.v))}</div>
  <table>{_floor_rows(cf, bc)}</table>
</div>
<div class="card">
  <h2>anchored free basis &rarr; combinations &nbsp;<span style="font-weight:400;color:#5a6b7b;font-size:13px">
    round 1 = free anchored differences; round 2 = combine them (shared structure cancels)</span></h2>
  <p style="font-size:13px;color:#33414f;margin:0 0 12px">{free}</p>
  <div class="graph">{graph}</div>
</div>
<div class="card">
  <h2>multi-step decomposition of the simplest difference &nbsp;<span style="font-weight:400;color:#5a6b7b;font-size:13px">
    {html.escape(str(bc.u0))} &minus; {html.escape(str(bc.v0))}</span></h2>
  <div class="graph">{dsvg}</div>
</div>
<div class="card">
  <h2>generators &amp; combinations</h2>
  <table>
    <tr><th>round</th><th>difference</th><th>combination</th><th>core</th></tr>
    {g_rows}{c_rows}
  </table>
</div>
"""


def result_html(word, mode="all") -> str:
    seed = roll(word)
    if mode == "anchored":
        return lattice_html(word, seed)
    best, reds = simplify_set(seed, pairs=mode)
    if best is None:
        return ('<p class="err">no non-trivial differences &mdash; the word is too '
                'short or all its rotations coincide (imprimitive).</p>')
    bc = best[1]
    cf = compare_to_floor(word, r=bc)
    npairs = len(reds)
    big = len(word) > GRAPH_MAX_LEN

    # graph -- skipped for big words; else guarded against the all-pairs explosion
    if big:
        graph = _NOGRAPH
    elif npairs > GRAPH_EDGE_LIMIT:
        graph = (f'<p class="warn">{npairs} pairs is too many to draw legibly. '
                 'Pick <b>star</b> or <b>adjacent</b> in the selector (O(n) edges) '
                 'to visualize this case; the stats above are over the chosen view.</p>')
    else:
        graph = ('<div class="graph">'
                 + render_svg(reduction_dot(seed, pairs=mode, seed_label=f"roll{word}"))
                 + '</div>')

    # multi-step decomposition of the simplest difference (counts are cheap; skip SVG if big)
    droot = decompose(bc.u0, bc.v0)
    dleaves = decomp_leaves(droot)
    n_split = sum(1 for x in dleaves if x.kind == "NULL")
    n_atom = sum(1 for x in dleaves if x.kind == "LEAF")
    decomp_svg = _NOGRAPH if big else render_svg(decomposition_dot(bc.u0, bc.v0))

    # if a sparse view might be hiding a smaller global core, say so
    gnote = ""
    if mode != "all" and len(word) <= 40:
        gb = simplify_set(seed, pairs="all")[0]
        if gb and gb[1].core_sixfree() < bc.core_sixfree():
            gnote = ('<tr><th>global simplest (all pairs)</th><td class="mono">'
                     f'6-free=<b>{gb[1].core_sixfree()}</b> from '
                     f'{html.escape(str(gb[1].core_pair))} &mdash; '
                     'select "all pairs" to see it</td></tr>')

    srt = sorted(reds, key=lambda t: (t[1].is_null, t[1].core_sixfree()))
    rows = []
    for (i, j), r in srt[:TABLE_ROWS]:
        if r.is_null:
            tgt = '<b>0 (relation)</b>'
        else:
            mark = ' &#9733;' if r.core_pair == bc.core_pair else ''
            tgt = (f'{html.escape(str(r.u))} | {html.escape(str(r.v))} '
                   f'&nbsp; 6-free=<b>{r.core_sixfree()}</b>{mark}')
        steps = ", ".join(f"{k} {s}" for k, s in r.steps) or "&mdash;"
        rows.append(
            f'<tr class="rtab"><td class="mono">w{i} &minus; w{j}</td>'
            f'<td class="mono">{html.escape(str(r.u0))} &minus; '
            f'{html.escape(str(r.v0))}</td>'
            f'<td class="mono">X^{r.ux} Y^{r.uy}</td>'
            f'<td class="mono">{steps}</td>'
            f'<td class="mono">{tgt}</td></tr>')
    more = (f'<tr><td colspan="5" style="color:#5a6b7b;padding-top:6px">&hellip; and '
            f'{len(srt) - TABLE_ROWS} more pairs (sorted smallest first)</td></tr>'
            if len(srt) > TABLE_ROWS else "")

    return f"""
<div class="card">
  <h2>simplest representative &nbsp;<span style="font-weight:400;color:#5a6b7b;font-size:13px">
    over the <b>{mode}</b> view ({npairs} pairs), |w|={len(word)}</span></h2>
  <div class="big mono">{html.escape(str(bc.u))} &nbsp;&minus;&nbsp; {html.escape(str(bc.v))}</div>
  <table>
    {_floor_rows(cf, bc)}
    {gnote}
  </table>
</div>

<div class="card">
  <h2>simplifying graph &nbsp;<span style="font-weight:400;color:#5a6b7b;font-size:13px">
    seed = roll{html.escape(str(word))} &rarr; word set &rarr; reduce each difference; gold = simplest</span></h2>
  {graph}
</div>

<div class="card">
  <h2>multi-step decomposition of the simplest difference &nbsp;<span style="font-weight:400;color:#5a6b7b;font-size:13px">
    {html.escape(str(bc.u0))} &minus; {html.escape(str(bc.v0))} &rarr; split at every shared anchor &rarr;
    {n_split} NULL segment(s) + {n_atom} atomic leaf(s); gold = smallest atom</span></h2>
  <div class="graph">{decomp_svg}</div>
</div>

<div class="card">
  <h2>reductions ({npairs} pairs) &nbsp;<span style="font-weight:400;color:#5a6b7b;font-size:13px">
    each is a verified exact Z[X,Y] identity; &#9733; = simplest</span></h2>
  <table>
    <tr><th>pair</th><th>difference</th><th>unit</th><th>strips</th><th>core</th></tr>
    {''.join(rows)}{more}
  </table>
</div>
"""


def page(word_value: str, mode: str, body: str) -> str:
    form = FORM.format(val=html.escape(word_value), mode_sel=mode_select(mode))
    return (f"<!doctype html><html><head><meta charset='utf-8'>"
            f"<title>word simplifier</title><style>{CSS}</style></head><body>"
            f"<header><h1>Cocycle word simplifier</h1>"
            f"<p>roll seeds a word set &rarr; the engine reduces the differences "
            f"&rarr; compare the simplest representative to the controlled lower "
            f"bound (Rhin/de Weger if critical, else min(2<sup>E</sup>,3<sup>o</sup>))</p></header>"
            f"<main>{form}{RANDFORM}{body}</main>"
            f"</body></html>")


class Handler(BaseHTTPRequestHandler):
    def _send(self, body, code=200, ctype="text/html; charset=utf-8"):
        data = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        u = urllib.parse.urlparse(self.path)
        if u.path not in ("/", ""):
            self._send("not found", 404, "text/plain")
            return
        q = urllib.parse.parse_qs(u.query)
        word_str = q.get("word", [""])[0].strip()
        mode = q.get("mode", [""])[0].strip()
        rand = q.get("rand", [""])[0].strip()
        if rand and not word_str:                    # generate a random critical word
            try:
                o = int(rand)
                if 2 <= o <= 200:
                    word_str = ",".join(str(g)
                                        for g in random_critical_word(o, _RNG))
                    if mode not in VALID_MODES:
                        mode = "anchored"
            except ValueError:
                pass
        body = ""
        if word_str:
            try:
                w = parse_word(word_str)
                if mode not in VALID_MODES:
                    mode = default_mode(w)               # all for small, star for big
                body = result_html(w, mode)
            except Exception as e:                       # noqa: BLE001
                body = f'<p class="err">{html.escape(str(e))}</p>'
        self._send(page(word_str, mode or "all", body))

    def log_message(self, *a):                            # keep the console quiet
        pass


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, default=8765)
    ap.add_argument("--host", default="127.0.0.1")
    args = ap.parse_args()
    last = None
    for port in range(args.port, args.port + 8):
        try:
            srv = ThreadingHTTPServer((args.host, port), Handler)
        except OSError as e:                              # port busy -> try next
            last = e
            continue
        print(f"word simplifier UI  ->  http://localhost:{port}", flush=True)
        srv.serve_forever()
        return
    raise SystemExit(f"no free port in {args.port}..{args.port+7}: {last}")


if __name__ == "__main__":
    main()
