#!/usr/bin/env python3
"""Build index.html for the cocycle-program review.

The narrative sections are hand-written below. The bibliography is generated from lit/bib-*.jsonl
(verified entries only, deduplicated). The threshold chart is computed from the closed-form bounds:
Ellison 1971 and Rhin / Simons–de Weger Lemma 12, at critical E = ceil(o log2 3).
Run with: python3 -I build_report.py   (writes index.html next to this file).
"""
import html
import json
import math
import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent
LIT = HERE / "lit"
DATE = "2026-10-30"

THEMES = [
    ("arithmetic", "Arithmetic of gcd(S, D)"),
    ("chase-arithmetic", "Arithmetic, round 2"),
    ("words", "Words and pigeonhole"),
    ("chase-words-limits", "Words and limits, round 2"),
    ("generalized-maps", "Generalized maps and limits"),
    ("frames", "Cocycle frames"),
    ("queue", "Incubator queue (THREADS.md)"),
]


def esc(s):
    return html.escape(str(s), quote=True)


# ---------------------------------------------------------------- bibliography
DROP = {"wrong_link", "metadata_mismatch", "url_dead"}
MARK = {"quote_not_found", "unreachable_but_exists"}


def load_verify():
    v = {}
    p = LIT / "verify.jsonl"
    if p.exists():
        for line in p.read_text().splitlines():
            try:
                j = json.loads(line)
            except json.JSONDecodeError:
                continue
            st = j.get("status", "ok")
            if st == "title_mismatch":
                st = "wrong_link" if str(j.get("note", "")).startswith("WRONG LINK") else "secondary_link"
            v[(j.get("file"), j.get("line"))] = st
            if j.get("id"):
                v[(j.get("file"), j.get("id"))] = st
    return v


VERIFY_STATS = {"dropped": 0, "marked": 0, "via": 0}


def load_bib():
    entries, seen, unverified = [], {}, 0
    ver = load_verify()
    for key, _ in THEMES:
        p = LIT / f"bib-{key}.jsonl"
        if not p.exists():
            continue
        for lineno, line in enumerate(p.read_text().splitlines(), start=1):
            line = line.strip()
            if not line:
                continue
            try:
                j = json.loads(line)
            except json.JSONDecodeError:
                continue
            j.setdefault("theme", key)
            j["theme"] = key
            if not j.get("verified"):
                unverified += 1
                continue
            st = ver.get((p.name, lineno)) or ver.get((p.name, j.get("id")))
            if st in DROP:
                VERIFY_STATS["dropped"] += 1
                continue
            j["mark"] = st in MARK
            VERIFY_STATS["marked"] += j["mark"]
            j["via"] = st == "secondary_link"
            VERIFY_STATS["via"] += j["via"]
            norm = re.sub(r"[^a-z0-9]", "", (j.get("title") or j.get("id") or "").lower())[:60]
            if norm in seen:
                seen[norm]["themes"].add(key)
                continue
            j["themes"] = {key}
            seen[norm] = j
            entries.append(j)
    return entries, unverified


def bib_html(entries):
    out = []
    for key, label in THEMES:
        group = [e for e in entries if e["theme"] == key]
        if not group:
            continue
        group.sort(key=lambda e: (str(e.get("authors", "")), e.get("year") or 0))
        out.append(f'<details class="bibg"><summary><b>{esc(label)}</b> · {len(group)} sources</summary><ol class="bib">')
        for e in group:
            url = e.get("url") or (f"https://doi.org/{e['doi']}" if e.get("doi") else "")
            via = ""
            if e.get("via"):
                if e.get("doi"):
                    url = f"https://doi.org/{e['doi']}"
                    via = ' <span title="key quote taken from a secondary source that restates the result">‡</span>'
                else:
                    via = f' <span title="no primary link; quote and link via a secondary source">‡ <a href="{esc(e.get("url",""))}">via secondary</a></span>'
                    url = ""
            title = esc(e.get("title", ""))
            title = f'<a href="{esc(url)}">{title}</a>' if url else title
            verdict = esc(e.get("verdict", ""))
            hook = esc(e.get("hook", ""))
            mark = ' <span title="source exists; key quote not re-located or page paywalled">†</span>' if e.get("mark") else ""
            out.append(
                f'<li><span class="au">{esc(e.get("authors",""))}</span> ({esc(e.get("year",""))}). '
                f'{title}{mark}{via}. <i>{esc(e.get("venue",""))}</i>. '
                f'<span class="chip v-{verdict}">{verdict}</span>'
                + (f'<span class="hook">{hook}</span>' if hook else "")
                + "</li>"
            )
        out.append("</ol></details>")
    return "\n".join(out)


# ---------------------------------------------------------------- threshold chart
def chart_svg():
    d = math.log2(3)
    W, H, L, R, T, B = 760, 300, 56, 150, 18, 40
    xs = list(range(18, 1001, 2))

    def ell(o):
        E = math.ceil(o * d)
        return (E * math.log(2) - E / 10 - o * math.log(3)) / math.log(10)

    def rhin(o):
        return (math.log(0.00219) - 13.3 * math.log(o)) / math.log(10)

    ymin, ymax = -75, 0
    sx = lambda o: L + (o - 0) / 1000 * (W - L - R)
    sy = lambda y: T + (ymax - y) / (ymax - ymin) * (H - T - B)
    pts = lambda f: " ".join(f"{sx(o):.1f},{sy(f(o)):.1f}" for o in xs)
    grid = []
    for y in range(0, -76, -15):
        grid.append(f'<line class="hair" x1="{L}" x2="{W-R}" y1="{sy(y):.1f}" y2="{sy(y):.1f}"/>'
                    f'<text class="tick" x="{L-8}" y="{sy(y)+4:.1f}" text-anchor="end">{y}</text>')
    for o in range(0, 1001, 200):
        grid.append(f'<text class="tick" x="{sx(o):.1f}" y="{H-B+18}" text-anchor="middle">{o}</text>')
    xc = 574
    yc = ell(xc)
    lines = [
        f'<polyline class="ln ln1" points="{pts(ell)}"/>',
        f'<polyline class="ln ln2" points="{pts(rhin)}"/>',
        f'<line class="cross" x1="{sx(xc):.1f}" x2="{sx(xc):.1f}" y1="{T}" y2="{H-B}"/>',
        f'<circle class="dot1" cx="{sx(xc):.1f}" cy="{sy(yc):.1f}" r="4.5"/>',
        f'<text class="lbl" x="{sx(xc)+6:.1f}" y="{T+14}">o = 574: Rhin overtakes Ellison</text>',
        f'<circle class="dot1" cx="{sx(1000):.1f}" cy="{sy(ell(1000)):.1f}" r="4.5"/>',
        f'<circle class="dot2" cx="{sx(1000):.1f}" cy="{sy(rhin(1000)):.1f}" r="4.5"/>',
        f'<text class="lbl" x="{sx(1000)+8:.1f}" y="{sy(ell(1000))+4:.1f}">Ellison {ell(1000):.0f}</text>',
        f'<text class="lbl" x="{sx(1000)+8:.1f}" y="{sy(rhin(1000))+4:.1f}">Rhin {rhin(1000):.0f}</text>',
        f'<text class="lbl" x="{sx(90):.1f}" y="{sy(-20):.1f}">Rhin bound exceeds 5 from o = 56</text>',
    ]
    rows = "".join(
        f"<tr><td class='num'>{o}</td><td class='num'>{ell(o):.1f}</td><td class='num'>{rhin(o):.1f}</td></tr>"
        for o in (18, 56, 100, 306, 574, 1000)
    )
    data = json.dumps([[o, round(ell(o), 2), round(rhin(o), 2)] for o in xs])
    svg = (
        f'<svg id="thr" viewBox="0 0 {W} {H}" role="img" aria-labelledby="thr-t">'
        f'<title id="thr-t">Lower bounds on |2^E − 3^o| at critical E, in orders of magnitude below 3^o</title>'
        + "".join(grid)
        + f'<line class="axis" x1="{L}" x2="{W-R}" y1="{sy(ymin):.1f}" y2="{sy(ymin):.1f}"/>'
        + "".join(lines)
        + f'<text class="tick" x="{(L+W-R)/2:.0f}" y="{H-4}" text-anchor="middle">o (number of odd steps)</text>'
        + f'<line id="thr-x" class="crosshair" x1="0" x2="0" y1="{T}" y2="{H-B}" visibility="hidden"/>'
        + "</svg>"
    )
    return svg, rows, data, (L, W - R, 1000)


# ---------------------------------------------------------------- page
CSS = r"""
:root{color-scheme:light;
 --surface:#fcfcfb;--plane:#f6f6f3;--ink:#0b0b0b;--ink2:#52514e;--muted:#6f6e69;--grid:#e1e0d9;--axis:#c3c2b7;--border:rgba(11,11,11,.12);
 --c1:#2a78d6;--c2:#eb6834;--c3:#1baf7a;--c4:#eda100;--c5:#4a3aa7;
 --c1-wash:rgba(42,120,214,.10);--c2-wash:rgba(235,104,52,.10);--c3-wash:rgba(27,175,122,.12);--c4-wash:rgba(237,161,0,.14);--c5-wash:rgba(74,58,167,.10);
 --crit:#d03b3b;--link:#1f63b8;--mono:ui-monospace,"SF Mono",Menlo,Consolas,monospace}
:root[data-theme="dark"]{color-scheme:dark;
 --surface:#1a1a19;--plane:#0d0d0d;--ink:#f4f3ee;--ink2:#c3c2b7;--muted:#9a998f;--grid:#2c2c2a;--axis:#45453f;--border:rgba(255,255,255,.14);
 --c1:#3987e5;--c2:#d95926;--c3:#199e70;--c4:#c98500;--c5:#9085e9;
 --c1-wash:rgba(57,135,229,.18);--c2-wash:rgba(217,89,38,.18);--c3-wash:rgba(25,158,112,.20);--c4-wash:rgba(201,133,0,.20);--c5-wash:rgba(144,133,233,.18);
 --crit:#e5534b;--link:#8cbcff}
*{box-sizing:border-box}
html{background:var(--plane)}
body{margin:0;color:var(--ink);font:16px/1.5 system-ui,-apple-system,"Segoe UI",sans-serif}
a{color:var(--link)}
.wrap{max-width:1180px;margin:0 auto;padding:28px 32px 60px;display:grid;grid-template-columns:220px minmax(0,1fr);gap:40px}
nav.toc{position:sticky;top:18px;align-self:start;font-size:13.5px;line-height:1.5}
nav.toc ol{list-style:none;padding:0;margin:0}nav.toc li{margin:5px 0}
nav.toc a{color:var(--ink2);text-decoration:none}nav.toc a:hover{color:var(--link);text-decoration:underline}
nav.toc .k{font-size:11px;text-transform:uppercase;letter-spacing:.08em;color:var(--muted);font-weight:650;margin-bottom:8px}
main{min-width:0}
.kicker{font-size:12.5px;text-transform:uppercase;letter-spacing:.08em;color:var(--muted);font-weight:650}
h1{font-size:34px;line-height:1.15;margin:6px 0 12px;letter-spacing:-.01em}
h2{font-size:26px;line-height:1.2;margin:48px 0 6px;letter-spacing:-.01em;scroll-margin-top:16px}
h3{font-size:18px;margin:26px 0 6px}
.lede{font-size:17.5px;color:var(--ink2);max-width:860px}
.sub{color:var(--ink2);max-width:860px;margin:0 0 14px}
p,li{max-width:860px}
section{border-top:1px solid var(--grid);margin-top:36px}
.lanes{display:grid;grid-template-columns:repeat(3,1fr);gap:14px;margin:20px 0 12px}
.lane{border:1px solid var(--border);border-radius:10px;padding:12px 14px;background:var(--surface)}
.lane h4{margin:0 0 8px;font-size:12px;text-transform:uppercase;letter-spacing:.07em;color:var(--muted)}
.lane.rec{border-color:var(--c1);box-shadow:inset 3px 0 0 var(--c1)}
.lane.cut{border-style:dashed}
.lane ul{margin:0;padding-left:18px;font-size:14px}.lane li{margin:6px 0}
.lane .m{display:block;font-size:12.3px;color:var(--ink2)}
.rec-box{border:1px solid var(--c1);background:var(--c1-wash);border-radius:10px;padding:12px 16px;margin:14px 0;max-width:900px}
.rec-box b.h{display:block;font-size:12px;text-transform:uppercase;letter-spacing:.07em;color:var(--ink2);margin-bottom:4px}
.fig{background:var(--surface);border:1px solid var(--border);border-radius:10px;padding:14px 16px;margin:16px 0}
.fig svg{width:100%;height:auto;display:block}
.cap{font-size:13px;color:var(--muted);margin-top:8px}
.twin{font-size:13.5px;color:var(--ink2);max-width:420px}
.twin th:not(:first-child){text-align:right}
td.nw{white-space:nowrap}
table{border-collapse:collapse;width:100%;font-size:14px;margin:10px 0}
th,td{text-align:left;padding:6px 8px;border-bottom:1px solid var(--grid);vertical-align:top}
th{font-size:11.5px;text-transform:uppercase;letter-spacing:.06em;color:var(--muted);font-weight:650}
td.num{font-variant-numeric:tabular-nums;text-align:right;white-space:nowrap}
code,.mono{font-family:var(--mono);font-size:.9em}
code{background:var(--c1-wash);padding:1px 5px;border-radius:4px}
.chip{display:inline-block;font-size:10.5px;font-weight:650;letter-spacing:.05em;text-transform:uppercase;padding:1px 7px;border-radius:999px;border:1.5px solid var(--border);margin:0 4px 0 2px;vertical-align:1px;white-space:nowrap}
.chip.proved{border-color:var(--c1)}.chip.cond{border-color:var(--c4)}.chip.open{border-color:var(--c2)}.chip.lit{border-color:var(--c5)}.chip.heur{border-style:dashed}
.chip.v-keep{border-color:var(--c3)}.chip.v-kill{border-color:var(--axis)}.chip.v-open{border-color:var(--c4)}
.cards{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:14px;margin:14px 0}
.card{border:1px solid var(--border);border-radius:10px;padding:13px 15px;background:var(--surface)}
.card.rec{box-shadow:inset 3px 0 0 var(--c1)}
.card.spec{border-style:dashed}
.card h3{margin:0 0 4px;font-size:16.5px}
.card dl{display:grid;grid-template-columns:96px 1fr;gap:3px 10px;margin:8px 0 0;font-size:13.6px}
.card dt{color:var(--muted);font-size:11.5px;text-transform:uppercase;letter-spacing:.05em;padding-top:2px}
.card dd{margin:0}
.ladder .rung{fill:var(--surface);stroke:var(--axis);stroke-width:1.2}
.ladder .r1{fill:var(--c1-wash);stroke:var(--c1)}.ladder .r2{fill:var(--c4-wash);stroke:var(--c4)}.ladder .r3{fill:var(--c2-wash);stroke:var(--c2);stroke-dasharray:5 4}
svg text{font-family:system-ui,-apple-system,"Segoe UI",sans-serif;fill:var(--ink)}
svg .t2{fill:var(--ink2)}svg .tm{fill:var(--muted)}svg .b{font-weight:650}
svg .tick{font-size:11.5px;fill:var(--muted)}svg .lbl{font-size:12px;fill:var(--ink2)}
svg .hair{stroke:var(--grid);stroke-width:1}svg .axis{stroke:var(--axis);stroke-width:1}
svg .ln{fill:none;stroke-width:2;stroke-linejoin:round;stroke-linecap:round}
svg .ln1{stroke:var(--c1)}svg .ln2{stroke:var(--c2)}
svg .dot1{fill:var(--c1);stroke:var(--surface);stroke-width:2}svg .dot2{fill:var(--c2);stroke:var(--surface);stroke-width:2}
svg .cross{stroke:var(--axis);stroke-width:1}
svg .crosshair{stroke:var(--ink2);stroke-width:1}
svg .edge{stroke:var(--ink2);stroke-width:1.5;fill:none;marker-end:url(#arr)}
svg .box{fill:var(--surface);stroke:var(--axis);stroke-width:1.2}
svg .bx1{fill:var(--c1-wash);stroke:var(--c1);stroke-width:1.4}
.legend{display:flex;gap:16px;font-size:12.5px;color:var(--ink2);flex-wrap:wrap;margin:4px 0 6px}
.legend .k{display:inline-block;width:18px;height:0;border-top:2.5px solid;vertical-align:middle;margin-right:6px}
#tip{position:fixed;pointer-events:none;background:var(--surface);color:var(--ink);border:1px solid var(--border);border-radius:6px;padding:6px 9px;font-size:12px;box-shadow:0 4px 14px rgba(0,0,0,.14);display:none;z-index:20}
.bibg{margin:8px 0;border:1px solid var(--border);border-radius:8px;padding:6px 12px;background:var(--surface)}
.bibg summary{cursor:pointer;font-size:14.5px}
ol.bib{font-size:13.3px;padding-left:24px}ol.bib li{margin:6px 0;max-width:none}
ol.bib .au{font-weight:600}ol.bib .hook{display:block;color:var(--ink2);font-size:12.5px}
.prov{font-size:12.5px;color:var(--muted)}
.theme-btn{position:fixed;top:12px;right:16px;background:var(--surface);color:var(--ink);border:1px solid var(--border);border-radius:6px;padding:4px 10px;font-size:12px;cursor:pointer}
footer{margin-top:50px;border-top:1px solid var(--grid);padding-top:10px;font-size:12.5px;color:var(--muted)}
@media (max-width:900px){.wrap{grid-template-columns:minmax(0,1fr);padding:14px}nav.toc{position:static}.lanes,.cards{grid-template-columns:1fr}h1{font-size:25px}table{display:block;overflow-x:auto;max-width:100%}.card dl{grid-template-columns:1fr}.card dt{padding-top:6px}}
code,.mono{overflow-wrap:anywhere}
p,li,dd,td,.lede,.cap{overflow-wrap:anywhere}
.fig{overflow-x:auto}
@media print{.theme-btn,nav.toc{display:none}.wrap{grid-template-columns:1fr}details{open:true}}
"""

JS = r"""
(function(){
 const q=new URLSearchParams(location.search).get('theme');
 let t=q||localStorage.getItem('cr-theme')||(matchMedia('(prefers-color-scheme: dark)').matches?'dark':'light');
 const set=v=>{document.documentElement.dataset.theme=v;localStorage.setItem('cr-theme',v)};set(t);
 const b=document.getElementById('themebtn');if(b){b.hidden=false;b.onclick=()=>set(document.documentElement.dataset.theme==='dark'?'light':'dark')}
 const svg=document.getElementById('thr'),tip=document.getElementById('tip'),x=document.getElementById('thr-x');
 if(svg&&tip){const D=JSON.parse(svg.dataset.d),L=+svg.dataset.l,R=+svg.dataset.r,M=+svg.dataset.m;
  svg.addEventListener('mousemove',e=>{const r=svg.getBoundingClientRect(),vb=svg.viewBox.baseVal;
   const px=(e.clientX-r.left)/r.width*vb.width;if(px<L||px>R){tip.style.display='none';x.setAttribute('visibility','hidden');return}
   const o=(px-L)/(R-L)*M;let best=D[0];for(const d of D){if(Math.abs(d[0]-o)<Math.abs(best[0]-o))best=d}
   const bx=L+best[0]/M*(R-L);x.setAttribute('x1',bx);x.setAttribute('x2',bx);x.setAttribute('visibility','visible');
   tip.innerHTML='<b>o = '+best[0]+'</b><br>Ellison: '+best[1]+'<br>Rhin: '+best[2]+'<br><span style="color:var(--muted)">orders of magnitude below 3^o</span>';
   tip.style.display='block';tip.style.left=(e.clientX+14)+'px';tip.style.top=(e.clientY+10)+'px'});
  svg.addEventListener('mouseleave',()=>{tip.style.display='none';x.setAttribute('visibility','hidden')});}
})();
"""


def ladder_svg():
    rows = [
        ("r1", "1 growing run", "βdᴸ, uᵖβ, dᵃ e dᵇ",
         "S and D linear in one run coordinate → resultant = the bounded-defect lever. Effective, o-independent.",
         "proved", "Already excluded for positive cycles by the ratio sandwich (fixed slope)."),
        ("r1", "2 growing runs", "d₁ᵃ d₂ᵇ;  dᵃ e₁ dᵃ e₂ dᵃ",
         "D divides (2^d₁ − 2^d₂)·gcd(2^(d₁a) − 3ᵃ, 2^(d₂b) − 3ᵇ): Corvaja–Zannier shape.",
         "cond. Ellison", "All 1ᵃdᵇ excluded given Ellison (Lean); b = 1 is Steiner's circuit theorem."),
        ("r2", "m ≥ 3 growing runs, m fixed", "m-run families",
         "Levin 2019: G ≤ e^(εo) outside finitely many computable sub-tori (Laurent).",
         "cond", "Rests on the Subspace theorem: finite but ineffective, no computable o₀."),
        ("r3", "unboundedly many runs", "Sturmian-like, slope ≈ log₂3",
         "Balanced: excluded (Lean). Two runs of a standard pair, any level: excluded given Ellison.",
         "open", "Open: unbalanced words with ≥ 3 runs at every level. Near-misses bind (G ≈ |D|^0.9997)."),
    ]
    W, h, gap, y0 = 900, 74, 12, 8
    parts = [f'<svg class="ladder" viewBox="0 0 {W} {y0 + len(rows)*(h+gap)}" role="img" aria-labelledby="lad-t">'
             '<title id="lad-t">The run-count hierarchy: what the arithmetic literature gives for each class of gap word</title>']
    for i, (cls, name, ex, mech, st, note) in enumerate(rows):
        y = y0 + i * (h + gap)
        parts.append(f'<rect class="rung {cls}" x="1" y="{y}" width="{W-2}" height="{h}" rx="9"/>')
        parts.append(f'<text class="b" x="16" y="{y+24}" font-size="15">{esc(name)}</text>')
        parts.append(f'<text class="tm" x="16" y="{y+44}" font-size="12">{esc(ex)}</text>')
        parts.append(f'<text class="tm" x="16" y="{y+62}" font-size="11.5">status: {esc(st)}</text>')
        parts.append(f'<text x="250" y="{y+28}" font-size="13">{esc(mech)}</text>')
        parts.append(f'<text class="t2" x="250" y="{y+52}" font-size="12.5">{esc(note)}</text>')
    parts.append("</svg>")
    return "".join(parts)


def pipeline_svg():
    return """<svg viewBox="0 0 900 192" role="img" aria-labelledby="pipe-t">
<title id="pipe-t">The program in one picture: a gap word, its two numbers S and D, their gcd, and the shift k</title>
<defs><marker id="arr" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0L10,5L0,10z" fill="currentColor" style="fill:var(--ink2)"/></marker></defs>
<rect class="box" x="4" y="40" width="150" height="70" rx="9"/>
<text class="b" x="18" y="66" font-size="14">gap word w</text>
<text class="tm" x="18" y="88" font-size="12">(d₀, …, dₒ₋₁), E = Σ d</text>
<rect class="box" x="196" y="20" width="200" height="110" rx="9"/>
<text class="b" x="210" y="46" font-size="14">two integers</text>
<text x="210" y="70" font-size="13">S = Σₖ 2^eₖ · 3^(o−1−k)</text>
<text x="210" y="92" font-size="13">D = 2ᴱ − 3ᵒ</text>
<text class="tm" x="210" y="116" font-size="11.5">rotations add nothing: ideal = (S, D)</text>
<rect class="bx1" x="438" y="30" width="200" height="90" rx="9"/>
<text class="b" x="452" y="56" font-size="14">G = gcd(S, D)</text>
<text x="452" y="80" font-size="13">k(w) = D / G</text>
<text class="tm" x="452" y="104" font-size="11.5">w is a cycle of 3x + k(w)</text>
<rect class="box" x="680" y="20" width="214" height="110" rx="9"/>
<text class="b" x="694" y="46" font-size="14">3x+1 cycle with word w</text>
<text x="694" y="70" font-size="13">⇔ k(w) = 1 ⇔ D ∣ S</text>
<text class="tm" x="694" y="94" font-size="11.5">moves certify G small:</text>
<text class="tm" x="694" y="112" font-size="11.5">αS + βD small ⇒ G ≤ it</text>
<path class="edge" d="M154,75 L194,75"/><path class="edge" d="M396,75 L436,75"/><path class="edge" d="M638,75 L678,75"/>
<text class="t2" x="4" y="160" font-size="12">Lean: Limits.G_eq_gcd, every_word_is_a_cycle, positive_cycle_iff_kOf_eq_one</text><text class="t2" x="4" y="180" font-size="12">Literature: Lagarias 1990 (rational cycles); Belaga–Mignotte 2006, Thm 4 (the corona formulation)</text>
</svg>"""


def page(bib_entries, unverified):
    svg, thr_rows, thr_data, (cl, cr, cm) = chart_svg()
    svg = svg.replace('<svg id="thr"', f'<svg id="thr" data-d=\'{thr_data}\' data-l="{cl}" data-r="{cr}" data-m="{cm}"')
    nbib = len(bib_entries)
    by_theme = {k: sum(1 for e in bib_entries if e["theme"] == k) for k, _ in THEMES}
    body = BODY.format(
        pipeline=pipeline_svg(), ladder=ladder_svg(), thr=svg, thr_rows=thr_rows, nbib=nbib,
        unverified=unverified, bib=bib_html(bib_entries), date=DATE,
        **{f"n_{k.replace('-', '_')}": v for k, v in by_theme.items()},
    )
    return f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Cocycle program: review, limits and directions</title>
<style>{CSS}</style></head><body>
<button id="themebtn" class="theme-btn" hidden aria-label="Toggle light/dark">◐ theme</button>
<div id="tip" role="tooltip"></div>
{body}
<script>{JS}</script></body></html>"""


BODY = open(HERE / "body.html").read() if (HERE / "body.html").exists() else ""

if __name__ == "__main__":
    entries, unverified = load_bib()
    BODY = (HERE / "body.html").read_text()
    out = page(entries, unverified)
    (HERE / "index.html").write_text(out)
    print(f"index.html written: {len(out)} bytes, {len(entries)} verified unique sources, {unverified} unverified excluded, "
          f"verification pass: {VERIFY_STATS['dropped']} dropped, {VERIFY_STATS['marked']} marked †, {VERIFY_STATS['via']} via secondary ‡")
