#!/usr/bin/env python3
"""The ETT programme's blueprint site: reports/blueprint/index.html, generated from the programme's files.

    python3 build.py            write index.html beside this file
    python3 build.py --out F    write F instead (the reproducibility check builds twice and compares)

Inputs, all read, none written:
  * programme/ladder.toml          through tools/ladder.py: check, closure, refuted, matrix, and
                                   emitted (which edges emit-lean makes rules) when the tool has it
  * papers/*/certificate/binder.toml  through tools/binder.py: binders, check
  * programme/roadmap.toml         through tools/roadmap.py: load, check, open_questions
  * papers/<slug>/ledger/ledger.json  row kind, title, file and line; the statement text is read from
                                   the ledger's labeled source at its tex_span (as the atlas does)
  * papers/<slug>/legacy/MANIFEST.json  the edition of each bound paper
  * programme/README.md            the names of the layers
  * registers/DECISIONS.md         the status and text of the OQ rows a blocked target waits on
  * lean-causal/Causal/**/*.lean   where each Lean name is declared (read as text; no Lean is run)

Every number on the page is counted here or in the page's script from these files; nothing is typed.
The output is deterministic: no clock, no environment, every set sorted, so two builds of the same
inputs give the same bytes (`make -C reports/blueprint check`).

The ladder's `under` is shown on its edge. tools/ladder.py's closure chains an edge with `under` as if
it were unconditional; this page classifies the same pairs, then splits off those classified only
through such an edge (closure recomputed without them) and marks them conditional.
"""
import glob
import hashlib
import json
import os
import re
import sys
import tomllib

sys.dont_write_bytecode = True   # nothing written beside the sources, here or in tools/

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import binder as bd   # noqa: E402
import ladder as ld   # noqa: E402
import roadmap as rm  # noqa: E402

LADDER = os.path.join(ROOT, "programme", "ladder.toml")
ROADMAP = os.path.join(ROOT, "programme", "roadmap.toml")
README = os.path.join(ROOT, "programme", "README.md")
DECISIONS = os.path.join(ROOT, "registers", "DECISIONS.md")
LEAN_ROOT = os.path.join(ROOT, "lean-causal")
CONDITION_KEYS = ("under",)          # an edge carrying one of these is conditional
SORT_KEY, DEFAULT_SORT = "sort", "causality"   # programme/ladder.toml's header: no `sort` means causality
EDGE_KEYS = {"from", "to", "witness", "status", "under", "at", "statement", "note", "id", "lean", "label", "what"}
TEX_MAX = 1600


def rel(p):
    return os.path.relpath(p, ROOT)


def sha(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


# ------------------------------------------------------------------ Lean names -> file:line
DECL_LINE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*"
                       r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+([^\s(:{\[]+)")
NS_OPEN = re.compile(r"^\s*namespace\s+(\S+)")
SEC_OPEN = re.compile(r"^\s*(?:noncomputable\s+)?section\b(?:\s+(\S+))?")
SCOPE_END = re.compile(r"^\s*end\b(?:\s+(\S+))?\s*$")


def lean_index(root=LEAN_ROOT):
    """Fully qualified name -> 'lean-causal/Causal/X.lean:N', with namespaces tracked line by line."""
    out = {}
    for f in sorted(glob.glob(os.path.join(root, "Causal", "**", "*.lean"), recursive=True)):
        stack, depth = [], 0
        for n, line in enumerate(open(f, encoding="utf-8", errors="replace").read().split("\n"), 1):
            if depth:                                  # inside a block comment
                depth += line.count("/-") - line.count("-/")
                depth = max(depth, 0)
                continue
            s = line.lstrip()
            if s.startswith("/-"):
                depth = max(line.count("/-") - line.count("-/"), 0)
                if depth:
                    continue
            if s.startswith("--"):
                continue
            m = NS_OPEN.match(line)
            if m:
                stack.append(("ns", m[1]))
                continue
            m = SEC_OPEN.match(line)
            if m and not s.startswith("section_"):
                stack.append(("sec", m[1] or ""))
                continue
            if SCOPE_END.match(line):
                if stack:
                    stack.pop()
                continue
            m = DECL_LINE.match(line)
            if m:
                name = m[1]
                if name.startswith("_root_."):
                    full = name[len("_root_."):]
                else:
                    full = ".".join([x for k, x in stack if k == "ns"] + [name])
                out.setdefault(full, "%s:%d" % (rel(f), n))
    return out


def lean_locate(name, index, by_last):
    """(location or '', how): exact, suffix (tools/ladder.py's rule), or ''."""
    if name in index:
        return index[name], "exact"
    cands = sorted(c for c in by_last.get(name.split(".")[-1], ())
                   if c.endswith("." + name) or name.endswith("." + c))
    if cands:
        return index[cands[0]], "suffix" if len(cands) == 1 else "suffix, %d candidates" % len(cands)
    return "", ""


# ------------------------------------------------------------------ TeX of a ledger row
def tex_clean(s):
    s = re.sub(r"(?m)(?<!\\)%.*$", "", s)
    s = re.sub(r"\\label\{[^}]*\}", "", s)
    out, i = [], 0
    while i < len(s):                                 # \index{...} with nested braces
        if s.startswith("\\index{", i):
            d, j = 0, i + len("\\index")
            while j < len(s):
                d += {"{": 1, "}": -1}.get(s[j], 0)
                j += 1
                if d == 0:
                    break
            i = j
            continue
        out.append(s[i])
        i += 1
    s = "".join(out)
    # text-mode boxes inside display math (\parbox in an equation) are not math: unwrap them
    def unbox(m):
        body = m[2]
        if "\\parbox" not in body:
            return m[0]
        res, i = [], 0
        while True:
            j = body.find("\\parbox", i)
            if j < 0:
                break
            k = body.find("{", j)
            _, k = braced(body, k)                     # the width
            txt, i = braced(body, body.find("{", k))   # the text
            res.append(txt or "")
        return "\n\n" + "\n\n".join(res) + "\n\n"
    s = re.sub(r"\\begin\{(equation\*?|displaymath)\}(.*?)\\end\{\1\}", unbox, s, flags=re.S)
    s = re.sub(r"\\(?:noindent|medskip|smallskip|bigskip)\b\s*|\\[hv]space\*?\{[^}]*\}", " ", s)
    return re.sub(r"\n{3,}", "\n\n", s).strip()


def braced(s, i):
    d = 0
    for j in range(i, len(s)):
        if s[j] == "{":
            d += 1
        elif s[j] == "}":
            d -= 1
            if d == 0:
                return s[i + 1:j], j + 1
    return None, len(s)


def tex_macros(files):
    """\\newcommand, \\def, \\DeclareMathOperator of the given files, for MathJax (the atlas's reading)."""
    mac = {}
    for fp in files:
        try:
            s = open(fp, encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        s = re.sub(r"(?m)(?<!\\)%.*$", "", s)
        for m in re.finditer(r"\\(?:re)?newcommand\*?\s*\{?\\([A-Za-z]+)\}?\s*(?:\[(\d)\])?\s*(?:\[[^\]]*\])?\s*(?=\{)", s):
            body, _ = braced(s, m.end())
            if body is None or len(body) > 200:
                continue
            body = body.replace("\\ensuremath", "").replace("\\xspace", "")
            mac[m[1]] = [body, int(m[2])] if m[2] else body
        for m in re.finditer(r"\\DeclareMathOperator\*?\s*\{?\\([A-Za-z]+)\}?\s*(?=\{)", s):
            body, _ = braced(s, m.end())
            if body is not None:
                mac[m[1]] = "\\operatorname{" + body + "}"
        for m in re.finditer(r"\\def\\([A-Za-z]+)\s*(?=\{)", s):
            body, _ = braced(s, m.end())
            if body is not None and len(body) < 200:
                mac.setdefault(m[1], body)
    for bad in ("section", "label", "ref", "cite", "emph", "textbf", "begin", "end", "item", "newline", "index"):
        mac.pop(bad, None)
    return dict(sorted(mac.items()))


class Ledger:
    """One paper's ledger.json, with its rows' statement text read off the labeled source."""

    def __init__(self, slug):
        self.slug = slug
        self.path = os.path.join(ROOT, "papers", slug, "ledger", "ledger.json")
        self.ok = os.path.exists(self.path)
        self.rows, self.macros, self.src = {}, {}, {}
        if not self.ok:
            return
        L = json.load(open(self.path, encoding="utf-8"))
        root = L["paper"]["root"]
        if not os.path.isdir(root):
            root = os.path.join(ROOT, "papers", slug, "legacy", "labeled")
        self.root, self.files, self.document = root, L["paper"].get("files", []), L["paper"].get("document", "")
        for f in self.files:
            p = os.path.join(root, f)
            if f.endswith(".tex") and os.path.exists(p):
                self.src[f] = open(p, encoding="utf-8", errors="replace").read().split("\n")
        self.order = [r["label"] for r in L["statements"]]
        for r in L["statements"]:
            self.rows[r["label"]] = r
        self.macros = tex_macros(sorted(glob.glob(os.path.join(root, "*.tex")) + glob.glob(os.path.join(root, "*.sty"))))

    def row(self, label):
        r = self.rows.get(label)
        if not r:
            return None
        tex = ""
        lines = self.src.get(r.get("file"))
        if lines and r.get("tex_span"):
            a, b = r["tex_span"]
            tex = tex_clean("\n".join(lines[a - 1:b]))
            if len(tex) > TEX_MAX:
                tex = tex[:TEX_MAX] + " …"
        return {"kind": r.get("kind") or "", "number": r.get("number") or "", "title": r.get("title") or "",
                "file": r.get("file") or "", "line": r.get("line"), "proof": r.get("proof") or "",
                "nl": r.get("nl_status") or "", "lean": r.get("lean_proved") or "", "decls": r.get("decls") or [],
                "deps": [d for d in r.get("deps") or [] if d != label], "tex": tex}

    def title(self):
        lines = self.src.get(self.document) or []
        text = "\n".join(lines[:400])
        m = re.search(r"\\title\{", text)
        if not m:
            return ""
        t, _ = braced(text, m.end() - 1)
        t = re.sub(r"\\thanks\{[^}]*\}", "", t or "")
        return re.sub(r"\s+", " ", re.sub(r"\\[a-zA-Z]+\*?|[{}$]", "", t)).strip()


# ------------------------------------------------------------------ the ladder
def conditional(e):
    return any(str(e.get(k) or "").strip() for k in CONDITION_KEYS)


def extras(e):
    return {k: e[k] for k in sorted(e) if k not in EDGE_KEYS}


def derive(start, target, implies):
    """Edge indices deriving `target` from {start}: forward chaining, unconditional edges to a fixpoint
    before each conditional one, so a derivation uses a conditional edge only when it must."""
    have = {start: None}
    order = []
    while True:
        changed = True
        while changed:
            changed = False
            for i, e in enumerate(implies):
                if not e["cond"] and e["to"] not in have and all(x in have for x in e["from"]):
                    have[e["to"]] = i
                    order.append(i)
                    changed = True
        if target in have:
            break
        nxt = next((i for i, e in enumerate(implies)
                    if e["cond"] and e["to"] not in have and all(x in have for x in e["from"])), None)
        if nxt is None:
            break
        have[implies[nxt]["to"]] = nxt
        order.append(nxt)
    if target not in have:
        return None
    need, stack = set(), [target]
    while stack:
        x = stack.pop()
        i = have.get(x)
        if i is None or i in need:
            continue
        need.add(i)
        stack.extend(implies[i]["from"])
    return [i for i in order if i in need]


def ladder_block(lindex, by_last, ett):
    data = ld.load(LADDER)
    errs = sorted(ld.check(data))
    props = data.get("property", [])
    ids = [p.get("id") for p in props]

    def loc(name):
        return lean_locate(name, lindex, by_last)[0] if name else ""
    P = []
    for p in props:
        P.append({"id": p.get("id"), "lean": p.get("lean", ""), "leanloc": loc(p.get("lean")),
                  "label": p.get("label", ""), "what": p.get("what", ""), "sort": p.get(SORT_KEY) or DEFAULT_SORT,
                  "extra": {k: v for k, v in extras(p).items() if k != SORT_KEY},
                  "ett": ett.row(p["label"]) if p.get("label") else None})
    # Which implications `tools/ladder.py emit-lean` makes `causal_ladder` rules, when the tool says so
    # (ladder.emitted, read off the sources; absent from older versions of the tool).
    emit, emit_note = {}, ""
    if hasattr(ld, "emitted"):
        try:
            rules, skipped = ld.emitted(data)
            for e, mod in rules:
                emit[id(e)] = {"rule": True, "module": mod}
            for e, why in skipped:
                emit[id(e)] = {"rule": False, "why": why}
        except Exception as ex:
            emit_note = "tools/ladder.py emitted() failed: %s: %s" % (type(ex).__name__, ex)
    I = []
    for e in data.get("implies", []):
        I.append({"from": list(e.get("from", [])), "to": e.get("to"), "witness": e.get("witness", ""),
                  "loc": loc(e.get("witness")), "status": e.get("status", ""), "under": e.get("under", ""),
                  "cond": conditional(e), "extra": extras(e), "emit": emit.get(id(e))})
    F = [{"from": e.get("from"), "to": e.get("to"), "witness": e.get("witness", ""), "loc": loc(e.get("witness")),
          "status": e.get("status", ""), "under": e.get("under", ""), "cond": conditional(e), "extra": extras(e)}
         for e in data.get("fails", [])]
    C = [{"at": e.get("at"), "statement": e.get("statement", ""), "witness": e.get("witness", ""),
          "loc": loc(e.get("witness")), "status": e.get("status", ""), "under": e.get("under", ""), "extra": extras(e)}
         for e in data.get("consequence", [])]
    O = [{"from": e.get("from"), "to": e.get("to"), "note": e.get("note", ""), "extra": extras(e)}
         for e in data.get("open", [])]

    pairs, summary = {}, None
    sort_of = {p["id"]: p["sort"] for p in P}
    try:
        m = ld.matrix(data)
        clo = ld.closure(data)
        plain = dict(data, implies=[e for e in data.get("implies", []) if not conditional(e)])
        clo0 = ld.closure(plain)
        bad0 = ld.refuted(data, clo0)
        opens = {}
        for k, o in enumerate(data.get("open", [])):
            opens.setdefault((o.get("from"), o.get("to")), k)
        for a in ids:
            for b in ids:
                if a == b:
                    continue
                v = m[(a, b)]
                if v == "implied":
                    d = derive(a, b, I)
                    assert d is not None, "no derivation for an implied pair %s => %s" % (a, b)
                    pairs[a + "|" + b] = {"c": "implied" if b in clo0[a] else "implied-c", "d": d}
                elif v == "fails":
                    for k, f in enumerate(data.get("fails", [])):
                        if a in clo.get(f["from"], ()) and f["to"] in clo.get(b, ()):
                            pairs[a + "|" + b] = {"c": "fails" if (a, b) in bad0 else "fails-c", "f": k,
                                                  "da": derive(f["from"], a, I) or [], "db": derive(b, f["to"], I) or []}
                            break
                    else:
                        raise AssertionError("no counterexample for a refuted pair %s, %s" % (a, b))
                elif v == "open":
                    pairs[a + "|" + b] = {"c": "open", "o": opens[(a, b)]}
                elif sort_of[a] != sort_of[b]:
                    pairs[a + "|" + b] = {"c": "cross"}     # ladder.py says unknown; the two sorts do not compare
                else:
                    pairs[a + "|" + b] = {"c": "unknown"}
        cnt = {}
        for v in pairs.values():
            cnt[v["c"]] = cnt.get(v["c"], 0) + 1
        summary = {"pairs": len(pairs), "classified": sum(v for k, v in cnt.items() if k not in ("unknown", "cross")),
                   "within": len(pairs) - cnt.get("cross", 0),
                   **{k.replace("-", "_"): cnt.get(k, 0) for k in ("implied", "implied-c", "fails", "fails-c", "open", "unknown", "cross")}}
    except Exception as ex:   # a ladder mid-edit: the page still shows the file and the checker's verdict
        errs.append("the pair classification could not be computed: %s: %s" % (type(ex).__name__, ex))
    line = "%d properties, %d implications, %d counterexamples, %d consequences; %s" % (
        len(props), len(I), len(F), len(C),
        "%d violation(s)" % len(errs) if errs else "%d of %d ordered pairs classified" % (summary["classified"], summary["pairs"]))
    sorts = []
    for p in P:
        if p["sort"] not in sorts:
            sorts.append(p["sort"])
    return {"props": P, "implies": I, "fails": F, "cons": C, "open": O, "pairs": pairs, "summary": summary,
            "errors": errs, "line": line, "conditionKeys": list(CONDITION_KEYS), "sorts": sorts,
            "sortKey": SORT_KEY, "defaultSort": DEFAULT_SORT, "emitKnown": hasattr(ld, "emitted") and not emit_note,
            "emitNote": emit_note}


# ------------------------------------------------------------------ binders
LEMMA_HEAD = re.compile(r"^((?:Def|Definition|Thm|Theorem|Lemma|Cor|Corollary|Prop|Proposition|Remark|Rem|"
                        r"Conjecture|Conj|Example|Claim)\.?\s+[0-9]+(?:\.[0-9]+)*)\b")


def binder_block(lindex, by_last, ladder_ids, target_ids, ledgers):
    out = []
    names = ld.lean_names()
    for slug, b in sorted(bd.binders().items()):
        led = ledgers.setdefault(slug, Ledger(slug))
        errs = sorted(bd.check(slug, b, names, ladder_ids, target_ids))

        def ref(x):
            if x.startswith("T-"):
                return {"x": x, "t": "target" if x in target_ids else "missing"}
            if ld.resolves(x, names):
                where, how = lean_locate(x, lindex, by_last)
                return {"x": x, "t": "lean", "loc": where, "how": how}
            return {"x": x, "t": "missing"}
        rows = []
        for r in b.get("bind", []):
            lab = r.get("label", "")
            m = LEMMA_HEAD.match(r.get("note", ""))
            rows.append({"label": lab, "ref": m[1] if m else "", "ledger": led.row(lab),
                         "ett": [ref(x) for x in r.get("ett", [])],
                         "loc": list(r.get("localisation", [])), "open": list(r.get("open_localisation", [])),
                         "open_reason": r.get("open_reason", ""), "note": r.get("note", ""),
                         "geo": [{"model": g.get("model", ""), "proves": list(g.get("proves", [])),
                                  "by": [ref(x) for x in g.get("by", [])],
                                  "extra": {k: g[k] for k in sorted(g) if k not in ("model", "proves", "by")}}
                                 for g in r.get("geometric", [])],
                         "extra": {k: r[k] for k in sorted(r) if k not in ("label", "ett", "localisation", "open_localisation",
                                                                          "open_reason", "note", "geometric")}})
        bound = {r["label"] for r in rows}
        unbound = [dict(led.row(l), label=l) for l in led.order if l not in bound] if led.ok else []
        man = os.path.join(ROOT, "papers", slug, "legacy", "MANIFEST.json")
        edition = json.load(open(man, encoding="utf-8")).get("edition", "") if os.path.exists(man) else ""
        other = {k: b[k] for k in sorted(b) if k not in ("bind", "proposed")}
        out.append({"slug": slug, "title": led.title() if led.ok else "", "edition": edition,
                    "document": led.document if led.ok else "", "ledgerRows": len(led.order) if led.ok else 0,
                    "rows": rows, "unbound": unbound,
                    "proposed": [dict(p, leanloc=lean_locate(p.get("lean", ""), lindex, by_last)[0]
                                      if p.get("lean") and " " not in p.get("lean", "") else "")
                                 for p in b.get("proposed", [])],
                    "other": other, "errors": errs, "macros": led.macros,
                    "path": rel(os.path.join(ROOT, "papers", slug, "certificate", "binder.toml"))})
    return out


# ------------------------------------------------------------------ roadmap, layers, OQ rows
def layers():
    """The four layers as programme/README.md numbers and names them."""
    out, cur = [], None
    for line in open(README, encoding="utf-8"):
        m = re.match(r"^(\d+)\.\s+\*\*(.+?)\*\*\s*(.*)$", line)
        if m:
            cur = {"n": int(m[1]), "title": m[2].rstrip("."), "text": m[3].strip()}
            out.append(cur)
        elif cur and line.startswith("   ") and line.strip():
            cur["text"] = (cur["text"] + " " + line.strip()).strip()
        else:
            cur = None
    for x in out:
        x["text"] = re.sub(r"\*\*|`", "", x["text"])
    return out


def oq_rows(wanted):
    out = {}
    if not os.path.exists(DECISIONS):
        return out
    status = rm.open_questions(ROOT)
    for line in open(DECISIONS, encoding="utf-8"):
        m = re.match(r"^\|\s*(OQ-\d+)\s*\|\s*([^|]*)\|(.*)\|\s*([^|]*)\|\s*([^|]*)\|\s*$", line)
        if m and m[1] in wanted:
            out[m[1]] = {"date": m[2].strip(), "text": m[3].strip(), "where": m[4].strip(),
                         "status": status.get(m[1], m[5].strip())}
    return out


def roadmap_block():
    data = rm.load(ROADMAP)
    errs = sorted(rm.check(data, ROOT))
    targets = data.get("target", [])
    oqs = oq_rows({t.get("oq") for t in targets if t.get("oq")})
    return {"targets": targets, "errors": errs, "known_red": data.get("gates", {}).get("known_red", []),
            "statuses": list(rm.STATUS), "oqs": oqs}


# ------------------------------------------------------------------ assemble
def main(argv):
    out_path = argv[argv.index("--out") + 1] if "--out" in argv else os.path.join(HERE, "index.html")
    lindex = lean_index()
    by_last = {}
    for n in lindex:
        by_last.setdefault(n.split(".")[-1], []).append(n)
    ledgers = {"ett": Ledger("ett")}
    L = ladder_block(lindex, by_last, ledgers["ett"])
    R = roadmap_block()
    ladder_ids = {p["id"] for p in L["props"]}
    target_ids = {t.get("id") for t in R["targets"]}
    B = binder_block(lindex, by_last, ladder_ids, target_ids, ledgers)
    inputs = [LADDER, ROADMAP, README, DECISIONS] + [os.path.join(ROOT, b["path"]) for b in B] + sorted(
        ld_.path for ld_ in ledgers.values() if ld_.ok) + sorted(
        p for p in (os.path.join(ROOT, "papers", b["slug"], "legacy", "MANIFEST.json") for b in B) if os.path.exists(p))
    prov = {"inputs": [{"path": rel(p), "sha256": sha(p)} for p in inputs],
            "leanCommit": {s: (json.load(open(l.path, encoding="utf-8")).get("lean") or {}).get("git_commit", "")
                           for s, l in sorted(ledgers.items()) if l.ok},
            "leanDecls": len(lindex)}
    DATA = {"ladder": L, "binders": B, "road": R, "layers": layers(), "ettMacros": ledgers["ett"].macros, "prov": prov}
    blob = json.dumps(DATA, ensure_ascii=False, separators=(",", ":"), default=str).replace("</", "<\\/")
    tpl = open(os.path.join(HERE, "template.html"), encoding="utf-8").read()
    assert tpl.count("__DATA__") == 1, "template.html must hold __DATA__ exactly once"
    page = tpl.replace("__DATA__", blob)
    with open(out_path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(page)
    s = L["summary"] or {}
    print("blueprint: %s (%d bytes); ladder: %s; binders: %s; roadmap: %d targets%s" % (
        rel(out_path) if out_path.startswith(ROOT) else out_path, len(page.encode("utf-8")), L["line"],
        ", ".join("%s %d rows" % (b["slug"], len(b["rows"])) for b in B), len(R["targets"]),
        "".join("; %s: %d violation(s)" % (k, n) for k, n in (("ladder", len(L["errors"])),
                ("binders", sum(len(b["errors"]) for b in B)), ("roadmap", len(R["errors"]))) if n)))
    if s.get("implied_c"):
        print("blueprint: %d implied pair(s) only through an edge with `under`" % s["implied_c"])


if __name__ == "__main__":
    main(sys.argv[1:])
