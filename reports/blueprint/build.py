#!/usr/bin/env python3
"""The ETT programme's blueprint site: reports/blueprint/index.html, generated from the programme's files.

    python3 build.py              write index.html beside this file
    python3 build.py --out F      write F instead (the reproducibility check builds twice and compares)
    python3 build.py --ladder L   read the ladder from L instead of programme/ladder.toml (as
                                  `tools/ladder.py check --file L` does): a trial ladder drawn into a
                                  page of its own, with --out; the repository's page is built from
                                  programme/ladder.toml only

Inputs, all read, none written:
  * programme/ladder.toml          through tools/ladder.py only (below); --ladder L reads L instead
  * papers/*/certificate/binder.toml  through tools/binder.py: binders, check
  * programme/roadmap.toml         through tools/roadmap.py: load, check, open_questions
  * papers/<slug>/ledger/ledger.json  row kind, title, file and line; the statement text is read from
                                   the ledger's labeled source at its tex_span (as the atlas does)
  * papers/<slug>/legacy/MANIFEST.json  the edition of each bound paper
  * programme/README.md            the names of the layers
  * registers/DECISIONS.md         the status and text of the OQ rows a blocked target waits on
  * lean-causal/Causal/**/*.lean   through tools/ladder.py's lean_index (which names exist, and in
                                   which module); read here as text only for the line of each name

The ladder is evaluated by tools/ladder.py and by nothing else on this page:
  * check, summary, check_line   the violations, the counts and the summary line `ladder.py check`
                                 prints, verbatim;
  * matrix                       the class of every ordered pair (ill-typed, implied, fails, open,
                                 fails-off, implied-standing, unknown), verbatim;
  * ambient, standing, valid, space, on_ambient, vocab_closure, STANDING
                                 the ambient space, each edge's standing words, a counterexample's
                                 space and whether it is one of the ambient's, the vocabulary of words;
  * off_spaces                   the spaces (word lists) of the counterexamples off the ambient that
                                 refute a pair the matrix calls fails-off;
  * counterexample, edges_on, closure, needed_standing, _saturate
                                 what a counterexample has and lacks (read forwards and, through
                                 conjunctive edges, backwards), which edges are valid on a space,
                                 and the saturation through them;
  * facts_on, _start             the [[fact]]s valid on a space (a property holding outright on its
                                 sort's objects) and what a space has before any edge;
  * _transfer_sides              which causality of a [[transfer]] is its source;
  * emitted                      which implications emit-lean makes rules of causal_ladder.
What the page adds is presentation: for a pair the matrix calls implied (or a counterexample's
reading: of a fails pair, the counterexamples on the ambient, those off it listed apart; of a
fails-off pair, those off it, whose spaces must be the ones off_spaces names), an irredundant set
of the edges the tool's own saturation used, found by dropping edges while tools/ladder.py's
_saturate still reaches the target from tools/ladder.py's _start (so a derivation is a witness chain
the tool accepts, never a second closure), with the facts it starts from; and, at a nesting, the
transfers recorded along a nesting it implies or is implied by, read through tools/ladder.py's
closure as its transfer check reads them.
A counterexample lacks an id either forwards (the id implies its `to` on its space: a chain as above)
or backwards (T-tool-ladder-py-2). A backward lack is explained from the edges tools/ladder.py's
counterexample() needs for it: edges are dropped, latest first, while counterexample() on the ladder
with the remaining edges still lacks the id; on those edges and counterexample()'s own has and lacks,
each step is an edge whose conclusion it lacks and all of whose premises but one it has, so it lacks
the remaining one, and every id implying it. Every id counterexample() puts in `lacks` must be so
explained, or the build fails; nothing is put in `lacks` here.
A [[transfer]] with a witness and `under` is conditional, as tools/ladder.py's contradiction check
reads it (it applies `t.get("witness") and not t.get("under")` only).

Every number on the page is counted here or in the page's script from these files; nothing is typed.
The output is deterministic: no clock, no environment, every set sorted, so two builds of the same
inputs give the same bytes (`make -C reports/blueprint check`).
"""
import glob
import hashlib
import json
import os
import re
import sys

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
TOOLS = [os.path.join(ROOT, "tools", x) for x in ("ladder.py", "binder.py", "roadmap.py")]
TEX_MAX = 1600


def rel(p):
    return os.path.relpath(p, ROOT)


def sha(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


# ------------------------------------------------------------------ Lean names -> file:line
# Which names exist, and in which module, is tools/ladder.py's lean_index (namespace-exact, as check
# and tools/binder.py resolve them). The line is read here: the first declaration of that full name in
# that module's file, namespaces tracked line by line; when this scan does not find it there, the
# location is the file alone.
DECL_LINE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|partial|unsafe|nonrec)\s+)*"
                       r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\s+([^\s(:{\[⦃]+)")
NS_OPEN = re.compile(r"^\s*namespace\s+(\S+)")
SEC_OPEN = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:public|private|noncomputable)\s+)*section\b(?:\s+(\S+))?")
SCOPE_END = re.compile(r"^\s*end\b(?:\s+(\S+))?\s*$")


def module_file(mod):
    return rel(os.path.join(LEAN_ROOT, *mod.split("."))) + ".lean"


def decl_lines(path):
    """Fully qualified name -> line, for the declarations of one Lean file."""
    out, stack, depth = {}, [], 0
    for n, line in enumerate(open(path, encoding="utf-8", errors="replace").read().split("\n"), 1):
        if depth:                                  # inside a block comment
            depth = max(depth + line.count("/-") - line.count("-/"), 0)
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
            stack.extend(("ns", x) for x in m[1].split("."))
            continue
        m = SEC_OPEN.match(line)
        if m and not s.startswith("section_"):
            stack.extend(("sec", x) for x in (m[1].split(".") if m[1] else [""]))
            continue
        m = SCOPE_END.match(line)
        if m:
            for _ in (m[1].split(".") if m[1] else [""]):
                if stack:
                    stack.pop()
            continue
        m = DECL_LINE.match(line)
        if m:
            name = m[1]
            full = name[len("_root_."):] if name.startswith("_root_.") else ".".join(
                [x for k, x in stack if k == "ns"] + [name])
            out.setdefault(full, n)
    return out


class Lean:
    """The names of lean-causal/Causal as tools/ladder.py resolves them, with a file:line for each."""

    def __init__(self):
        self.index = ld.lean_index()
        self.decls = self.index["decls"]
        self.names = ld.lean_names()
        self._lines = {}

    def resolves(self, name):
        return ld.resolves(name, self.names)

    def locate(self, name):
        if not isinstance(name, str) or not self.resolves(name):
            return ""
        f = module_file(self.decls[name])
        if f not in self._lines:
            p = os.path.join(ROOT, f)
            self._lines[f] = decl_lines(p) if os.path.exists(p) else {}
        n = self._lines[f].get(name)
        return "%s:%d" % (f, n) if n else f


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



# ------------------------------------------------------------------ the ladder, through tools/ladder.py
# The keys of each table the page shows in their own place; any other key is shown as it is written.
SHOWN = {
    "property": {"id", "lean", "what", "label", "sort"},
    "implies": {"from", "to", "witness", "status", "under", "standing"},
    "fails": {"from", "to", "witness", "status", "space"},
    "consequence": {"at", "statement", "witness", "status", "under", "standing"},
    "open": {"from", "to", "note"},
    "transfer": {"pair", "property", "direction", "narrower", "wider", "witness", "counterexample",
                 "status", "under", "standing", "space"},
    "fact": {"property", "witness", "status", "standing", "note"},
}


def extras(kind, e):
    return {k: e[k] for k in sorted(e) if k not in SHOWN[kind]}


def ids(x):
    """tools/ladder.py's reading of an id or a list of ids (a malformed value reads as none)."""
    return ld.ids_of(x) or []


def words(x):
    return list(x) if isinstance(x, list) else []


class Derive:
    """Witness chains for what tools/ladder.py decides: an irredundant subset of the edges valid on a
    space through which the tool's saturation reaches the target, in an order in which every edge's
    premises are already had. Edges are dropped latest first, so the chain keeps the earliest edges
    of programme/ladder.toml. A target the tool's saturation does not reach is an error: a pair the
    matrix decides always has a chain here, or the build fails."""

    def __init__(self, data):
        self.implies = data.get("implies", [])
        self.at = {id(e): i for i, e in enumerate(self.implies)}
        self.memo = {}

    def __call__(self, src, target, edges):
        src = frozenset(src)
        key = (src, target, tuple(self.at[id(e)] for e in edges))
        if key in self.memo:
            return self.memo[key]
        if target in src:
            self.memo[key] = []
            return []
        if target not in ld._saturate(src, edges):
            raise AssertionError("tools/ladder.py does not reach %s from %s through the edges given" % (
                target, " ∧ ".join(sorted(src))))
        keep = list(edges)
        for e in reversed(list(edges)):
            trial = [x for x in keep if x is not e]
            if target in ld._saturate(src, trial):
                keep = trial
        have, order, rest = set(src), [], list(keep)
        while rest:
            e = next((x for x in rest if set(ids(x.get("from"))) <= have), None)
            if e is None:
                raise AssertionError("an irredundant chain to %s does not fire in order" % target)
            order.append(self.at[id(e)])
            have.add(e.get("to"))
            rest.remove(e)
        self.memo[key] = order
        return order


class Reading:
    """Chains on a space with its facts, and why a counterexample lacks what tools/ladder.py says it
    lacks. Every set read here is the tool's: counterexample()'s has and lacks, closure() on the
    counterexample's space, facts_on() and _start(); a step is shown only between ids the tool
    puts in them, so the page never claims more than the tool reads."""

    def __init__(self, data, derive):
        self.data, self.derive, self.sort = data, derive, ld.sort_of(data)
        self.implies, self.facts = data.get("implies", []), data.get("fact", [])
        self.fails = data.get("fails", [])
        self.at = {id(e): i for i, e in enumerate(self.implies)}
        self.cache, self.read_memo, self.lack_memo, self.clo_memo = {}, {}, {}, {}

    def chain(self, src, target, on, edges):
        """(edge indices, fact indices): a chain from `src` with the facts valid on `on` (the tool's
        _start) to `target` through `edges`, and the facts it uses (the target or a premise)."""
        on = frozenset(on)
        start = ld._start(list(src), ld.facts_on(self.data, on), self.sort)
        order = self.derive(start, target, edges)
        extra = start - set(src)
        used = extra & ({target} | {x for i in order for x in ids(self.implies[i].get("from"))})
        return order, [j for j, r in enumerate(self.facts) if r.get("property") in used and ld.valid(r, on)]

    def read(self, k):
        if k not in self.read_memo:
            self.read_memo[k] = ld.counterexample(self.data, self.fails[k], self.cache)
        return self.read_memo[k]

    def forward(self, k, y):
        """Does counterexample k lack y forwards (y implies its `to` on its space, tools/ladder.py's closure)?"""
        f = self.fails[k]
        on = ld.space(f, self.data)
        if on not in self.clo_memo:
            self.clo_memo[on] = ld.closure(self.data, on)
        return f.get("to") in self.clo_memo[on].get(y, ())

    def lack(self, k, y):
        """Why counterexample k lacks y: {"d", "fd": the chain from y to the root r it implies, "r",
        "bk": the backward steps from its `to` up to r} (no "bk" when y implies `to`)."""
        key = (k, y)
        if key in self.lack_memo:
            return self.lack_memo[key]
        f, data = self.fails[k], self.data
        on = ld.space(f, data)
        edges = ld.edges_on(data, on)
        if y not in self.read(k)[1]:
            raise AssertionError("tools/ladder.py's counterexample %s does not lack %s" % (f.get("witness"), y))
        to = f.get("to")
        if self.forward(k, y):
            d, fd = self.chain([y], to, on, edges)
            out = {"d": d, "fd": fd, "r": to}
        else:
            # the edges counterexample() needs to lack y: dropped latest first while it still lacks y
            keep = list(edges)
            for e in reversed(list(edges)):
                trial = [x for x in keep if x is not e]
                if y in ld.counterexample(dict(data, implies=trial), f)[1]:
                    keep = trial
            out = self.backward(k, on, keep, y)
        self.lack_memo[key] = out
        return out

    def backward(self, k, on, edges, y):
        f = self.fails[k]
        d = dict(self.data, implies=edges)
        has, lacks = ld.counterexample(d, f)
        clo = ld.closure(d, on)
        to = f.get("to")
        root = {x: to for x in sorted(lacks) if to in clo[x]}   # x implies `to`: lacked forwards
        made = {}                                               # x -> (the edge, its conclusion)
        changed = True
        while y not in root and changed:
            changed = False
            for e in edges:
                frm = ids(e.get("from"))
                if len(frm) < 2 or e.get("to") not in root:
                    continue
                miss = [x for x in frm if x not in has]
                if len(miss) == 1 and miss[0] in lacks and miss[0] not in made and miss[0] != to:
                    x = miss[0]
                    made[x] = (e, e.get("to"))
                    changed = True
                    for z in sorted(lacks):
                        if z not in root and x in clo[z]:
                            root[z] = x
        if y not in root:
            raise AssertionError("tools/ladder.py's counterexample %s (without %s) lacks %s, and the edges it needs "
                                 "for that (%s) explain it neither forwards nor backwards" % (
                                     f.get("witness"), to, y, ", ".join(str(self.at[id(e)]) for e in edges) or "none"))
        steps, r = [], root[y]
        while r != to:
            e, c = made[r]
            frm = ids(e.get("from"))
            dc, fc = self.chain([c], root[c], on, edges)
            hp = []
            for p in frm:
                if p != r:
                    hd, hf = self.chain(ids(f.get("from")), p, on, edges)
                    hp.append({"p": p, "d": hd, "fx": hf})
            steps.append({"e": self.at[id(e)], "x": r, "c": c, "r": root[c], "dc": dc, "fc": fc, "hp": hp})
            r = root[c]
        steps.reverse()
        dy, fy = self.chain([y], root[y], on, edges)
        return {"d": dy, "fd": fy, "r": root[y], "bk": steps, "edges": sorted(self.at[id(e)] for e in edges)}


def needed_with_facts(data, a, b, every, amb):
    """tools/ladder.py's needed_standing for a pair implied under standing, the facts of a's sort
    counted as premise-free steps from a with their own standing (needed_standing reads edges only);
    the words are then checked against tools/ladder.py's closure on the space they give."""
    sort = ld.sort_of(data)
    fe = [{"from": [a], "to": r.get("property"), "standing": ld.standing(r)} for r in data.get("fact", [])
          if sort.get(r.get("property")) is not None and sort.get(r.get("property")) == sort.get(a)]
    need = ld.needed_standing((a,), b, list(every) + fe, amb)
    on = ld.vocab_closure(set(need) | amb)
    if b not in ld.closure(data, on).get(a, ()):
        raise AssertionError("tools/ladder.py does not reach %s from %s on %s" % (b, a, ", ".join(sorted(on))))
    return need, on


def space_block(e, data, amb):
    """A counterexample's space (its `space`, or the ambient), as tools/ladder.py closes it."""
    on = ld.space(e, data)
    return {"space": words(e.get("space")) if "space" in e else None, "spaceWords": sorted(on),
            "lacksAmbient": sorted(amb - on), "onAmbient": ld.on_ambient(e, data)}


def ladder_block(lean, ett, path=LADDER):
    data = ld.load(path)
    errs = list(ld.check(data))
    S = ld.summary(data, errs)
    line = ld.check_line(S)
    amb = ld.ambient(data)
    sort = ld.sort_of(data)
    props = data.get("property", [])
    pids = [p.get("id") for p in props]
    raw_amb = data.get("ambient") if isinstance(data.get("ambient"), dict) else None
    ambient = {"words": sorted(amb), "standing": words((raw_amb or {}).get("standing", list(ld.AMBIENT))),
               "label": (raw_amb or {}).get("label", "" if raw_amb else ld.AMBIENT_LABEL),
               "note": (raw_amb or {}).get("note", ""), "declared": raw_amb is not None}
    vocab = {w: {"cls": c, "implies": list(imp)} for w, (c, imp) in ld.STANDING.items()}

    P = [{"id": p.get("id"), "lean": p.get("lean", ""), "leanloc": lean.locate(p.get("lean")),
          "label": p.get("label", ""), "what": p.get("what", ""), "sort": sort.get(p.get("id"), ld.DEFAULT_SORT),
          "extra": extras("property", p), "ett": ett.row(p["label"]) if p.get("label") else None}
         for p in props]

    # Which implications `tools/ladder.py emit-lean` makes rules of causal_ladder (ladder.emitted).
    emit, emit_note = {}, ""
    try:
        rules, skipped = ld.emitted(data, lean.index)
        for e, mod in rules:
            emit[id(e)] = {"rule": True, "module": mod}
        for e, why in skipped:
            emit[id(e)] = {"rule": False, "why": why}
    except Exception as ex:   # a ladder mid-edit: the page says so rather than guess
        emit_note = "tools/ladder.py emitted() failed: %s: %s" % (type(ex).__name__, ex)

    I = []
    for e in data.get("implies", []):
        std = ld.standing(e)
        on_amb = ld.valid(e, amb)
        I.append({"from": ids(e.get("from")), "to": e.get("to"), "witness": e.get("witness", ""),
                  "loc": lean.locate(e.get("witness")), "status": e.get("status", ""), "under": e.get("under", ""),
                  "standing": std, "beyond": sorted(set(std) - amb), "onAmbient": on_amb,
                  "cond": (not on_amb) or bool(str(e.get("under") or "").strip()),
                  "extra": extras("implies", e), "emit": emit.get(id(e))})
    C = []
    for e in data.get("consequence", []):
        std = ld.standing(e)
        C.append({"at": ids(e.get("at")), "statement": e.get("statement", ""), "witness": e.get("witness", ""),
                  "loc": lean.locate(e.get("witness")), "status": e.get("status", ""), "under": e.get("under", ""),
                  "standing": std, "beyond": sorted(set(std) - amb), "extra": extras("consequence", e)})
    O = [{"from": e.get("from"), "to": e.get("to"), "note": e.get("note", ""), "extra": extras("open", e)}
         for e in data.get("open", [])]

    ok = not errs                       # tools/ladder.py classifies only a ladder that checks
    derive = Derive(data)
    R = Reading(data, derive)
    F = []
    for k, f in enumerate(data.get("fails", [])):
        has, lacks = R.read(k) if ok else (set(), set())
        # every id counterexample() reads it to lack backwards, with why (Reading.lack): the build
        # fails on one it cannot explain
        back = {y: R.lack(k, y) for y in sorted(lacks) if not R.forward(k, y)} if ok else {}
        F.append({"from": ids(f.get("from")), "to": f.get("to"), "witness": f.get("witness", ""),
                  "loc": lean.locate(f.get("witness")), "status": f.get("status", ""),
                  **space_block(f, data, amb), "has": sorted(has), "lacks": sorted(lacks), "back": back,
                  "extra": extras("fails", f)})

    # [[fact]]: a property holding outright on every object of its sort (tools/ladder.py's facts_on)
    FX = []
    for r in data.get("fact", []):
        std = ld.standing(r)
        FX.append({"property": r.get("property"), "witness": r.get("witness", ""), "loc": lean.locate(r.get("witness")),
                   "status": r.get("status", ""), "standing": std, "beyond": sorted(set(std) - amb),
                   "onAmbient": ld.valid(r, amb), "sort": sort.get(r.get("property"), ""), "note": r.get("note", ""),
                   "extra": extras("fact", r)})

    T = []
    for t in data.get("transfer", []):
        src, tgt = ld._transfer_sides(t)
        proved = bool(t.get("witness"))
        # conditional: proved only under a condition in words, which tools/ladder.py's contradiction
        # check does not apply (it applies `t.get("witness") and not t.get("under")`)
        cond = bool(t.get("witness")) and bool(t.get("under"))
        name = t.get("witness") or t.get("counterexample") or ""
        std = ld.standing(t)
        rec = {"pair": t.get("pair"), "property": t.get("property"),
               "direction": t.get("direction", ld.DIRECTIONS[0]), "narrower": ids(t.get("narrower")),
               "wider": ids(t.get("wider")), "src": list(src), "tgt": list(tgt),
               "kind": "witness" if proved else "counterexample", "cond": cond, "name": name, "loc": lean.locate(name),
               "status": t.get("status", ""), "under": t.get("under", ""), "standing": std,
               "beyond": sorted(set(std) - amb), "extra": extras("transfer", t)}
        if not proved:
            rec.update(space_block(t, data, amb))
        T.append(rec)

    pairs, counts, along = {}, {}, {}
    if ok:
        m = ld.matrix(data)
        on_amb = ld.edges_on(data, amb)
        every = ld.edges_on(data, None)
        opens = {}
        for k, o in enumerate(data.get("open", [])):
            opens.setdefault((o.get("from"), o.get("to")), k)
        reading = [(f, R.read(k)) for k, f in enumerate(data.get("fails", []))]

        def put(rec, key, d, fkey, fx):
            rec[key] = d
            if fx:
                rec[fkey] = fx
        for a in pids:
            for b in pids:
                if a == b:
                    continue
                v = m[(a, b)]
                counts[v] = counts.get(v, 0) + 1
                rec = {"c": v}
                if v == "implied":
                    d, fx = R.chain([a], b, amb, on_amb)
                    put(rec, "d", d, "fx", fx)
                elif v == "implied-standing":
                    need, on = needed_with_facts(data, a, b, every, amb)
                    rec["w"] = need
                    d, fx = R.chain([a], b, on, ld.edges_on(data, on))
                    put(rec, "d", d, "fx", fx)
                elif v in ("fails", "fails-off"):
                    # every counterexample the tool reads as having a and lacking b, on the ambient (fails)
                    # or off it (fails-off, tools/ladder.py's on_ambient); shown: one that lacks b forwards
                    # if any, then the one whose explanation is shortest (the first of the file among
                    # equals), the others listed; of a fails pair, those off the ambient that refute it
                    # too are listed apart (`off`). A backward lack's explanation is the counterexample's
                    # own (`back` of its entry), not copied here.
                    on_f, off_f = [], []
                    for k, (f, (has, lacks)) in enumerate(reading):
                        if a in has and b in lacks:
                            (on_f if ld.on_ambient(f, data) else off_f).append((k, f))
                    use = on_f if v == "fails" else off_f
                    if not use:
                        raise AssertionError("tools/ladder.py calls %s ⇒ %s %s, and no counterexample %s the ambient "
                                             "has %s and lacks %s" % (a, b, v, "on" if v == "fails" else "off", a, b))
                    cands = []
                    for k, f in use:
                        on = ld.space(f, data)
                        da, fa = R.chain(ids(f.get("from")), a, on, ld.edges_on(data, on))
                        L = R.lack(k, b)
                        size = len(L["d"]) + sum(1 + len(s["dc"]) + sum(len(h["d"]) for h in s["hp"]) for s in L.get("bk", []))
                        cands.append(((1 if "bk" in L else 0, len(da) + size, k), k, da, fa, L))
                    _, k, da, fa, L = min(cands, key=lambda c: c[0])
                    rec.update({"f": k, "da": da})
                    if fa:
                        rec["fa"] = fa
                    if "bk" in L:
                        rec["bw"] = 1               # read backwards: LAD.fails[f].back[b]
                    else:
                        put(rec, "db", L["d"], "fb", L["fd"])
                    rec["also"] = sorted(c[1] for c in cands if c[1] != k)
                    if v == "fails":
                        if off_f:
                            rec["off"] = [k for k, _ in off_f]
                    else:
                        spaces = [list(w) for w in ld.off_spaces(data, a, b)]
                        mine = sorted({tuple(sorted(words(f.get("space")))) for _, f in off_f})
                        if [list(w) for w in mine] != spaces:
                            raise AssertionError("tools/ladder.py's off_spaces(%s, %s) is %s; its counterexamples off "
                                                 "the ambient that refute it are on %s" % (a, b, spaces, mine))
                        rec["s"] = spaces
                elif v == "open":
                    rec["o"] = opens[(a, b)]
                pairs[a + "|" + b] = rec
        # A transfer along a nesting reaches the nestings around it as tools/ladder.py's transfer check
        # reads them: a proved transfer along Q holds along every X with X ⇒ Q on ETT's spacetimes (an
        # X-nesting is a Q-nesting); a counterexample along P is a nesting of every X that P reaches
        # through the closure on the counterexample's own space.
        clo = ld.closure(data)
        for X in (x for x in pids if sort.get(x) == "pair"):
            for k, (t, raw) in enumerate(zip(T, data.get("transfer", []))):
                Q = t["pair"]
                if Q == X:
                    along.setdefault(X, []).append({"t": k, "how": "recorded"})
                elif t["kind"] == "witness" and Q in clo.get(X, ()):
                    rec = {"t": k, "how": "through"}
                    d, fx = R.chain([X], Q, amb, on_amb)
                    put(rec, "d", d, "fx", fx)
                    along.setdefault(X, []).append(rec)
                elif t["kind"] == "counterexample":
                    on = ld.space(raw, data)
                    if X in ld.closure(data, on).get(Q, ()):
                        rec = {"t": k, "how": "through"}
                        d, fx = R.chain([Q], X, on, ld.edges_on(data, on))
                        put(rec, "d", d, "fx", fx)
                        along.setdefault(X, []).append(rec)

    sorts = []
    for p in P:
        if p["sort"] not in sorts:
            sorts.append(p["sort"])
    return {"props": P, "implies": I, "fails": F, "facts": FX, "cons": C, "open": O, "transfers": T, "along": along,
            "pairs": pairs, "summary": S, "counts": dict(sorted(counts.items())), "classifiedAs": list(ld.CLASSIFIED),
            "errors": errs, "line": line, "ambient": ambient, "vocab": vocab, "sorts": sorts,
            "sortKey": "sort", "defaultSort": ld.DEFAULT_SORT, "sortNames": list(ld.SORTS),
            "emitKnown": not emit_note, "emitNote": emit_note}


# ------------------------------------------------------------------ binders
LEMMA_HEAD = re.compile(r"^((?:Def|Definition|Thm|Theorem|Lemma|Cor|Corollary|Prop|Proposition|Remark|Rem|"
                        r"Conjecture|Conj|Example|Claim)\.?\s+[0-9]+(?:\.[0-9]+)*)\b")


def binder_block(lean, ladder_ids, target_ids, ledgers):
    out = []
    for slug, b in sorted(bd.binders().items()):
        led = ledgers.setdefault(slug, Ledger(slug))
        errs = sorted(bd.check(slug, b, lean.names, ladder_ids, target_ids))

        def ref(x):
            if x.startswith("T-"):
                return {"x": x, "t": "target" if x in target_ids else "missing"}
            if lean.resolves(x):
                return {"x": x, "t": "lean", "loc": lean.locate(x)}
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
                    "proposed": [dict(p, leanloc=lean.locate(p.get("lean"))) for p in b.get("proposed", [])],
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
def arg(argv, flag, default):
    if flag not in argv:
        return default
    k = argv.index(flag)
    if k + 1 >= len(argv):
        sys.exit("blueprint: %s needs a path" % flag)
    return argv[k + 1]


def shown(p):
    """A path as the page names it: relative to the repository, or absolute when outside it."""
    p = os.path.abspath(p)
    return rel(p) if p.startswith(ROOT + os.sep) else p


def main(argv):
    out_path = arg(argv, "--out", os.path.join(HERE, "index.html"))
    ladder = os.path.abspath(arg(argv, "--ladder", LADDER))
    lean = Lean()
    ledgers = {"ett": Ledger("ett")}
    L = ladder_block(lean, ledgers["ett"], ladder)
    R = roadmap_block()
    ladder_ids = {p["id"] for p in L["props"]}
    target_ids = {t.get("id") for t in R["targets"]}
    B = binder_block(lean, ladder_ids, target_ids, ledgers)
    inputs = [ladder, ROADMAP, README, DECISIONS] + [os.path.join(ROOT, b["path"]) for b in B] + sorted(
        ld_.path for ld_ in ledgers.values() if ld_.ok) + sorted(
        p for p in (os.path.join(ROOT, "papers", b["slug"], "legacy", "MANIFEST.json") for b in B) if os.path.exists(p))
    prov = {"inputs": [{"path": shown(p), "sha256": sha(p)} for p in inputs],
            "tools": [{"path": rel(p), "sha256": sha(p)} for p in TOOLS],
            "leanCommit": {s: (json.load(open(l.path, encoding="utf-8")).get("lean") or {}).get("git_commit", "")
                           for s, l in sorted(ledgers.items()) if l.ok},
            "leanDecls": len(lean.decls)}
    DATA = {"ladder": L, "binders": B, "road": R, "layers": layers(), "ettMacros": ledgers["ett"].macros, "prov": prov}
    blob = json.dumps(DATA, ensure_ascii=False, separators=(",", ":"), default=str).replace("</", "<\\/")
    tpl = open(os.path.join(HERE, "template.html"), encoding="utf-8").read()
    assert tpl.count("__DATA__") == 1, "template.html must hold __DATA__ exactly once"
    page = tpl.replace("__DATA__", blob)
    with open(out_path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(page)
    print("blueprint: %s (%d bytes); %s; binders: %s; roadmap: %d targets%s" % (
        shown(out_path), len(page.encode("utf-8")), L["line"],
        ", ".join("%s %d rows" % (b["slug"], len(b["rows"])) for b in B), len(R["targets"]),
        "".join("; %s: %d violation(s)" % (k, n) for k, n in (("ladder", len(L["errors"])),
                ("binders", sum(len(b["errors"]) for b in B)), ("roadmap", len(R["errors"]))) if n)))


if __name__ == "__main__":
    main(sys.argv[1:])
