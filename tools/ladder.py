#!/usr/bin/env python3
"""The causality ladder of ETT (programme/ladder.toml): check it, classify it, emit its Lean rules.

    python3 tools/ladder.py check        schema, ids, Lean witnesses resolve, no implication contradicts a counterexample
    python3 tools/ladder.py matrix       every ordered pair of properties: implied | fails | open | unknown
    python3 tools/ladder.py emit-lean    write lean-causal/Causal/Ladder/Rules.lean from the checked edges
                                         (and its tests, Causal/Ladder/Test.lean)
    python3 tools/ladder.py dot          the implication DAG in Graphviz

Implication is read through the transitive closure of the `implies` edges (a conjunction premise
counts only when all its ids hold): (a, b) is `implied` when b is in the closure of {a}. A
counterexample to (a, b), a space with a and without b, also refutes (a', b') for every a' that a
implies and every b' that implies b; such pairs are `fails`. A pair both implied and refuted is a
contradiction, and `check` fails on it. No model is called; Lean names are resolved by reading the
sources (a declared name matches a witness when one is a dotted suffix of the other).
"""
import glob
import os
import re
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FILE = os.path.join(ROOT, "programme", "ladder.toml")
LEAN_ROOT = os.path.join(ROOT, "lean-causal")
RULES = os.path.join(LEAN_ROOT, "Causal", "Ladder", "Rules.lean")
STATUS = ("seed", "checked")
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(?:theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+([^\s(:{\[]+)", re.M)


def load(path=FILE):
    with open(path, "rb") as fh:
        return tomllib.load(fh)


def lean_names(root=LEAN_ROOT):
    names = set()
    for f in glob.glob(os.path.join(root, "Causal", "**", "*.lean"), recursive=True):
        names.update(DECL.findall(open(f, encoding="utf-8").read()))
    return names


def resolves(name, names):
    if name in names:
        return True
    for d in names:
        if name.endswith("." + d) or d.endswith("." + name):
            return True
    return False


def closure(data):
    """id -> set of ids implied (reflexive), through the implies edges."""
    props = [p["id"] for p in data.get("property", [])]
    out = {}
    for a in props:
        have = {a}
        changed = True
        while changed:
            changed = False
            for e in data.get("implies", []):
                if set(e["from"]) <= have and e["to"] not in have:
                    have.add(e["to"])
                    changed = True
        out[a] = have
    return out


def refuted(data, clo):
    """Pairs (a, b) refuted by a counterexample, propagated along the closure."""
    props = [p["id"] for p in data.get("property", [])]
    bad = set()
    for f in data.get("fails", []):
        a, b = f["from"], f["to"]
        for a2 in props:
            if a2 in clo.get(a, ()):          # the counterexample has a, hence a2
                for b2 in props:
                    if b in clo.get(b2, ()):  # b2 would give b, which it lacks
                        bad.add((a2, b2))
    return bad


def check(data, names=None):
    errs = []
    names = lean_names() if names is None else names
    props = data.get("property", [])
    ids = [p.get("id") for p in props]
    known = set(ids)
    for i in set(x for x in ids if ids.count(x) > 1):
        errs.append("property %s: duplicate id" % i)
    for p in props:
        for k in ("id", "lean", "what"):
            if not p.get(k):
                errs.append("property %s: missing %s" % (p.get("id"), k))
        if p.get("lean") and not resolves(p["lean"], names):
            errs.append("property %s: Lean definition %s not found in lean-causal" % (p["id"], p["lean"]))
    for kind in ("implies", "fails", "consequence"):
        for e in data.get(kind, []):
            tag = "%s %s" % (kind, e.get("witness", "?"))
            if e.get("status") not in STATUS:
                errs.append("%s: status must be one of %s" % (tag, STATUS))
            if not e.get("witness"):
                errs.append("%s: missing witness" % tag)
            elif not resolves(e["witness"], names):
                errs.append("%s: witness not found in lean-causal" % tag)
            ends = []
            if kind == "implies":
                ends = list(e.get("from", [])) + [e.get("to")]
                if not e.get("from"):
                    errs.append("%s: empty premise" % tag)
            elif kind == "fails":
                ends = [e.get("from"), e.get("to")]
            else:
                ends = [e.get("at")]
                if not e.get("statement"):
                    errs.append("%s: missing statement" % tag)
            for x in ends:
                if x not in known:
                    errs.append("%s: unknown property %r" % (tag, x))
    for o in data.get("open", []):
        for x in (o.get("from"), o.get("to")):
            if x not in known:
                errs.append("open %s→%s: unknown property %r" % (o.get("from"), o.get("to"), x))
    if not errs:
        clo = closure(data)
        bad = refuted(data, clo)
        for a in known:
            for b in clo[a]:
                if (a, b) in bad:
                    errs.append("contradiction: %s ⇒ %s by implications, refuted by a counterexample" % (a, b))
        opens = {(o["from"], o["to"]) for o in data.get("open", [])}
        for a, b in opens:
            if b in clo[a] or (a, b) in bad:
                errs.append("open %s→%s is already settled; remove it" % (a, b))
    return errs


def matrix(data):
    clo = closure(data)
    bad = refuted(data, clo)
    opens = {(o["from"], o["to"]) for o in data.get("open", [])}
    ids = [p["id"] for p in data.get("property", [])]
    out = {}
    for a in ids:
        for b in ids:
            if a == b:
                continue
            out[(a, b)] = ("implied" if b in clo[a] else "fails" if (a, b) in bad
                           else "open" if (a, b) in opens else "unknown")
    return out


# ------------------------------------------------------------------ emit-lean
#
# `emit-lean` writes two generated modules of the strict library:
#   Causal/Ladder/Rules.lean  one aesop rule `safe forward` of the rule set CausalLadder per emitted
#                             edge, and the imports of the witnesses' modules;
#   Causal/Ladder/Test.lean   `example`s: `causal_ladder` derives every pair of the closure of the
#                             EMITTED edges, and fails on every other ordered pair.
# An edge is emitted when it is `checked`, has a premise, carries no `under` (a side condition is
# not a ladder node, and a rule with an unprovable side goal must not exist), joins properties of
# the sort `causality` only (a `geometry` property is not a predicate on one causality), and its
# witness is declared in a module of the ETT layer: one that imports, directly or transitively, no
# model (MODEL_LAYER), so that the layer-1 modules which call `causal_ladder` stay model-free.
# A skipped checked edge is a comment line in Rules.lean that names it and says why.

TEST = os.path.join(LEAN_ROOT, "Causal", "Ladder", "Test.lean")
GENERATED = "-- generated by tools/ladder.py emit-lean from programme/ladder.toml: do not edit"
MODEL_LAYER = ("Causal.Minkowski", "Causal.Static", "Causal.SingularFlat",
               "Causal.Flat", "Causal.Model", "Causal.Port")
DECL_FQ = re.compile(r"(?:(?:private|protected|noncomputable|public|partial|unsafe|nonrec)\s+)*"
                     r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)"
                     r"\s+([^\s(:{\[⦃]+)")
IMPORT = re.compile(r"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.']+)\s*$")


def _code(text):
    """`text` with its comments (`--`, nested `/- -/`, docstrings) blanked, newlines kept."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif not depth and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j == -1 else j
            out.append(" " * (j - i))
            i = j
        else:
            out.append(text[i] if (not depth or text[i] == "\n") else " ")
            i += 1
    return "".join(out)


def _signature(code, pos):
    """The explicit binders and the type of the declaration whose name ends at `pos`:
    ([binder text, ...], type text or None). Read up to the first top-level `:=` or `where`."""
    close = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    explicit, stack, start, i = [], [], None, pos
    end = min(len(code), pos + 4000)
    while i < end:
        c = code[i]
        if c in close:
            if not stack and c == "(":
                start = i + 1
            stack.append(close[c])
        elif stack and c == stack[-1]:
            stack.pop()
            if not stack and start is not None:
                explicit.append(" ".join(code[start:i].split()))
                start = None
        elif not stack and c == ":" and not code.startswith(":=", i):
            rest = code[i + 1:end]
            m = re.search(r":=|\bwhere\b|^\s*\|", rest, re.M)
            return explicit, " ".join((rest[:m.start()] if m else rest).split())
        elif not stack and (code.startswith(":=", i) or (
                code.startswith("where", i) and not re.match(r"[\w.']", code[i - 1])
                and not re.match(r"[\w']", code[i + 5:i + 6]))):
            return explicit, None
        i += 1
    return explicit, None


def lean_index(root=LEAN_ROOT):
    """What emit-lean reads off the Causal library's sources, without Lean:
    `decls`   fully qualified name -> module, for every declaration (namespaces tracked);
    `imports` module -> the Causal modules its header imports;
    `sigs`    fully qualified name -> (explicit binders, type), for every `def` and `abbrev`."""
    decls, imports, sigs = {}, {}, {}
    for f in sorted(glob.glob(os.path.join(root, "Causal", "**", "*.lean"), recursive=True)):
        mod = os.path.relpath(f, root)[:-len(".lean")].replace(os.sep, ".")
        with open(f, encoding="utf-8") as fh:
            code = _code(fh.read())
        imports[mod] = []
        stack = []          # one entry per namespace component or section: (kind, component)
        header = True
        offset = 0
        for line in code.split("\n"):
            here, offset = offset, offset + len(line) + 1
            s = line.strip()
            if not s:
                continue
            if header:
                if s in ("module", "prelude"):
                    continue
                m = IMPORT.match(s)
                if m:
                    if m.group(1).startswith("Causal."):
                        imports[mod].append(m.group(1))
                    continue
                header = False
            m = re.match(r"namespace\s+(\S+)", s)
            if m:
                stack.extend(("namespace", x) for x in m.group(1).split("."))
                continue
            m = re.match(r"(?:@\[.*\]\s*)?(?:(?:public|private|noncomputable)\s+)*section\b\s*(\S*)", s)
            if m:
                stack.extend(("section", x) for x in (m.group(1).split(".") if m.group(1) else [""]))
                continue
            m = re.match(r"end\b\s*(\S*)", s)
            if m:
                for _ in (m.group(1).split(".") if m.group(1) else [""]):
                    if stack:
                        stack.pop()
                continue
            while s.startswith("@["):                  # attributes, brackets balanced
                d, k = 0, 1
                for k in range(1, len(s)):
                    d += s[k] == "["
                    d -= s[k] == "]"
                    if d == 0:
                        break
                s = s[k + 1:].lstrip()
            m = DECL_FQ.match(s)
            if not m:
                continue
            name = m.group(2)
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                full = ".".join([x for k, x in stack if k == "namespace"] + [name])
            decls.setdefault(full, mod)
            if m.group(1) in ("def", "abbrev"):
                at = here + (len(line) - len(line.lstrip())) + (len(line.strip()) - len(s)) + m.end()
                sigs.setdefault(full, _signature(code, at))
    return {"decls": decls, "imports": imports, "sigs": sigs}


def is_model(mod):
    """A module of the model layer (MODEL_LAYER): one of them, or below one of them."""
    return any(mod == m or mod.startswith(m + ".") for m in MODEL_LAYER)


def model_path(mod, imports):
    """The shortest import chain from `mod` to a model module, or None if `mod` is ETT-layer."""
    seen, queue = {mod: None}, [mod]
    while queue:
        m = queue.pop(0)
        if is_model(m):
            path = [m]
            while seen[path[-1]] is not None:
                path.append(seen[path[-1]])
            return path[::-1]
        for n in imports.get(m, []):
            if n not in seen:
                seen[n] = m
                queue.append(n)
    return None


def _sort(data):
    return {p["id"]: p.get("sort", "causality") for p in data.get("property", [])}


def emitted(data, index=None):
    """(edges emitted as rules, with the witness's module; checked edges skipped, with the reason)."""
    index = lean_index() if index is None else index
    sort = _sort(data)
    rules, skipped = [], []
    for e in data.get("implies", []):
        if e.get("status") != "checked":
            continue
        w = e.get("witness", "?")
        mod = index["decls"].get(w)
        chain = model_path(mod, index["imports"]) if mod else None
        if not e.get("from"):
            skipped.append((e, "no premise"))
        elif e.get("under"):
            skipped.append((e, "under: %s" % " ".join(e["under"].split())))
        elif any(sort.get(x, "causality") != "causality" for x in list(e["from"]) + [e.get("to")]):
            skipped.append((e, "sort: joins a property not of the sort causality"))
        elif mod is None:
            skipped.append((e, "not found: no declaration of this name in lean-causal/Causal"))
        elif chain:
            skipped.append((e, "layer: %s lives in %s, which imports a model (%s)" % (
                w, mod, " → ".join(chain))))
        else:
            rules.append((e, mod))
    return rules, skipped


def _edge(e):
    return "%s ⇒ %s" % (" ∧ ".join(e["from"]), e["to"])


def emit_lean(data, index=None):
    """The text of Causal/Ladder/Rules.lean."""
    rules, skipped = emitted(data, index)
    mods = sorted({m for _, m in rules})
    lines = [GENERATED, "import Causal.Ladder.Basic"] + ["import %s" % m for m in mods] + [
        "",
        "/-!",
        "# The rules of `causal_ladder`, generated from the causality ladder",
        "",
        "One aesop `safe forward` rule of the rule set `CausalLadder` per `checked` implication of",
        "`programme/ladder.toml` with no side condition (`under`), between properties of the sort",
        "`causality`, whose witness lives in the ETT layer (no model imported, directly or",
        "transitively). Every other checked implication is a `-- skipped` line below, with its reason.",
        "Regenerate with `python3 tools/ladder.py emit-lean`; `Causal.Ladder.Test` is generated with it.",
        "",
        "Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.",
        "-/",
        ""]
    for e, _ in rules:
        lines.append("-- %s" % _edge(e))
        lines.append("attribute [aesop safe forward (rule_sets := [CausalLadder])] %s" % e["witness"])
    if skipped:
        lines.append("")
    for e, why in skipped:
        lines.append("-- skipped %s (%s): %s" % (e.get("witness", "?"), _edge(e) if e.get("from") else "?", why))
    return "\n".join(lines) + "\n"


def _saturate(start, edges):
    have = set(start)
    changed = True
    while changed:
        changed = False
        for e in edges:
            if set(e["from"]) <= have and e["to"] not in have:
                have.add(e["to"])
                changed = True
    return have


def lean_form(prop, index):
    """`P C` for a property of one causality `C : Causal.Causality M`, or (None, why)."""
    name = prop.get("lean", "")
    if prop.get("sort", "causality") != "causality":
        return None, "sort %s" % prop["sort"]
    mod = index["decls"].get(name)
    if mod is None or name not in index["sigs"]:
        return None, "no def or abbrev %s in lean-causal/Causal" % name
    if model_path(mod, index["imports"]):
        return None, "%s lives in %s, which imports a model" % (name, mod)
    explicit, typ = index["sigs"][name]
    if typ != "Prop":
        return None, "%s is not a Prop-valued def (type %s)" % (name, typ)
    ns = name.rsplit(".", 1)[0]
    subject = {"Causal.Causality": "C", "Causal.Precausality": "C.toPrecausality"}
    if not explicit and ns in subject:
        return "%s %s" % (name, subject[ns]), None
    if len(explicit) == 1:
        m = re.match(r"[^:]*:\s*(?:Causal\.)?(Causality|Precausality)\b", explicit[0])
        if m:
            return "%s %s" % (name, subject["Causal." + m.group(1)]), None
    return None, "%s is not a predicate on one causality (explicit binders %s)" % (name, explicit)


def emit_test(data, index=None):
    """The text of Causal/Ladder/Test.lean: the closure of the emitted edges, both ways."""
    index = lean_index() if index is None else index
    rules, _ = emitted(data, index)
    edges = [e for e, _ in rules]
    props = [p for p in data.get("property", []) if p.get("sort", "causality") == "causality"]
    form, why = {}, {}
    for p in props:
        f, w = lean_form(p, index)
        if f:
            form[p["id"]] = f
        else:
            why[p["id"]] = w
    ids = [p["id"] for p in props if p["id"] in form]
    mat = matrix(data)
    mods = sorted({index["decls"][p["lean"]] for p in props if p["id"] in form})
    note = {"implied": "the matrix chains it through an edge not emitted",
            "fails": "refuted by a counterexample", "open": "an open pair", "unknown": "unknown"}
    pos, neg, seen = [], [], set()
    sources = [(a,) for a in ids] + [tuple(e["from"]) for e in edges if len(e["from"]) > 1]
    for src in sources:
        if src in seen or not all(x in form for x in src):
            continue
        seen.add(src)
        for b in sorted(_saturate(src, edges) - set(src)):
            if b in form:
                pos.append((src, b))
    seen = set()
    for a in ids:
        reach = _saturate((a,), edges)
        for b in ids:
            if b != a and b not in reach:
                seen.add(((a,), b))
                neg.append(((a,), b, "matrix: %s" % note.get(mat.get((a, b)), mat.get((a, b)))))
    for e in edges:                      # a conjunctive rule needs every premise
        if len(e["from"]) > 1 and all(x in form for x in e["from"]) and e["to"] in form:
            for x in e["from"]:
                src = tuple(y for y in e["from"] if y != x)
                if e["to"] not in _saturate(src, edges) and (src, e["to"]) not in seen:
                    seen.add((src, e["to"]))
                    neg.append((src, e["to"], "%s dropped from %s" % (x, e["witness"])))

    def hyps(src):
        return " ".join("(_h%d : %s)" % (i, form[x]) for i, x in enumerate(src))

    lines = [GENERATED, "import Causal.Ladder.Rules"] + ["import %s" % m for m in mods] + [
        "",
        "/-!",
        "# Tests of `causal_ladder`, generated from the causality ladder",
        "",
        "For `C` a causality on a topological space, `causal_ladder` derives every implication of",
        "the transitive closure of the rules of `Causal.Ladder.Rules` (the emitted edges of",
        "`programme/ladder.toml`), from each property and from the premises of each conjunctive rule",
        "(%d examples, `Derived`). It fails on every other ordered pair of the properties of the" % len(pos),
        "sort `causality` written here, and on each conjunctive rule with one premise dropped",
        "(%d examples, `Not derived`). A pair the ladder's matrix calls `implied` that is not" % len(neg),
        "derived goes through an edge that was not emitted (a side condition `under`, or a witness",
        "outside the ETT layer). The first command fails if a model module is imported, directly or",
        "transitively: the ladder's Lean stays in the ETT layer, so that layer-1 modules may use it.",
        "Regenerate with `python3 tools/ladder.py emit-lean`.",
        "",
        "Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.",
        "-/",
        "",
        "open Lean in",
        "run_cmd do",
        "  let models : List Name := [%s]" % ", ".join("`" + m for m in MODEL_LAYER),
        "  for m in (← getEnv).header.moduleNames do",
        "    if models.any (·.isPrefixOf m) then",
        "      throwError \"the ladder's Lean imports the model module {m}\"",
        ""]
    for p in props:
        if p["id"] in why:
            lines.append("-- no example for %s: %s" % (p["id"], why[p["id"]]))
    lines += ["", "section", "", "universe u", "",
              "variable {M : Type u} [TopologicalSpace M] (C : Causal.Causality M)", "",
              "/-! ## Derived -/", ""]
    for src, b in pos:
        lines.append("-- %s ⇒ %s" % (" ∧ ".join(src), b))
        lines.append("example %s : %s := by causal_ladder" % (hyps(src), form[b]))
    lines += ["", "/-! ## Not derived -/", ""]
    for src, b, reason in neg:
        lines.append("-- %s ⇏ %s (%s)" % (" ∧ ".join(src), b, reason))
        lines.append("example %s : True := by" % hyps(src))
        lines.append("  fail_if_success have : %s := by causal_ladder" % form[b])
        lines.append("  trivial")
    lines += ["", "end"]
    return "\n".join(lines) + "\n"


def main(argv):
    if not argv:
        sys.exit(__doc__)
    data = load()
    cmd = argv[0]
    if cmd == "check":
        errs = check(data)
        for e in errs:
            print("ladder: " + e)
        m = matrix(data) if not errs else {}
        n = len(data.get("property", []))
        print("ladder: %d properties, %d implications, %d counterexamples, %d consequences; %s" % (
            n, len(data.get("implies", [])), len(data.get("fails", [])), len(data.get("consequence", [])),
            "%d violation(s)" % len(errs) if errs else
            "%d of %d ordered pairs classified" % (sum(1 for v in m.values() if v != "unknown"), len(m))))
        sys.exit(1 if errs else 0)
    if cmd == "matrix":
        for (a, b), v in sorted(matrix(data).items()):
            print("%-24s %-24s %s" % (a, b, v))
        return
    if cmd == "emit-lean":
        index = lean_index()
        rules, skipped = emitted(data, index)
        text, test = emit_lean(data, index), emit_test(data, index)
        os.makedirs(os.path.dirname(RULES), exist_ok=True)
        for path, body in ((RULES, text), (TEST, test)):
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(body)
        print("ladder: wrote %s (%d rules, %d checked edges skipped) and %s (%d derived, %d not derived)" % (
            os.path.relpath(RULES, ROOT), len(rules), len(skipped), os.path.relpath(TEST, ROOT),
            sum(1 for x in test.splitlines() if x.startswith("example") and x.endswith("by causal_ladder")),
            test.count("fail_if_success")))
        return
    if cmd == "dot":
        print("digraph ladder { rankdir=BT; node [shape=box];")
        for e in data.get("implies", []):
            for a in e["from"]:
                print('  "%s" -> "%s" [style=%s];' % (a, e["to"], "solid" if e["status"] == "checked" else "dashed"))
        print("}")
        return
    sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
