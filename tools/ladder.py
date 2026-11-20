#!/usr/bin/env python3
"""The causality ladder of ETT (programme/ladder.toml): check it, classify it, emit its Lean rules.

    python3 tools/ladder.py check        schema, ids, Lean witnesses resolve, no implication contradicts a counterexample
    python3 tools/ladder.py matrix       every ordered pair of properties: implied | fails | open | unknown
    python3 tools/ladder.py emit-lean    write lean-causal/Causal/Ladder/Rules.lean from the checked edges
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


def emit_lean(data):
    lines = ["-- generated by tools/ladder.py emit-lean from programme/ladder.toml: do not edit",
             "import Causal.Ladder.Basic", ""]
    for e in data.get("implies", []):
        if e.get("status") == "checked" and len(e["from"]) == 1:
            lines.append("attribute [aesop safe apply (rule_sets := [CausalLadder])] %s" % e["witness"])
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
        text = emit_lean(data)
        os.makedirs(os.path.dirname(RULES), exist_ok=True)
        open(RULES, "w", encoding="utf-8").write(text)
        print("ladder: wrote %s (%d rules)" % (os.path.relpath(RULES, ROOT), text.count("attribute")))
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
