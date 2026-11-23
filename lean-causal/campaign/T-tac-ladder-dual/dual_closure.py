"""The closure of `causal_ladder` across time reversal, over literals (property, side).

Side 0 is a property of `C`, side 1 of `C.dual`. The rules modelled are those `causal_ladder` has
with `Causal.Ladder.Rules` and `Causal.Ladder.Dual` imported, on a bare topological space (no
standing instance): every edge rule of Rules.lean without `standing`, on each side; the transport
of every two-sided node between the sides; and the two one-sided introductions
(P_future of C and of C.dual give the two-sided node of C).

The edges are read off Rules.lean (the `-- from ⇒ to (standing: …)` line emit-lean writes above
each rule), not off programme/ladder.toml, so the derived examples are those of the rules the
build has, also while the ladder is ahead of the last emit-lean; the ladder gives the properties,
their Lean forms and the counterexamples. The script refuses to run when Rules.lean has a fact rule
without standing (not modelled: it would fire on a bare space), or when Dual.lean lacks the rule
pair `p_of_dual` / `p_dual` of a two-sided node (p the Lean name of the node, first letter
lowered) or the introduction `t_of_future_of_past` of a one-sided one.

    python3 -I dual_closure.py counts            the numbers of the report
    python3 -I dual_closure.py shipped OUT       Causal/Ladder/DualTest.lean (hand-written part included)
    python3 -I dual_closure.py exact OUT         a scratch file: every cross pair, derived or not

Run from anywhere; it reads the repository's programme/ladder.toml through tools/ladder.py, and
lean-causal/Causal/Ladder/Rules.lean and Dual.lean. Rerun `shipped` after `tools/ladder.py emit-lean`.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "tools"))
import ladder as ld  # noqa: E402

ONE_SIDED = {"causally_open_future": "causally_open",
             "locally_causally_open_future": "locally_causally_open"}
LADDER_DIR = os.path.join(REPO, "lean-causal", "Causal", "Ladder")
EDGE_RULE = "attribute [aesop safe forward (rule_sets := [CausalLadder])] "
PLAIN = "attribute [aesop safe forward (rule_sets := [CausalLadder])]\n"
PATTERNED = "attribute [aesop safe forward (pattern := Causality.dual C) (rule_sets := [CausalLadder])]\n"


def rules_edges(ids):
    """The edge rules of Rules.lean, as ladder edges {from, to, standing, witness}."""
    with open(os.path.join(LADDER_DIR, "Rules.lean"), encoding="utf-8") as fh:
        lines = fh.read().split("\n")
    edges = []
    for i, line in enumerate(lines):
        if line.startswith("-- fact: ") and "(standing: " not in line:
            raise SystemExit("Rules.lean: a fact rule without standing is not modelled: %s" % line)
        if not line.startswith(EDGE_RULE):
            continue
        m = re.match(r"-- (.+) ⇒ (\S+)(?: \(standing: ([^)]*)\))?$", lines[i - 1])
        if not m:
            raise SystemExit("Rules.lean:%d: no `-- from ⇒ to` line above the rule" % (i + 1))
        frm, to = m.group(1).split(" ∧ "), m.group(2)
        unknown = [x for x in frm + [to] if x not in ids]
        if unknown:
            raise SystemExit("Rules.lean:%d: %s not a property with a Lean form" % (i + 1, unknown))
        edges.append({"from": frm, "to": to, "witness": line[len(EDGE_RULE):].strip(),
                      "standing": m.group(3).split(", ") if m.group(3) else []})
    return edges


def check_dual(two, lean):
    """Dual.lean has the transport pair of every two-sided node and the introduction of every
    one-sided one, in the attribute blocks of `causal_ladder`'s rule set."""
    with open(os.path.join(LADDER_DIR, "Dual.lean"), encoding="utf-8") as fh:
        src = fh.read()

    def block(head):
        i = src.find(head)
        if i < 0:
            raise SystemExit("Dual.lean: no attribute block %r" % head.strip())
        return set(src[i + len(head):].split("\n\n", 1)[0].split())

    plain, patterned = block(PLAIN), block(PATTERNED)

    def short(x):
        n = lean[x].rsplit(".", 1)[1]
        return n[0].lower() + n[1:]
    missing = ["%s_of_dual" % short(x) for x in two if "%s_of_dual" % short(x) not in plain]
    missing += ["%s_dual" % short(x) for x in two if "%s_dual" % short(x) not in patterned]
    missing += ["%s_of_future_of_past" % short(t) for t in ONE_SIDED.values()
                if "%s_of_future_of_past" % short(t) not in plain]
    if missing:
        raise SystemExit("Dual.lean lacks the rules %s: add them, or list a node that is not "
                         "invariant under time reversal in ONE_SIDED" % ", ".join(missing))


def setup():
    data = ld.load()
    index = ld.lean_index()
    props = [p for p in data["property"] if p.get("sort", "causality") == "causality"]
    form = {}
    for p in props:
        f, _ = ld.lean_form(p, index)
        if f:
            form[p["id"]] = f
    ids = [p["id"] for p in props if p["id"] in form]
    two = [x for x in ids if x not in ONE_SIDED]
    check_dual(two, {p["id"]: p["lean"] for p in props})
    edges = [e for e in rules_edges(ids) if not ld.standing(e)]
    return data, edges, ids, two, form


def lit(form, x, s):
    """The Lean form of the literal (x, s)."""
    name, subject = form[x].split(" ", 1)
    return "%s %s" % (name, subject.replace("C", "C.dual", 1) if s else subject)


def close(start, edges, two):
    have = set(start)
    changed = True
    while changed:
        changed = False
        new = set()
        for e in edges:
            frm = ld.ids_of(e["from"])
            for s in (0, 1):
                if all((p, s) in have for p in frm):
                    new.add((e["to"], s))
        for p in two:
            if (p, 0) in have or (p, 1) in have:
                new |= {(p, 0), (p, 1)}
        for f, t in ONE_SIDED.items():
            if (f, 0) in have and (f, 1) in have:
                new.add((t, 0))
        if not new <= have:
            have |= new
            changed = True
    return have


def refutations(data, edges, ids, two):
    """Pairs (literal set, literal) refuted by a counterexample of the ladder or its time reversal:
    a list of (has, lacks) literal sets, one per counterexample and per time orientation."""
    out, cache = [], {}
    for f in data.get("fails", []):
        has, lacks = ld.counterexample(data, f, cache)
        hl = close({(p, 0) for p in has if p in ids}, edges, two)
        ll = {(q, 0) for q in lacks if q in ids} | {(q, 1) for q in lacks if q in two}
        changed = True
        while changed:
            changed = False
            for x in ids:
                for s in (0, 1):
                    if (x, s) in hl or (x, s) in ll:
                        continue
                    if close(hl | {(x, s)}, edges, two) & ll:
                        ll.add((x, s))
                        changed = True
        if hl & ll:
            raise SystemExit("contradiction at %s: %s" % (f.get("witness"), sorted(hl & ll)))
        out.append((hl, ll, f.get("witness")))
        out.append(({(x, 1 - s) for x, s in hl}, {(x, 1 - s) for x, s in ll},
                    "%s, time-reversed" % f.get("witness")))
    return out


def refuted_by(refs, src, goal):
    for hl, ll, w in refs:
        if set(src) <= hl and goal in ll:
            return w
    return None


def pairs(data, edges, ids, two):
    """Single-premise cross pairs: derived, refuted (with a witness), unknown; and same-side pairs
    derived only through the dual rules."""
    refs = refutations(data, edges, ids, two)
    der, ref, unk, newsame = [], [], [], []
    for a in ids:
        base = ld._saturate((a,), edges)
        for s in (0, 1):
            clo = close({(a, s)}, edges, two)
            for b in ids:
                if b != a and (b, s) in clo and b not in base:
                    newsame.append(((a, s), (b, s)))
                t = 1 - s
                if (b, t) in clo:
                    der.append(((a, s), (b, t)))
                else:
                    w = refuted_by(refs, [(a, s)], (b, t))
                    (ref if w else unk).append(((a, s), (b, t), w))
    return der, ref, unk, newsame, refs


def mixed(edges, ids, two):
    """Each emitted conjunctive edge used on C.dual with its two-sided premises given on C."""
    out = []
    for e in edges:
        frm = ld.ids_of(e["from"])
        if len(frm) > 1 and any(p in two for p in frm) and all(p in ids for p in frm):
            src = [(p, 0) if p in two else (p, 1) for p in frm]
            out.append((src, (e["to"], 1), e["witness"]))
    return out


def side(s):
    return "C.dual" if s else "C"


def name(l):
    return "%s(%s)" % (l[0], side(l[1]))


def example_pos(form, src, goal, comment):
    hyps = " ".join("(_h%d : %s)" % (i, lit(form, *l)) for i, l in enumerate(src))
    return ["-- %s" % comment, "example %s : %s := by causal_ladder" % (hyps, lit(form, *goal))]


def example_neg(form, src, goal, comment):
    hyps = " ".join("(_h%d : %s)" % (i, lit(form, *l)) for i, l in enumerate(src))
    return ["-- %s" % comment, "example %s : True := by" % hyps,
            "  fail_if_success have : %s := by causal_ladder" % lit(form, *goal), "  trivial"]


HEAD = """\
import Causal.Ladder.Rules
import Causal.Ladder.Dual
{imports}

/-!
# Tests of `causal_ladder` across time reversal (`Causal.Ladder.Dual`)

For `C` a causality on a topological space, `causal_ladder` with the rules of
`Causal.Ladder.Rules` and `Causal.Ladder.Dual` closes a goal about `C.dual` from hypotheses about
`C`, and conversely. The examples come in two parts.

* Hand-written: more than one time reversal, the two one-sided nodes, the node
  `has_chronal_neighbour`, the two pair nodes, rules with standing instances, and the shapes the
  time-reversed witnesses use (kb/0091): a conjunction about `C.dual` from facts about `C`, a
  term argument, a negation read backwards.
* Written by `campaign/T-tac-ladder-dual/dual_closure.py` from the edge rules of
  `Causal.Ladder.Rules` and the properties and counterexamples of `programme/ladder.toml` (not by
  `tools/ladder.py emit-lean`; the script is rerun after it): every single-property
  pair `P(C) ⊢ Q(C.dual)` and `P(C.dual) ⊢ Q(C)` of the closure ({nder} examples, `Derived`), each
  conjunctive rule used on `C.dual` with its two-sided premises given on `C` ({nmix} examples),
  and the pairs across time reversal that a counterexample of the ladder, or its time reversal,
  refutes ({nref} examples, `Not derived`: every `P(C) ⇏ Q(C.dual)`, and every
  `P(C.dual) ⇏ Q(C)` with a one-sided end). A refuted pair stays underived however the ladder
  grows, so these negatives cannot go stale; a derived one can, if an edge is withdrawn.

The script's exhaustive form (all {nall} cross pairs, the {nunk} unknown ones included) was
checked against Lean in the campaign directory: the tactic derives exactly the closure the
script computes. The first command fails if a model module is imported, directly or
transitively, as in `Causal.Ladder.Test`.

## SCOPE (disclosed)

* The examples are on a bare topological space; a rule with `standing` instances is exercised
  only in the hand-written section, with its instances.
* No example is about a time reversal of a property of an open set (`…On W`): those are not
  nodes and have no rule.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Lean in
run_cmd do
  let models : List Name := [{models}]
  for m in (← getEnv).header.moduleNames do
    if models.any (·.isPrefixOf m) then
      throwError "the ladder's Lean imports the model module {{m}}"

section

universe u

variable {{M : Type u}} [TopologicalSpace M] (C C' : Causal.Causality M)

open Causal Causal.Causality

/-! ## More than one time reversal -/

example (h : C.dual.dual.IsCausal) : C.IsCausal := by causal_ladder
example (h : C.IsCausal) : C.dual.dual.IsCausal := by causal_ladder
example (h : C.dual.dual.dual.CausallyOpen) : C.dual.CausallyOpenFuture := by causal_ladder
-- `C.dual.dual` is `C` by definition: the builtin `assumption` closes this, no rule does
example (h : C.CausallyOpenFuture) : C.dual.dual.CausallyOpenFuture := by causal_ladder

/-! ## The one-sided nodes: the two-sided node from the future and the past forms -/

example (hf : C.CausallyOpenFuture) (hp : C.dual.CausallyOpenFuture) : C.CausallyOpen := by
  causal_ladder
example (hf : C.CausallyOpenFuture) (hp : C.dual.CausallyOpenFuture) : C.dual.CausallyOpen := by
  causal_ladder
example (hf : C.CausallyOpenFuture) (hp : C.dual.CausallyOpenFuture) :
    C.dual.LocallyCausallyOpen := by
  causal_ladder
example (hf : C.LocallyCausallyOpenFuture) (hp : C.dual.LocallyCausallyOpenFuture) :
    C.LocallyCausallyOpen := by
  causal_ladder
example (hM : C.AbsolutelyMinimal) (hf : C.LocallyCausallyOpenFuture)
    (hp : C.dual.LocallyCausallyOpenFuture) : C.dual.CausallyOpen := by
  causal_ladder
-- the one-way membrane (`Causal.OneWayMembrane`) is causally open in the future, not in the past
example (_hf : C.CausallyOpenFuture) (_hM : C.AbsolutelyMinimal) (_hT : C.Tarentin) : True := by
  fail_if_success have : C.dual.CausallyOpenFuture := by causal_ladder
  trivial

/-! ## `has_chronal_neighbour`: one side at each point, so invariant under time reversal -/

-- an odd number of reversals (`C.dual.dual.dual` is `C.dual` by `rfl`, not `C`)
example (h : C.dual.dual.dual.HasChronalNeighbourEverywhere) :
    C.HasChronalNeighbourEverywhere := by
  causal_ladder
-- the point predicate of the time reversal: `h` transported, then applied at `p` (builtin rule)
example (h : C.HasChronalNeighbourEverywhere) (p : M) : C.dual.HasChronalNeighbour p := by
  causal_ladder
-- the closed half-line (`closedHalfLine_separates_chronalNeighbours`): `I⁻(0) = ∅`
example (_hK : C.CausallyArcConnected) (_hH : C.HasChronalNeighbourEverywhere) : True := by
  fail_if_success have : C.dual.ChronalNeighbours := by causal_ladder
  trivial

/-! ## The pair nodes -/

example (h : LeNested C C') : LeNested C.dual C'.dual := by causal_ladder
example (h : LeNested C.dual C'.dual) : LeNested C C' := by causal_ladder
example (W : TopologicalSpace.Opens M) (h : CurveNestedOn C C' W) :
    CurveNestedOn C.dual C'.dual W := by
  causal_ladder
example (W : TopologicalSpace.Opens M) (h : CurveNestedOn C.dual C'.dual W) :
    CurveNestedOn C C' W := by
  causal_ladder
-- one reversal only: false for `C = C'` the timelike line
example (_h : LeNested C C') : True := by
  fail_if_success have : LeNested C.dual C' := by causal_ladder
  trivial

/-! ## Rules with standing instances, across time reversal -/

example [T1Space M] (h : C.StronglyCausal) : C.dual.IsCausal := by causal_ladder
example [T1Space M] (h : C.dual.StronglyCausal) : C.IsCausal := by causal_ladder
example [T2Space M] [SecondCountableTopology M] (hG : C.GloballyHyperbolic) (hT : C.Tarentin) :
    C.dual.HasTimeFunction := by
  causal_ladder
example [T2Space M] [SecondCountableTopology M] (hG : C.dual.GloballyHyperbolic)
    (hT : C.Tarentin) : C.dual.StronglyCausal := by
  causal_ladder

/-! ## The shapes of the time-reversed witnesses (kb/0091) -/

-- the half-lit line's facts give its time reversal's
example (hM : C.AbsolutelyMinimal) (hK : C.CausallyArcConnected) (hG : C.GloballyHyperbolic)
    (hP : C.PushUp) (hS : C.StronglyCausalOpen) (hT : C.HasTimeFunction)
    (_hF : C.CausallyOpenFuture) :
    C.dual.AbsolutelyMinimal ∧ C.dual.CausallyArcConnected ∧ C.dual.GloballyHyperbolic ∧
      C.dual.PushUp ∧ C.dual.LocallyPushUp ∧ C.dual.StronglyCausalOpen ∧
      C.dual.StronglyCausal ∧ C.dual.HasTimeFunction ∧ C.dual.CurvesExtend ∧ C.dual.IsCausal ∧
      C.dual.CausallyCompact := by
  causal_ladder
-- and not causal openness in the future of the time reversal (`halfLightLine.dual`)
example (_hM : C.AbsolutelyMinimal) (_hK : C.CausallyArcConnected) (_hG : C.GloballyHyperbolic)
    (_hP : C.PushUp) (_hS : C.StronglyCausalOpen) (_hT : C.HasTimeFunction)
    (_hF : C.CausallyOpenFuture) : True := by
  fail_if_success have : C.dual.CausallyOpenFuture := by causal_ladder
  trivial
-- as a term argument
example (h : C.GloballyHyperbolic) (f : C.dual.IsCausal → False) : False := f (by causal_ladder)
-- negations read backwards (kb/0080): one failure of the time reversal gives the others
example (hn : ¬ C.dual.CausallyOpenFuture) : ¬ C.CausallyOpen ∧ ¬ C.dual.CausallyOpen :=
  ⟨fun _ => hn (by causal_ladder), fun _ => hn (by causal_ladder)⟩
example (hM : C.AbsolutelyMinimal) (hn : ¬ C.dual.CausallyOpenFuture) :
    ¬ C.dual.LocallyCausallyOpenFuture ∧ ¬ C.LocallyCausallyOpen ∧ ¬ C.dual.LocallyCausallyOpen :=
  ⟨fun _ => hn (by causal_ladder), fun _ => hn (by causal_ladder), fun _ => hn (by causal_ladder)⟩
"""


def shipped(out):
    data, edges, ids, two, form = setup()
    der, ref, unk, newsame, refs = pairs(data, edges, ids, two)
    ref = [r for r in ref if r[0][1] == 0 or r[0][0] in ONE_SIDED or r[1][0] in ONE_SIDED]
    mix = mixed(edges, ids, two)
    index = ld.lean_index()
    mods = sorted({index["decls"][p["lean"]] for p in data["property"] if p.get("id") in form})
    lines = [HEAD.format(imports="\n".join("import %s" % m for m in mods),
                         nder=len(der), nmix=len(mix), nref=len(ref),
                         nall=len(der) + len(pairs(data, edges, ids, two)[1]) + len(unk),
                         nunk=len(unk),
                         models=", ".join("`" + m for m in ld.MODEL_LAYER))]
    lines += ["/-! ## Derived across time reversal, from one property -/", ""]
    for a, b in der:
        lines += example_pos(form, [a], b, "%s ⇒ %s" % (name(a), name(b)))
    lines += ["", "/-! ## Derived on `C.dual` through a conjunctive rule, two-sided premises on `C` -/", ""]
    for src, goal, w in mix:
        lines += example_pos(form, src, goal, "%s ⇒ %s (%s on C.dual)" % (
            " ∧ ".join(name(l) for l in src), name(goal), w))
    lines += ["", "/-! ## Not derived across time reversal: refuted pairs -/", ""]
    for a, b, w in ref:
        lines += example_neg(form, [a], b, "%s ⇏ %s (refuted: %s)" % (name(a), name(b), w))
    lines += ["", "end"]
    with open(out, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")


def exact(out):
    data, edges, ids, two, form = setup()
    der, ref, unk, newsame, refs = pairs(data, edges, ids, two)
    mods = sorted({ld.lean_index()["decls"][p["lean"]] for p in data["property"]
                   if p.get("id") in form})
    lines = ["import Causal.Ladder.Rules", "import Causal.Ladder.Dual"] + ["import %s" % m for m in mods] + [
        "", "-- scratch (T-tac-ladder-dual): every single-premise cross pair, derived or not", "",
        "section", "universe u", "variable {M : Type u} [TopologicalSpace M] (C : Causal.Causality M)", ""]
    for a, b in der:
        lines += example_pos(form, [a], b, "derived %s ⇒ %s" % (name(a), name(b)))
    for a, b, w in ref + unk:
        lines += example_neg(form, [a], b, "not derived %s ⇏ %s (%s)" % (name(a), name(b), w or "unknown"))
    for a, b in newsame:
        lines += example_pos(form, [a], b, "same side, only through the dual rules %s ⇒ %s" % (name(a), name(b)))
    lines += ["", "end"]
    with open(out, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")


def counts():
    data, edges, ids, two, form = setup()
    der, ref, unk, newsame, refs = pairs(data, edges, ids, two)
    print("properties with a Lean form:", len(ids), "two-sided:", len(two))
    print("bare emitted edges:", len(edges))
    print("cross pairs: derived", len(der), "refuted", len(ref), "unknown", len(unk),
          "total", len(der) + len(ref) + len(unk))
    print("same-side pairs derived only through the dual rules:", newsame)
    print("mixed conjunctive examples:", len(mixed(edges, ids, two)))
    for a, b, w in unk:
        print("  unknown", name(a), "⇏?", name(b))


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "counts"
    {"counts": lambda: counts(), "shipped": lambda: shipped(sys.argv[2]),
     "exact": lambda: exact(sys.argv[2])}[cmd]()
