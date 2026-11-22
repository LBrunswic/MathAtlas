import Causal.Ladder.Basic
import Causal.Properties
import Causal.PushUp
import Causal.Minimal
import Causal.ArcConnected
import Causal.LadderLocal
import Causal.CauchyExtension
import Causal.CurvesExtend
import Causal.Inextensible
import Causal.NestedCausalities
import Causal.NestedConverse

/-!
# `causal_ladder` across time reversal: the hand-written rules of the dual lemmas

The generated rules of `Causal.Ladder.Rules` apply to any term `C`, so `causal_ladder` already
reasons about `C.dual` from hypotheses about `C.dual`; it never crossed from `C` to `C.dual`
(kb/0048, kb/0091). This file adds the rules that cross, to the same rule set `CausalLadder`, one
pair per **two-sided** node of the ladder (`programme/ladder.toml`, sort `causality`), from its
dual lemma `C.dual.P ↔ C.P`:

* `P_of_dual : C.dual.P → C.P`, a forward rule that shrinks the term;
* `P_dual : C.P → C.dual.P`, a forward rule with the aesop **rule pattern** `Causality.dual C`:
  its `C` is not read off the hypothesis but off a subterm `C.dual` of the goal or of a
  hypothesis, so it fires only for a `C` whose time reversal is already in sight. Without the
  pattern it would loop (`C.dual.dual.…`): aesop's deduplication compares types up to reducible
  transparency, and `Causality.dual` is not reducible, so `C.dual.dual.P` is not seen as `C.P`.

**Termination.** The one-causality rules create no new subterm `t.dual`: `P_dual` writes `t.dual`
only for a `t.dual` already present, `P_of_dual` and the generated rules write terms already
present, and the introductions below conclude about `C` from facts about `C` and `C.dual`. The two
pair rules `leNested_dual` and `curveNestedOn_dual` do create one: their pattern binds the first
causality only, so from `LeNested C C'` with `C.dual` in sight they write `C'.dual` (then
`C'.dual.IsCausal`, …). Termination still holds, because such a new reversal appears only beside
an existing one of the same depth along a nesting already in the context: the reversal depths in
sight stay bounded by those of the goal and hypotheses, and over the finitely many causalities
named there the saturated facts are finite (a cycle of three nestings with `C.dual.dual.dual` in
sight ends by exhaustive search; T-tac-ladder-dual's audit). When no `C.dual` occurs in the goal
or a hypothesis nothing is transported, so a goal without a time reversal costs about what it cost
before (the generated tests replay 0.2–0.6 s slower, out of about 4.5 s).

So, once `C.dual` is in sight, a two-sided fact of `C` is a fact of `C.dual` and conversely, and
the generated rules fire on `C.dual` as on any causality, which gives the past forms of the
one-sided nodes (`C.CausallyOpen ⊢ C.dual.CausallyOpenFuture`, through `C.dual.CausallyOpen` and
`CausallyOpen.future`). The two **one-sided** nodes,
`causally_open_future` and `locally_causally_open_future`, have no dual lemma: their dual form
`C.dual.P` (the past form) is not a node. Their only rules here conclude the two-sided node from
both forms (`causallyOpen_of_future_of_past`, `locallyCausallyOpen_of_future_of_past`, the
definitions read backwards). A one-sided fact is never transported: `C.CausallyOpenFuture` does
not give `C.dual.CausallyOpenFuture`, and must not (the one-way membrane,
`Causal.OneWayMembrane`). The two nodes of sort `pair`, `le_nested` and `curve_nested`, get the
same pair of rules, the pattern on the first causality.

Each rule is a theorem of this file, a restatement of a library lemma, because an aesop rule is a
declaration and an iff gives a forward rule nothing to match. Rules of the ladder and their dual
lemmas, node by node (ladder id: lemma, module):

| node | dual lemma |
|---|---|
| `is_causal` | `Causality.dual_isCausal` (`Causal.Properties`) |
| `strongly_causal` | `Causality.dual_stronglyCausal` (`Causal.Properties`) |
| `strongly_causal_open` | `Causality.dual_stronglyCausalOpen` (`Causal.Properties`) |
| `globally_hyperbolic` | `Causality.dual_globallyHyperbolic` (`Causal.Properties`) |
| `causally_compact` | `Causality.dual_causallyCompact` (`Causal.LadderLocal`) |
| `push_up` | `Causality.dual_pushUp` (`Causal.PushUp`) |
| `causally_open` | `Causality.dual_causallyOpen` (`Causal.Properties`) |
| `absolutely_minimal` | `Causality.dual_absolutelyMinimal` (`Causal.Minimal`) |
| `causally_arc_connected` | `Causality.dual_causallyArcConnectedOn` at `⊤` (`ArcConnected`) |
| `causally_plain` | `Causality.dual_causallyPlain` (`Causal.Properties`) |
| `tarentin` | `Causality.dual_tarentin` (`Causal.Properties`) |
| `time_function` | proved here, `hasTimeFunction_dual_iff` (see SCOPE) |
| `curves_extend` | proved here, `curvesExtend_dual_iff` (see SCOPE) |
| `locally_push_up` | `Causality.dual_locallyPushUp` (`Causal.LadderLocal`) |
| `locally_causally_open` | `Causality.dual_locallyCausallyOpen` (`Causal.LadderLocal`) |
| `chronal_neighbours` | `Causality.dual_chronalNeighbours` (`Causal.LadderLocal`) |
| `causally_open_future` | one-sided: no dual lemma; `causallyOpen_iff` read backwards |
| `locally_causally_open_future` | one-sided: no dual lemma; `LocallyCausallyOpen`'s definition |
| `le_nested` (pair) | `Causality.dual_leNested_iff` (`Causal.NestedCausalities`) |
| `curve_nested` (pair) | `Causality.dual_curveNestedOn_iff` (`Causal.NestedConverse`) |

Usage: import this file (with `Causal.Ladder.Rules` for the ladder's own rules); then
`causal_ladder` closes `C.dual.CausallyOpenFuture` from `hO : C.CausallyOpen`, or
`C.dual.CausallyOpenFuture` from `hM : C.AbsolutelyMinimal` and
`hL : C.dual.LocallyCausallyOpenFuture` (the generated rule fires on `C.dual` once `hM` is
transported). `Causal.Ladder.DualTest` shows what it derives and what it does not.

## SCOPE (disclosed)

* Time reversal is entered only where a `C.dual` occurs in the goal or a hypothesis (the
  pattern). A goal about `C` from hypotheses about `C` is never sent through `C.dual`: on the
  current ladder nothing is lost (no pair of the closure from at most three properties on one
  side needs the detour, `campaign/T-tac-ladder-dual/dual_closure.py`), but an edge of the ladder
  that is not invariant under time reversal could make one needed.
* A goal about `C.dual.dual` is closed through the hypotheses of its terms or the builtin
  `assumption`, which sees `C.dual.dual` as `C` up to definitional equality; nothing rewrites
  `C.dual.dual` to `C`.
* `time_function` and `curves_extend` have their dual lemmas outside what this file may import:
  `Causality.dual_hasTimeFunction` is in `Causal.HalfLitDual`, a witness module that imports
  `Causal.Ladder.Rules`, and `Causality.CurvesExtend.dual` is in `Causal.LemmaKBare`, which imports
  `Causal.Model.CurvesExtendModels`. Their two proofs (`−T` is a time function of `C.dual`;
  reverse the curve, extend it, reverse back) are repeated here under the names
  `hasTimeFunction_dual_iff` and `curvesExtend_dual_iff`, in this file's namespace; hoisting the
  library's lemmas into `Causal.CurvesExtend` and `Causal.CauchyExtension` would let these two
  become one-liners.
* No rule is given for the past-based conjuncts `ChronalPastNeighbours` and `NoPastEndpoint` (not
  nodes; DEC-166 renames them to a future base), nor for `IsCausalIso` (`IsCausalIso.dual`, not a
  node), nor for the `…On W` forms (`dual_tarentinOn`, `dual_pushUpOn`, …), which are not nodes.
* Like the generated rules, these are forward: a hypothesis under a binder is not used, and no
  hypothesis is destructed through a definition (`C.CausallyOpen` is not split into its two
  halves; `causallyOpen_of_future_of_past` only builds it).
* Transport doubles the facts of a saturation, and every forward step counts towards aesop's
  `maxRuleApplicationDepth` (30, left at its default by `causal_ladder`). With seven facts of `C`
  a conjunction of eleven goals about `C.dual` is closed and one of twelve, about `C.dual` and
  `C.dual.dual`, stops at the depth (measured): close a long conjunction one conjunct at a time
  (`⟨by causal_ladder, …⟩`), as the witnesses do. A single goal with one reversal is not affected;
  with nested reversals in a large context it can be: from 16 facts of `C`, the provable
  `C.dual.dual.CausallyOpen` and `C.dual.dual.dual.CausallyOpenFuture` stop at depth 30 and close
  at 60, and a refuted goal about `C.dual⁵` ends at the depth rather than by exhaustion; the
  extreme case (16 facts, seven reversals) also meets aesop's `maxSafePrefixRuleApplications`
  (50). Raising both limits in `causal_ladder` is a proposal for `Causal/Ladder/Basic.lean`
  (T-tac-ladder-dual's audit).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; aesop at the
manifest's revision.
-/

namespace Causal.LadderDual

open Causal Causal.Causality TopologicalSpace

universe u

variable {M : Type u} [TopologicalSpace M] {C C' : Causality M} {W : Opens M}

/-! ## The two dual lemmas proved here -/

/-- `time_function` of the time reversal: `−T` (as `Causality.dual_hasTimeFunction`,
`Causal.HalfLitDual`, which this file does not import). -/
theorem hasTimeFunction_dual_iff : C.dual.HasTimeFunction ↔ C.HasTimeFunction := by
  have key : ∀ D : Causality M, D.HasTimeFunction → D.dual.HasTimeFunction := by
    rintro D ⟨T, hTc, hT⟩
    exact ⟨fun x => -T x, hTc.neg, fun x y hxy hne => neg_lt_neg (hT y x hxy (Ne.symm hne))⟩
  exact ⟨fun h => key C.dual h, key C⟩

/-- `curves_extend` of the time reversal: reverse the curve, extend it, reverse back (as
`Causality.CurvesExtend.dual`, `Causal.LemmaKBare`, which imports a model). -/
theorem curvesExtend_dual_iff : C.dual.CurvesExtend ↔ C.CurvesExtend := by
  have key : ∀ D : Causality M, D.CurvesExtend → D.dual.CurvesExtend := by
    intro D h c a b hab hc
    have hc' : D.CausalCurveOn ⊤ (fun t => c (-t)) (-b) (-a) :=
      CurveOn.neg (r := D.dual.le) (W := ⊤) (c := c) (a := -b) (b := -a)
        (by rw [neg_neg, neg_neg]; exact hc)
    obtain ⟨I, c', hc'i, hsub⟩ := h _ (-b) (-a) (neg_le_neg hab) hc'
    refine ⟨-I, fun t => c' (-t), hc'i.dual_reverse, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨u, hu, hcu⟩ := hsub ⟨-t, ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩, rfl⟩
    exact ⟨-u, by simpa using hu, by simpa using hcu⟩
  exact ⟨fun h => key C.dual h, key C⟩

/-! ## Two-sided nodes: `C.dual.P → C.P` and `C.P → C.dual.P` -/

theorem isCausal_of_dual (h : C.dual.IsCausal) : C.IsCausal := dual_isCausal.1 h
theorem isCausal_dual (h : C.IsCausal) : C.dual.IsCausal := dual_isCausal.2 h

theorem stronglyCausal_of_dual (h : C.dual.StronglyCausal) : C.StronglyCausal :=
  dual_stronglyCausal.1 h
theorem stronglyCausal_dual (h : C.StronglyCausal) : C.dual.StronglyCausal :=
  dual_stronglyCausal.2 h

theorem stronglyCausalOpen_of_dual (h : C.dual.StronglyCausalOpen) : C.StronglyCausalOpen :=
  dual_stronglyCausalOpen.1 h
theorem stronglyCausalOpen_dual (h : C.StronglyCausalOpen) :
    C.dual.StronglyCausalOpen :=
  dual_stronglyCausalOpen.2 h

theorem globallyHyperbolic_of_dual (h : C.dual.GloballyHyperbolic) : C.GloballyHyperbolic :=
  dual_globallyHyperbolic.1 h
theorem globallyHyperbolic_dual (h : C.GloballyHyperbolic) :
    C.dual.GloballyHyperbolic :=
  dual_globallyHyperbolic.2 h

theorem causallyCompact_of_dual (h : C.dual.CausallyCompact) : C.CausallyCompact :=
  dual_causallyCompact.1 h
theorem causallyCompact_dual (h : C.CausallyCompact) :
    C.dual.CausallyCompact :=
  dual_causallyCompact.2 h

theorem pushUp_of_dual (h : C.dual.PushUp) : C.PushUp := dual_pushUp.1 h
theorem pushUp_dual (h : C.PushUp) : C.dual.PushUp := dual_pushUp.2 h

theorem causallyOpen_of_dual (h : C.dual.CausallyOpen) : C.CausallyOpen := dual_causallyOpen.1 h
theorem causallyOpen_dual (h : C.CausallyOpen) : C.dual.CausallyOpen :=
  dual_causallyOpen.2 h

theorem absolutelyMinimal_of_dual (h : C.dual.AbsolutelyMinimal) : C.AbsolutelyMinimal :=
  dual_absolutelyMinimal.1 h
theorem absolutelyMinimal_dual (h : C.AbsolutelyMinimal) :
    C.dual.AbsolutelyMinimal :=
  dual_absolutelyMinimal.2 h

theorem causallyArcConnected_of_dual (h : C.dual.CausallyArcConnected) :
    C.CausallyArcConnected :=
  dual_causallyArcConnectedOn.1 h
theorem causallyArcConnected_dual (h : C.CausallyArcConnected) :
    C.dual.CausallyArcConnected :=
  dual_causallyArcConnectedOn.2 h

theorem causallyPlain_of_dual (h : C.dual.CausallyPlain) : C.CausallyPlain :=
  dual_causallyPlain.1 h
theorem causallyPlain_dual (h : C.CausallyPlain) : C.dual.CausallyPlain :=
  dual_causallyPlain.2 h

theorem tarentin_of_dual (h : C.dual.Tarentin) : C.Tarentin := dual_tarentin.1 h
theorem tarentin_dual (h : C.Tarentin) : C.dual.Tarentin := dual_tarentin.2 h

theorem hasTimeFunction_of_dual (h : C.dual.HasTimeFunction) : C.HasTimeFunction :=
  hasTimeFunction_dual_iff.1 h
theorem hasTimeFunction_dual (h : C.HasTimeFunction) :
    C.dual.HasTimeFunction :=
  hasTimeFunction_dual_iff.2 h

theorem curvesExtend_of_dual (h : C.dual.CurvesExtend) : C.CurvesExtend :=
  curvesExtend_dual_iff.1 h
theorem curvesExtend_dual (h : C.CurvesExtend) : C.dual.CurvesExtend :=
  curvesExtend_dual_iff.2 h

theorem locallyPushUp_of_dual (h : C.dual.LocallyPushUp) : C.LocallyPushUp :=
  dual_locallyPushUp.1 h
theorem locallyPushUp_dual (h : C.LocallyPushUp) : C.dual.LocallyPushUp :=
  dual_locallyPushUp.2 h

theorem locallyCausallyOpen_of_dual (h : C.dual.LocallyCausallyOpen) : C.LocallyCausallyOpen :=
  dual_locallyCausallyOpen.1 h
theorem locallyCausallyOpen_dual (h : C.LocallyCausallyOpen) :
    C.dual.LocallyCausallyOpen :=
  dual_locallyCausallyOpen.2 h

theorem chronalNeighbours_of_dual (h : C.dual.ChronalNeighbours) : C.ChronalNeighbours :=
  dual_chronalNeighbours.1 h
theorem chronalNeighbours_dual (h : C.ChronalNeighbours) :
    C.dual.ChronalNeighbours :=
  dual_chronalNeighbours.2 h

/-! ## One-sided nodes: the two-sided node from the future and the past forms -/

/-- `causally_open` from `causally_open_future` and its past form (`causallyOpen_iff`). -/
theorem causallyOpen_of_future_of_past (hf : C.CausallyOpenFuture)
    (hp : C.dual.CausallyOpenFuture) : C.CausallyOpen :=
  causallyOpen_iff.2 ⟨hf, hp⟩

/-- `locally_causally_open` from `locally_causally_open_future` and its past form (the
definition). -/
theorem locallyCausallyOpen_of_future_of_past (hf : C.LocallyCausallyOpenFuture)
    (hp : C.dual.LocallyCausallyOpenFuture) : C.LocallyCausallyOpen :=
  ⟨hf, hp⟩

/-! ## Pair nodes (the pattern of `leNested_dual`, `curveNestedOn_dual` on the first causality) -/

theorem leNested_of_dual (h : LeNested C.dual C'.dual) : LeNested C C' := dual_leNested_iff.1 h
theorem leNested_dual (h : LeNested C C') : LeNested C.dual C'.dual :=
  dual_leNested_iff.2 h

theorem curveNestedOn_of_dual (h : CurveNestedOn C.dual C'.dual W) : CurveNestedOn C C' W :=
  dual_curveNestedOn_iff.1 h
theorem curveNestedOn_dual (h : CurveNestedOn C C' W) :
    CurveNestedOn C.dual C'.dual W :=
  dual_curveNestedOn_iff.2 h

/-! ## The rules

`P_of_dual` and the introductions are plain forward rules; `P_dual` carries the pattern
`Causality.dual C` (see the module docstring). -/

attribute [aesop safe forward (rule_sets := [CausalLadder])]
  isCausal_of_dual stronglyCausal_of_dual stronglyCausalOpen_of_dual globallyHyperbolic_of_dual
  causallyCompact_of_dual pushUp_of_dual causallyOpen_of_dual absolutelyMinimal_of_dual
  causallyArcConnected_of_dual causallyPlain_of_dual tarentin_of_dual hasTimeFunction_of_dual
  curvesExtend_of_dual locallyPushUp_of_dual locallyCausallyOpen_of_dual chronalNeighbours_of_dual
  causallyOpen_of_future_of_past locallyCausallyOpen_of_future_of_past
  leNested_of_dual curveNestedOn_of_dual

attribute [aesop safe forward (pattern := Causality.dual C) (rule_sets := [CausalLadder])]
  isCausal_dual stronglyCausal_dual stronglyCausalOpen_dual globallyHyperbolic_dual
  causallyCompact_dual pushUp_dual causallyOpen_dual absolutelyMinimal_dual
  causallyArcConnected_dual causallyPlain_dual tarentin_dual hasTimeFunction_dual
  curvesExtend_dual locallyPushUp_dual locallyCausallyOpen_dual chronalNeighbours_dual
  leNested_dual curveNestedOn_dual

end Causal.LadderDual
