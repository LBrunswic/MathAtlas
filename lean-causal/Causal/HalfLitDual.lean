import Causal.Dec8MinimalWitness
import Causal.Ladder.Rules

/-!
# The time-reversed half-lit line: causally arc-connected, globally hyperbolic, push-up, and neither causally open in the future nor locally so

Programme target `T-abs-halflit-dual-separates` (its block in `programme/roadmap.toml`; layer 1,
no label of `ETT.tex`). Imports: `Causal.Dec8MinimalWitness` (the half-lit line) and
`Causal.Ladder.Rules` (the `causal_ladder` tactic), both ETT layer: no model, no CBG, Splitting,
LemmaK* or LevinUtility module, transitively. Each property is stated with the ladder's definition
(`programme/ladder.toml`, the `lean` field of its `[[property]]`) applied to `halfLightLine.dual`.

* **`T-abs-halflit-dual-separates/1-transport`** — the half-lit line's ladder facts read on its
  time reversal through the `dual_*` transport lemmas: causally arc-connected
  (`Causality.dual_causallyArcConnectedOn` at `⊤`), absolutely minimal
  (`Causality.dual_absolutelyMinimal`), and on every open set for every cover of it
  (`halfLightLine_dual_absolutelyMinimalOn`), globally hyperbolic, push-up, strongly causal with
  open causally convex neighbourhoods, and neither tarentin, nor with chronal neighbours, nor
  causally plain; causally compact, causal, locally push-up, strongly causal and with curves
  extending by `causal_ladder`.
* **`T-abs-halflit-dual-separates/2-time-function`** — `Causality.dual_hasTimeFunction` (`T ↦ −T`),
  so `−id` is a time function of `halfLightLine.dual` (`halfLightLine_dual_hasTimeFunction`).
* **`T-abs-halflit-dual-separates/3-not-causally-open-future`** —
  `halfLightLine_dual_not_locallyCausallyOpenFuture`, by `causal_ladder` through the edge
  `absolutely_minimal ∧ locally_causally_open_future ⇒ causally_open_future` and
  `halfLightLine_not_causallyOpenPast` (`¬ halfLightLine.dual.CausallyOpenFuture`); directly, no
  open set containing `0` is causally open in the future for the dual
  (`halfLightLine_not_causallyOpenPastOn_of_zero_mem`).
* **`T-abs-halflit-dual-separates/4-separation`** —
  `halfLightLine_dual_separates_causallyOpenFuture`, the conjoined witness;
  `not_locallyCausallyOpenFuture_of_causallyArcConnected_bare`.

> Every piece is in Lean: Causal.halfLightLine_dual_separates (Causal/Dec8MinimalWitness.lean:432:
> the dual absolutely minimal, ¬ dual.CausallyOpenFuture), halfLightLine_not_causallyOpenPast
> (:219), halfLightLine_not_causallyOpenPastOn_of_zero_mem (:232), […] and the transport lemmas
> […]; ¬ dual.LocallyCausallyOpenFuture from absolute minimality and ¬ dual.CausallyOpenFuture
> (AbsolutelyMinimal.causallyOpenFuture_of_locallyCausallyOpenFuture, Causal/LadderLocal.lean:264),
> or at 0 from :232. Optional conjunct: a time function for the dual (−id […]).
> (the target's evidence, `programme/roadmap.toml`)

> Let $M$ be a topological spacetime. The causality of $M$ is open, and $M$ is causally open, if
> for every open subset $\U$ of $M$ and every open subset $\V\subset \U$ the set $J^+_\U(\V)$ is
> open. (`def:causally_open_spacetime_open`, `ETT.tex:694–697`)

## Hypothesis checklist

| target claim | here |
|---|---|
| causally arc-connected, absolutely minimal (`dual_causallyArcConnectedOn`, `dual_absolutelyMinimal`) | ✓ proved; absolutely minimal on every open set for every cover too |
| globally hyperbolic, hence causally compact (`dual_globallyHyperbolic`; GH ⇒ causally compact) | ✓ proved, the second by `causal_ladder` |
| push-up, strongly causal with open causally convex neighbourhoods (`dual_pushUp`, `dual_stronglyCausalOpen`) | ✓ proved |
| ¬ causally open in the future (`halfLightLine_not_causallyOpenPast`) | ✓ carried |
| ¬ locally causally open in the future (absolute minimality, or at `0`) | ✓ proved, by `causal_ladder` |
| optionally a time function, `−id` | ✓ proved, through `dual_hasTimeFunction` |

## SCOPE (disclosed)

* Every argued fact of the target's evidence is confirmed against the compiled definitions; none is
  refuted. Beyond the target's list the conjoined theorem also states the dual's causality, local
  push-up, strong causality, curves extending, and its failures of two-sided causal openness (global
  and local), tarentin, chronal neighbours and causal plainness, each a ladder node, so that it is
  the half-lit line's witness `halfLightLine_separates_causallyOpen` read in reversed time.
* **Either reading of `defi:causalite`** (OQ-18): the dual is absolutely minimal on every open set
  for every cover of it (`halfLightLine_dual_absolutelyMinimalOn`), the gluing reading's form.
* **For the ladder** (its recording is `T-lad-record-dual-vee`): the conjoined witness refutes, in
  either reading, `causally_arc_connected → causally_open_future` and `causally_arc_connected`,
  `causally_compact`, `globally_hyperbolic → locally_causally_open_future`, the four `[[open]]`
  pairs the target names, and gives `causally_compact`, `globally_hyperbolic →
  causally_open_future` an absolutely minimal witness (the jump line's is not).
* `ℝ` is Hausdorff and second countable (mathlib instances): the line is one of ETT's spacetimes.
  No metric notion appears in a statement: the order and the topology of `ℝ` only.
* `Causality.dual_hasTimeFunction` is general (any `C`); it belongs beside `HasTimeFunction` in
  `Causal.CurvesExtend`, which this target may not edit (a hoist for the master).
* Names checked unique against `Causal/`, the scaffold, `lean-gx/` and `lean-benzecri/`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology

namespace Causality

variable {M : Type*} [TopologicalSpace M] {C : Causality M}

/-- **A time function of the time reversal** (`time_function` of `C.dual`): `T` is continuous and
strictly increasing along `≤` of `C` iff `−T` is so along `≤` of `C.dual`. -/
theorem dual_hasTimeFunction : C.dual.HasTimeFunction ↔ C.HasTimeFunction := by
  have key : ∀ D : Causality M, D.HasTimeFunction → D.dual.HasTimeFunction := by
    rintro D ⟨T, hTc, hT⟩
    exact ⟨fun x => -T x, hTc.neg, fun x y hxy hne => neg_lt_neg (hT y x hxy (Ne.symm hne))⟩
  exact ⟨fun h => key C.dual h, key C⟩

end Causality

/-! ## The time-reversed half-lit line in the ladder -/

/-- **The time-reversed half-lit line is absolutely minimal on every open set, for every cover of
it** (the gluing reading of `defi:causalite`, OQ-18): every open set is causally arc-connected for
the dual. -/
theorem halfLightLine_dual_absolutelyMinimalOn (W : Opens ℝ) :
    halfLightLine.dual.AbsolutelyMinimalOn W :=
  Causality.CausallyArcConnectedOn.absolutelyMinimalOn
    (Causality.dual_causallyArcConnectedOn.2 (halfLightLine_causallyArcConnectedOn W))

/-- **A time function of the time-reversed half-lit line**: `−id`. -/
theorem halfLightLine_dual_hasTimeFunction : halfLightLine.dual.HasTimeFunction :=
  Causality.dual_hasTimeFunction.2 halfLightLine_hasTimeFunction

/-- **The time-reversed half-lit line is not locally causally open in the future**: being absolutely
minimal, it would otherwise be causally open in the future
(`absolutely_minimal ∧ locally_causally_open_future ⇒ causally_open_future`), and it is not
(`halfLightLine_not_causallyOpenPast`). At `0` directly: no open set containing `0` is causally open
in the future for the dual (`halfLightLine_not_causallyOpenPastOn_of_zero_mem`). -/
theorem halfLightLine_dual_not_locallyCausallyOpenFuture :
    ¬ halfLightLine.dual.LocallyCausallyOpenFuture := by
  intro h
  have hm : halfLightLine.dual.AbsolutelyMinimal :=
    Causality.dual_absolutelyMinimal.2 halfLightLine_absolutelyMinimal
  exact halfLightLine_not_causallyOpenPast (by causal_ladder)

/-! ## The separation -/

/-- **Causal arc-connectedness, global hyperbolicity and causal compactness do not give causal
openness in the future, nor locally** (`causally_arc_connected`, `causally_compact`,
`globally_hyperbolic` `⇏ causally_open_future`, `⇏ locally_causally_open_future`; with every
positive conjunct in the `from`). The time-reversed half-lit line is absolutely minimal, causally
arc-connected, push-up (hence locally), causal, globally hyperbolic (hence causally compact),
strongly causal (both forms), with a time function (`−id`, hence curves extend); it is neither
causally open in the future nor locally so, neither causally open nor locally so, not tarentin, not
causally plain, and has no chronal neighbours. The conjoined witness for the ladder: the half-lit
line's `halfLightLine_separates_causallyOpen` in reversed time. -/
theorem halfLightLine_dual_separates_causallyOpenFuture :
    halfLightLine.dual.AbsolutelyMinimal ∧ halfLightLine.dual.CausallyArcConnected ∧
      halfLightLine.dual.PushUp ∧ halfLightLine.dual.LocallyPushUp ∧
      halfLightLine.dual.IsCausal ∧ halfLightLine.dual.GloballyHyperbolic ∧
      halfLightLine.dual.CausallyCompact ∧ halfLightLine.dual.StronglyCausalOpen ∧
      halfLightLine.dual.StronglyCausal ∧ halfLightLine.dual.HasTimeFunction ∧
      halfLightLine.dual.CurvesExtend ∧
      ¬ halfLightLine.dual.CausallyOpenFuture ∧ ¬ halfLightLine.dual.LocallyCausallyOpenFuture ∧
      ¬ halfLightLine.dual.CausallyOpen ∧ ¬ halfLightLine.dual.LocallyCausallyOpen ∧
      ¬ halfLightLine.dual.Tarentin ∧ ¬ halfLightLine.dual.ChronalNeighbours ∧
      ¬ halfLightLine.dual.CausallyPlain := by
  -- the half-lit line's facts, transported (`dual_*`)
  have hAC : halfLightLine.dual.CausallyArcConnected :=
    Causality.dual_causallyArcConnectedOn.2 halfLightLine_causallyArcConnected
  have hAM : halfLightLine.dual.AbsolutelyMinimal :=
    Causality.dual_absolutelyMinimal.2 halfLightLine_absolutelyMinimal
  have hGH : halfLightLine.dual.GloballyHyperbolic :=
    Causality.dual_globallyHyperbolic.2 halfLightLine_globallyHyperbolic
  have hPU : halfLightLine.dual.PushUp := Causality.dual_pushUp.2 halfLightLine_pushUp
  have hSCO : halfLightLine.dual.StronglyCausalOpen :=
    Causality.dual_stronglyCausalOpen.2 halfLightLine_stronglyCausalOpen
  have hTF : halfLightLine.dual.HasTimeFunction := halfLightLine_dual_hasTimeFunction
  have hNCOF : ¬ halfLightLine.dual.CausallyOpenFuture := halfLightLine_not_causallyOpenPast
  have hNLCOF : ¬ halfLightLine.dual.LocallyCausallyOpenFuture :=
    halfLightLine_dual_not_locallyCausallyOpenFuture
  have hNT : ¬ halfLightLine.dual.Tarentin := fun h =>
    halfLightLine_not_tarentin (Causality.dual_tarentin.1 h)
  have hNCN : ¬ halfLightLine.dual.ChronalNeighbours := fun h =>
    halfLightLine_not_chronalNeighbours (Causality.dual_chronalNeighbours.1 h)
  have hNCP : ¬ halfLightLine.dual.CausallyPlain := fun h =>
    halfLightLine_not_causallyPlain (Causality.dual_causallyPlain.1 h)
  -- the ladder steps (`causal_ladder`): push_up ⇒ locally_push_up, globally_hyperbolic ⇒ is_causal,
  -- causally_compact, strongly_causal_open ⇒ strongly_causal, time_function ⇒ curves_extend; and,
  -- read backwards, causally_open ⇒ causally_open_future, locally_causally_open ⇒
  -- locally_causally_open_future
  exact ⟨hAM, hAC, hPU, by causal_ladder, by causal_ladder, hGH, by causal_ladder, hSCO,
    by causal_ladder, hTF, by causal_ladder, hNCOF, hNLCOF, fun _ => hNCOF (by causal_ladder),
    fun _ => hNLCOF (by causal_ladder), hNT, hNCN, hNCP⟩

/-- **Causal arc-connectedness does not give local causal openness in the future** (the ladder's
`causally_arc_connected → locally_causally_open_future`, hence `→ causally_open_future`), not even
with global hyperbolicity and push-up, on `ℝ`. -/
theorem not_locallyCausallyOpenFuture_of_causallyArcConnected_bare :
    ¬ ∀ C : Causality ℝ, C.CausallyArcConnected → C.GloballyHyperbolic → C.PushUp →
      C.LocallyCausallyOpenFuture := fun h =>
  let ⟨_, hAC, hPU, _, _, hGH, _⟩ := halfLightLine_dual_separates_causallyOpenFuture
  halfLightLine_dual_not_locallyCausallyOpenFuture (h _ hAC hGH hPU)

end Causal
