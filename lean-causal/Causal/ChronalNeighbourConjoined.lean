import Causal.ChronalNeighbourBridge
import Causal.ChronalTarentin
import Causal.NotchedPlane

/-!
# Conjoined witnesses for the separations of `has_chronal_neighbour`: the notched plane, its time reversal and the global line

No label of `ETT.tex` is certified here. The file is the programme target
`T-abs-chronal-neighbour-conjoined` (layer 1, `programme/roadmap.toml`). It implements the keeper's
proposals of T-lad-has-chronal-neighbour (5117a6d). Two `[[fails]]` entries of
`programme/ladder.toml` have `has_chronal_neighbour`
(`Causal.Causality.HasChronalNeighbourEverywhere`) in their `from`, but their witnesses state it
"through one or two named lemmas, not as a conjunct". Each conjoined declaration below carries
every conjunct of the recorded witness and the node as well, so the keeper can point the entry at
one declaration.

> Its has_chronal_neighbour is the other half, split as the gated line's global hyperbolicity is:
> every point has chronal past neighbours in every open set, v − (ε, ε) ≪_V v
> (Causal.notchedCausality_chronalPastNeighbours, Causal/NotchedPlane.lean), hence a chronological
> past in M (Causal.Causality.ChronalPastNeighbours.Iminus_nonempty), the past side of
> HasChronalNeighbour […] A conjoined Lean statement (the witness with
> HasChronalNeighbourEverywhere, or a lemma ChronalPastNeighbours.hasChronalNeighbourEverywhere) is
> the keeper's proposal. (`programme/ladder.toml:2526–2539`, the notched plane's entry)

> Its first conjunct, globalLine.NonemptyChronalCones, gives has_chronal_neighbour by one
> application of Causal.Causality.NonemptyChronalCones.hasChronalNeighbourEverywhere […]: split as
> the gated line's global hyperbolicity is, no one Lean statement conjoining the two halves.
> (`programme/ladder.toml:1898–1902`, the global line's third entry)

* `Causality.ChronalPastNeighbours.hasChronalNeighbourEverywhere` and its future form
  `Causality.ChronalFutureNeighbours.hasChronalNeighbourEverywhere`, with the point forms
  `….hasChronalNeighbour`: chronal neighbours on one side, in every open set, give the node. The
  proof reads the hypothesis at the open set `M` (`ChronalPastNeighbours.Iminus_nonempty`,
  `ChronalFutureNeighbours.Iplus_nonempty`) and takes that side of `HasChronalNeighbour`.
* `Causal.notchedCausality_separates_hasChronalNeighbour`: the twenty conjuncts of
  `Causal.notchedCausality_separates`. It adds the node, absolute minimality on every open set
  (`notchedCausality_absolutelyMinimalOn`, so the entry stands in either reading of
  `defi:causalite`, DEC-167), and the one-sidedness that settles `has_chronal_neighbour → tarentin`:
  chronal past neighbours and no chronal future neighbours
  (`notchedCausality_not_chronalFutureNeighbours`).
* `Causal.notchedCausality_dual_separates_hasChronalNeighbour`: the twenty conjuncts of
  `Causal.notchedCausality_dual_separates`, plus the node through the future form, absolute
  minimality on every open set, and chronal future neighbours without chronal past neighbours.
* `Causal.globalLine_separates_hasChronalNeighbour`: the seven conjuncts of
  `Causal.globalLine_separates`, plus the node and `globalLine.Tarentin`
  (`Causal.globalLine_tarentin`). So it also carries every conjunct of
  `Causal.globalLine_separates_tarentin`. **No-gluing reading only**: its last conjunct is
  `¬ globalLine.AbsolutelyMinimal`. Under DEC-167 every ETT causality is absolutely minimal, so
  `globalLine` is no causality in that reading, and T-lad-gluing-reading may remove the entry.
* Bare forms: `Causal.not_tarentin_of_hasChronalNeighbourEverywhere_bare` (either reading: the
  hypothesis class asks absolute minimality on every open set) and
  `Causal.not_absolutelyMinimal_of_hasChronalNeighbourEverywhere_bare` (no-gluing reading only).

## Hypothesis checklist

| target's assertion | here |
|---|---|
| the notched plane with `HasChronalNeighbourEverywhere` | ✓ every conjunct of `notchedCausality_separates`, plus the node |
| a lemma `ChronalPastNeighbours.hasChronalNeighbourEverywhere` | ✓ no hypothesis but its own |
| "and its future form" | ✓ `ChronalFutureNeighbours.hasChronalNeighbourEverywhere`, used for the time-reversed plane |
| the global line's separation conjoined with the node | ✓ every conjunct of `globalLine_separates`, plus the node (and tarentin) |
| the global line's conjoined form says it is no causality with gluing | ✓ `¬ AbsolutelyMinimal` is a conjunct; the docstrings say so |
| the notched plane's entry stands either way | ✓ `∀ W, AbsolutelyMinimalOn W` is a conjunct |
| instance arguments | none beyond `[TopologicalSpace M]` for the four general lemmas; the model statements are closed (the bare forms quantify over the class inside the negation) |

## SCOPE (disclosed)

* **Layer 1.** The imports are `Causal.ChronalNeighbourBridge`, `Causal.ChronalTarentin` and
  `Causal.NotchedPlane`. `tools/ladder.py`'s `model_path` is `None` for each, checked one at a
  time in memory (kb/0247): no `Causal.Minkowski`, `Static`, `Flat.*`, `Model.*`, `Port.*` or
  `SingularFlat`, transitively. No statement mentions a metric, a curve length or a geodesic. The
  notched plane is the subtype `{u ≤ 0 ∨ v ≤ 0}` of `ℝ × ℝ`, as in `Causal.NotchedPlane`.
* **Nothing new about the models.** Every conjunct is an existing theorem of the strict library
  or a one-line consequence of one. No ladder step is needed beyond those the recorded
  separations already took. `causal_ladder` does not derive the node from `ChronalPastNeighbours`
  or from `NonemptyChronalCones`, which are no nodes. It does carry the node across time
  reversal (scratch probe `lean-causal/campaign/T-abs-chronal-neighbour-conjoined/LadderProbe.lean`,
  2026-11-23, not rechecked by a gate). The time-reversed plane's node is proved through
  the future form instead, so that the future form has a witness.
* **The added conjuncts other than the node are not nodes**: `ChronalPastNeighbours`,
  `ChronalFutureNeighbours` and `∀ W, AbsolutelyMinimalOn W` are named in the ladder's comments
  only (`NonemptyChronalCones` was already a conjunct of `globalLine_separates`). They are
  conjoined for the reader: they show the one-sidedness and the reading. `globalLine.Tarentin` is
  a node, added so that one declaration carries all three of the global line's entries.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-! ## One-sided chronal neighbours give a chronal neighbour at every point -/

/-- **Chronal past neighbours give a chronal neighbour at each point**: a chronological past in
`M` (`ChronalPastNeighbours.Iminus_nonempty`), the past side of `HasChronalNeighbour`. -/
theorem ChronalPastNeighbours.hasChronalNeighbour (h : C.ChronalPastNeighbours) (p : M) :
    C.HasChronalNeighbour p :=
  Or.inr (h.Iminus_nonempty p)

/-- **Chronal past neighbours give `has_chronal_neighbour`**: in every open set every point has a
chronal past neighbour, so every point has a chronological past in `M`. -/
theorem ChronalPastNeighbours.hasChronalNeighbourEverywhere (h : C.ChronalPastNeighbours) :
    C.HasChronalNeighbourEverywhere :=
  h.hasChronalNeighbour

/-- **Chronal future neighbours give a chronal neighbour at each point**: a chronological future
in `M` (`ChronalFutureNeighbours.Iplus_nonempty`), the future side of `HasChronalNeighbour`. -/
theorem ChronalFutureNeighbours.hasChronalNeighbour (h : C.ChronalFutureNeighbours) (p : M) :
    C.HasChronalNeighbour p :=
  Or.inl (h.Iplus_nonempty p)

/-- **Chronal future neighbours give `has_chronal_neighbour`** (the future form of
`ChronalPastNeighbours.hasChronalNeighbourEverywhere`). -/
theorem ChronalFutureNeighbours.hasChronalNeighbourEverywhere (h : C.ChronalFutureNeighbours) :
    C.HasChronalNeighbourEverywhere :=
  h.hasChronalNeighbour

end Causality

/-! ## The notched plane -/

/-- **The notched plane has a chronal neighbour at every point**, to the past: every point has
chronal past neighbours in every open set (`notchedCausality_chronalPastNeighbours`). -/
theorem notchedCausality_hasChronalNeighbourEverywhere :
    notchedCausality.HasChronalNeighbourEverywhere :=
  notchedCausality_chronalPastNeighbours.hasChronalNeighbourEverywhere

/-- **The notched plane has no chronal future neighbours**: it has chronal past neighbours and no
chronal neighbours (the corner has no chronal future, `notchedCausality_not_chronalNeighbours`). -/
theorem notchedCausality_not_chronalFutureNeighbours :
    ¬ notchedCausality.ChronalFutureNeighbours :=
  fun h => notchedCausality_not_chronalNeighbours ⟨notchedCausality_chronalPastNeighbours, h⟩

/-- **The notched plane, conjoined with `has_chronal_neighbour` for the ladder**: every conjunct of
`notchedCausality_separates` (Hausdorff and second countable; absolutely minimal, causally
arc-connected, causally plain, push-up and locally, causally open in the future and locally,
causal, causally compact, globally hyperbolic, strongly causal in both forms, a time function,
curves extend; neither causally open nor locally, no chronal neighbours, not tarentin). Added: a
chronal neighbour at every point; absolute minimality on every open set for every cover, so the
separation stands in either reading of `defi:causalite` (DEC-167); chronal past neighbours and no
chronal future neighbours, the one-sidedness by which `has_chronal_neighbour` does not give
tarentin. -/
theorem notchedCausality_separates_hasChronalNeighbour :
    T2Space notchedPlane ∧ SecondCountableTopology notchedPlane ∧
      notchedCausality.HasChronalNeighbourEverywhere ∧
      notchedCausality.AbsolutelyMinimal ∧
      (∀ W : Opens notchedPlane, notchedCausality.AbsolutelyMinimalOn W) ∧
      notchedCausality.CausallyArcConnected ∧
      notchedCausality.CausallyPlain ∧ notchedCausality.PushUp ∧
      notchedCausality.LocallyPushUp ∧ notchedCausality.CausallyOpenFuture ∧
      notchedCausality.LocallyCausallyOpenFuture ∧ notchedCausality.IsCausal ∧
      notchedCausality.CausallyCompact ∧ notchedCausality.GloballyHyperbolic ∧
      notchedCausality.StronglyCausalOpen ∧ notchedCausality.StronglyCausal ∧
      notchedCausality.HasTimeFunction ∧ notchedCausality.CurvesExtend ∧
      notchedCausality.ChronalPastNeighbours ∧ ¬ notchedCausality.ChronalFutureNeighbours ∧
      ¬ notchedCausality.CausallyOpen ∧ ¬ notchedCausality.LocallyCausallyOpen ∧
      ¬ notchedCausality.ChronalNeighbours ∧ ¬ notchedCausality.Tarentin :=
  let ⟨hT2, hSC, hAM, hAC, hCP, hPU, hLPU, hCOF, hLCOF, hIC, hCC, hGH, hSCO, hSC', hTF, hCE,
    hNCO, hNLCO, hNCN, hNT⟩ := notchedCausality_separates
  ⟨hT2, hSC, notchedCausality_hasChronalNeighbourEverywhere, hAM,
    notchedCausality_absolutelyMinimalOn, hAC, hCP, hPU, hLPU, hCOF, hLCOF, hIC, hCC, hGH, hSCO,
    hSC', hTF, hCE, notchedCausality_chronalPastNeighbours,
    notchedCausality_not_chronalFutureNeighbours, hNCO, hNLCO, hNCN, hNT⟩

/-! ## The time-reversed notched plane -/

/-- **The time-reversed notched plane has a chronal neighbour at every point**, to the future:
its chronal future neighbours are the plane's chronal past neighbours
(`dual_chronalFutureNeighbours`), and the future form applies. -/
theorem notchedCausality_dual_hasChronalNeighbourEverywhere :
    notchedCausality.dual.HasChronalNeighbourEverywhere :=
  Causality.ChronalFutureNeighbours.hasChronalNeighbourEverywhere (C := notchedCausality.dual)
    (Causality.dual_chronalFutureNeighbours.2 notchedCausality_chronalPastNeighbours)

/-- **The time-reversed notched plane, conjoined with `has_chronal_neighbour`**: every conjunct of
`notchedCausality_dual_separates` (Hausdorff and second countable; absolutely minimal, causally
arc-connected, causally plain, push-up and locally, causal, causally compact, globally hyperbolic,
strongly causal in both forms, a time function, curves extend; not causally open in the future,
nor locally, nor two-sided, nor locally two-sided, no chronal neighbours, not tarentin). Added: a
chronal neighbour at every point, absolute minimality on every open set for every cover, chronal
future neighbours and no chronal past neighbours. -/
theorem notchedCausality_dual_separates_hasChronalNeighbour :
    T2Space notchedPlane ∧ SecondCountableTopology notchedPlane ∧
      notchedCausality.dual.HasChronalNeighbourEverywhere ∧
      notchedCausality.dual.AbsolutelyMinimal ∧
      (∀ W : Opens notchedPlane, notchedCausality.dual.AbsolutelyMinimalOn W) ∧
      notchedCausality.dual.CausallyArcConnected ∧
      notchedCausality.dual.CausallyPlain ∧ notchedCausality.dual.PushUp ∧
      notchedCausality.dual.LocallyPushUp ∧ notchedCausality.dual.IsCausal ∧
      notchedCausality.dual.CausallyCompact ∧ notchedCausality.dual.GloballyHyperbolic ∧
      notchedCausality.dual.StronglyCausalOpen ∧ notchedCausality.dual.StronglyCausal ∧
      notchedCausality.dual.HasTimeFunction ∧ notchedCausality.dual.CurvesExtend ∧
      notchedCausality.dual.ChronalFutureNeighbours ∧
      ¬ notchedCausality.dual.ChronalPastNeighbours ∧
      ¬ notchedCausality.dual.CausallyOpenFuture ∧
      ¬ notchedCausality.dual.LocallyCausallyOpenFuture ∧
      ¬ notchedCausality.dual.CausallyOpen ∧ ¬ notchedCausality.dual.LocallyCausallyOpen ∧
      ¬ notchedCausality.dual.ChronalNeighbours ∧ ¬ notchedCausality.dual.Tarentin :=
  let ⟨hT2, hSC, hAM, hAC, hCP, hPU, hLPU, hIC, hCC, hGH, hSCO, hSC', hTF, hCE, hNCOF, hNLCOF,
    hNCO, hNLCO, hNCN, hNT⟩ := notchedCausality_dual_separates
  ⟨hT2, hSC, notchedCausality_dual_hasChronalNeighbourEverywhere, hAM,
    notchedCausality_dual_absolutelyMinimalOn, hAC, hCP, hPU, hLPU, hIC, hCC, hGH, hSCO, hSC', hTF,
    hCE, Causality.dual_chronalFutureNeighbours.2 notchedCausality_chronalPastNeighbours,
    fun h => notchedCausality_not_chronalFutureNeighbours
      (Causality.dual_chronalPastNeighbours.1 h),
    hNCOF, hNLCOF, hNCO, hNLCO, hNCN, hNT⟩

/-! ## The globally chronological line -/

/-- **The global line has a chronal neighbour at every point**: its chronological cones are
non-empty (`globalLine_nonemptyChronalCones`). -/
theorem globalLine_hasChronalNeighbourEverywhere : globalLine.HasChronalNeighbourEverywhere :=
  globalLine_nonemptyChronalCones.hasChronalNeighbourEverywhere

/-- **The global line, conjoined with `has_chronal_neighbour` for the ladder**: a chronal neighbour
at every point, tarentin (`globalLine_tarentin`), and every conjunct of `globalLine_separates`:
non-empty chronological cones, push-up, causally open, causal; no chronal past neighbours, no
chronal neighbours, **not absolutely minimal**. So it also carries every conjunct of
`globalLine_separates_tarentin`. A witness in the reading of `defi:causalite` without gluing only:
under DEC-167 every causality is absolutely minimal, and `globalLine` is none. -/
theorem globalLine_separates_hasChronalNeighbour :
    globalLine.HasChronalNeighbourEverywhere ∧ globalLine.Tarentin ∧
      globalLine.NonemptyChronalCones ∧ globalLine.PushUp ∧ globalLine.CausallyOpen ∧
      globalLine.IsCausal ∧ ¬ globalLine.ChronalPastNeighbours ∧
      ¬ globalLine.ChronalNeighbours ∧ ¬ globalLine.AbsolutelyMinimal :=
  let ⟨hNCC, hPU, hCO, hIC, hNCPN, hNCN, hNAM⟩ := globalLine_separates
  ⟨globalLine_hasChronalNeighbourEverywhere, globalLine_tarentin, hNCC, hPU, hCO, hIC, hNCPN, hNCN,
    hNAM⟩

/-! ## Bare forms -/

/-- **A chronal neighbour at every point does not give tarentin**, among Hausdorff, second
countable spacetimes absolutely minimal on every open set for every cover (either reading of
`defi:causalite`), causally plain, push-up, globally hyperbolic and causally open in the future:
the notched plane, which has chronal past neighbours in every open set but not chronal future
neighbours. -/
theorem not_tarentin_of_hasChronalNeighbourEverywhere_bare :
    ¬ ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      (C : Causality M), (∀ W : Opens M, C.AbsolutelyMinimalOn W) →
        C.HasChronalNeighbourEverywhere → C.CausallyPlain → C.PushUp →
        C.GloballyHyperbolic → C.CausallyOpenFuture → C.Tarentin :=
  fun h => notchedCausality_not_tarentin
    (h notchedPlane notchedCausality notchedCausality_absolutelyMinimalOn
      notchedCausality_hasChronalNeighbourEverywhere notchedCausality_causallyPlain
      notchedCausality_pushUp notchedCausality_globallyHyperbolic
      notchedCausality_causallyOpenFuture)

/-- **A chronal neighbour at every point does not give absolute minimality**, among Hausdorff,
second countable spacetimes that are tarentin, push-up, causally open and causal: the global
line. In the reading of `defi:causalite` without gluing only (under DEC-167 every causality is
absolutely minimal, and the global line is none). -/
theorem not_absolutelyMinimal_of_hasChronalNeighbourEverywhere_bare :
    ¬ ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      (C : Causality M), C.HasChronalNeighbourEverywhere → C.Tarentin → C.PushUp →
        C.CausallyOpen → C.IsCausal → C.AbsolutelyMinimal :=
  fun h => globalLine_not_absolutelyMinimal
    (h ℝ globalLine globalLine_hasChronalNeighbourEverywhere globalLine_tarentin globalLine_pushUp
      globalLine_causallyOpen globalLine_isCausal)

end Causal
