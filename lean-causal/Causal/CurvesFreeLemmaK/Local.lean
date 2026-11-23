import Causal.LemmaKSCLocal
import Causal.CurvesFreeLemmaK.SC

/-!
# Lemma K's local conditions on a second countable spacetime, without `CurvesExtend`

Programme target `T-abs-curves-free-lemma-k` (`programme/roadmap.toml`; DEC-190; layer 1: it
imports `Causal.LemmaKSCLocal` (which imports `Causal.LemmaKLocal`) and
`Causal.CurvesFreeLemmaK.SC`, ETT-layer; no model; no metric notion in a statement).
**No label is marked** (SCOPE). Lemma K is DEC-44's abstraction of Barbot's Rem 2.3 `clomax`
(`GHFspace.tex:572`); it carries no paper label.

`Causal.LemmaKLocal` has thirteen theorems carrying the named model fact `hext : C.CurvesExtend`
(kb/0012). Four already have their form, exactly the original less `hext` plus
`[SecondCountableTopology M]`, in `Causal.LemmaKSCLocal` (`isLocallyCauchyTwoSided_of_secondCountable`,
`isCauchySurface_iff_isOpen_Jplus_chartFutureSide_of_secondCountable`,
`isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus_of_secondCountable`,
`local_conditions_of_isOpen_Jplus_of_secondCountable`: Levin's route). The other nine have here a
form **beside the original**, of the same name suffixed `_secondCountable`: exactly the
original's binders less `hext`, with `[SecondCountableTopology M]` inserted after the original's
`[T2Space M]`. `hext` is discharged by `Causality.curvesExtend_of_t1_secondCountable C`
(kb/0142); for the three originals with no `Tarentin`/`GloballyHyperbolic` binder
(`strictJplus_eq_Jplus_chartFutureSide` here, and `Causal.LemmaKBare`'s `isOpen_strictJplus_of_twoSided`,
`isOpen_strictJplus_of_isCauchySplitting`) Levin's route would not apply, and the T1 route does.

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`ETT.tex:255`)

## What is proved (no `sorry`)

* The chart step `exists_nhds_subset_Jplus_of_isCauchySurfaceOn_secondCountable` and the open
  chart sides `isOpen_Jplus_diff_of_isCauchySurfaceOn_secondCountable`,
  `isOpen_Jminus_diff_of_isCauchySurfaceOn_secondCountable`.
* Two-sidedness and local Cauchyness coincide: `isLocallyCauchyTwoSided_iff_secondCountable`.
* Lemma K's consequences: the gx shape without two-sidedness
  (`isCauchySurface_of_isLocallyCauchy_of_pushUp_of_isOpen_Jplus_secondCountable`) and
  `CompactCauchy`'s proved form without two-sidedness
  (`isCauchySurface_of_isLocallyCauchy_of_splitting_secondCountable`).
* The residue: `isOpen_chartFutureSide_secondCountable`,
  `strictJplus_eq_Jplus_chartFutureSide_secondCountable`,
  `isCauchySurface_of_isOpen_Jplus_chartFutureSide_secondCountable`.
* Witnesses (kb/0011) on the timelike line, `Σ = {0}`, no curve hypothesis supplied:
  `timelikeLine_isCauchySurface_zero_of_lemmaKLocal_pushUp_secondCountable`,
  `timelikeLine_isCauchySurface_zero_of_lemmaKLocal_splitting_secondCountable`,
  `timelikeLine_isLocallyCauchyTwoSided_zero_secondCountable`,
  `timelikeLine_strictJplus_zero_eq_secondCountable` and
  `timelikeLine_isCauchySurface_zero_of_chartFutureSide_secondCountable` (the sharp residue
  applied, its openness hypotheses from `isOpen_chartFutureSide_secondCountable`).

## Hypothesis checklist

| original (`Causal/LemmaKLocal.lean:103–296`) | here |
|---|---|
| `[T2Space M]`, no countability | ✓ carried; `[SecondCountableTopology M]` added (`ETT.tex:255`) |
| `hext : C.CurvesExtend` (named, kb/0012) | ✓ dropped: `curvesExtend_of_t1_secondCountable C` |
| every other binder (openness, push-up, `Z^+`, the splitting) | ✓ carried unchanged |

## SCOPE (disclosed)

* **Nothing marked.** No ledger row lists a declaration of `Causal.LemmaKLocal`.
* **Beside, not replacing** (OQ-98 open), checked by elaborated binder lists (kb/0227); the four
  pre-existing forms of `Causal.LemmaKSCLocal` are re-verified there and not restated.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-! ## 1. The chart sides without `hext` -/

/-- `exists_nhds_subset_Jplus_of_isCauchySurfaceOn` without `hext`, `M` second countable: in a
chart, a point just above `Σ` has a whole neighbourhood above one point of `Σ`. -/
theorem exists_nhds_subset_Jplus_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    {U : Opens M} (hU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M} (hSc : IsClosed S)
    (hSU : C.IsCauchySurfaceOn U (S ∩ U)) {z y : M} (hz : z ∈ S ∩ U) (hy : y ∈ U)
    (hyS : y ∉ S) (hzy : C.le ⊤ z y) :
    ∃ s ∈ S ∩ U, ∃ N ∈ 𝓝 y, N ⊆ (U : Set M) ∩ Sᶜ ∧ ∀ y' ∈ N, C.le ⊤ s y' :=
  exists_nhds_subset_Jplus_of_isCauchySurfaceOn hT hG hC (curvesExtend_of_t1_secondCountable C) hU
    hSc hSU hz hy hyS hzy

/-- `isOpen_Jplus_diff_of_isCauchySurfaceOn` without `hext`, `M` second countable. -/
theorem isOpen_Jplus_diff_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    {U : Opens M} (hU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M} (hSc : IsClosed S)
    (hSU : C.IsCauchySurfaceOn U (S ∩ U)) : IsOpen (C.Jplus U (S ∩ U) \ S) :=
  isOpen_Jplus_diff_of_isCauchySurfaceOn hT hG hC (curvesExtend_of_t1_secondCountable C) hU hSc hSU

/-- `isOpen_Jminus_diff_of_isCauchySurfaceOn` without `hext`, `M` second countable. -/
theorem isOpen_Jminus_diff_of_isCauchySurfaceOn_secondCountable [T2Space M]
    [SecondCountableTopology M] (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    {U : Opens M} (hU : C.CausallyConvexIn (U : Set M) ⊤) {S : Set M} (hSc : IsClosed S)
    (hSU : C.IsCauchySurfaceOn U (S ∩ U)) : IsOpen (C.Jminus U (S ∩ U) \ S) :=
  isOpen_Jminus_diff_of_isCauchySurfaceOn hT hG hC (curvesExtend_of_t1_secondCountable C) hU hSc hSU

/-- `isLocallyCauchyTwoSided_iff` without `hext`, `M` second countable: for a closed set,
two-sidedness and local Cauchyness coincide. -/
theorem isLocallyCauchyTwoSided_iff_secondCountable [T2Space M] [SecondCountableTopology M]
    (hT : C.Tarentin)
    (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    {S : Set M} (hSc : IsClosed S) :
    C.IsLocallyCauchyTwoSided S ↔ C.IsLocallyCauchy S :=
  isLocallyCauchyTwoSided_iff hT hG hC (curvesExtend_of_t1_secondCountable C) hSc

/-! ## 2. Lemma K's consequences without `hext` -/

/-- **Lemma K in the shape gx needs, without two-sidedness, on a second countable spacetime**
(`isCauchySurface_of_isLocallyCauchy_of_pushUp_of_isOpen_Jplus` without `hext`). -/
theorem isCauchySurface_of_isLocallyCauchy_of_pushUp_of_isOpen_Jplus_secondCountable [T2Space M]
    [SecondCountableTopology M]
    [ConnectedSpace M] (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p}) (hpush : C.PushUp)
    (hZp : ∀ p : M, p ∈ C.Zplus) (hOp : ∀ V : Opens M, IsOpen (C.Jplus ⊤ V)) {S : Set M}
    (hSc : IsCompact S) (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchy_of_pushUp_of_isOpen_Jplus hT hG hC hJm hJp
    (curvesExtend_of_t1_secondCountable C) hpush hZp hOp hSc hSconn hloc

/-- **`CompactCauchy`'s proved form without two-sidedness, on a second countable spacetime**
(`isCauchySurface_of_isLocallyCauchy_of_splitting` without `hext`): a splitting suffices. -/
theorem isCauchySurface_of_isLocallyCauchy_of_splitting_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    {S₀ : Set M} {ψ : S₀ × ℝ ≃ₜ M} (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p})
    (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hψ : C.IsCauchySplitting S₀ ψ) {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchy S) : C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchy_of_splitting hT hG hC hJm hJp
    (curvesExtend_of_t1_secondCountable C) hψ hSc hSconn hloc

/-! ## 3. The residue without `hext` -/

/-- `isOpen_chartFutureSide` without `hext`, `M` second countable. -/
theorem isOpen_chartFutureSide_secondCountable [T2Space M] [SecondCountableTopology M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic)
    (hC : C.CausallyArcConnected) {S : Set M} (hSc : IsClosed S) :
    IsOpen (C.chartFutureSide S) :=
  isOpen_chartFutureSide hT hG hC (curvesExtend_of_t1_secondCountable C) hSc

/-- `strictJplus_eq_Jplus_chartFutureSide` without `hext`, `M` second countable: the strict causal
future of `Σ` is the causal future of its chart future side. -/
theorem strictJplus_eq_Jplus_chartFutureSide_secondCountable [T2Space M]
    [SecondCountableTopology M] (hcaus : C.IsCausal)
    (hC : C.CausallyArcConnected) {S : Set M}
    (hloc : C.IsLocallyCauchy S) : C.strictJplus S = C.Jplus ⊤ (C.chartFutureSide S) :=
  strictJplus_eq_Jplus_chartFutureSide hcaus hC (curvesExtend_of_t1_secondCountable C) hloc

/-- **Lemma K from the openness of `J^+(O^+)` and `J^-(O^-)`, on a second countable spacetime**
(`isCauchySurface_of_isOpen_Jplus_chartFutureSide` without `hext`). -/
theorem isCauchySurface_of_isOpen_Jplus_chartFutureSide_secondCountable [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S)
    (hloc : C.IsLocallyCauchy S) (hp : IsOpen (C.Jplus ⊤ (C.chartFutureSide S)))
    (hm : IsOpen (C.Jminus ⊤ (C.dual.chartFutureSide S))) : C.IsCauchySurface S :=
  isCauchySurface_of_isOpen_Jplus_chartFutureSide hT hG hC hJm hJp
    (curvesExtend_of_t1_secondCountable C) hSc hSconn hloc hp hm

end Causality

/-! ## 4. Witnesses on the timelike line (kb/0011) -/

/-- The gx shape without two-sidedness, new form, applied on the timelike line to `Σ = {0}`, no
curve hypothesis supplied. -/
theorem timelikeLine_isCauchySurface_zero_of_lemmaKLocal_pushUp_secondCountable :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, hpush, hZp, -, hSc, hSconn, hloc⟩ :=
    timelikeLine_lemmaKBare_hypotheses
  exact Causality.isCauchySurface_of_isLocallyCauchy_of_pushUp_of_isOpen_Jplus_secondCountable hT
    hG hC hJm hJp hpush hZp timelikeLine_isOpen_Jplus hSc hSconn hloc

/-- `CompactCauchy`'s form without two-sidedness, new form, applied on the timelike line along the
splitting `ψ(0, t) = t`, no curve hypothesis supplied. -/
theorem timelikeLine_isCauchySurface_zero_of_lemmaKLocal_splitting_secondCountable :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, hψ, hSc, hSconn, hloc⟩ := timelikeLine_lemmaK_hypotheses
  exact Causality.isCauchySurface_of_isLocallyCauchy_of_splitting_secondCountable hT hG hC hJm hJp
    hψ hSc hSconn hloc.isLocallyCauchy

/-- Two-sidedness of `{0}` on the timelike line from its local Cauchyness, through the new
form. -/
theorem timelikeLine_isLocallyCauchyTwoSided_zero_secondCountable :
    timelikeLine.IsLocallyCauchyTwoSided ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, -, -, -, -, -, -, hSc, -, hloc⟩ := timelikeLine_lemmaKBare_hypotheses
  exact (Causality.isLocallyCauchyTwoSided_iff_secondCountable hT hG hC hSc.isClosed).2 hloc

/-- The strict causal future of `{0}` on the timelike line is the causal future of its chart
future side, through the new form. -/
theorem timelikeLine_strictJplus_zero_eq_secondCountable :
    timelikeLine.strictJplus ({0} : Set ℝ) =
      timelikeLine.Jplus ⊤ (timelikeLine.chartFutureSide ({0} : Set ℝ)) := by
  obtain ⟨-, hG, hC, -, -, -, -, -, -, -, -, hloc⟩ := timelikeLine_lemmaKBare_hypotheses
  exact Causality.strictJplus_eq_Jplus_chartFutureSide_secondCountable hG.1 hC hloc

/-- The sharp residue's new form applied on the timelike line to `Σ = {0}`: the causal future of
the chart future side and the causal past of the chart past side are open (the chart sides are
open by `isOpen_chartFutureSide_secondCountable`, and `J^±` of an open set is open on the line). -/
theorem timelikeLine_isCauchySurface_zero_of_chartFutureSide_secondCountable :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, -, -, -, hSc, hSconn, hloc⟩ :=
    timelikeLine_lemmaKBare_hypotheses
  have hOp : IsOpen (timelikeLine.chartFutureSide ({0} : Set ℝ)) :=
    Causality.isOpen_chartFutureSide_secondCountable hT hG hC hSc.isClosed
  have hOm : IsOpen (timelikeLine.dual.chartFutureSide ({0} : Set ℝ)) :=
    Causality.isOpen_chartFutureSide_secondCountable (C := timelikeLine.dual)
      (Causality.dual_tarentin.2 hT) (Causality.dual_globallyHyperbolic.2 hG)
      (Causality.dual_causallyArcConnectedOn.2 hC) hSc.isClosed
  exact Causality.isCauchySurface_of_isOpen_Jplus_chartFutureSide_secondCountable hT hG hC hJm hJp
    hSc hSconn hloc (timelikeLine_isOpen_Jplus ⟨_, hOp⟩) (timelikeLine_isOpen_Jminus ⟨_, hOm⟩)

end Causal
