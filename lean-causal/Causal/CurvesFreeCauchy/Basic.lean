import Causal.CurvesExtendSecondCountable
import Causal.CausalIsoInvariance
import Causal.NestedCausalities
import Causal.ErsUniqueness

/-!
# Segments, time reversal and causal isomorphisms without `CurvesExtend`

Programme target `T-abs-curves-free-cauchy` (`programme/roadmap.toml`; DEC-190; layer 1: it
imports `Causal.CurvesExtendSecondCountable`, `Causal.CausalIsoInvariance`,
`Causal.NestedCausalities` and `Causal.ErsUniqueness`, all ETT-layer; no model; no metric notion in
a statement). **No label is marked**: no ledger row lists the three originals (SCOPE).

The three theorems of `Causal.NestedCausalities`, `Causal.CausalIsoInvariance` and
`Causal.CauchyExtension` with a named `CurvesExtend` binder (kb/0012) and no curve-free form yet
have one here, **beside the originals**: the original's binders less the `CurvesExtend` one, with
`[SecondCountableTopology M]` inserted after `[T2Space M]`, or `[T1Space M]
[SecondCountableTopology M]` appended where the original has no separation axiom. Names: the
original's suffixed `_secondCountable`, an original's `_of_curvesExtend` replaced by
`_of_secondCountable`. The discharge is `Causality.curvesExtend_of_t1_secondCountable` (kb/0142).

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`ETT.tex:255`)

## What is proved (no `sorry`)

1. `Causality.image_Icc_subset_of_secondCountable` (`image_Icc_subset_of_curvesExtend`,
   `Causal.NestedCausalities`; the step of ERS19 Lemma 4.72 behind
   `ers_lemma_4_72_secondCountable`): a causal segment of `M` with one end in `U` and one on an
   acausal Cauchy surface `S ⊆ U` of `U` lies in `U`, `M` causal, Hausdorff, second countable.
2. `Causality.CurvesExtend.dual_secondCountable` (`CurvesExtend.dual`, `Causal.CauchyExtension`).
3. `IsCausalIso.curvesExtend_secondCountable` (`IsCausalIso.curvesExtend`,
   `Causal.CausalIsoInvariance`): curves extend in the target of a causal isomorphism whose
   *source* is T1 and second countable; nothing is asked of the target.
4. Witnesses (kb/0011) on the timelike line: `timelikeLine_image_Icc_subset_secondCountable`
   (`U = ]-1, 1[`, `S = {0}`), `timelikeLine_dual_curvesExtend_secondCountable`, and
   `timelikeLine_transport_curvesExtend_secondCountable` (the transport of the line along any
   homeomorphism `ℝ ≃ₜ N`, with no instance on `N`).

## Hypothesis checklist

| original | here |
|---|---|
| `hext : C.CurvesExtend` (`image_Icc_subset_of_curvesExtend`) | ✓ dropped; `[T2Space M]` carried, `[SecondCountableTopology M]` added |
| `h : C.CurvesExtend` (`CurvesExtend.dual`), no separation axiom | ✓ dropped; ⚠ `[T1Space M] [SecondCountableTopology M]` added |
| `hC : C.CurvesExtend` (`IsCausalIso.curvesExtend`), no separation axiom | ✓ dropped; ⚠ `[T1Space M] [SecondCountableTopology M]` added, on the source only |

## SCOPE (disclosed)

* **Nothing marked**: no ledger row lists `image_Icc_subset_of_curvesExtend`,
  `CurvesExtend.dual` or `IsCausalIso.curvesExtend`; ERS19 Lemma 4.72's rows take
  `ers_lemma_4_72_secondCountable` (`Causal.ErsSecondCountable`), which needs no step form.
* **Beside, not replacing** (OQ-98 open); each pair is checked by elaborated binder lists
  (kb/0227).
* Forms 2 and 3 conclude `CurvesExtend` itself. Form 2 is the curves theorem for `C.dual`, kept
  because the target asks one form per binder; form 3 carries it to a target `N` on which no
  instance is asked (`timelikeLine_transport_curvesExtend_secondCountable`). `curvesExtend_iff`
  (`Causal.CausalIsoInvariance`) has no curve binder and is left.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u v

/-! ## 1. A segment ending on a Cauchy surface stays in the open set -/

namespace Causality

section Segment

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {U : Opens M} {S : Set M}

/-- **A curve segment of `M` with an end in `U` and an end on an acausal Cauchy surface `S` of `U`
lies in `U`**, `M` Hausdorff, second countable and causal: `image_Icc_subset_of_curvesExtend`
without `hext`. -/
theorem image_Icc_subset_of_secondCountable [T2Space M] [SecondCountableTopology M]
    (hcaus : C.IsCausal) (hSU : S ⊆ U) (hU : C.IsCauchySurfaceOn U S) (hS : C.IsAcausal S)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) (hγ : C.CausalCurveOn ⊤ γ a b)
    (hend : (γ a ∈ U ∧ γ b ∈ S) ∨ (γ a ∈ S ∧ γ b ∈ U)) :
    γ '' Icc a b ⊆ U :=
  image_Icc_subset_of_curvesExtend hcaus (curvesExtend_of_t1_secondCountable C) hSU hU hS hab hγ
    hend

end Segment

/-! ## 2. Time reversal -/

section Dual

variable {M : Type u} [TopologicalSpace M] {C : Causality M}

/-- `CurvesExtend.dual` without its hypothesis, `M` T1 and second countable: curves of the
reversed causality extend. -/
theorem CurvesExtend.dual_secondCountable [T1Space M] [SecondCountableTopology M] :
    C.dual.CurvesExtend :=
  (curvesExtend_of_t1_secondCountable C).dual

end Dual

end Causality

/-! ## 3. Causal isomorphisms -/

section Iso

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {C : Causality M} {D : Causality N} {e : M ≃ₜ N}

/-- `IsCausalIso.curvesExtend` without `hC`, the source `M` T1 and second countable: curves of `N`
extend along a causal isomorphism `M ≃ N`, with nothing asked of `N`. -/
theorem IsCausalIso.curvesExtend_secondCountable (h : IsCausalIso C D e) [T1Space M]
    [SecondCountableTopology M] : D.CurvesExtend :=
  h.curvesExtend (Causality.curvesExtend_of_t1_secondCountable C)

end Iso

/-! ## 4. Witnesses on the timelike line (kb/0011) -/

/-- **`image_Icc_subset_of_secondCountable` applies with no curve hypothesis supplied**: on the
timelike line, `U = ]-1, 1[`, `S = {0}` (acausal, Cauchy in `U`), the segment `id` on
`[0, 1/2]`, which starts on `S` and ends in `U`. -/
theorem timelikeLine_image_Icc_subset_secondCountable {U : Opens ℝ}
    (hU : (U : Set ℝ) = Ioo (-1) 1) : id '' Icc (0 : ℝ) (1 / 2) ⊆ U := by
  have h0 : (0 : ℝ) ∈ (U : Set ℝ) := by rw [hU]; norm_num
  have h1 : (1 / 2 : ℝ) ∈ (U : Set ℝ) := by rw [hU]; norm_num
  exact Causality.image_Icc_subset_of_secondCountable timelikeLine_isCausal
    (singleton_subset_iff.2 h0) (timelikeLine_isCauchySurfaceOn_Ioo one_pos hU)
    timelikeLine_isAcausal_zero (by norm_num) (timelikeLine_causalCurveOn_id 0 (1 / 2))
    (Or.inr ⟨rfl, h1⟩)

/-- Curves of the time-reversed timelike line extend, by `CurvesExtend.dual_secondCountable`
(no `timelikeLine_curvesExtend` supplied). -/
theorem timelikeLine_dual_curvesExtend_secondCountable : timelikeLine.dual.CurvesExtend :=
  Causality.CurvesExtend.dual_secondCountable

/-- **Curves extend in the transport of the timelike line along any homeomorphism `e : ℝ ≃ₜ N`**,
by `IsCausalIso.curvesExtend_secondCountable` on `isCausalIso_transport`: no instance on `N` and
no curve hypothesis is supplied. -/
theorem timelikeLine_transport_curvesExtend_secondCountable {N : Type v} [TopologicalSpace N]
    (e : ℝ ≃ₜ N) : (timelikeLine.transport e).CurvesExtend :=
  (isCausalIso_transport timelikeLine e).curvesExtend_secondCountable

end Causal
