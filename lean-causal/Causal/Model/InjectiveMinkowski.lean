import Causal.CBG.Injective
import Causal.Splitting
import Causal.Model.CurvesExtendModels

/-!
# Sbierski's Lemma 3.3 on Minkowski space: the witnesses

No label is marked. The Minkowski witnesses of `Causal.CBG.Injective` (Sbierski 1309.7591,
Lemma 3.3, p. 13, in the abstract setting), moved here verbatim with the same full names
(T-abs-hoist-time-function), so that `Causal.CBG.Injective` imports no model: they need the time
slices of Minkowski space (`minkowskiSlice`, `minkowski_isCauchySurface_slice`, `Causal.Splitting`)
and `minkowski_curvesExtend`, `minkowski_isAcausal_of_isCauchySurface`
(`Causal.Model.CurvesExtendModels`). A model module: a layer-1 module never imports it.

> **Lemma 3.3.** Say $(M,g)$ and $(M',g')$ are two globally hyperbolic spacetimes with Cauchy
> surfaces $\Sigma$ and $\Sigma'$, respectively. Let $\psi : M\to M'$ be an isometric immersion
> such that $\psi|_\Sigma:\Sigma\to\Sigma'$ is a diffeomorphism. Then $\psi$ is an isometric
> embedding.

## What is proved

* **Witnesses** (kb/0011): `CBG.minkowski_injective_hypotheses` — every hypothesis of the
  principal theorem `CBG.injOn_of_injOn_cauchy` holds on `𝐌^{1,d}` for the identity, the time
  coordinate and the slice `{t = 0}`; `CBG.minkowski_sbierski_lemma_3_3` — the identity of
  Minkowski space is a Cauchy embedding by `CBG.sbierski_lemma_3_3`, every hypothesis discharged.

## Hypothesis checklist

| hypothesis of `injOn_of_injOn_cauchy` / `sbierski_lemma_3_3` | on `𝐌^{1,d}` |
|---|---|
| `φ` an abstract morphism, injective on `Σ` | ✓ the identity |
| a continuous `T` strictly increasing along `≤_M` | ✓ the time coordinate (`minkowski_time_strict`) |
| `Σ` a Cauchy surface, `φ(Σ)` acausal (Cauchy) | ✓ `minkowskiSlice d 0` |
| `N` causal, GH, causally arc-connected, curves extend | ✓ `minkowski_isCausal`, `minkowski_globallyHyperbolic`, `minkowski_causallyArcConnected`, `minkowski_curvesExtend` |

## SCOPE (disclosed)

* Moved, not restated (T-abs-hoist-time-function, 2026-11-21): the section "Witnesses on
  Minkowski space" of `Causal.CBG.Injective`, verbatim, less its last witness: the timelike-line
  witness `timelikeLine_injective_of_globallyHyperbolic` is model-free and stays in
  `Causal.CBG.Injective`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u v

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]

namespace CBG

/-! ### Witnesses on Minkowski space -/

/-- **The hypotheses of the principal theorem are jointly satisfiable on Minkowski space**
`𝐌^{1,d}` (kb/0011): the identity, the time coordinate, the slice `{t = 0}`. -/
theorem minkowski_injective_hypotheses (d : ℕ) :
    IsEMorphism (minkowski d) (minkowski d) id ∧ Continuous (fun p : Minkowski d => p.1) ∧
      (∀ x y : Minkowski d, (minkowski d).le ⊤ x y → x ≠ y → x.1 < y.1) ∧
      (minkowski d).IsCauchySurface (minkowskiSlice d 0) ∧ InjOn id (minkowskiSlice d 0) ∧
      (minkowski d).IsAcausal (id '' minkowskiSlice d 0) ∧ (minkowski d).IsCausal := by
  refine ⟨IsEMorphism.id, continuous_fst, minkowski_time_strict.2,
    minkowski_isCauchySurface_slice 0, injOn_id _, ?_, minkowski_isCausal⟩
  rw [image_id]
  exact minkowski_isAcausal_of_isCauchySurface (minkowski_isCauchySurface_slice 0)

/-- **Sbierski's form is non-vacuous**: the identity of Minkowski space is a Cauchy embedding by
`sbierski_lemma_3_3`, every hypothesis discharged. -/
theorem minkowski_sbierski_lemma_3_3 (d : ℕ) :
    IsCauchyEmbedding (minkowski d) (minkowski d) id := by
  have hS := minkowski_isCauchySurface_slice (d := d) 0
  exact sbierski_lemma_3_3 minkowski_globallyHyperbolic minkowski_globallyHyperbolic
    IsEMorphism.id continuous_fst minkowski_time_strict.2 hS (by rw [image_id]; exact hS)
    (injOn_id _) minkowski_causallyArcConnected (minkowski_curvesExtend d)

end CBG

end Causal
