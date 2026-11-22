---
id: 0023
title: Spheres, SO(n), SU(d) and S¹: the toolkit of EGF.SphereFamilies
kind: pattern
created: 2026-11-22
---
Found by T-egf-families-sphere (`EGF/SphereFamilies.lean`).
- `EGF.RoundSphere n` with `EGF.sphereVolume n = volume.toSphere`. A linear isometry preserves it
  through `Measure.toSphere_apply'` and the set identity `(0,1)•e⁻¹(A) = e⁻¹((0,1)•A)`, with
  `MeasurePreserving.measure_preimage_equiv` for `e.toHomeomorph.toMeasurableEquiv` (no
  measurability of the cone needed); `toSphere` is `IsOpenPosMeasure`; `EGF.sphereVolume_univ_ne_zero`.
- `SO(n)` acts on `EuclideanSpace` through `Unitary.linearIsometryEquiv ⟨Matrix.toEuclideanCLM A.1,
  Unitary.map_mem _ A.2.1⟩` (`ofLp` of the image is `A *ᵥ ofLp x` by `rfl`); `SO(2)` entries from
  `Matrix.mem_specialOrthogonalGroup_fin_two_iff`.
- `SU(d)` needs instances Mathlib lacks: `IsTopologicalGroup` (`Submonoid.continuousMul`, inverse
  `star`), `CompactSpace` (`entry_norm_bound_of_unitary`, root namespace, with
  `isCompact_univ_pi`), `MeasurableSpace := borel`; its Haar probability is `haarMeasure ⊤`
  (`EGF.suHaar`). **Name** such instances on matrix groups (`EGF.instMeasurableSpaceSU`, …): a future
  Mathlib `MeasurableSpace (Matrix …)` would form a non-defeq diamond (AUDIT-1).
- On `S¹`, `ζ(x) = x₀ + i x₁` turns rotations into multiplication by a unit complex number
  (`EGF.zeta_rotSphere`); `∫ ζ^m dσ = 0` by the rotation of angle `π/m`; finitely many unit complex
  numbers have a common power near 1 (`EGF.exists_pow_near_one`, by `IsCompact.tendsto_subseq` and
  `Metric.cauchySeq_iff'`). Ergodicity of an irrational rotation for `σ`: transport `σ` to
  `AddCircle (2π)` (`AddCircle.homeomorphCircle'` and `ζ`), `Measure.isAddInvariant_eq_smul_of_compactSpace`
  gives `c • volume`, then `AddCircle.ergodic_add_right` (`EGF.ergodic_rotSphere_two`); it needs
  `haveI : Fact (0 < 2 * Real.pi)` locally, and `AddCircle.coe_add` takes the period explicitly.
- Density in `SU(2)`: `EGF.mem_topologicalClosure_zpowers` (a continuous hom `ℝ → G` with
  `h(2π) = 1` and `θ/2π` irrational has `h(t)` in the closure of the powers of `h(θ)`) and the Euler
  angles `EGF.su2_euler`.
