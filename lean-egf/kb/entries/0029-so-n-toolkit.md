---
id: 0029
title: SO(n): named instances, transitivity on the sphere, the SO(3) computations
kind: pattern
created: 2026-11-22
---
Found by T-egf-sphere-dense-ergodic (`EGF/SphereDense.lean`). Named instances on `SO n`
(`EGF.instIsTopologicalGroupSO`, `instCompactSpaceSO`, `instSecondCountableTopologySO`,
`instMeasurableSpaceSO := borel`, `instBorelSpaceSO`; `EGF.soHaar n := haarMeasure ⊤`).
`SecondCountableTopology (SO n)` is not found by `infer_instance` (a coerced `Submonoid`, and `Matrix`
has no such instance): build the matrix one by `inferInstanceAs (SecondCountableTopology (Fin n →
Fin n → ℝ))` and apply `TopologicalSpace.Subtype.secondCountableTopology _`. Right invariance on a
compact group: `Measure.isMulInvariant_eq_smul_of_compactSpace (map (· * g) μ) μ`, evaluated at
`univ`. Transitivity on `S^{n−1}`, `n ≥ 2`: `Submodule.reflection_sub` sends `x` to `y`,
`Submodule.det_reflection` gives `(−1)^{finrank Kᗮ}`, a second reflection in a non-zero `v ⊥ y` fixes
`y`; a determinant-1 linear isometry is an element of `SO n` (`EGF.exists_SO_of_det_eq_one`, through
`LinearMap.toMatrix` in `EuclideanSpace.basisFun`). `SO(3)`: `rotZ`, `rotX` membership by `ext`,
`fin_cases`, `simp [Matrix.mul_apply, Fin.sum_univ_three]`, `nlinarith [cos_sq_add_sin_sq]`; Euler
angles by `EGF.exists_angle` and `EGF.exists_rotZ_of_fix`; density by `mem_topologicalClosure_zpowers`.
