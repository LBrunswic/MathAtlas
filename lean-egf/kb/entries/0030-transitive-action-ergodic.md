---
id: 0030
title: Ergodicity of a transitive compact-group action by Fubini; dense subgroups through aestabilizer
kind: pattern
created: 2026-11-22
---
Found by T-egf-sphere-dense-ergodic. Without a homogeneous-space API: Fubini on `G × X`
(`Measure.prod_apply`, `prod_apply_symm` of `{p | p.1 • p.2 ∈ s}`, transitivity and
`measure_preimage_mul_right`) gives `σ = σ(X) • (g ↦ g • x₀)₊ Haar`, so the orbit map is
quasi-measure-preserving; an a.e.-invariant set pulls back to an a.e.-invariant subset of `G`, where
Mathlib's instance `ErgodicSMul G G μ` (`Dynamics/Ergodic/Action/Regular.lean`) finishes
(`EGF.ergodicSMul_rotSphere`). Dense subgroups: `closure (range Φ) ≤ MulAction.aestabilizer` via
`Set.preimage_smul` and `inv_mem`, then `aeconst_of_dense_aestabilizer_smul` (`InnerRegular` of
`volume.toSphere` is found automatically): `EGF.ae_const_of_dense_rotations`.
