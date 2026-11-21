---
id: 0019
title: Universality from ergodicity alone (Cesàro, von Neumann); necessity with no invariant measure
kind: pattern
created: 2026-11-21
---
Found by T-egf-universality-ergodic. Prove `EGF.IsUniversalPolicy` from ergodicity with
`EGF.isUniversalPolicy_of_ergodic` (finite invariant `λ̂ ~ λ`, `IsKernelErgodic π λ̂`); ergodicity of
an EGF kernel from its moves by `EGF.isKernelErgodic_egfKernel_uniform` (uniform weights,
measure-preserving moves) or `EGF.IsEGFPolicy.isKernelErgodic` (positive weights), of a Mathlib
`Ergodic` map by `EGF.isKernelErgodic_deterministic`; the family by `EGF.universality_of_ergodic_family`.
Cesàro mixing in total variation is `EGF.exists_tvMass_cesaro_lt_of_ergodic`, on the ported density
action `EGF.Markov.densityActionL2` (a contraction of `L²(λ̂)`) whose fixed points are constant
(`EGF.Markov.ae_eq_const_of_densityAction_eq`: `(z − c)⁺` is an invariant density, `{z > c}` an
invariant set, then `exists_eventuallyEq_const_of_forall_separating` with rational half-lines), and
Mathlib's `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`. Necessity needs no
invariant measure: an invariant set blocks every outflow `≪ λ` (`EGF.two_le_errors_of_invariant_set`).
"Ergodic" here is for `λ̂`, not `def:egf`'s topological ergodicity (OQ-48). Pitfalls at this pin:
`ENNReal.mul_lt_mul_left` multiplies on the right; `Measure.map_dirac` needs
`MeasurableSingletonClass` (the measurable form is `Measure.map_dirac'`).
