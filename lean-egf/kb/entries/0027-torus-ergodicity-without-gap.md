---
id: 0027
title: Ergodicity on tori without a spectral gap; NoAtoms of volume on AddCircle is not an instance
kind: pattern
created: 2026-11-22
---
Found by T-egf-tori-minimal. An invariant `L²` function with no non-zero frequency is constant
(`EGF.ergodic_of_mFourierCoeff`, applied to an invariant indicator); hyperbolic linear parts give
ergodicity for every translation (`EGF.ergodic_torusAffine_of_noPeriodic`), translations by
Kronecker (`EGF.ergodic_torusAffine_one_of_mFourier_ne_one`; almost every translation: the image of
`volume` under a surjective character is Haar, `isAddHaarMeasure_map_of_isFiniteMeasure` with
`isAddHaarMeasure_eq_of_isProbabilityMeasure`); then one ergodic element makes the group ergodic
(`EGF.isGroupErgodic_of_ergodic_mem`) and `EGF.universality_tori_of_ergodic` applies. At this pin
`NoAtoms (volume : Measure (AddCircle T))` is not an instance: `volume {0} = 0` by
`Metric.closedBall_zero` and `AddCircle.volume_closedBall` at `ε = 0` (T-egf-def-egf found the same).
