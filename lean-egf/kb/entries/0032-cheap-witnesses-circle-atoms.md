---
id: 0032
title: Cheap witnesses on the circle and on atoms
kind: pattern
created: 2026-11-22
---
Found by T-egf-def-egf. The forward `ℕ`-orbit of a rotation of infinite order of `AddCircle T` is
dense (`EGF.denseRange_nsmul_of_addOrderOf_eq_zero`; Mathlib has only the `ℤ`-orbit,
`AddCircle.denseRange_zsmul_iff`). A.e. statements for finite sums of Dirac masses reduce to the
atoms (`ae_add_measure_iff`, `ae_dirac_eq` with `MeasurableSingletonClass`, then `decide` on `Fin n`
after a `show` of the concrete membership); every group is ergodic for a Dirac mass
(`EGF.isGroupErgodic_dirac`); a finite measure with atoms on a `ℤ`-orbit is `EGF.orbitLam`
(`Measure.sum` with weights `2⁻¹ ^ (Equiv.intEquivNat n)`, finite by `Equiv.tsum_eq`,
`ENNReal.tsum_geometric`, `ENNReal.one_sub_inv_two`).
