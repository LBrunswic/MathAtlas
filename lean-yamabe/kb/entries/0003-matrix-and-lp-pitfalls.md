---
id: 0003
title: Positive definite factorisation, squared L^q norms, and dominated derivatives at this pin
kind: pitfall
created: 2026-11-20
---
A real positive definite matrix factors as `A = star R * R` via
`CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg` (needs `open scoped MatrixOrder`).
Squared real L^q norms are best taken as `(eLpNorm f q ν).toReal ^ 2` and compared at the level of
measures (`eLpNorm_mono_measure`, `eLpNorm_smul_measure_of_ne_top`, `withDensity_mono`).
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` gets stuck on instances unless `(μ := …) (F := …)
(F' := …)` are named. A negative first variation gives a strict decrease through
`IsLocalMin.hasDerivAt_eq_zero` by contradiction (T-yamabe-quotient).
