---
id: 0024
title: Two descending indices per period: one step recursion around the period, with no ascending index needed
kind: pattern
created: 2026-11-21
---
Found by T-syr-two-descents (`theo:syracuse_cycle`, `Syracuse.TwoDescents`). Run the step recursion `two_pow_mul_AunAlt_succ` once around the period in Z_u = A'_u + (2^P − 3ⁿ), where an ascending step reads 2Z_{u+1} = 3Z_u. One `linear_combination` with explicit coefficients gives D·(Z_c − 2^{r₁+1}E) = 0, and D odd cancels (`twoDesc_key`). Unlike `DeltaAlt_eq_asc`, it needs no ascending index, so a gap with none (k₂ = k₁ + 1) is no separate case (`twoDesc_adjacent`).
