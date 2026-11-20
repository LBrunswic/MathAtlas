---
id: 0007
title: Over ℤ every bound on p_n log 2 − n log 3 is a sum of log(1 + 1/(3Tᵏx))
kind: pattern
created: 2026-11-20
---
Found by T-syr-integer-bounds. The product form of lem:base, `Syracuse.pow_p_mul_T_iterate_eq_prod` (2^{p_n(x)} Tⁿ(x) = 3ⁿ x Π_{k<n}(1 + 1/(3Tᵏx)) for x ≠ 0), and its log form `Syracuse.log_identity_int` (`Syracuse.IntegerBounds`); the orbit never meets 0 (`T_iterate_ne_zero_int`) and keeps its sign (`T_iterate_pos_int`, `T_iterate_neg_int`). Concrete values come from `T_unique` with an explicit odd t and exponent k (`T_one_int`, `T_neg_one_int`); `decide`/`simp` do not compute `v2` (Mathlib's multiplicity).
