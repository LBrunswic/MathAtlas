---
id: 0013
title: § 2 sums are A_u^n sums; windows of a periodic sequence; ν₂, ν₃ by divisibility
kind: pattern
created: 2026-11-21
---
Found by T-syr-cycle-gcd. `gcdSum n (p_n x) α l = AunAlt n (l+1) α` (`Syracuse.gcdSum_eq_AunAlt`, `Syracuse.CycleGcd`), so `Syracuse.Aun_cast_of_cycle` evaluates them on a cycle. Every n-window of a periodic α : ℤ → ℕ has the same sum (`Syracuse.sum_range_periodic`); `sum_Ico_int_eq_sum_range` turns an Ico sum over ℤ into a range sum. `Aun`, `AunAlt` are computable and ℕ-valued, so small values close by `decide`. Write ν₂ ≥ b as `(b : ℕ∞) ≤ nu2 x`, ν₃ as `emultiplicity 3`, and switch to divisibility with `← pow_dvd_iff_le_emultiplicity`.
