---
id: 0016
title: An explicit cycle in Lean: T_unique per step, then decide on the periodic sequence
kind: pattern
created: 2026-11-21
---
Found by T-syr-upper-bounds (`cycle_neg_seventeen`, `four_cycles`). Get each step of the orbit from `T_unique` with an explicit odd t and exponent k (its `.1` is k = v2(3x+1)). Chain the steps with `Function.iterate_succ_apply'`. Reduce a k x to a (k % n) x through `periodic_a_iff_periodic_T` and `Function.Periodic.map_mod_nat`, then use `interval_cases`. On an explicit periodic `seq : ℤ → ℕ`, `Aun`, `AunAlt`, `Delta`, `Finset.gcd` and `GCDMonoid.gcd` on ℤ all close by `decide`.
