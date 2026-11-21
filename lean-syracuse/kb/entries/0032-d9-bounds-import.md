---
id: 0032
title: Pitfall: the d9 bounds on e and log 2 need an import Syracuse does not have
kind: pitfall
created: 2026-11-21
---
Found by T-syr-no-circuit and T-syr-cited-steps. `Real.exp_one_gt_d9`, `Real.exp_one_lt_d9` and `Real.log_two_gt_d9` live in `Mathlib.Analysis.Complex.ExponentialBounds`, which `Syracuse.TwoDescents` does not import (NoCircuit.lean adds it). Without it: log 2 ≥ 1/2 and log 3 ≥ 1/2 from `Real.one_sub_inv_le_log_of_pos`; log₁₀ 3 through 10^47 < 3^100 < 10^48 with `Real.log_lt_log` and `Real.log_pow`.
