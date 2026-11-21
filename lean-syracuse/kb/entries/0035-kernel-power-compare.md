---
id: 0035
title: A power comparison 3^q < 2^p with q ≈ 8·10⁴ by decide in the kernel
kind: pattern
created: 2026-11-21
---
Found by T-syr-cited-steps (`citedSteps_logb_lt`). `decide` closes it in under a second under `set_option exponentiation.threshold 200000 in`; then `exact_mod_cast` to ℝ, `Real.log_lt_log` and `Real.log_pow` give logb 2 3 < p/q. Take a convergent of log₂3 from above: 125743/79335 gives about 10⁻¹⁰.
