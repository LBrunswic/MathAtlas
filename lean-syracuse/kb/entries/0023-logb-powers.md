---
id: 0023
title: Powers of 2 against powers of 3 with logb: reduce to the exponents, then to integer powers
kind: pattern
created: 2026-11-21
---
Found by T-syr-steiner (`steiner_printed_bound_iff`, `steiner_bound`). `Real.rpow_le_rpow_left_iff` or `rpow_lt_rpow_of_exponent_lt` reduce to the exponents; `Real.log_div_log` turns `logb 3 2` into `log 2 / log 3`, then `div_le_iff₀` and `Real.log_le_log_iff` with `Real.log_pow` give an integer power inequality.
