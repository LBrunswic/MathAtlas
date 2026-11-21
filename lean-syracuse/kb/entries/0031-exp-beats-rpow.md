---
id: 0031
title: Exponential beats polynomial with a real exponent C
kind: pattern
created: 2026-11-21
---
Found by T-syr-no-circuit (`noCircuit_eventually`). Bound (2en)^C by (2e)^⌈C⌉₊ n^⌈C⌉₊ (`Real.rpow_le_rpow_of_exponent_le`, base ≥ 1), then use `tendsto_pow_const_div_const_pow_of_one_lt`. No hypothesis on the sign of C is needed.
