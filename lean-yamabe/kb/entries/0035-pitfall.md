---
id: 0035
title: pitfall:
kind: pitfall
created: 2026-11-22
---
Found by T-perf-capacity. pitfall: at this pin `zero_le` for ℝ≥0∞ takes its argument implicitly (write `fun _ => zero_le`), `tendsto_finset_sum` is deprecated for `tendsto_finsetSum`, `ofReal_norm_eq_enorm` for `ofReal_norm`; in `ENNReal.rpow_ne_top_of_nonneg` give the exponent `(y := …)` or the side goal is a metavariable
