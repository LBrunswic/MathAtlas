---
id: 0078
title: pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-perf-star-n. pitfall: toReal_enorm' does not rewrite norm-e of a real m; use Real.enorm_eq_ofReal_abs, then ENNReal.toReal_ofReal (abs_nonneg m), for eLpNorm_const's toReal = |m| * V^(1/q).
