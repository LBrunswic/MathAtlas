---
id: 0072
title: pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-perf-poincare. pitfall: MeasuredModel.mean_eq_volMean and toy_lambda1_pos already live in the strict Yamabe.Perforated.Main. Import Main instead of redefining them: a duplicate breaks any module that imports both.
