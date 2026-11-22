---
id: 0038
title: Pattern:
kind: pattern
created: 2026-11-22
---
Found by T-perf-star3. Pattern: a two-point MeasuredModel with weights uses mu := ENNReal.ofReal a • dirac true + ENNReal.ofReal b • dirac false. IsFiniteMeasure comes from Measure.smul_finite ENNReal.ofReal_ne_top, and integrals from integral_add_measure, integral_smul_measure and integral_dirac (Yamabe.star3Cex_integral). It is a cheap counterexample to a constant that depends on lambda_1 and C_SP.
