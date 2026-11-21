---
id: 0147
title: A finite measure with the null sets of an s-finite one: Measure.toFinite
kind: pattern
created: 2026-11-21
---
Use `μ.toFinite` (`Mathlib.MeasureTheory.Measure.WithDensityFinite`); no Gaussian density is needed. Its lemmas `toFinite_absolutelyContinuous`, `absolutelyContinuous_toFinite`, `toFinite_apply_eq_zero_iff` live in namespace `MeasureTheory`, not `MeasureTheory.Measure`. A finite measure on `ℝ × ℂ` is `Regular` by instance (`Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`) (T-ett-measures-e0).
