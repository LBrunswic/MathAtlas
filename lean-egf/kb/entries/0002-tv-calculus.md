---
id: 0002
title: Defects of a generative flow are truncated differences of finite measures; the TV calculus needs no SignedMeasure
kind: pattern
created: 2026-11-20
---
Found by T-egf-headline. δF_init and δF_term are Mathlib's truncated differences `R - B` of finite measures. `Measure.sub_le_iff_le_add`, `Measure.le_of_add_le_add_left` and `Measure.toJordanDecomposition_toSignedMeasure_sub` (`Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub`) give the whole total-variation calculus without passing through `SignedMeasure`: `EGF.tvMass`, `EGF.initialError_eq_negPart`, `EGF.errors_eq_tvMass`.
