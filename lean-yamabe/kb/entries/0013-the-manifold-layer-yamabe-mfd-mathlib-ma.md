---
id: 0013
title: The manifold layer Yamabe.Mfd: Mathlib manifolds with boundary, a Riemannian bundle metric, measures read chartwise
kind: pattern
created: 2026-11-22
---
Found by T-yamabe-analysis. The manifold layer of lean-yamabe is Yamabe.Mfd (YamabeScaffold.Sobolev): Mathlib manifolds with boundary (ChartedSpace (EuclideanHalfSpace N) M, IsManifold (𝓡∂ N) ∞ M), a smooth Bundle.ContMDiffRiemannianMetric on TangentSpace, |∇u|_g = Mfd.gradNorm (dual norm of mfderiv), volumes as Mfd.IsLocallyLebesgue measures, boundary areas as Mfd.IsBoundaryMeasure (Trace); a MeasuredModel is tied to (M, g, μ, σ) by Mfd.Reads, and Mfd.readingModel / Mfd.reads_readingModel shows Reads is satisfiable for all data (orthonormal frame chosen pointwise: the model asks no measurability of d).
