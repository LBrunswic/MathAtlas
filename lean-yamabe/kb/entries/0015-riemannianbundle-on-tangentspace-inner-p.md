---
id: 0015
title: RiemannianBundle on TangentSpace: inner product by rfl, FiniteDimensional by inferInstanceAs, mfderiv's codomain
kind: pitfall
created: 2026-11-22
---
Found by T-yamabe-analysis. Pitfall: with letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩ the tangent spaces become inner product spaces (‖v‖² = g.inner x v v by rfl); FiniteDimensional must be given by inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin N))). mfderiv u x lands in TangentSpace 𝓘(ℝ, ℝ) (u x), on which ^ 2 fails: wrap it in a def with declared codomain ℝ (Mfd.dcov).
