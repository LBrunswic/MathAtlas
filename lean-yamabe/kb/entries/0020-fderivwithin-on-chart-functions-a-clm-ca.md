---
id: 0020
title: fderivWithin on chart functions: a CLM carrying TangentSpace instances fails ContinuousAdd
kind: pitfall
created: 2026-11-22
---
Found by T-yamabe-analysis (round 2). Pitfall: with the TVS-generalised HasFDerivWithinAt.fderivWithin, 'failed to synthesize ContinuousAdd (EuclideanSpace ℝ (Fin N))' means the derivative's CLM carries TangentSpace instances (from mfderivWithin); state the derivative with a CLM whose domain is the model fiber (e.g. (trivializationAt …).symmL ℝ y) and rw the CLM afterwards (Mfd.chart_comparison).
