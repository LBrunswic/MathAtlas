---
id: 0164
title: Admissible measures through a chart isomorphism: choose the model's set first
kind: pattern
created: 2026-11-21
---
`Causal.MeasuresManifolds.ChartIso.admissiblePastOn` / `admissibleFutureOn` (module `Causal.MeasureTransfer`, ETT layer) carry a measure admissible on `e(U)` back to `U`, for every open `U` in the source, with no causal convexity, only `R1Space M`. `ChartIso.exists_admissiblePastOn` takes `U = e⁻¹(U′)` with `U′` causally convex in the model inside any neighbourhood; assembled as `ModelMeasuresLocal`, `isoChartsCover_modelMeasures(Local)`; at E≥0-manifolds `massA_modelMeasures(Local)` (`Causal.Remarks.MeasuresManifolds`) (T-ett-measures-manifolds).
