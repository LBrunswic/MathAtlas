---
id: 0165
title: U causally convex in M does not make its chart image causally convex in the model
kind: pitfall
created: 2026-11-21
---
Witness: `Causal.MeasuresManifolds.cutDiamond_separates` (`E^{1,2}` minus a point, the cut diamond; compact closure in `E^{1,2}`, not relatively compact in `M`). Pick `U′` convex in the model, then prove `U = e⁻¹(U′)` convex in `M` (`ChartIso.causallyConvexIn_source_inter_preimage`, via `le_of_causallyConvexIn_of_subset`: a convex `V` inside an open `S` gives `≤_S` from `≤_M` under causal arc-connectedness). `K⁻` through a chart: `mem_Kminus_of_intertwine`, `ChartIso.symm_mem_Kminus_iff` (pass to the tail of the sequence inside the open set) (T-ett-measures-manifolds).
