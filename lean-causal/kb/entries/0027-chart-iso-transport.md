---
id: 0027
title: Transport through a chart which is an isomorphism (ChartIso)
kind: pattern
created: 2026-11-20
---
A chart which is an isomorphism of topological spacetimes (`ChartIso`, `Causal.GXSingular`)
carries curves (`ChartIso.curveOn_symm`), causal arc-connectedness
(`ChartIso.causallyArcConnectedOn`) and push-up (`ChartIso.pushUpOn`) from the model to the chart
domain (`Causal/Remarks/MassiveManifold.lean`, T-ett-unanchored). With
`existsUnique_causality_singularGX` this makes a property of the model spaces a property of every
manifold of the atlas in one line (`massA_cac`, `pushup_sing`). Reuse these before transporting a
local property chart by chart.
