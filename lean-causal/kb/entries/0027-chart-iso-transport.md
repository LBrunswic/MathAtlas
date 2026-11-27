---
id: 0027
title: Transport through a chart which is an isomorphism (ChartIso)
kind: pattern
created: 2026-11-20
---
A chart which is an isomorphism of topological spacetimes (`ChartIso`, `Causal.GXStructure`)
carries curves (`ChartIso.curveOn_symm`, in `Causal.GXStructure` since T-abs-hoist-stranded-homes,
with `chronalCurveOn_image`/`_symm_image`), causal arc-connectedness
(`ChartIso.causallyArcConnectedOn`) and push-up (`ChartIso.pushUpOn`) from the model to the chart
domain (the last two in `Causal/Remarks/MassiveManifold.lean`, T-ett-unanchored). With
`existsUnique_causality_singularGX` this makes a property of the model spaces a property of every
manifold of the atlas in one line (`massA_cac`, `pushup_sing`). Reuse these before transporting a
local property chart by chart.
