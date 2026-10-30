---
id: 0018
title: Causalities through charts: transport, ChartIso, and the maximal atlas
kind: pattern
created: 2026-10-30
---
A causality given by a chart into a model is `Causality.chartTransport D e`; "the chart is an
isomorphism" is `ChartIso` (relational, equivalent to DEC-10's by `chartIso_iff_strongMorphism`).
Gluing with (B) asked only locally: `existsUnique_absolutelyMinimal_of_agree_locally`
(`Causal/GXStructure.lean`). A (G,X)-manifold has a maximal atlas (DEC-16):
`chartIso_of_mem_maximalAtlas` extends the chart condition from an atlas to its maximal atlas.
Mathlib details at this pin: a `ChartedSpace` given as a def must be `@[reducible]` and passed
with `@`; `HasGroupoid.compatible` needs `(G := …)`; compose with `e.symm.trans e'`.
