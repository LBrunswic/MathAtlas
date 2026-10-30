---
id: 0021
title: A space given by a distance formula with identifications: SeparationQuotient
kind: pattern
created: 2026-10-30
---
Define a `PseudoMetricSpace` on coordinates and take mathlib's `SeparationQuotient`, which is a
metric space (the cone `C_α`, `Causal/Model/Cone.lean`: `(r, θ)`, `θ ∈ AddCircle α`, apex
identified). Planar triangle inequalities with angles: write the law of cosines as
`‖r − s·e^{ia}‖` in ℂ. At this pin `AddCircle.norm_le_half_period` takes the period explicitly,
`AddCircle.norm_eq` implicitly. Lake's glob `CausalScaffold.*` includes submodules
(`CausalScaffold.Model.Cone`), and so does `Causal.*`.
