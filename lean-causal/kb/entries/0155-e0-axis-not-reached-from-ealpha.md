---
id: 0155
title: No a.e. isomorphism chart joins E₀'s axis to an E_κ: a causal proof, no holonomy
kind: pattern
created: 2026-11-21
---
`Causal.MassAModelsInstance.notMem_axis_of_isAEChart`: `J⁻` of a BTZ point lies on the axis (`E0.le_axis_iff'`), `J⁺` is closed in E₀ (`E0.isClosed_Jplus`), and a radial static curve in `E_κ` approaches the line from a regular point (`τ ↦ (τ, polar((t − τ)/2, θ))`, ½-Lipschitz; avoid `staticLe_of_ball` near the line, whose ball contains the apex). Consequences: (b′) `E₀ ↔ E_κ` (`hiso_row_none`, `hiso_column_none`), E₀-manifolds natural over the whole family (`massA_dec25_e0_manifolds`). To make an a.e. isomorphism chart a `ChartIso` on the regular part of its source, restrict with `isAEChart_restrOpen` and apply `chartIso_of_isAEChart_of_subset_reg` (T-ett-massa-models-instance).
