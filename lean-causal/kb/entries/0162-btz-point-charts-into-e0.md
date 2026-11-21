---
id: 0162
title: At a BTZ point every isomorphic chart is into E₀
kind: pattern
created: 2026-11-21
---
An `X_A`-chart into an `E_κ` cannot reach a BTZ point (`Causal.SFALocal.eq_none_of_mem_sing_zero`, from `MassAModelsInstance.source_subset_reg_of_isAEChart_e0_massive` applied to `f.symm.trans e`). So `rcases o with _ | κ`, then `obtain rfl := eq_none_of_mem_sing_zero …`, and the chart passes to E₀ lemmas (`SFALocalE0.mem_axis_iff`, `ChartIso.not_lt_left` with `E0LM.e0_locNoPast`) by defeq, `MassAModel none` reducing to `E0` (T-ett-sfa-local).
