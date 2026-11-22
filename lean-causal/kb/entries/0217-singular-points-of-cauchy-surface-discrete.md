---
id: 0217
title: The singular points of a Cauchy surface form a discrete subspace
kind: pattern
created: 2026-11-22
---
Each component of sing_α(M) is open in Sing(M) (`SingularRowsSecondCountable.exists_isOpen_inter_sing_subset`, from `IsLineDevelopment.local_onto` at t = 0) and meets every Cauchy surface exactly once (`existsUnique_mem_component_inter`), so Sing(M) ∩ S is discrete in S; countable by `discreteTopology_iff_isOpen_singleton` then `separableSpace_iff_countable` when S is second countable (T-ett-sc-cauchy-e0).
