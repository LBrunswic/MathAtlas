---
id: 0321
title: The first exit of a curve from an open set is attained and lies in its closure
kind: pattern
created: 2026-11-28
---
First exit of a curve from an open `V`: `τ = sInf (Icc a b ∩ c ⁻¹' Vᶜ)` is attained (`ContinuousOn.preimage_isClosed_of_isClosed`, `IsClosed.csInf_mem`), and `c τ ∈ closure V` by `ContinuousWithinAt.mem_closure` with `closure_Ico`. Then `futureInextensible_of_leaving` applies with the larger open `W ⊔ Ũ`, since it asks `W ≤ U` (`Causal.BoundaryChartCauchy`).
