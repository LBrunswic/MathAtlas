---
id: 0324
title: A Cauchy surface of an open set meets each vertical line through it: exists_mem_connectedComponentIn
kind: pattern
created: 2026-11-28
---
To make a Cauchy surface of an open `W` meet a vertical line `τ ↦ (τ, y)` of a static spacetime, use `Causality.IsCauchySurfaceOn.exists_mem_connectedComponentIn` (`Causal.InextensiblePiece`) with `T = Prod.fst`: the maximal piece never needs computing (`Causal.Model.MinkowskiPastBoundaryChart`, the per-point failure of (B)). `Causal.InextensiblePiece` is not in `Causal.FlrwType`'s closure: import it.
