---
id: 0056
title: Hörmann's 3+1 conical spacetime as a static causality on an L² product
kind: pattern
created: 2026-11-20
---
`cosmicString α = staticCausality (WithLp 2 (Cone α × ℝ))`. L² products of geodesic or proper
metric spaces are geodesic or proper (instances `GeodesicSpace.withLpTwo`, `properSpace_withLpTwo`,
proof-only, so no second metric on ordinary products); `withLp_dist_two` is the √(d₁² + d₂²)
formula. `properSpace_withLpTwo` uses mathlib's `WithLp.dist_fst_le`/`_snd_le` (the duplicates
`Causal.withLp_dist_fst_le`/`_snd_le` were removed by T-loc-ealpha-tidy).
Hörmann's α_H is α/2π (`Causal.Model.EAlphaCauchy`, T-loc-ealpha-cauchy).
