---
id: 0173
title: Global BTZ facts at an E≥0-manifold, one chart at a time
kind: pattern
created: 2026-11-21
---
Run a causal curve `c : [0,1] → M` (causal arc-connectedness) and take the last parameter at `x` / the first at `q` (`csSup_mem` / `csInf_mem` of `Icc 0 1 ∩ c ⁻¹' {x}`, closed by T1), or the last BTZ parameter; then `CurveOn.rel` at it with `N = ballSource` gives a point over the axis just above/below, compared in E₀. No chart transitions are needed; push-up in `M` after leaving `sing₀` (`Causal.SFABTZ.singularPastAt`, `Iplus_of_lt`) (T-ett-sfa-btz-e0).
