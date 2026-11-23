---
id: 0249
title: The one-sided chronal and endpoint notions have the future as base
kind: convention
created: 2026-11-23
---
Since T-abs-one-sided-future-base (DEC-166 (a)), `Causality.ChronalFutureNeighbours` (`∀ V, ∀ v ∈ V, ∃ p ∈ V, v ≪_V p`) and `NoFutureEndpoint` (`J⁺(x) ≠ {x}`) are the definitions; `ChronalPastNeighbours := C.dual.ChronalFutureNeighbours` and `NoPastEndpoint := C.dual.NoFutureEndpoint`, their old bodies `chronalPastNeighbours_def`, `noPastEndpoint_def` (Iff.rfl). `ChronalNeighbours` and `NoCausalEndpoint` keep their meaning and order (past `.1`, future `.2`). As `CausallyOpenFuture`, state the future form and get the past one by `dual` (kb/0002).
