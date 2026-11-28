---
id: 0323
title: The past boundary chart is inhabited: the half-space of Minkowski space at 0
kind: pattern
created: 2026-11-28
---
`Causal.minkowski_pastBoundaryChart` (`Causal.Model.MinkowskiPastBoundaryChart`): on `ℝ^{1,n}`, `n ≥ 1`, `W = {t > 0}` has a past boundary chart at `0` (kb/0322), with `Ũ = (−1, 1) × B(0, 1/10)`, `V = W ⊓ Ũ`, `γ̃(s) = (s/2, 0)`, `s₀ = 1/4`, `σ(τ) = (9τ/10, x₀)`. Hypotheses (A) and (B) of `not_pastBoundaryChart_of_flrwType` both fail there (`minkowski_posHalfSpace_flrwType_check`), and `ℝ^{1,0}` has no chart (`minkowski_zero_not_pastBoundaryChart`). In Minkowski space a future-closedness field `I⁺(x, Ũ) ⊆ I⁺(x, V)` on convex `Ũ`, `V` is two applications of `Causal.Flat.lt_iff_of_convex` and "`x ≪ y` raises `t`": no Cauchy data needed.
