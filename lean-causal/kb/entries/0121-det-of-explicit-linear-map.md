---
id: 0121
title: The determinant of an explicit linear map of ℝ × ℝ × ℝ
kind: pattern
created: 2026-11-21
---
Conjugate to `Fin 3 → ℝ` and compute: `LinearMap.det_conj` with the equivalence `Causal.BPrimeE0.coordsNull`, then `LinearMap.det_toMatrix'` and `Matrix.det_fin_three`. `simp [LinearMap.toMatrix'_apply, coordsNull, h]` evaluates the entries, given `h : ∀ a b c, N (a, b, c) = (…)` (`linear_of_null_fixed`) (T-ett-bprime-e0).
