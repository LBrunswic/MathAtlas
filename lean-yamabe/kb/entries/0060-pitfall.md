---
id: 0060
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-yamabe-analysis (round 3). Pitfall: after `set φ := extChartAt (𝓡∂ N) x₀`, `simp only [chartFun_chart (hVs hy)]` does not fire on `chartFun N x₀ f (↑φ y)` (unused simp arg), while `rw [chartFun_chart (hVs hy)]` does.
