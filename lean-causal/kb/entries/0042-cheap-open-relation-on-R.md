---
id: 0042
title: A cheap open transitive relation on ℝ from two semicontinuous functions
kind: pattern
created: 2026-11-20
---
a ≪ b iff φ a < ψ b, with ψ ≤ φ, φ upper and ψ lower semicontinuous: transitive by ψ ≤ φ, open by
the semicontinuities. Build φ, ψ from id plus indicators (`IsClosed.upperSemicontinuous_indicator`,
`IsOpen.lowerSemicontinuous_indicator`, `IsClosed.lowerSemicontinuous_indicator` with a value ≤ 0)
(`Causal.deuxPushup`, T-ett-deux-pushup).
