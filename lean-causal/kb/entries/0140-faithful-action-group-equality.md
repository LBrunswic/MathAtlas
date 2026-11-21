---
id: 0140
title: A faithful action turns « acts as » into a group equality
kind: pattern
created: 2026-11-21
---
`Flat.isom 2` acts faithfully (`IsAnalyticAction`), so an equality of actions on `Minkowski 2` is a group equality by `eq_of_smul_eq_smul (α := Minkowski 2)`. That makes `EAlphaSector.rotIsom` a homomorphism `ℝ → Isom` (`Causal.EAlphaContinuation.rotIsom_add`, `rotIsom_zero`, `rotIsom_eq_of_exp_eq`), and chaining charts around a loop becomes group algebra (T-ett-ealpha-gx-structure).
