---
id: 0017
title: Periodic functions on ℤ: reduce mod n, extend from one period, induct both ways
kind: pattern
created: 2026-11-21
---
Found by T-syr-upper-bounds. `Syracuse.periodic_emod` gives g i = g (i % n) for n-periodic g : ℤ → _. `forall_of_range` turns a hypothesis over 𝒟 ∩ ⟦0, n−1⟧ into one over all of 𝒟 ⊆ ℤ. `forall_of_step` is induction in both directions from a base point (`Int.inductionOn'`).
