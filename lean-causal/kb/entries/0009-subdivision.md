---
id: 0009
title: The Lebesgue-number step is `exists_subdivision_Icc`
kind: pattern
created: 2026-09-27
---
## When
A proof says "a Lebesgue number for the cover provides a subdivision `0 = t_0 < … < t_n = 1`".

## Do
`Causal.exists_subdivision_Icc` (`Causal/Subdivision.lean`): for an open cover of `Icc a b` it
gives `t : ℕ → ℝ` monotone, `t 0 = a`, stationary at `b`, each `Icc (t n) (t (n+1))` in a member.
Then induct on `n` proving `t n = a ∨ <the relation from a to t n>`; at a repeated point
(`t n = t (n+1)`) carry the hypothesis over. For a chain along a curve this is already done:
`CurveOn.rel_of_lt`, `CurveOn.transGen_link` (`Causal/Curves.lean`, `Causal/ArcConnected.lean`).
