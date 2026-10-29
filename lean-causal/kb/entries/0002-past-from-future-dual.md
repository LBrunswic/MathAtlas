---
id: 0002
title: Prove the future statement, get the past one from `C.dual`
kind: pattern
created: 2026-09-27
---
## When
A statement has a past and a future form (`J^±`, `I^±`, `K^±`, `Z^±`, admissible measures).

## Do
Prove one. The other is the same theorem applied to `C.dual`:
`theorem foo_minus … := foo_plus (C := C.dual) (dual_bar.2 h) …`. Every property needs its
`dual_…` lemma (`dual_tarentin`, `dual_globallyHyperbolic`, `dual_causallyPlain`,
`dual_absolutelyMinimalOn`, `dual_causallyArcConnectedOn`, `dual_admissiblePast`, …): write it
when you define the property. `C.dual.Jplus U A = C.Jminus U A` and the like hold by `rfl`.

## Why
Half the proofs, and the two forms cannot drift apart.
