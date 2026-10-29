---
id: 0012
title: The singular part's model facts are named hypotheses, witnessed on a line
kind: pattern
created: 2026-10-29
---
## Context
The BTZ model `E_0`, `sing_0` and the singular flat spacetimes are not in the library (the paper
does not construct `E_0`). Statements of the singular part still have an order-topological core.

## Do
Carry each model fact as an explicit hypothesis with a name: a set `S` for `sing_0`,
`SingularPastAt p` for the half-line below a BTZ point, `∀ p, p ∈ Z⁺`, `∀ p ∉ S, p ∈ Z⁻`
(`Causal/PushUp.lean`). Then prove a witness that a line of `Causal/Lines.lean` satisfies all of
them, so the hypothesis set is not vacuous (`timelikeLine_K_monotone_hypotheses`). The row is
`partial`, bucket `D`, never marked. Where the paper invokes `prop:tarentin_fort_K` for
E≥0-manifolds, use push-up instead (`PushUp.Kminus_eq_Iminus`); causal plainness is not
established for them (OQ-16).
