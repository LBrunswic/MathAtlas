---
id: 0001
title: Everything is indexed by an open set; no subtype of `M` in a statement
kind: convention
created: 2026-09-27
---
## When
Stating anything about "the open subset `U` seen as a spacetime", a restriction, a chart domain.

## Do
Use the relations of the ambient causality at the open set: `C.le U x y`, `C.Jplus U A`,
`C.Kplus U A`. The spacetime itself is `U = ⊤`. A property of `W` seen as a spacetime is a
predicate `…On W` quantifying over the open sets `U ≤ W` (`CausallyPlainOn`, `AbsolutelyMinimalOn`,
`CausallyArcConnectedOn`, `PushUpOn`), with a lemma `…On ⊤ ↔ …`.
A causality given on `W` alone is `LocalCausality W` (`Causal/Local.lean`); it extends to `M`.

## Why
`Causality ↥U` forces coercions between `Opens M` and `Opens ↥U` and between points, in every
statement and every proof. Yesterday's 3,700 lines contain none.
