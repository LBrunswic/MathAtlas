---
id: 0028
title: Minkowski facts may already exist under the Flat namespace
kind: pitfall
created: 2026-11-20
---
The Barbot campaign proved many facts about Minkowski space under `Causal.Flat` (e.g.
`Causal.Flat.minkowski_not_lt_self` in `Causal/Flat/Achronal.lean`), not under `Causal` where the
ETT files look first. `grep -rn` the whole of `Causal/Flat/` before proving a Minkowski fact
(T-ett-unanchored reused it for `rem:relation_not_assumed_reflexive`).
