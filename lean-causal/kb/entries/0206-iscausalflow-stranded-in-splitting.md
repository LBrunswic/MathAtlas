---
id: 0206
title: IsCausalFlow lives in Causal.Splitting, whose closure is not model-free
kind: pitfall
created: 2026-11-22
---
`IsCausalFlow` and the hitting-time splitting (Causal.Splitting's Target 2) are model-free but sit in a module importing `Causal.Flat.IsomCausal`, so Minkowski, Static, GXStructure and mathlib's manifold and ODE parts enter the closure of any module stating a splitting (e.g. `Causal.SingularSplitting`). Hoisting them (kb/0047) would drop those modules from the closure, but not make it model-free in `tools/ladder.py`'s sense, which counts `Causal.SingularFlat` (reached through `Causal.SingularCauchy`) as model layer (T-ett-geroch-split-flow, AUDIT-1).
