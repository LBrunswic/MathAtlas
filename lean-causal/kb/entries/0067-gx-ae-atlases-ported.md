---
id: 0067
title: gx's a.e. (G,X)-atlases are in lean-causal; Causal.IsComplete shadows mathlib's
kind: pattern
created: 2026-11-21
---
Found by T-ett-gxsingular-dec25. `Causal.Port.Portly` and `Causal.Port.SingularAtlas` are verbatim ports (GX.x as Causal.x): a singular (G,X)-manifold is `[SingularGXStructure G X M]` (maximal a.e. atlas, DEC-25), with `Reg`, `Sing`, `aeAtlas`, `IsRegularOn`, `IsAEMorphism`, `regLocus` as in gx. The proposition under DEC-25 is `Causal.existsUnique_causality_singularGX_dec25` (`Causal.GXSingularDEC25`), with the added (b′) (OQ-64). `Causal.IsComplete` (the a.e.-atlas notion) shadows Mathlib's root `IsComplete` inside `namespace Causal`: write `_root_.IsComplete` there. Nine gx names from Tame and Branched/Basic are restated in GXSingularDEC25 and will clash with a later verbatim port of those files.
