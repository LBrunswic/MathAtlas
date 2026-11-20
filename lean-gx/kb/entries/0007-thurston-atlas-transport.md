---
id: 0007
title: Reusing ConicStructure.mk_mem_sing for the Thurston atlas: transport along liftSO
kind: pattern
created: 2026-11-20
---
To reuse `GX.ConicStructure.mk_mem_sing` (rays over singular points are singular) for the Thurston
atlas, the link action must be of a subgroup of SO(ℝ ⊕ W): transport a singular (SO(W), 𝕊(W))-structure
along `GX.liftSO`; `IsGXAtlas` and `IsThinner` only see the maps x ↦ g • x, so the transport is
definitional chasing. Not done yet (T-gx-troyanov-suspension) (T-gx-spherical-cone).
