---
id: 0319
title: The two-piece gluing core is ETT-layer in Causal.TwoPiece
kind: pattern
created: 2026-11-28
---
The two-piece gluing core is ETT-layer in `Causal.TwoPiece` (T-abs-two-piece-hoist; same full names; it imports `Causal.CurveComponents` only): `TwoPiece`, `twoPieceRel`, `TwoPiece.symm`, `rel_trans`, `le_top_iff`, `le_of_le_top`, `mem_of_le_top`, `exists_mid`, `diamond_top_eq`, `isCausal`, `isCauchySurface` and the witness `timelikeLine_twoPiece`. Crossing, CauchySide, PieceChart, `TwoPiece.globallyHyperbolic` and `isCompact_diamond_mixed` stay in the model-layer `Causal.CBG.Ppcm` (an update to kb/0047's list of hoisted model-free results). A module that imports Ppcm still sees the moved names.
