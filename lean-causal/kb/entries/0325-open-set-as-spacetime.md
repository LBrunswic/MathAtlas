---
id: 0325
title: An open set as a spacetime of its own: Subtype.val is an injective IsEMorphism
kind: pattern
created: 2026-11-28
---
An open set `U` as a spacetime of its own: `Subtype.val` is an injective `IsEMorphism` from `(C.restrict U).toSubtype` (`Causality.isEMorphism_restrict_toSubtype_val`, `Causal.ErsEtaleMghd`), so `S ⊆ U` is Cauchy in `U` iff `val⁻¹(S)` is Cauchy in `↥U` (`Causality.isCauchySurfaceOn_iff_restrict_toSubtype`). The connected component of `U₁ ∩ U₂` through `x`, as an open set, is the existing `Causal.componentOpens (U₁ ⊓ U₂) x` (`Causal.ErsUnions`): do not redefine it.
