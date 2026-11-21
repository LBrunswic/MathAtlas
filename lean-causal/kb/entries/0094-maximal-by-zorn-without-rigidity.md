---
id: 0094
title: Maximal developments by Zorn, without rigidity
kind: pattern
created: 2026-11-21
---
state a class as carriers + a morphism predicate on functions (Causal.AbstractDev.MorphismsCompose), prove ChainsInherit (an upper bound for every non-empty coherent chain) and SizeBound; Causal.AbstractDev.exists_isMaximal gives a maximal development (Zorn on towers: coherent chains with their chosen morphisms, so no uniqueness of morphisms is needed); RigidEndomorphisms only upgrades maximal to inextensible (IsMaximal.isInextensible). With unique morphisms, Zorn on the preorder itself (exists_isMaximal_of_uniqueMorphisms) (T-abs-maximal-zorn).
