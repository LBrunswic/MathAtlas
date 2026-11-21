---
id: 0043
title: Corresponding boundary points in layer 1 are `Gluing.IsCorrespondingBoundaryPair`, not `CBG.Corresponds`
kind: pitfall
created: 2026-11-20
---
`Causal.Gluing.IsCorrespondingBoundaryPair j₁ j₂ x y` (`Causal.GluingHausdorff`) is Sbierski's
Def 3.5 for any open embeddings: the neighbourhood condition together with both boundary
memberships, with its closure-of-graph, filter and sequence forms. `Causal.CBG.Corresponds` is only
the neighbourhood condition, in (U, ψ) form, so graph points (p, ψ p) satisfy it
(T-abs-gluing-hausdorff). Since T-abs-hoist-cbg-cores it lives, with `IsCorrPair` and `KSide`, in the
ETT-layer `Causal.CorrespondingPoints`, which a layer-1 file may import (kb/0062).
