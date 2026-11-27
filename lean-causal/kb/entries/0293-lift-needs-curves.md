---
id: 0293
title: "Sends causal curves to causal curves" says nothing about ≤ unless ≤ is realised by curves
kind: pitfall
created: 2026-11-27
---
A map that sends causal curves to causal curves need not be monotone for `≤`: on `symmRationalLine` (`Causal.StrongCausalityLifts`; two rationals related both ways when the segment between them lies in the open set) every causal curve is constant, so the identity to the timelike line sends curves to curves, yet `2 ∈ J(0, 0)`. Arguments that put a diamond's point on a causal curve assume the order is realised by causal curves (`CausallyArcConnected`, or only that `≤` at `⊤` is realised by curves over `[0, 1]`). The lifting of strong causality holds with it (`stronglyCausal_lift`) and fails without it (`not_stronglyCausal_lift_of_curves`, OQ-145). Monotonicity plus connected diamonds is the general form (`stronglyCausal_of_lift`). On an absolutely minimal source a weak morphism is already monotone (`WeakMorphism.le_top_of_absolutelyMinimal`).
