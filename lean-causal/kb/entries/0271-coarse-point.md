---
id: 0271
title: Causal.CoarsePoint refutes a property's passage to a smaller open set
kind: pattern
created: 2026-11-23
---
To refute "holds on W, V ≤ W ⇒ holds on V" for a curve property, use `Causal.CoarsePoint` (Causal/InextensibleNestedBasics.lean): two near points forming the open set `nearOpens`, a far point `far S` for each `S : Set ℝ`, and open sets ∅, `nearOpens` and everything (`CoarsePoint.isOpen_iff`). On the whole space no causal curve of `allRelated` is inextensible (`CoarsePoint.allRelated_extensible`: by Cantor its image misses a far point, reached after an `arctan` squeeze of the parameter), so any inextensible-curve condition holds there vacuously; on `nearOpens` the step between the near points is inextensible. Every precausality of it is absolutely minimal on every open set (`CoarsePoint.absolutelyMinimalOn`), so a witness stands in either form of DEC-167's gluing (OQ-95). It is not T1 (nor T0): a refutation on an ETT spacetime still needs a Hausdorff example. The cousin of `Causal.ForkPoint` (kb/0268).
