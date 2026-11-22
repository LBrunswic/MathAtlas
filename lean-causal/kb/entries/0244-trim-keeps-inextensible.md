---
id: 0244
title: Constant end pieces do not affect inextensibility
kind: pattern
created: 2026-11-23
---
`Causal.Causality.Inextensible.of_retraction`: inextensible over `I` ⇒ inextensible over the trimmed `I₀` of `exists_tailFree_retraction`, no separation axiom, through `Extensible.of_top_tail` / `of_bottom_tail` (pausing the old extension with `pauseTop`) and `CausalCurveIn.comp_monotoneOn` (a causal curve through a continuous non-decreasing reparametrisation; the model module `Remarks/SingularRowsCauchyExt.lean`:191 has a twin, `causalCurveIn_comp_monotoneOn`, to merge at the next hoist, kb/0061).
