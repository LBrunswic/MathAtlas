---
id: 0333
title: Extending a causal curve with no causality hypothesis: extensible_of_eq_comp_monotoneOn
kind: pattern
created: 2026-11-28
---
To show a causal curve is extensible with no causality hypothesis (no `IsCausal`, no `StronglyCausal`), use `Causal.Causality.extensible_of_eq_comp_monotoneOn` (`Causal.ExtensibleAlongCurve`; named `extensible_of_graph` until T-abs-extensible-comp-hoist): if `c = γ ∘ h` on `I`, with `h` continuous and non-decreasing, `γ` a causal curve over `J`, and `γ t'` a new value with `t' ≥ h(I)`, then `c` is extensible over any interval, the parameter compressed by arctan. It generalises the model-layer `extensible_of_timeGraph_openEnd` and is an alternative to `extensible_of_tendsto` when the curve lies on a known causal curve, with no causality hypothesis. To show a path is a causal curve of an `arcCausality`, `causalCurveIn_top_of_pieces`: continuity, and each piece inside an open `N` one `arcStep` along a reparametrised arc.
