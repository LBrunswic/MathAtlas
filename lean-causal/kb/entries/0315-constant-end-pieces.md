---
id: 0315
title: Constant end pieces do not affect past-inextensibility; extend one-sidedly without a pause
kind: pattern
created: 2026-11-28
---
`Causal.Causality.PastInextensible.of_retraction` (`Causal.CExtConnexeCauchy.SubArc` since T-abs-end-pieces-one-sided; no separation axiom): constant end pieces do not affect past-inextensibility. `Extensible.of_top_tail`'s pause (`pauseTop`, now written once, in `FutureExtensible.of_top_tail`) does not keep an extension at the past end: for the final piece of a past extension append through `v ↦ min v a` (`PastExtensible.of_top_tail`); for the initial piece use `FutureExtensible.of_top_tail` (the pause with the initial segment kept) through time reversal (`PastExtensible.of_bottom_tail`). To place a point of an inextensible curve relative to a sub-arc, `pastExtensible_of_subArc`: if `c = γ ∘ ψ` on `I` and `γ` has a new value below `ψ '' I`, then `γ` cut at the top of `ψ '' I` strictly extends `c` at the past end.
