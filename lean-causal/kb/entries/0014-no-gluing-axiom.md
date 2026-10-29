---
id: 0014
title: The library's causality has no gluing axiom — a counterexample may exploit that
kind: pitfall
created: 2026-10-29
---
`Causality` is the paper's "equivalently" form of `defi:causalite` (`Causal/Causality.lean:37`):
no gluing. So a causality is not determined by its restrictions to a cover, and a relation built
with `Causality.ofRelation` (the global relation restricted to each `U`) is a causality even when
it is not local. A counterexample built that way refutes the paper only where the claim reads
`U = ⊤` alone; disclose it, and say whether the witness is causal and absolutely minimal
(`timelikeLineTop`, `Causal/Morphism` in the scaffold). To prove two causalities equal from local
data, ask one of them absolutely minimal (`LocalIsomorphism.unique`).
