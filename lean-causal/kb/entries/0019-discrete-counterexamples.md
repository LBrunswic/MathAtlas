---
id: 0019
title: A discrete counterexample is non-local, and says nothing about local causalities
kind: pitfall
created: 2026-10-30
---
A finite discrete type with `Causality.ofRelation` is the cheapest carrier of a counterexample
(every subset compact, every subset a chain), and the wrong one for a claim about local
causalities: on a discrete space an absolutely minimal causality has `≤` the diagonal
(`AbsolutelyMinimalOn.eq_of_discrete`, `Causal/Chains.lean`). Scope such a refutation to
non-local causalities in its statement and SCOPE (kb/0014), or find a witness in a line or a
union of lines. Pitfalls met on the way: `push_neg` is deprecated at this pin (write
`push Not at h`); a theorem named `IsCausalChain.insert` shadows `Set.insert` in its own body.
