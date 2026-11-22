---
id: 0235
title: The causality of a linear order glues iff its intervals are connected enough
kind: pattern
created: 2026-11-22
---
`linearCausality_absolutelyMinimalOn_all` (`Causal.GluingGeneric.Linear`) needs every `Icc` preconnected (`IsPreconnected.induction₂'` with `GluingGeneric.reflTransGen_union`); ℤ and ℚ fail. This matters for `IsCausalChainMap` (`Causal/Chains.lean`:110), which quantifies over every linearly ordered `X`.
