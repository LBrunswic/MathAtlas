---
id: 0322
title: Sbierski's past boundary chart in ETT, and why the timelike line has none
kind: pattern
created: 2026-11-28
---
Sbierski's past boundary chart is `Causal.Causality.PastBoundaryChart C W Ũ p` (`Causal.FlrwType`), `Nonempty` of the six-field structure `PastBoundaryChartData`, which lives in `Type` because a `Prop` structure cannot hold `V`, `γ̃`, `s₀`; the future chart is its `C.dual`. Abstract Thm 1.5 is `not_pastBoundaryChart_of_flrwType`; for extensions `IsSpacetimeExtension.not_pastBoundaryChart_of_flrwType` (OQ-154's reading). Every `IsSpacetimeExtension` is an `IsEMorphismOn` (`IsSpacetimeExtension.isEMorphismOn`), so the Cauchy and inextensibility transports apply to extensions. On the timelike line no open set has a past boundary chart (`timelikeLine_not_pastBoundaryChart`): a witness there shows the hypotheses consistent, not the chart inhabited; an instance needs dimension ≥ 2 (layer 3, T-loc-minkowski-past-boundary-chart).
