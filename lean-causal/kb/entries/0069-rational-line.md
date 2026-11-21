---
id: 0069
title: The rational line: absolutely minimal, push-up, only constant causal curves
kind: pattern
created: 2026-11-21
---
`Causal.rationalLine` (`Causal.NestedConverse`): x ≤_U y iff x = y ∈ U, or x < y both rational with
[x, y] ⊆ U; ≪ is empty. It is absolutely minimal (equal rational steps below a Lebesgue number of the
cover), causal, push-up (vacuously), and its causal curves are constant (a non-constant one takes an
irrational value), so it is neither causally arc-connected nor causally open in the future
(`rationalLine_separates_absolutelyMinimal`). A line whose causal curves are constant (`pointedLine`,
`rationalLine`) is curve-nested in every causality of ℝ; curve nesting and ≤-nesting agree when the
narrower causality is causally arc-connected (`Causality.leNested_iff_curveNestedOn_top`)
(T-abs-nested-converse).
