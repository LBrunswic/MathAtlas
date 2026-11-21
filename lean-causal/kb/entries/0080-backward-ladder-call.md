---
id: 0080
title: A ladder failure read backwards through a conjunctive edge is one causal_ladder call
kind: pattern
created: 2026-11-21
---
To refute P from ¬ R and Q when the ladder has Q ∧ P ⇒ R: `intro h; have := hQ; exact hNotR (by
causal_ladder)` (`rationalLine_not_locallyCausallyOpenFuture`, through absolutely_minimal ∧
locally_causally_open_future ⇒ causally_open_future). The other premise must be in context (a
`have`): `causal_ladder` uses no lemma that is not a rule (kb/0048) (T-abs-rational-line-extras).
