---
id: 0339
title: Real.exp is a cheap future-inextensible chronal curve of (0, ∞) on the timelike line
kind: pattern
created: 2026-11-28
---
`Real.exp` over ℝ is a chronal curve of (0, ∞) for the timelike line on every segment (`timelikeLine_chronalCurveOn_iff`, `Causal.TimelikeHomotopy`), and future-inextensible there (`LineDevelopment.futureInextensible_of_not_tendsto_atTop` with `not_tendsto_nhds_of_tendsto_atTop Real.tendsto_exp_atTop`). Run backwards (`dual_pastInextensible_iff`, `neg_univ`), t ↦ exp (−t) is a past-inextensible one for `timelikeLine.dual`. Use it to show an (A)-type hypothesis on (0, ∞) is not vacuous: `campaign/T-abs-flrw-future-a-witness/Probe.lean` (kb/0011: the timelike line is the ETT layer's witness model).
