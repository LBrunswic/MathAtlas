---
id: 0221
title: causal_ladder does not close a ladder fact such as CurvesExtend
kind: pitfall
created: 2026-11-22
---
`causal_ladder` closes goals by the ladder's checked implications only; a `[[fact]]` of `programme/ladder.toml` (e.g. `curves_extend` on T1, second countable spaces) is not a rule, and `Causal/Ladder/Rules.lean` does not import `Causal.CurvesExtendSecondCountable`. Discharge `C.CurvesExtend` by the term `Causality.curvesExtend_of_t1_secondCountable C` (tested 2026-11-22: aesop fails with T2 and second countable in context).
