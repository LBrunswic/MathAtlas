---
id: 0008
title: A literal −1 into an implicit real; Real.iInf over an empty type is 0
kind: pitfall
created: 2026-11-21
---
Found by T-yamabe-gluing-algebra. A literal `-1` passed through unification to an implicit `{m : ℝ}` can elaborate as `Real.neg 1`, which `norm_num` does not close: give `(m := -1)`. `Real.iInf_of_isEmpty`: the infimum over an empty type is 0, so `CurvedMetric.kobM = 0` on an empty model; case on `isEmpty_or_nonempty X` before `ciInf_const` or `le_ciInf`.
