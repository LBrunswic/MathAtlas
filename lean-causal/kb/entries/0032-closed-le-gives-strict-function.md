---
id: 0032
title: With ≤ closed, an admissible past measure gives a strictly increasing continuous function
kind: pattern
created: 2026-11-20
---
With the causal relation closed, `prop:cont_ext_cont` needs no global hyperbolicity:
`AdmissiblePast.exists_strict_continuous_of_isClosed_le` (`Causal.LimitCurves`) gives a continuous
function strictly increasing along ≤. It is NOT a DEC-10 time function (openness and the
strong-morphism property are not proved), but it is enough for `Causal.CurvesExtend`: an
inextensible curve through every point, and acausal Cauchy surfaces (T-ett-geroch-iii-i).
