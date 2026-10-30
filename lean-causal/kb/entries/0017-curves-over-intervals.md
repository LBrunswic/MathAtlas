---
id: 0017
title: Curves over an interval, inextensibility, and the two traps of "maximal under extension"
kind: pattern
created: 2026-10-30
---
A causal curve over an interval `I` is `CausalCurveIn W I c` (`Causal/Inextensible.lean`):
reparametrise with `CausalCurveIn.comp` (continuous strictly monotone), reverse with
`CausalCurveIn.reverse` (a curve of `C.dual`). Strict extension asks a strictly increasing `φ`
onto a sub-interval and a **new value** (DEC-11, DEC-13): with DEC-6's constant curves, "larger
domain, same values" makes every curve extensible (`exists_naive_extension`), and domain
inclusion without `φ` makes every curve over `ℝ` inextensible. One-sided:
`PastInextensible`/`FutureInextensible`, `inextensible_iff`. In a causally arc-connected causal
T1 spacetime with `J⁻(x) ≠ {x}`, `J⁺(x)` is not a neighbourhood of `x` (`Jplus_not_mem_nhds`):
that is where chronology and the openness of measure-built time functions come from.
