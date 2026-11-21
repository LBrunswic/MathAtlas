---
id: 0065
title: The time-function layer is in the ETT layer; HasTimeFunction and IsTimeFunction are incomparable
kind: pattern
created: 2026-11-21
---
`Causality.HasTimeFunction` (a continuous T strictly increasing along ≤_M: the ladder node
`time_function`) lives in `Causal.CurvesExtend`, with `HasTimeFunction.curvesExtend` and
`HasTimeFunction.isCausal`; `Causal.CurvesExtend`, `Causal.CBG.Injective` (Sbierski Lemma 3.3,
`injOn_of_injOn_cauchy`), `Causal.CBG.CausalConvex` and the new `Causal.CauchyDual`
(`dual_isCauchySurfaceOn`) import no model since T-abs-hoist-time-function; the static and Minkowski
instances are in `Causal.Model.CurvesExtendModels` and `Causal.Model.InjectiveMinkowski`.
`HasTimeFunction` and ETT's `IsTimeFunction` are incomparable: `IsTimeFunction` is only
non-decreasing (the doubled line, kb/0058), and `HasTimeFunction` asks no openness.
