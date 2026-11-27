---
id: 0304
title: A relation defined by curves holds between a curve's ends: IsRelFamily, CurveOn, rel_of_lt
kind: pattern
created: 2026-11-27
---
To show that a relation defined by curves holds between the ends of a curve without inverting a time function: show that the relation family is an `IsRelFamily`; show that the curve is a `CurveOn` of it (locally, by straight segments in small balls); then apply `CurveOn.rel_of_lt`. That is how `galileoCurveLt_iff_graphLt` and `galileoCurve_lt_iff_transGen_convex` go (`Causal.GalileoCurveForm`), with no Lebesgue number and no inverse function.
