---
id: 0047
title: Model-free lemmas stranded in model-importing modules
kind: pitfall
created: 2026-11-20
---
A layer-1 module may not import a model (`programme/README.md`), and these model-free results sit
in modules that do: `exists_minimal_of_isCompact` (Sbierski Lemma 3.9) in `Causal.CBG.NoCorresponding`;
`dependenceDomain` in `Causal.Flat.LipschitzGraph`; `curveOn_of_rel_imp` and
`inextensible_ordConnectedComponent_of_le` in `Causal.CBG.CausalConvex` (imports Minkowski and
Static). `Causal.NestedCausalities` re-proves them as `exists_minimal_of_isCompact_on`,
`dependenceDomainOn`, `CurveOn.of_rel_imp`, `inextensible_ordConnectedComponent_on` (the last for an
ambient open W). Hoisting them into an ETT-layer module would remove the duplicates
(T-abs-nested-causalities).
