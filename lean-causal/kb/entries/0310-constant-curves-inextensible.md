---
id: 0310
title: Constant causal curves make every causal curve inextensible; the converse of le_nested under arc-connectedness
kind: pattern
created: 2026-11-28
---
`Causal.Causality.inextensible_iff_of_causalCurveOn_eq` (`Causal.InextensibleNotLeNested`): if every causal curve of `W` over a segment is constant, a curve is inextensible iff it is a causal curve. It is model-free and needs `I` non-empty, which `CausalCurveIn` carries. Two causalities with only constant causal curves on `W` are inextensibly nested on `W` both ways (`inextensibleNestedOn_of_causalCurveOn_eq`): the rational and spacelike lines have the same inextensible curves on every open set, and `rationalLine_separates_inextensibleNested` is the witness of `inextensible_nested ⇏ le_nested` in either reading of DEC-167. On T1, second countable spaces the converse holds when the narrower causality is causally arc-connected (`InextensibleNestedOn.leNested_of_causallyArcConnected`), so a counterexample needs a narrower causality that is not.
