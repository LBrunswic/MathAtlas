---
id: 0272
title: A nesting of inextensible curves composes with no hypothesis
kind: pattern
created: 2026-11-23
---
`Causality.Inextensible C W I c` is `C.CausalCurveIn W I c ∧ ¬ C.Extensible W I c`, so `InextensibleNestedOn C C' W` already delivers `C'`-causal curves: `.trans` is composition and needs nothing of the middle causality (Causal/InextensibleNestedBasics.lean). Time reversal goes through `Inextensible.of_dual_reverse` / `dual_inextensible_iff` (the converse of the library's `Inextensible.dual_reverse`, by `neg_neg`). Passing to a smaller open `V ≤ W` is false in general (kb/0271); `InextensibleNestedOn.mono_of_inextensible` takes the sufficient condition that every `C`-inextensible curve of `V` is one of `W`, and `Inextensible.restrict` goes the other way (an inextensible curve of `W` with image in `V` is one of `V`).
