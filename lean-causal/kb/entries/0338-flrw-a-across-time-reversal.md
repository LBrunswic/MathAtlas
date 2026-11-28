---
id: 0338
title: (A) crosses time reversal both ways, and along an extension through C.dual
kind: pattern
created: 2026-11-28
---
(A) crosses time reversal both ways with no hypothesis: `Causal.Causality.dual_iUnion_Iplus_eq_of_futureInextensible` (C → C.dual) and its converse `Causal.Causality.iUnion_Iminus_eq_of_dual_pastInextensible` (C.dual → C), both in `Causal.FlrwTypeClosedAmbient`. So (A⁻) for C and (A) for C.dual are equivalent on every open set. To carry (A⁻) along an extension ι, convert it to (A) for `CN.dual` at ⊤, apply `hι.dual.iUnion_Iplus_eq_of_pastInextensible` after `rw [← exp_rangeOpens_eq]`-style rewriting (`exact` closes: `hι.dual.rangeOpens` is `hι.rangeOpens` by `rfl`), and read it back with the converse. At W = ⊤ the (A)-shape says `= ↑⊤` and the extension transport asks `= univ`: bridge with `Opens.coe_top` and its symm (T-abs-flrw-future-a-witness, `Causal.timelikeLine_posHalfLine_iUnion_Iminus_eq`).
