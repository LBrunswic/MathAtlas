---
id: 0265
title: When the acausal-for-Cauchy trade needs no arc-connectedness
kind: pattern
created: 2026-11-23
---
`IsAcausalOn W S` is needed (and so `harc` to derive it, kb/0218) only where two points of `S` related directly by `≤_W` must coincide (Remark 4.67's time orientations, `Jplus_inter_subset_…`). Where it only serves a union of opens `D ≤ W`, each with a Cauchy surface inside `S`, `S` Cauchy in `W` replaces it on a T2, second countable `M` with no `harc` (`isCauchySurfaceOn_sSup_of_secondCountable`), and `SplitBy` comes from `splitBy_of_t1_secondCountable`. That covers Prop 4.63, 4.64 in a region and Thm 4.75 (`Causal.Ers475CauchyForm`); `Causal.Ers464SecondCountable`'s trade forms for 4.64, 4.67 (first sentence) and 4.68 asked `harc` they did not need: `Causal.Ers464WithoutArc`'s `…_noArc` forms drop it, with 4.69, 4.71, 4.73 and the m-GHD form (T-abs-ers-4-64-without-arc, 2026-11-27).
