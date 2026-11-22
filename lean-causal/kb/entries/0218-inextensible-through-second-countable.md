---
id: 0218
title: Through-hypotheses and SplitBy on T1, second countable spaces
kind: pattern
created: 2026-11-22
---
On every T1, second countable space, for every causality `C` and open `W`: `Causal.Causality.inextensibleThrough_of_t1_secondCountable C W : C.InextensibleThrough W` (the constant curve at `x`, extended by `curvesExtendOn_of_t1_secondCountable`), `splitBy_of_t1_secondCountable` (`SplitBy W S` for `S` Cauchy in `W` for `C`) and `IsCauchySurfaceOn.isAcausalOn_of_t1_secondCountable` (`IsAcausalOn W S` when `W` is also causally arc-connected) (`Causal.ErsSecondCountable`). They discharge every `hthrough`, `hthrough₂`, `hthroughτ` of `Causal.NestedCausalities`, `Causal.ErsUniqueness` and `Causal.ErsMughd`, as kb/0142 does for `hext`/`hmext`. An `hsplit` is discharged only where the theorem also has `S` Cauchy in `W` for the same causality; elsewhere (most of `ErsUniqueness.lean`:405–755, `NestedCausalities.lean`:1310) it can only be traded for an `IsCauchySurfaceOn` hypothesis (audit of T-abs-ers-4-72-second-countable).
