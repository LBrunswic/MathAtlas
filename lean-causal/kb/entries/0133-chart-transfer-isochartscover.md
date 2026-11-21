---
id: 0133
title: Model facts pass through isomorphic charts: Causal.SFATransfer over IsoChartsCover
kind: pattern
created: 2026-11-21
---
The local model facts `E0LM.LocZplus`, `LocZminus`, `LocTarentin`, `LocNoPast`, `LocPastIn` pass through one `ChartIso` to every open set of `M` (`Causal.SFATransfer.ChartIso.exists_lt_right`, …), and through `SFATransfer.IsoChartsCover`, which is `IsoChartsCoverDEC25` without the `(G,X)` data. `IsoChartsCoverDEC25` sits behind Port imports (`Causal.Remarks.MassADEC25`), so an ETT-layer module cannot use it; the bridge is `Causal.SFALocalE0.isoChartsCover_of_dec25`. Call the `ChartIso` lemmas by full name: dot notation fails on `ChartIso` (kb/0010), and they live in `Causal.SFATransfer.ChartIso`, not `Causal.ChartIso` (T-ett-sfa-local-e0).
