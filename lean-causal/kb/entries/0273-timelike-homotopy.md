---
id: 0273
title: Sbierski's timelike homotopy and future one-connectedness in ETT
kind: pattern
created: 2026-11-23
---
Sbierski 1507.00601 Def 2.13 is `Causality.ChronalHomotopyOn W Γ γ₀ γ₁` (jointly continuous on `[0,1]²`, every slice a future chronal curve of `W` over `[0, 1]`, fixed endpoints), `ChronallyHomotopicOn` (∃ Γ) and `FutureOneConnectedOn W` / `FutureOneConnected` (Causal/TimelikeHomotopy.lean). The relation is an equivalence on chronal curves (`chronallyHomotopicOn_equivalence`; `trans` glues in t through `ContinuousOn.union_of_isClosed` on `[0,1/2]×[0,1] ∪ [1/2,1]×[0,1]`). It is two-sided (`dual_futureOneConnectedOn`), reads only `≪` (`futureOneConnectedOn_congr_lt`), and passes through `IsCausalIso` (`futureOneConnectedOn_iff`, with `e.opensCongr W`) and through a `ChartIso` on `W ≤ chartSource e`; the curve transport it uses (`ChartIso.chronalCurveOn_image`, `ChartIso.chronalCurveOn_symm_image`, `chartImage_subset_target`) is in `Causal.GXStructure` since T-abs-hoist-stranded-homes, beside `ChartIso.curveOn_symm`. It is not hereditary to smaller opens, as Sbierski's is not. Timelike curves are read as chronal curves (the binder's `schwdef:timelike_curve`): an incomparable class under `C0`, so the row is partial.
