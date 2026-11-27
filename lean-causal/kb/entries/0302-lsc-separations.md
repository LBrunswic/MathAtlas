---
id: 0302
title: locally_strongly_causal is separated both ways on ETT-layer models
kind: pattern
created: 2026-11-27
---
The symmetric rational line lacks local strong causality at every point: no open set holding a point is `StronglyCausalOn` (`Causal.symmRationalLine_not_stronglyCausalOn`). The loop fan has it and is strongly causal in neither form (`Causal.loopFan_locallyStronglyCausal`); the full forms are `symmRationalLine_separates_locallyStronglyCausal` and `loopFan_separates_locallyStronglyCausal` (`Causal.LscSeparations`). For `StronglyCausalOn W` with an arc causality in the plane, the centred boxes are causally convex in `W` once no tent piece inside `W` passes a top it does not stay below (`loopFan_causallyConvexIn_box`): choose `W` holding no top (`loopLow`, `loopSide`) or a single top (`loopCap n`). `ArcCoherent.mem_diamond_on` and `causallyConvexIn_on` are the `U`-forms of the `⊤`-only lemmas of `Causal.GHWithoutTarentin`.
