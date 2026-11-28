---
id: 0306
title: Stacking scaled copies of a witness creates accumulation points: re-check what does not transfer
kind: pitfall
created: 2026-11-27
---
Stacking scaled copies of a witness on a common axis creates new accumulation points: in `Causal.LoopFanEveryScale` the tops of level `k ≥ 1` lie on the segment that level `k − 1` accumulates on, which kills causal openness in every form although the single loop fan is argued causally open. The tool is a set that misses a whole level by its plane (`V = W ∩ {Y < X}`, `scaledFan_not_causallyOpenFutureOn`). For any multi-scale witness, re-check causal openness and local strong causality away from the accumulation point: neither transfers from one level.
