---
id: 0086
title: A « (1 + O(F)) » factor from an explicit O(F²) remainder: corRem and its uniform bound
kind: pattern
created: 2026-11-23
---
Found by T-perf-cor-yamabe. a « (1 + O(F)) » factor built from an explicit O(F²) remainder: define corRem := (first-order term) + mainRem. Get the uniform bound |corRem| ≤ (3/7)|ÃF/a_N| from mainRem_le_uniform and θ/(1+θ)² ≤ 1/4, then get IsBigO and the limit θ/(1+θ)(1 + corRem) → 1/2 from that bound (Yamabe.corRem_le_uniform, corRem_isBigO, corConst_tendsto_half).
