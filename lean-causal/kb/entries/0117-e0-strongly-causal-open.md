---
id: 0117
title: E₀ is StronglyCausalOpen, but not through StronglyCausal.stronglyCausalOpen
kind: pitfall
created: 2026-11-21
---
`Causal.ModelRowsE0.e0_stronglyCausalOpen`: `J⁺(B) ∩ J⁻(B)`, `B` a ball, is open by `E0.isOpen_Jplus` / `E0.isOpen_Jminus`. The generic `StronglyCausal.stronglyCausalOpen` does not apply, because it asks `C.CausallyOpen` (causal openness in every open set) and E₀'s openness of `J^±` is proved for `U = ⊤` only. Use the global openness of `J^±` of an open set directly (T-ett-model-rows-e0).
