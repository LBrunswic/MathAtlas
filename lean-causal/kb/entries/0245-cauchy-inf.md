---
id: 0245
title: A Cauchy surface Cauchy in A and in B is Cauchy in A ∩ B
kind: pattern
created: 2026-11-23
---
`Causal.Causality.isCauchySurfaceOn_inf_of_secondCountable` (causal, T2, second countable): a Cauchy surface of `M` that is Cauchy in the opens `A` and `B` is Cauchy in `A ⊓ B`. The end-point step, reusable: `Inextensible.mem_image_or_tendsto_of_above` / `_below` (a sub-arc relation `c = γ ∘ ψ` and a parameter `s` of `γ` after `ψ(I)` give `γ(s) ∈ c(I)` or a limit of `c` at its end outside `W`). The past form by time reversal of the whole configuration (`Inextensible.dual_reverse`, `CausalCurveIn.reverse`, `TailFree.neg`, `ordConnected_image_neg`; then `simpa [neg_neg]`).
