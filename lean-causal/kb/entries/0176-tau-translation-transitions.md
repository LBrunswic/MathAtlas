---
id: 0176
title: Two X_A-charts into E₀ at a BTZ point differ along the axis by a τ-translation
kind: pattern
created: 2026-11-21
---
`Causal.SFALine.trans_tau` (`∃ t, ∀ᶠ y in 𝓝 x, (e′ y).1 = (e y).1 + t`): one `BPrimeE0.exists_eqOn_rotE0_tauShift` on `he.symm.trans he′`, the open set pulled back by `e.isOpen_inter_preimage`; `rotE0` keeps `.1` and `tauShift` adds `t`, both by `rfl`. Neither `y ∈ sing₀` nor any causality is used. Pitfall: `rw [coe_chartImage_of_le …]` fails on `x ∈ chartImage e U` (an `Opens` membership); `show x ∈ (chartImage e U : Set _)` first (T-ett-sfa-line-e0).
