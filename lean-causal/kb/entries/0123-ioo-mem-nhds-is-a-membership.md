---
id: 0123
title: `Ioo_mem_nhdsGT` is a set membership: state the `∀ᶠ` first
kind: pitfall
created: 2026-11-21
---
`Ioo_mem_nhdsGT h : Ioo a b ∈ 𝓝[>] a` (and `Ioo_mem_nhdsLT`) is a membership, so `Filter.Eventually.mono` does not apply by dot notation. Write `have : ∀ᶠ x in 𝓝[>] a, x ∈ Ioo a b := Ioo_mem_nhdsGT h` first, or use `filter_upwards` / `mem_of_superset`. To identify the values at `a` of two maps continuous at `a` that agree on one side, `Causal.BPrimeE0.eq_of_eventuallyEq_of_continuousAt` (T-ett-bprime-e0).
