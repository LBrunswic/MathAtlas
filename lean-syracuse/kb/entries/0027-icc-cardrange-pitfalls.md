---
id: 0027
title: Pitfalls: noncomputable Finset.Icc on ℤ, rw with card_range, and an n that omega does not infer
kind: pitfall
created: 2026-11-21
---
Found by T-syr-two-descents. A def using `Finset.Icc` on ℤ must be `noncomputable` (the order instance is), and `unfold` then `decide` still evaluates it (`twoDescCount`). `rw [← Finset.card_range n]` rewrites every `n`, the one inside `range n` included: bound a product with `Finset.prod_le_prod (g := fun _ => c)`, then `prod_const` and `card_range`. For `twoDesc_rep`, `twoDesc_rep_unique` and `twoDesc_not_mul`, pass `(n := n)` explicitly: it is not inferred from q * n = m with omega/linarith side goals.
