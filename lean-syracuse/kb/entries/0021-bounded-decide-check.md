---
id: 0021
title: A bounded Diophantine check in the kernel: decide, with three scoped set_options
kind: pattern
created: 2026-11-21
---
Found by T-syr-steiner (`steinerArith_check_pos`, `steinerArith_check_neg`). `decide` on '∀ n < 101, ∀ e < 2n, … % … = 0 → …' over ℕ runs in about 5 s. It needs `set_option synthInstance.maxSize 1024` (otherwise the Decidable instance of five nested implications is not found), `maxRecDepth 100000` from n ≈ 80, and `exponentiation.threshold 1024` (otherwise it warns, an error under warningAsError). Scope each to its theorem with `in`; never `native_decide`.
