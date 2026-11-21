---
id: 0118
title: `A ∩ B \ C` does not parse: write `(A ∩ B) \ C`
kind: pitfall
created: 2026-11-21
---
`\` (`SDiff.sdiff`) is a non-associative `infix:70`, the precedence of `∩`, so `A ∩ B \ C` is a parse error, not `(A ∩ B) \ C` and not `A ∩ (B \ C)`. Parenthesise every set difference next to `∩` (T-ett-model-rows-e0).
