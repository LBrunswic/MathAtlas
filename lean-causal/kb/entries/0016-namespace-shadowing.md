---
id: 0016
title: Names that resolve to the wrong lemma inside `namespace Causality`
kind: pitfall
created: 2026-10-29
---
Inside `namespace Causality`, `le_of_lt` is `Causality.le_of_lt`: write `_root_.le_of_lt` for the
order lemma. With `Filter` open, `mem_sdiff` is ambiguous: write `Set.mem_sdiff`. A `CObj`-valued
definition used as a category object should be an `abbrev`, or its carrier does not unfold to
`↥U`. In a `Quot.eqvGen_exact h` induction, `clear h` first (kb/0003).
