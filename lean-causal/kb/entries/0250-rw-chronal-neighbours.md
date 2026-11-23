---
id: 0250
title: rw [ChronalNeighbours, foo_iff (C := C.dual)] no longer finds the future side
kind: pitfall
created: 2026-11-23
---
After the future-base swap, the future side of `ChronalNeighbours` is syntactically `C.ChronalFutureNeighbours`, so `rw [ChronalNeighbours, foo_iff (C := C.dual) …]` no longer finds `C.dual.ChronalPastNeighbours`. Rewrite with the future-form lemma, or with `← dual_chronalPastNeighbours`. Term-mode `h.2` passed where `C.dual.ChronalPastNeighbours` is expected still elaborates (structure eta) (T-abs-one-sided-future-base).
