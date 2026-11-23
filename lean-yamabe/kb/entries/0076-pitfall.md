---
id: 0076
title: pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-perf-star-n. pitfall: after `set s := E with hs`, `rcases (ENNReal.toReal_nonneg : 0 <= s).eq_or_lt with h0 | h` states h0 with the body E, not s, so `rw [<- h0]` on a goal in s fails; write `rw [hs, <- h0]`.
