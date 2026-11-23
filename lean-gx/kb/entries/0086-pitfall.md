---
id: 0086
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-hs-singularities. Pitfall: after `set k := a * b`, `rw [GTilde.coe_mul_apply]` can unfold k; `clear_value k` first.
