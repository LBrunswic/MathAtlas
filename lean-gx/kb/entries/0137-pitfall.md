---
id: 0137
title: Pitfall:
kind: pitfall
created: 2026-11-25
---
Found by T-bbs-p-p. Pitfall: `rw [← h2]` with h2 : f (y − 2m) = y rewrites every y in the goal, the right-hand side included; use `conv_lhs => rw [← h2]`.
