---
id: 0091
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-gammap-elements. Pitfall: after `set e := a • u + b • v`, a later `rw [smul_add]` can unfold the let-bound e. Use `clear_value e` once its definition has been used.
