---
id: 0049
title: pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-perf-upper. pitfall: a HasDerivAt.comp result closes a goal on fun e => |1 + e * f x| ^ q by exact this.congr_deriv (by ring). Do not use convert ... using 1, which leaves a function-equality goal that ring cannot close.
