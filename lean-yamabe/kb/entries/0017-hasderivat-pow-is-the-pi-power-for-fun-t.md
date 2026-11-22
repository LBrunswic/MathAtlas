---
id: 0017
title: HasDerivAt.pow is the Pi power; for fun t => f t ^ 2 use fun_pow and congr_deriv
kind: pitfall
created: 2026-11-22
---
Found by T-yamabe-analysis. Pitfall: HasDerivAt.pow is about f ^ n (Pi power); for fun t => f t ^ 2 use (h.fun_pow 2).congr_deriv (by simp); `convert … using 1` fails on instance paths there.
