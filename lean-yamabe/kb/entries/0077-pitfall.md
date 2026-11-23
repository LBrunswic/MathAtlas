---
id: 0077
title: pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-perf-star-n. pitfall: `rw [integral_add (i1.add i2) i3]` fails to find the pattern, which is a Pi sum. State the integrability with an explicit lambda first (`have i12 : Integrable (fun x => f x + g x) nu := i1.add i2`), then `rw [integral_add i12 i3]`.
