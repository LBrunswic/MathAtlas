---
id: 0073
title: pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-perf-poincare. pitfall: a hypothesis obtained after `set ν := M.vol g` is stated with M.vol g, so `simp only [lemmas stated in ν] at h` makes no progress. Restate it first: `have h' : … ν … := h`.
