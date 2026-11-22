---
id: 0031
title: Pitfall:
kind: pitfall
created: 2026-11-22
---
Found by T-bbs-hs-model. Pitfall: for sigma : RaySphere V, `rw [<- abs_one]` (any rewrite that abstracts the literal 1) fails with 'motive is not type correct', because the 1 of `sphere 0 1` is in sigma's type. Rewrite in a hypothesis instead (`rwa [abs_one] at h`).
