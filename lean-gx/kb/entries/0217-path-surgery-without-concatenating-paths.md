---
id: 0217
title: Path surgery without concatenating paths
kind: pattern
created: 2026-11-28
---
Found by T-btz-reg-complete-tail. Path surgery without concatenating paths: bound edist by the triangle inequality between points of ONE curve, and the pieces by localLength over subintervals (localLength_add); a curve on [a,b] lowers to a Path by clamping with projIcc (1-Lipschitz, LocLipAt.comp_lipschitz) and an affine reparametrisation (localLength_comp_affine) — RegCompleteTail.edist_le_localLength_of_mem.
