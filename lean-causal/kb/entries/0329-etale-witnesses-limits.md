---
id: 0329
title: What the étale development can show on the line: a doubled point needs a disconnected S
kind: pitfall
created: 2026-11-28
---
A doubled point of the étale development on the line needs a disconnected `S`: `ErsEtaleWitness.timelikeLine_ers_theorem_3_45_etale_twoPoint` has `S = {0, 3}`; with `S` preconnected, `Causal.real_eqOn_inter_of_isDevelopment` excludes it for every causality (`Causal.ErsEtaleMghdWitnesses`). A witness of `ers_isOpenEmbedding_proj_of_eqOn` necessarily has `A = U₁ ∩ U₂` (`ers_coe_eq_inter_of_eqOn`): do not look for one with a proper common development.
