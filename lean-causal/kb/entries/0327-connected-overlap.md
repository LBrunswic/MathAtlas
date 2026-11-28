---
id: 0327
title: A connected Cauchy surface of U₁, U₂ and U₁ ⊔ U₂ makes the overlap connected
kind: pattern
created: 2026-11-28
---
One causality with a connected `S` Cauchy in `U₁`, `U₂` and `U₁ ⊔ U₂` (`≤` antisymmetric there) gives a connected `U₁ ∩ U₂` (`Causality.isPreconnected_inter_of_isCauchySurfaceOn_sup`, `Causal.ErsEtaleMghd`), by a direct curve argument: neither kb/0245's `isCauchySurfaceOn_inf_of_secondCountable` (stated at `⊤`) nor `Causal.CExtConnexeCauchy.SubArc` is needed. Hence agreement ⇒ connected overlap ⇒ injectivity in ERS's subluminal setting (`ers_isPreconnected_inter_of_eqOn`, `ers_isOpenEmbedding_proj_of_eqOn`), which settles what `Causal/ErsMughd.lean:91–95` argued; ERS :930 suggests it fails without an m-acausal `S`.
