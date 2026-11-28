---
id: 0316
title: Einstein-style gluing of two open sets: étale, injective iff the overlap is in A, Hausdorff iff A is relatively closed
kind: pattern
created: 2026-11-28
---
`Causal.EtaleGluing h₁ h₂` (`Causal.ErsEtaleGluing`) glues `U₁`, `U₂ ⊆ M` along `A ⊆ U₁ ∩ U₂` (`Causal.Gluing` of the two inclusions), with projection `EtaleGluing.proj`. It is injective iff `U₁ ∩ U₂ ⊆ A` (`injective_proj_iff`, no topology) and a local homeomorphism for `U₁`, `U₂`, `A` open (`isLocalHomeomorph_proj`). With `M` T2 the gluing is Hausdorff iff `U₁ ∩ U₂ ∩ closure A ⊆ A` (`t2Space_iff`); the forward direction holds for any `M` (`subset_of_t2Space`). Glued functions descend iff they agree on `U₁ ∩ U₂` (`exists_glue_eq_comp_proj_iff`). To make a map out of a `Causal.Gluing` a local homeomorphism, apply `IsLocalHomeomorphOn.of_comp_right` on each sheet and cover by `Gluing.exists_ι`.
