---
id: 0317
title: Injectivity of the Einstein-style projection is U₁ ∩ U₂ ⊆ A, not agreement of the solutions
kind: pitfall
created: 2026-11-28
---
Injectivity of the Einstein-style projection is `U₁ ∩ U₂ ⊆ A` (`Causal.EtaleGluing.injective_proj_iff`; with `A` the component, the overlap connected), while agreement on the overlap is descent of the glued function (`exists_glue_eq_comp_proj_iff`). Injectivity gives agreement; the converse fails as topology (`punctured_witness`, `Causal.ErsEtaleGluing`), with `A` a component chosen by hand. Whether two GHDs can agree on all of a disconnected overlap is a causal question: state the two separately in the causal half (T-abs-ers-etale-mghd).
