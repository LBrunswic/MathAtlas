---
id: 0057
title: A causal isomorphism is a global ChartIso; transport lemmas and opensCongr
kind: pitfall
created: 2026-11-20
---
`IsCausalIso` (`Causal.CausalIsoInvariance`: a homeomorphism with e, e⁻¹ strong morphisms) is the
strict `ChartIso` (`Causal.GXStructure`) for a chart on all of M (`isCausalIso_iff_chartIso`), and
`Causality.transport e` is `Causality.chartTransport` along e⁻¹
(`chartTransport_toOpenPartialHomeomorph`): reuse them, do not define a third. Prove a transport
in one direction for every isomorphism and get the iff from `h.symm`; rewrite the round trip with
`symm_opensCongr_opensCongr` / `homeomorph_symm_image_image` — `simp` does NOT see through
`e.opensCongr` (`Homeomorph.opensCongr_apply` turns it into `Opens.comap`), so apply lemmas about it
with `rw`. A helper in a `where` clause shares its parent's universes and fails on `h.symm`: make it
a top-level theorem (T-abs-causal-iso-invariance).
