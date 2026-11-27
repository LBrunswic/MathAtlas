---
id: 0061
title: Model-free lemmas stranded under Causal.E0 / Causal.E0LM: hoist on demand
kind: convention
created: 2026-11-21
---
Found by T-ett-port-e0-sfa (with kb 0047). The verbatim E₀ ports leave model-free facts under `Causal.E0`/`Causal.E0LM`: `SliceAt` with pullback/pushforward, `LocZplus`…`LocPastIn` with `rel_of_causallyConvex` and `locZplus_of`/`locZminus_of`/`locTarentin_of`, the push-up link steps `lt_of_lt_of_le_link`/`lt_of_le_link_of_lt`, real induction `prop_zero_of_down`/`prop_one_of_up`; `E0LM.pushUpOn_of_chartIso` follows from the strict `Causal.ChartIso.pushUpOn`. Hoist them on demand, not inside a port.

**Update 2026-11-21 (T-abs-hoist-plain-locz, kb 0077):** `LocZplus`…`LocPastIn`, `rel_of_causallyConvex` and `locZplus_of`/`locZminus_of`/`locTarentin_of` are hoisted into the ETT-layer `Causal.CausallyPlainLocZ` (namespace `Causal.E0LM` kept). The rest of the list above is still stranded.

**Update 2026-11-27 (T-abs-merge-stranded-duplicates):** the Cauchy-surface congruence, proved three times (`Causal.CBG.isCauchySurfaceOn_congr` in `Causal.Flat.CBG`, `isCauchySurfaceOn_congr'` in `Causal.Flat.CBGSlice`, `Causality.IsCauchySurfaceOn.of_inter_eq` in `Causal.Ers475CauchyForm`), is one proof: `IsCauchySurfaceOn.of_inter_eq` moved verbatim (same full name) to `Causal.Cauchy`, where `IsCauchySurfaceOn` is defined, and the two CBG names cite it through `Set.ext fun _ => and_congr_left fun hx => (hS _ hx).symm`.
