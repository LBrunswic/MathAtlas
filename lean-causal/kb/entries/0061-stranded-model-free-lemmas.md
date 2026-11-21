---
id: 0061
title: Model-free lemmas stranded under Causal.E0 / Causal.E0LM: hoist on demand
kind: convention
created: 2026-11-21
---
Found by T-ett-port-e0-sfa (with kb 0047). The verbatim E₀ ports leave model-free facts under `Causal.E0`/`Causal.E0LM`: `SliceAt` with pullback/pushforward, `LocZplus`…`LocPastIn` with `rel_of_causallyConvex` and `locZplus_of`/`locZminus_of`/`locTarentin_of`, the push-up link steps `lt_of_lt_of_le_link`/`lt_of_le_link_of_lt`, real induction `prop_zero_of_down`/`prop_one_of_up`; `E0LM.pushUpOn_of_chartIso` follows from the strict `Causal.ChartIso.pushUpOn`. Hoist them on demand, not inside a port.
