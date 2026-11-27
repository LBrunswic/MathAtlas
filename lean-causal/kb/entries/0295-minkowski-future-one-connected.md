---
id: 0295
title: Minkowski space is future one-connected; its chronal curves are the continuous ≪-increasing maps
kind: pattern
created: 2026-11-27
---
`Causal.Model.MinkowskiFutureOneConnected`: in `Causal.minkowski n`, a chronal curve of any open `W` is exactly a continuous map into `W` with `c s ≪ c s'` at `⊤` for `s < s'` (`minkowski_chronalCurveOn_iff`: the local condition is met inside a ball, where `Causal.Flat.lt_iff_of_convex` makes `≪_N` the restriction of `≪`). Hence the convex combination of two chronal curves with the same endpoints is a chronal homotopy in every convex open (`minkowski_futureOneConnectedOn`), and `minkowski_futureOneConnected` holds for every `n`. Sbierski's printed homotopy (1507.00601 :575–579) splits at `s = 1/2` and its end slices pause, so it is no chronal homotopy (`minkowski_not_chronalHomotopyOn_sbierskiPrinted`, for every `λ`); the split at `s = t` is one (`sbierskiSplitHomotopy`). Non-convex opens are not covered (ℝ^{1,2} minus the time axis is argued not future one-connected).
