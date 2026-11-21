---
id: 0073
title: Two cheap non-local separations: the jump line and the gated line
kind: pattern
created: 2026-11-21
---
`Causal.jumpLine` (ℝ, ≪ empty, ≤_U the diagonal plus 0 ≤ 1 when 0, 1 ∈ U) is push-up and two-sided
locally causally open but not causally open in the future (`Causal.PushUpNotOpen`). `Causal.gateLine`
is causally open in the future but not in the past (J⁻_M(⋆) = (−∞, 10] ∪ {⋆}), locally push-up but not
push-up (`Causal.GateLineLocal`). Neither is absolutely minimal, so both separations hold in the
library's reading of `defi:causalite` without gluing (kb/0014, OQ-18): under gluing they are not
ETT spacetimes. For a separation valid in both readings, look for an absolutely minimal witness
(as the rational line is for push_up ⇏ causally_open_future) (T-abs-pushup-not-open,
T-abs-gateline-local).
