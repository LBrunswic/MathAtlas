---
id: 0240
title: No lemma restricts CausallyPlain to CausallyPlainOn W
kind: pitfall
created: 2026-11-23
---
`Causal.Properties` has `causallyPlainOn_top` and `dual_causallyPlainOn`, but no `CausallyPlain.causallyPlainOn W`; it is a one-liner, inlined in `Causal.Model.EAlphaPlain` (`staticCausality.causallyPlainOn`), and a candidate for `Causal.Properties` (T-loc-ealpha-plain).
