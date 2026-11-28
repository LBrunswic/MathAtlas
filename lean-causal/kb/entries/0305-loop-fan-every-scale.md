---
id: 0305
title: The loop fan at every scale: globally hyperbolic, causally compact, not locally strongly causal
kind: pattern
created: 2026-11-27
---
`Causal.scaledFan` on `Causal.scaledFanSet ⊆ ℝ³` (`Causal.LoopFanEveryScale`) is the ETT-layer witness of `globally_hyperbolic, causally_compact ⇏ locally_strongly_causal`: level `k` is the loop fan carried into the plane `Y = ε_k X` by `(x, y) ↦ 2⁻ᵏ(x, ε_k x, y)`. Slopes in place of angles keep trigonometry out, and `levelEmbed_injective` reduces coherence within a level to `Causal.loopγ_coherent`; across levels the vertical holds only tops, whose heights lie in the disjoint intervals `(2⁻ᵏ, 2¹⁻ᵏ]` (`scaledFanArc_level_eq`). `scaledFan_separates` decides all 21 causality nodes; `not_locallyStronglyCausal_of_globallyHyperbolic_bare`: prop:GH_fortement_causal needs tarentin even for local strong causality.
