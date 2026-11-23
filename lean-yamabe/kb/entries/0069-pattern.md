---
id: 0069
title: pattern:
kind: pattern
created: 2026-11-23
---
Found by T-perf-poincare. pattern: the contradiction proof of a Poincaré inequality on the model (meanPoincare_of_rellich). Normalise w_k = (v_k − v̄_k)/‖v_k − v̄_k‖₂ and show ∫ w_k = 0. Pass the integral to the L² limit with abs_integral_le_mul_eLpNorm_two (Capacity). The limit f = c a.e. gives ∫ f = cV, hence c = 0. Then eLpNorm (val w_k) 2 = 1 contradicts eLpNorm (val w_k − f) → 0.
