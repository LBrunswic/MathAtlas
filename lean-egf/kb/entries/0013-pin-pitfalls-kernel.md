---
id: 0013
title: At this pin: Kernel.piecewise needs DecidablePred; mul_le_mul_left multiplies on the right
kind: pitfall
created: 2026-11-21
---
Found by T-egf-sampling. Define with `Kernel.piecewise` by `by classical exact`, and open the proofs of its apply lemmas with `classical`. `mul_le_mul_left h a` multiplies on the right (`b * a ≤ c * a`): use `gcongr`. After `filter_upwards` on an `=ᵐ` of sets the goal is `{w | p w} w = …`: `apply propext`, then `change p w ↔ q w`, since `simp` does not unfold a setOf application.
