---
id: 0064
title: pattern:
kind: pattern
created: 2026-11-23
---
Found by T-yamabe-trace-compact. pattern: the q = 2 trace on the half-space with the gradient over ℍ̄ only. Apply trace_halfSpace to w = Half.ext v ∘ Half.Φ n. Bound |∂_t w p| by ‖Half.extD v (Φ p)‖ at every p: extD is continuous, so no measurability is lost, and it equals fderivWithin v ℍ̄ on ℍ̄. Pass to ℍ̄ by lintegral_mono_set and MeasurePreserving.setLIntegral_comp_preimage_emb, with (Φ n).toHomeomorph.measurableEmbedding (Yamabe.Half.trace_interp_halfSpace).
