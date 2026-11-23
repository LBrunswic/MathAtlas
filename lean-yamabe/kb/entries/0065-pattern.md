---
id: 0065
title: pattern:
kind: pattern
created: 2026-11-23
---
Found by T-yamabe-trace-compact. pattern: from an interpolation inequality to an L²(σ) limit. Use EMetric.cauchySeq_iff with Lp.edist_toLp_toLp, then ENNReal.lt_iff_exists_real_btwn to get a real r, choosing δ against the W^{1,2} bound before the index. Conclude with cauchySeq_tendsto_of_complete and Lp.tendsto_Lp_iff_tendsto_eLpNorm', as RellichCriterion does (Yamabe.Mfd.trace_compact).
