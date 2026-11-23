---
id: 0045
title: pattern:
kind: pattern
created: 2026-11-23
---
Found by T-perf-upper. pattern: the first variation of ||1 + eps f||^2_{L^q} for an unbounded f in L^q, q > 1 (Yamabe.hasDerivAt_normSq_one_add_of_memLp). Use Mathlib's hasDerivAt_abs_rpow (Analysis/InnerProductSpace/NormPow), dominate by q(1 + |f|)^q, and get integrability from MemLp.integrable_norm_rpow' on (memLp_const 1).add hf.norm.
