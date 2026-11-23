---
id: 0048
title: pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-perf-upper. pitfall: (memLp_const 1).add (hf.const_mul c) against a goal MemLp (fun x => 1 + c * f x) times out in whnf. Give memLp_const its (μ := ...) (p := ...), bind the sum with have, then exact it.
