# 0012 — A positive lower bound for finitely many positive reals

*Found 2026-11-20 by T-bz-c2-projection; recorded by the master session.*

Use `(Filter.eventually_all_finset t).2` with `eventually_lt_nhds`, filtered to `𝓝[>] 0`, then
`(·.and self_mem_nhdsWithin).exists`. No `Finset.min'`, and no case split on nonemptiness.
