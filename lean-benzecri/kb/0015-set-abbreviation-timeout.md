# 0015 — In long continuity proofs, do not abbreviate a function with `set`

*Found 2026-11-20 by T-bz-c2-hilbert; recorded by the master session.*

`set N := fun P => …` made elaboration time out; write the expressions out. And `interior_subset ht`
against an expected type `t ∈ T` elaborates `interior T`: write `interior_subset (s := …) ht`.
