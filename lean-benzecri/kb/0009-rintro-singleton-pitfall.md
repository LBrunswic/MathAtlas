# 0009 — `rintro _ rfl` on `x ∈ {M}` eliminates M

*Found 2026-11-20 by T-bz-c2-mesure; recorded by the master session.*

`rintro _ rfl` on a goal `x ∈ {M} → …` substitutes away the variable `M`, not `x`, and every later
reference to `M` breaks. Rewrite with `Set.mem_singleton_iff` and `rw [hx]` instead.
