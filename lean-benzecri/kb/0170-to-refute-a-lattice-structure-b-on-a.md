# 0170 — To refute « a lattice structure B on a subtype ordered by inclusion », state the lattice

*Found 2026-11-28 by T-bz-c3-boole-projectif-domaines; recorded by the master session.*

To refute « a lattice structure B on a subtype ordered by inclusion », state the lattice argument over an abstract [DistribLattice α] with f : α → Submodule and hle : x ≤ y ↔ f x ≤ f y, then apply it with @lemma _ B Subtype.val: inside a proof, letI := B does not override Subtype.instLE for `≤`, so `x ≤ y` silently elaborates to the subtype order.
