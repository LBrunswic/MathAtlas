# 0179 — Pitfall: `set L := span F (v i)` when a hypothesis c : ↥(span F (v i)) ≃ₗ … is in context

*Found 2026-11-28 by T-bz-c3-balayable-somme-cor; recorded by the master session.*

Pitfall: `set L := span F (v i)` when a hypothesis c : ↥(span F (v i)) ≃ₗ … is in context shadows c as c✝ and breaks every later term; write the span out. Likewise `rw [F_summand_eq]` on `↑u ∈ F (v i)` with u : ↥(span F (v i)) fails the motive; rewrite the membership with Set.ext_iff.1 h ↑u, or use congrArg (fun X => …) h.
