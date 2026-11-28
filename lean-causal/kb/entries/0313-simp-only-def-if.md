---
id: 0313
title: simp only on a def with an if over u = id rewrites the test to True: state the lemma in term mode
kind: pitfall
created: 2026-11-28
---
`simp only [f]` on a def `f := fun u => if u = id ∨ … then … else …` applied to `id` rewrites `id = id` to `True`, and `if_pos (Or.inl rfl)` then fails. State the lemma in term mode, `theorem f_id : f id = … := if_pos (Or.inl rfl)`: elaboration unfolds the def definitionally (`Causal.Ers482Separation.cauSep_id`).
