---
id: 0019
title: Adding or removing a marked point: Fin.insertNth / Fin.removeNth, and one rfl per index
kind: pitfall
created: 2026-11-20
---
Found by T-gx-troyanov-two-pi. Use `Fin.insertNth (α := fun _ => M) k q p` and `Fin.removeNth k` with `Fin.eq_self_or_eq_succAbove`; the cone-sphere versions are `GX.IsConeSphere.insertNth` and `.removeNth`. Do not `rcases … with rfl` twice on the same k: the first rfl eliminates k; `rw [hi, hj] at hij ⊢` instead.
