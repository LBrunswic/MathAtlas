---
id: 0071
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-3p1-funnel-gtilde. Pitfall: after `set b := (A : Matrix (Fin 2) (Fin 2) R) 0 1` and `ext i j; fin_cases i <;> fin_cases j`, the goals read ↑A ((fun i => i) ⟨0, _⟩) ... and neither the set names nor rw [hb] match. Open each case with `show Matrix.scalar (Fin 2) a 0 1 = b` (a defeq restatement), then rw (see kb/0024).
