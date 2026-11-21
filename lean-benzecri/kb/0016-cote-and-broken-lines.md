# 0016 — Cotes as linear forms; condition b on sub-segments; broken lines as an inductive predicate

*Found 2026-11-21 by T-bz-c2-lignes; recorded by the master session.*

An affine function on an open hemisphere H̊ of equation l is a linear form read on the normalised
representative: z(s(v)) = Λ(v)/l(v) (`Sphere.exists_linear_cote`, `Sphere.cote_eq_div`); along a
segment of H̊ it lies between its endpoint values (`Sphere.cote_mem_uIcc`). Condition b of a pocket,
applied to every sub-segment (M, X) (with `isProjSegment_of_chart`), puts the part of a segment from
M where z < 1 inside P, and there φ̃ = φ by `eqOn_of_germ_eq` (`IsPocheProj.septieme_majore`). Broken
lines are the inductive `IsLigneBrisee` (`isLigneBrisee_iff` gives the vertex form); induct on it, or
prepend with `.cons`, `.append`. Pitfall: `add_comm` with no arguments may rewrite the `n + 1` inside
`Fin (n + 1) → ℝ` (« motive is not type correct »); write `add_comm β α`.
