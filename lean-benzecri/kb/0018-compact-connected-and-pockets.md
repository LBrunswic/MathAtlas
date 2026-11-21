# 0018 — Compact connected sets in a manifold; a pocket point of small cote; broken lines under automorphisms

*Found 2026-11-21 by T-bz-c2-compact; recorded by the master session.*

Every point of a space charted on a locally compact, locally connected T2 model has a compact
preconnected neighbourhood, with no T2 on the space itself; a clopen argument then puts any compact
set inside a compact connected one (`exists_domaineGenerateur_proj`, `Benzecri.Chapter2.Compact`).
A point of a pocket with cote below ε > 0: `hP.isGLB.exists_between` (show `0 < ε`), then destructure
the image membership. `ligne_brisee` needs `(n := n)` when E's type does not fix n (else « typeclass
instance problem is stuck NeZero ?m »). Broken lines are invariant under projective automorphisms:
`IsLigneBrisee.smul`, by induction with `smul_set_union` — a candidate to move into Lignes.
