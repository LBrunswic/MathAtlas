# 0028 — Convex geometry of open parts of S(n): salient closure, half-lines through every point

*Found 2026-11-21 by T-bz-c2-theoreme; recorded by the master session.*

In `Chapter2/Theoreme.lean`: let C be an open strict convex part. If closure F(C) is salient, closure C is a convex body and C is its interior (`isCorpsConvexeS_closure_of_salient`). If ±x ∈ closure F(C), then p + ℝx ⊆ F(C) for every p ∈ F(C) (`demiDroite_of_not_salient`), so a half-line can be placed through any chosen point. A nonempty open convex part other than S(n) is strict (`Sphere.isStrictConvexPart_of_isOpen`). interior (closure C) = C when C is open and F(C) convex (`interior_closure_eq_of_convex_F`). The demi-droite lemma itself is `exists_demiDroite`; S(n) has none (`univ_not_demiDroite`). Next user: T-bz-c2-theoreme-affine, the affine 4°.
