# 0007 — The open hemisphere H̊ against S(n); open subsets of ℝⁿ as affine manifolds

*Found 2026-11-20 by T-bz-c2-poches; recorded by the master session.*

Affine segments of H̊ (Déf. 6) are the segments of S(n) (`Sphere.coe_image_affineSegment`); Déf. 8
convexity is convexity in H̊ (`Sphere.isConvexPart_iff_isAffConvex`); lines of H̊ are half-lines of
S(n) (`isAffLine_hemi_iff`); F(closure A) = closure F(A) − {O} (`Sphere.F_closure`); GS(E) carries
closed segments to closed segments (`Sphere.GSE.image_smul_closedSeg`).

An open subset of ℝⁿ is a locally affine manifold through Mathlib's `Opens.instChartedSpace` and
`instHasGroupoid` (`gxGroupoid` is `ClosedUnderRestriction`), and its inclusion is `IsDeveloping` by
`rfl` (`isDeveloping_val_demiDroiteOuverte`): a cheap source of non-degenerate examples.
