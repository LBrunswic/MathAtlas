# 0006 — Segments of a manifold in charts; germs; the projective structure of an affine manifold

*Found 2026-11-20 by T-bz-c2-poches and T-bz-c2-mesure; recorded by the master session.*

A segment of a manifold is a segment in **every** compatible chart around it:
`IsGXSegment.image_eq`, `IsAffSegment.image_eq` (ψ(M, N) = [ψM, ψN]) and `IsProjSegment.image_eq`
(ψ(M, N) = (ψM, ψN), ψN ≠ −ψM), all in `Benzecri.Chapter2.Poches`. Two compatible charts, or a chart
and a developing map, with the same germ at one point agree along any connected set
(`eqOn_of_germ_eq`, `eqOn_of_germ_eq_isDeveloping`): these are the tools for Chapter 2's « carte
compatible d'un voisinage de (M, N) ayant en M même germe que φ ».

The canonical projective structure of a locally affine manifold is `Benzecri.projOfAff`; use
`attribute [local instance] projOfAff hasGroupoid_projOfAff` in a section. A projective chart equal
to j ∘ (affine chart) near one point is so along any connected set
(`eventually_eq_affineEquiv_of_isPreconnected`). Pocket predicates depend only on the maximal atlas
(`IsPocheProj.of_maximalAtlas_eq`).

**Duplicates removed (T-bz-c2-dedupe, 2026-11-21).** `Benzecri.Chapter2.Mesure` had proved five
of these facts on its own. It now imports Poches and keeps its names (`Sphere.gse_image_closedSeg`,
`Sphere.gse_smul_neg`, `Sphere.isPreconnected_closedSeg_of_ne_neg`,
`IsProjSegment.isPreconnected_seg`, `IsProjSegment.image_eq_closedSeg`) as one-line derivations
from Poches's statements. `exists_smul_eq_on_of_isPreconnected` (Mesure) has no twin and stays.
