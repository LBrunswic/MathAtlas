# 0008 — Cross-ratio, projective measure and majorised segments on S(E)

*Found 2026-11-20 by T-bz-c2-mesure; recorded by the master session.*

The cross-ratio and the projective measure of S(E) are in `Benzecri.Chapter2.CrossRatio` (Mathlib has
none). `IsCrossRatio A' B' B A r` is the odds form: there are representatives a, b with a + b
representing A' and a + r • b representing B'. Compute it with `isCrossRatio_of_coords`
(r = odds(B')/odds(A')) or `isCrossRatio_affine` (the classical (pr/qr)(qs/ps)). `projMeasure` is
`EReal`-valued and ⊤ on degenerate quadruples.

Points and segments of S(E) in coordinates: `Sphere.IsRep v x` (v ∈ F(x)). `mem_closedSeg_iff` and
`mem_openSeg_iff` turn segment membership into nonnegative (resp. positive) combinations of
representatives. B ≠ A ∧ B ≠ −A iff the representatives are independent
(`linearIndependent_of_ne`, `ne_of_linearIndependent`).

Building majorised segments: `isMajoreSeg_of_chart` needs one chart φ with (a', b') ⊆ (a, b) ⊆
φ.target and measure < k. `exists_closedSeg_extend` extends a segment of S(n) lying in an open set
beyond both endpoints, by the tube lemma on (ε, t).
