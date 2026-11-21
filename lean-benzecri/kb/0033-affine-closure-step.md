# 0033 — The affine closure step of 1°c needs no hemisphere

*Found 2026-11-21 by T-bz-c2-premier-affine; recorded by the master session.*

Take a ball inside {z < 1} ∩ range φ̃ (`Metric.isOpen_iff`), a point of P over it (`mem_closure_iff`), `convex_ball.segment_subset`, then `isAffSegment_of_chart` (the affine twin of `isProjSegment_of_chart`) and condition b with ψ := φ̃. For z ≡ 0 the pocket is then clopen, so P = V, with no twin of `closure_poche_subset_preimage_hemisphere`.
