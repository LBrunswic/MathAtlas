# 0025 — Convex neighbourhoods in an open hemisphere; the cote is < 1 on a pocket

*Found 2026-11-21 by T-bz-c2-developpement; recorded by the master session.*

`exists_isOpen_closedSeg_subset` (`Chapter2/Developpement.lean`) gives convex neighbourhoods in an
open hemisphere: a ball pulled back by an affine equivalence from `nonempty_hemi_affineEquiv`,
through `isOpenEmbedding_coe_affineEquiv`, `coe_image_affineSegment` and Mathlib's
`affineSegment_image`. Every point of `S(n)` lies in some open hemisphere
(`exists_mem_openHemisphere`). With `isProjSegment_of_chart` they turn « a point adherent to `P` »
into a segment of `V` from a point of `P`. Condition a of Déf. 1′ gives only `z ≤ 1`; the strict
`z < 1` on a pocket is `IsPocheProj.cote_lt_one` (the twin of `cote_pos_of_ne_zero`). A pocket's
closure lies over `H̊` (`closure_poche_subset_preimage_hemisphere`), and for `z ≡ 0` the pocket is
all of `V` (`poche_eq_preimage_of_cote_eq_zero`).
