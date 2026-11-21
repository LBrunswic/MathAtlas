# 0022 — Cheap homogeneous affine manifolds, and a pocket with a non-constant cote

*Found 2026-11-21 by T-bz-c2-cas-affin; recorded by the master session.*

`Benzecri.GXAut.ofOpens` builds an automorphism of an open subset `U` of the model from any
`g ∈ G` with `g • x ∈ U ↔ x ∈ U`; on `Opens` of the model, `chartAt X x y = y.val` holds by `rfl`.
Ready-made examples in `Chapter2/CasAffin.lean`: the open half-space `demiEspaceOuvert n`
(homogeneous, with the pocket `{0 < x₀ < 1}` and the non-constant cote `x₀`,
`exists_isPocheAff_demiEspace`, by `exemple_poche_affine`) and the hyperplane complement
`complHyperplan n` (disconnected, homogeneous, same pocket). A pocket with a non-constant cote
exists in every dimension ≥ 1, so use it as the non-vacuity witness of any pocket statement that
must survive OQ-61 (a); in dimension 0 every affine function is constant and none exists.
