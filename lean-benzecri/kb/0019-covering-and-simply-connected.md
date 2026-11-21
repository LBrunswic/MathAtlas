# 0019 — Covering maps from local sheets; the section lemma; interiors of convex bodies are simply connected

*Found 2026-11-21 by T-bz-c2-hemisphere; recorded by the master session.*

`IsCoveringMapOn p s`: choose one sheet per point of the fibre and feed them to Mathlib's
`IsOpen.trivializationDiscrete` (`Benzecri.Chapter2.Hemisphere`). The section lemma
`mem_of_injOn_of_isPreconnected`: X Hausdorff, p open, O and O′ open with p injective on each, B
preconnected under both, sections meeting over B ⇒ equal there (fails without Hausdorff: the line
with two origins). The interior of a convex body of S(n) is simply connected
(`simplyConnectedSpace_corpsInterior`, homeomorphic through `nrm ℓ` to a convex set); a projective γ
with γ • int K = int K is an automorphism of `corpsInterior K` (`autInterior`). Uniformly small
pseudo-balls near a point: `exists_pos_eventually_pseudoBoule_subset`, standing in for the triangle
inequality the paper never states. Pitfall: `y ∈ γ • S` is not destructured by `rintro`; use
`Set.mem_smul_set.1`.
