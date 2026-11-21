# 0039 — In dimension n ≤ 1 every projective pocket is a shell

*Found 2026-11-21 by T-bz-c2-premier-full-proj; recorded by the master session.*

In dimension n ≤ 1 every projective pocket is a shell (isCoqueProj_of_le_one_proj, Chapter2/PremierFull.lean). φ(P) is connected in H̊ ≅ ℝⁿ, so it is convex: transport it through e : H̊ ≃ᵃ ℝⁿ (Sphere.nonempty_hemi_affineEquiv), whose inverse is an open embedding into S(n) (isOpenEmbedding_coe_affineEquiv), and apply convex_of_isPreconnected_of_le_one (PremierAffine). Any n ≤ 1 statement about pockets then reduces to shells, with no arc argument on S(1).
