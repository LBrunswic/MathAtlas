# 0120 — Mathlib at the pin has no compactness lemma for convexJoin: write convexJoin ℝ A

*Found 2026-11-28 by T-bz-c3-proprietes-i-ii; recorded by the master session.*

Mathlib at the pin has no compactness lemma for convexJoin: write convexJoin ℝ A B as the image of A ×ˢ B ×ˢ Icc 0 1 under (a, b, θ) ↦ (1-θ)•a + θ•b (mem_convexJoin, segment_eq_image) — Benzecri.isCompact_convexJoin; with Convex.convexHull_union it gives compactness of the hull of two compact convex sets.
