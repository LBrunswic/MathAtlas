---
id: 0023
title: A union of two convex bodies with a common interior point is a closed disc
kind: pattern
created: 2026-11-21
---
Found by T-gx-troyanov-four. `GX.exists_homeomorph_union_convex`: the gauge of the union is the min of the gauges (`gauge_union_eq_min`), and Mathlib's `gaugeRescale` is continuous with no convexity once the gauges are. The proof extends to n convex pieces sharing an interior point.
