---
id: 0016
title: Comparing cone charts through the developing map
kind: pattern
created: 2026-11-20
---
Found by T-gx-troyanov-triangle. Lift h ≠ 0 to the half-plane at (|h|, arg h / 2π), use `sphCone_chart_dev` there, and transport along the open map q ↦ Φ(polar q) (`GX.SphTriangle.eventually_chart_eq`); then compare every chart with one reference map per point (fold, ρ ∘ fold, refEdge k), so that two charts differ by one element of SO(3).
