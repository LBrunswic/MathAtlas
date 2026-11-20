---
id: 0012
title: Elements of SO(3) from matrices and orthonormal frames
kind: pattern
created: 2026-11-20
---
Found by T-gx-troyanov-triangle. `GX.matSO3` (orthogonal, det 1) and `GX.frameSO3` (an orthonormal pair (v, w) of `Fin 3 → ℝ` gives the rotation with rows v × w, v, w; the determinant by `triple_product_eq_det`), with coordinates `GX.toR3` / `GX.vec` on ℝ ⊕ ℂ (`GX.Spherical.TroyanovTriangle`). Use them instead of hand-built `LinearIsometryEquiv`s.
