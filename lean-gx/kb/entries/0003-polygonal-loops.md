---
id: 0003
title: Relations among polygonal loops in a planar subspace need no explicit homotopy
kind: pattern
created: 2026-11-20
---
Build the edges with `GX.segIn` from convex boxes inside the subspace S of ℝ², then close the
identity in `Path.Homotopic.Quotient` with `simp only [mk_trans, mk_symm, trans_assoc]` and the
cancellation `p.symm.trans (p.trans q) = q`; straight lines in a convex box are homotopic
(`GX.homotopic_of_convex_subset`). In an induction over the model's vertices, clamp indices
(`min k a`) so every edge exists for every k; make a base point that is a vertex an `abbrev`, or
`simp`'s `mk_trans` fails silently (endpoints do not unify at reducible transparency)
(T-3p1-theorem-m).
