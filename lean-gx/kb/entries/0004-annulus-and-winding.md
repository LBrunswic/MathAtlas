---
id: 0004
title: The annulus lemma, and winding numbers as holonomies for counterexamples
kind: pattern
created: 2026-11-20
---
`I × I` is simply connected (`(convex_Icc 0 1).contractibleSpace`, the product instance,
`SimplyConnectedSpace.ofContractible`); `SimplyConnectedSpace.paths_homotopic` then gives
`GX.mk_eq_conj_of_annulus` (freely homotopic loops are conjugate by the base point's track).
gx's winding number `GX.cWinding` (`GX.Branched.Paths`) packaged as `GX.windingHom : π₁ →
Multiplicative ℤ`, composed with `zpowersHom`, gives holonomies `g^wind` for counterexamples
(`GX.m3_printed_fails`) (T-3p1-theorem-m).
