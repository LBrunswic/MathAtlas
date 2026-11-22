---
id: 0021
title: Group-action notions live in EGF.TorusFamilies; IsGroupErgodic is ErgodicSMul without the invariance
kind: convention
created: 2026-11-22
---
Found by T-egf-families. The notions the cited theorems need (amenable, virtually abelian, almost
invariant vectors, `IsGroupErgodic`) are stated once, in `EGF.TorusFamilies`, for any measurable
space `X` and `H : Subgroup (Equiv.Perm X)`; the sphere and def:egf files import them, never
redefine them. `EGF.IsGroupErgodic` is Mathlib's `MeasureTheory.ErgodicSMul`
(`Dynamics/Ergodic/Action/Basic.lean`) without the invariance of the measure; for measure-preserving
`H` the two agree (`EGF.isGroupErgodic_iff_ergodicSMul`); `ErgodicSMul`'s parent
`SMulInvariantMeasure` is an instance argument of its constructor, so build it with `haveI` first.
Finite groups give cheap witnesses (`EGF.isAmenableGroup_of_finite`, via `Set.ncard`). A finitely
generated subgroup is countable by `FreeGroup.closure_eq_range`, `inferInstanceAs (Countable (Quot _))`
for the free group and `(Set.countable_range _).to_subtype` (`EGF.countable_torusAffineGroup`).
