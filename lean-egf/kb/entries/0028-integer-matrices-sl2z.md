---
id: 0028
title: Integer matrices without periodic vector; SL₂(ℤ) = ⟨S, T⟩; an irreducible cubic
kind: pattern
created: 2026-11-22
---
Found by T-egf-tori-minimal. `EGF.NoPeriodicVector A ↔ ∀ n > 0, det(Aⁿ − 1) ≠ 0`
(`Matrix.exists_mulVec_eq_zero_iff` over the domain `ℤ`). In `SL₂`: `det(X − 1) = 2 − tr X` and the
trace recursion (`EGF.noPeriodicVector_of_two_lt_trace`). Block diagonals:
`Matrix.reindex finSumFinEquiv finSumFinEquiv (fromBlocks X 0 0 Y)` seen as
`Matrix.reindexAlgEquiv ℤ ℤ` (`map_pow`, `map_sub`, `map_one`), its determinant by
`det_reindex_self` and `det_fromBlocks_zero₂₁`. An irreducible cubic over `ℚ`:
`irreducible_of_degree_le_three_of_not_isRoot` (`Mathlib.Algebra.Polynomial.SpecificDegree`) with
`exists_integer_of_is_root_of_monic` (`Mathlib.RingTheory.Polynomial.RationalRoot`), `compute_degree!`
and `monicity!` (`Mathlib.Tactic.ComputeDegree`); Bézout by `Irreducible.coprime_iff_not_dvd`,
evaluated by `Polynomial.aeval` at the matrix over `ℚ`. `SL₂(ℤ) = ⟨S, T⟩` is Mathlib's
`SpecialLinearGroup.SL2Z_generators` (`Mathlib.LinearAlgebra.Matrix.FixedDetMatrices`);
`ModularGroup.S`, `ModularGroup.T` are definitionally `EGF.matS`, `EGF.matT`; push to units by
`Matrix.SpecialLinearGroup.toGL` and `MonoidHom.map_closure`, identify with `Matrix.nonsingInvUnit`
by `Units.ext rfl`; the linear parts of the group of the moves contain the group the `Aᵢ` generate
(`EGF.coe_mem_linearParts_of_mem_closure`).
