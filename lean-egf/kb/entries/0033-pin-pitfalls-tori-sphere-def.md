---
id: 0033
title: Pitfalls at this pin from the tori, sphere-density and def:egf targets
kind: pitfall
created: 2026-11-22
---
Found by T-egf-tori-minimal, T-egf-sphere-dense-ergodic and T-egf-def-egf.
- `∆` (`symmDiff`, `open scoped symmDiff`) binds tighter than `⁻¹'`: `Φ ⁻¹' A ∆ A` parses as
  `Φ ⁻¹' (A ∆ A)`, a silently vacuous hypothesis; write `(Φ ⁻¹' A) ∆ A`.
  `measure_symmDiff_eq_zero_iff` needs `(μ := lam)`.
- `ℚ[X]` needs `open Polynomial` at section level (an `open … in` before a tactic does not reach the
  statement).
- `not_imp` is ambiguous (root vs `Classical`) and `_root_.not_imp` is deprecated: use
  `Classical.not_imp`.
- A `set` variable hides its body from `rw`: `simp only [hdef]` first.
- `simp` on the entries of `X.trace • X − X.det • 1` turns the scalars into casts into matrices:
  `simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]` first, then
  `fin_cases`.
- `Matrix.mem_orthogonalGroup_iff` takes `n` and `R` explicitly; `EuclideanSpace.single_apply` is
  deprecated for `PiLp.single_apply`.
- `A • v` on `EuclideanSpace` already means `A *ᵥ v` (Mathlib's `Module (Matrix n n R) (n → R)`
  through `WithLp.instSMul`): a possible second path to an action on the sphere.
