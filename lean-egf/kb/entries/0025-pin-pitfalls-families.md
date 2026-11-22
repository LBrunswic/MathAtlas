---
id: 0025
title: Pitfalls at this pin from the families and mixing targets
kind: pitfall
created: 2026-11-22
---
Found by T-egf-families, T-egf-families-sphere and T-egf-mixing-criteria (Mathlib `fabf563a`).
- `Equiv.Perm.apply_inv_self` does not exist: use `h.apply_symm_apply` (`h⁻¹ x` is `h.symm x`).
- `push_neg` is deprecated: `push Not`. `mul_le_mul_left'` is deprecated: `mul_le_mul' le_rfl h`.
- A `set` variable blocks `rw` of its body: state `show <body> = _` first.
- `integral_unique` produces `Unique`'s `default`, not `Inhabited`'s: finish with `congr 1` and
  `Subsingleton.elim`. `integral_fintype` takes only the integrability argument.
- On a quotient, `ext` a `LinearEquiv` and take `q = W.mkQ v` by `W.mkQ_surjective`.
- `first | ring | linear_combination h` never reaches its second branch (`ring` falls back to
  `ring_nf` without failing): put `linear_combination` first.
- `simp` rewrites `↑(Real.cos t)` to `Complex.cos ↑t`: use `-Complex.ofReal_cos, -Complex.ofReal_sin`.
- `rw [← h]` with `h : ‖α‖ e^{i arg α} = α` rewrites `α` inside `arg α` too: use `conv_rhs`.
- Integrability side goals from `.mul` combinators come out beta-unreduced: state them with an
  explicit `fun x => …`.
- `rw [lintegral_congr_ae (h.mono …)]` fails when the target integrand is a metavariable: state both
  integrals in a `calc`. `hac.ae_le h` has a set-membership type: annotate it as `=ᵐ[λ̂]` before `.mono`.
- `gcongr` on `ρ^N ≤ ρ^k` with `ρ ≤ 1` asks for `1 ≤ ρ`: use `pow_le_pow_right_of_le_one'`.
- `rw [← bind_deterministic_eq_map]` needs the measurability proof when the goal does not contain it.
