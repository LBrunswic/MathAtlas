---
id: 0024
title: Mixing under invariance; deterministic kernels are never summably mixing; OQ-47's vacuous reading
kind: pattern
created: 2026-11-22
---
Found by T-egf-mixing-criteria (`EGF/MixingCriteria.lean`). Under `λπ = λ` the transfer composes
a.e. (`EGF.transfer_add_ae`), keeps the mean (`EGF.integral_transfer`) and contracts `L²(λ)`
(`EGF.eLpNorm_transfer_le`); with `λ̂ = λ`, `γ` is submultiplicative (`EGF.mixingCoeff_self_add_le`).
Reduce a mixing claim to `γ_N < 1` (`EGF.isSummablyL2Mixing_of_mixingCoeff_lt_one`) or, for a
reversible kernel, to a two-sided Rayleigh bound (`EGF.isSummablyL2Mixing_of_reversible`). The kernel
of an automorphism `e` has `transfer … n φ =ᵐ φ ∘ e.symm^[n]` (`EGF.transfer_deterministic_ae`), so
`γ_n = γ_0` (`EGF.mixingCoeff_deterministic`) and it is never summably mixing
(`EGF.not_isSummablyL2Mixing_of_map_eq`). On `(Bool, Coin.lam)`, `EGF.Swap.eq_of_ae_eq` turns an a.e.
equality into an equality, so `rnDeriv` and `transfer` compute pointwise. OQ-47's reading with `H`
normalized in `L²(λ̂)` is vacuous for `λ̂ = ∞ • λ` (`EGF.unitMeanZero_top_smul`): a statement in that
reading must take `λ̂` finite (DEC-145 took the `L²(λ)` reading).
