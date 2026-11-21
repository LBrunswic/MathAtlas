---
id: 0017
title: The universality plug-in (IsUniversalPolicy → IsUniversalFamilyEps); cheap counterexamples on Bool
kind: pattern
created: 2026-11-21
---
Found by T-egf-universality. To prove a family ε-universal, prove `EGF.IsUniversalPolicy lam π` (the
conclusion of `EGF.main_universality` for one policy, no mixing inside), then apply
`EGF.isUniversalFamilyEps_of_policy_of_isDenseNonnegConeL2` (finite `λ`, outflows dense in the
non-negative cone of `L²`) or `EGF.isUniversalFamilyEps_of_policy` (`L¹` density on bounded `g ≥ 0`,
any `λ`); the family enters as `hD : ∀ f ∈ D, ∃ F ∈ 𝓕, F.policy = π ∧ F.outflow = lam.withDensity (ofReal ∘ f)`.
Finite counterexamples: `EGF.Coin.lam = 2⁻¹ • (dirac true + dirac false)` with `lam_singleton`,
`lam_withDensity_singleton`, `lam_withDensity_univ`; `Kernel.const Bool lam` is the EGF policy of the
moves `id, not` with `α = ½`, `Kernel.id` the one with `α = (1, 0)`. To refute an identity of finite
`ℝ≥0∞` expressions: `congrArg ENNReal.toReal`, `simp only` with `toReal_add/_mul/_ofReal` and the
`ne_top` side goals, then `linarith`. Pitfalls: `withDensity_congr_ae (h.mono fun s hs => by rw [hs])`
meets a beta-redex, use `simp only [hs]`; an anonymous `GenerativeFlow` constructor with an inferred
outflow loses `IsFiniteMeasure`: give the outflow in a `let`.
