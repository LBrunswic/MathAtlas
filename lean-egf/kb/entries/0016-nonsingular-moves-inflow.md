---
id: 0016
title: F_in ≪ λ for an EGF from nonsingular moves; Haar null sets without the Jacobian
kind: pattern
created: 2026-11-21
---
Found by T-egf-inflow-nonsingular. For an EGF policy the inflow is absolutely continuous as soon as
every move is nonsingular: `EGF.InflowAC.of_map_ac` (any measurable space, measurable `Φᵢ`, no
inverse, no σ-finiteness), through `EGF.IsEGFPolicy.bind_eq_sum_map` (`μπ = ∑ᵢ (Φᵢ)₊(αⁱ μ)` for any
`μ`). For measure-preserving moves (tori, spheres) use `EGF.map_ac_of_measurePreserving` or
`EGF.InflowAC.of_measurePreserving`, and `EGF.backward_policy_measurePreserving` (`J ≡ 1`). The
density `f_in` itself needs σ-finite `λ` (`EGF.inflow_eq_withDensity_of_map_ac`; it fails for
`λ = Leb|(0,1) + ∞·Leb` elsewhere). `Φ₊μ ≪ μ` for Haar `μ` needs no Jacobian formula: if `g ∘ Φ = id`
with `g` differentiable, `Φ⁻¹(A) ⊆ g(A)` and `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`
gives the null set (`EGF.map_ac_of_leftInverse`). Pitfall: `measure_mono_null (fun x hx => ⟨y, hy, h⟩)`
fails with "expected type could not be determined": state the inclusion with `show A ⊆ B from …`.
