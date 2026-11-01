import CausalScaffold.Flat.Externals

/-!
# A Lorentz transformation fixing two points of `𝒮` is a boost on their null plane

Linear half of Barbot's normal form in [10.M] (`GHFspace.tex` l.3235–3330, the prose served by
`loxo_elementary_misner`, `Flat/Loxodromic.lean`). **No label is marked**: [10.M] is prose, and
only its linear half is proved here.

* [10.M], `GHFspace.tex:3248` and `GHFspace.tex:3303–3323`, partial (linear part only; **no
  `sorry`**): `lorentz_normalForm_of_fix_two`. If `A ∈ SO₀(1,d)` fixes the two distinct
  directions `u₀ ≠ u₁` of `𝒮` (Barbot's `Δ₀`, `Δ₁`), then `A (1,u₀) = e^{-a} (1,u₀)`,
  `A (1,u₁) = e^{a} (1,u₁)`, `A` preserves `P = Δ₀^⊥ ∩ Δ₁^⊥`, `A` is loxodromic iff `a ≠ 0`, and
  `A` is elliptic when `a = 0`.

> The isometry $\gamma$ is loxodromic if and only if $a(\gamma) \neq 0$.

> Let $P$ be the spacelike direction $\Delta_{0}^{\perp} \cap \Delta_{1}^{\perp}$, and
> $E$ the quotient space of \mink by $P$.

> \[ \gamma(x, z, y) = (e^{-a(\gamma)}x, R(\gamma)(z) + u(\gamma), e^{a(\gamma)}y) \]

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `L(γ)` fixes the isotropic directions `Δ₀`, `Δ₁` (l.3313–3314) | ✓ carried (`h₀`, `h₁`) |
| `Δ₀ ≠ Δ₁` | ✓ carried (`hne`) |
| `γ ∈ Γ` acts by an isometry | ⚠ weakened: any `A ∈ SO₀(1,d)`, no group `Γ` |

## SCOPE (disclosed)

Only the linear part `L(γ)` is treated: the eigenvalues `e^{∓a}` on the null lines, invariance of
`P`, and the loxodromic/elliptic dichotomy. The affine half (`x(γ) = y(γ) = 0`, the translation
`u(γ)` in `P`) and the Bieberbach / Misner identification remain open in `loxo_elementary_misner`.
The rotation `R(γ)` on `P` is not extracted as a separate object; only `A(P) ⊆ P` is stated.

Proof: `A (1,uᵢ) = cᵢ (1,uᵢ)` with `cᵢ = lorentzScale A uᵢ > 0`; `⟨(1,u₀)|(1,u₁)⟩ ≠ 0` and is
preserved, so `c₀ c₁ = 1`; `a = log c₁`. For `a ≠ 0` use `isLoxodromic_of_null_eigen`; for
`a = 0`, `A` fixes the timelike `(1,u₀) + (1,u₁)` (`isElliptic_of_fixed_timelike`).

Provenance: plan `/tmp/loxplan/M1_TwoNullNormalForm.lean` (statement typechecked by the planner);
mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal.Flat.Lox

open Causal.Flat

variable {d : ℕ}

/-- A fixed point `u` of the action of `A` on `𝒮` is a null eigenvector: `A (1,u) = c (1,u)`
with `c = lorentzScale A u > 0`. -/
theorem lox_apply_nullVec_of_fix {A : lorentz d} {u : PenroseSphere d}
    (h : lorentzSphere A u = u) :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) = lorentzScale A u • nullVec u := by
  have e := nullVec_lorentzSphere A u
  rw [h] at e
  calc (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)
      = lorentzScale A u •
          ((lorentzScale A u)⁻¹ • (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u)) := by
        rw [smul_smul, mul_inv_cancel₀ (lorentzScale_pos A u).ne', one_smul]
    _ = lorentzScale A u • nullVec u := by rw [← e]

/-- For distinct `u₀ ≠ u₁ ∈ 𝒮`, `⟨(1,u₀)|(1,u₁)⟩ < 0`. -/
theorem lox_minkB_nullVec_neg {u₀ u₁ : PenroseSphere d} (hne : u₀ ≠ u₁) :
    minkB (nullVec u₀) (nullVec u₁) < 0 := by
  rw [minkB_nullVec_nullVec]
  have h1 : (u₀ : EuclideanSpace ℝ (Fin d)) - u₁ ≠ 0 :=
    sub_ne_zero.2 fun h => hne (Subtype.ext h)
  have h2 : 0 < ‖(u₀ : EuclideanSpace ℝ (Fin d)) - u₁‖ := norm_pos_iff.2 h1
  have h3 : 0 < ‖(u₀ : EuclideanSpace ℝ (Fin d)) - u₁‖ ^ 2 := by positivity
  linarith

/-- **Linear normal form** (Barbot [10.M], l.3248, l.3303–3323, linear half): an element of
`SO₀(1,d)` fixing two distinct points `u₀ ≠ u₁` of `𝒮` scales `(1,u₀)` by `e^{-a}` and `(1,u₁)` by
`e^{a}`, preserves `P = (1,u₀)^⊥ ∩ (1,u₁)^⊥`, is loxodromic iff `a ≠ 0`, and elliptic if `a = 0`. -/
theorem lorentz_normalForm_of_fix_two {A : lorentz d} {u₀ u₁ : PenroseSphere d} (hne : u₀ ≠ u₁)
    (h₀ : lorentzSphere A u₀ = u₀) (h₁ : lorentzSphere A u₁ = u₁) :
    ∃ a : ℝ, (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₀) = Real.exp (-a) • nullVec u₀ ∧
      (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u₁) = Real.exp a • nullVec u₁ ∧
      (∀ v, minkB (nullVec u₀) v = 0 → minkB (nullVec u₁) v = 0 →
        minkB (nullVec u₀) ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) v) = 0 ∧
          minkB (nullVec u₁) ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) v) = 0) ∧
      (IsLoxodromic (A : Minkowski d ≃ₗ[ℝ] Minkowski d) ↔ a ≠ 0) ∧
      (a = 0 → IsElliptic (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) := by
  set L : Minkowski d ≃ₗ[ℝ] Minkowski d := (A : Minkowski d ≃ₗ[ℝ] Minkowski d) with hL
  set c₀ := lorentzScale A u₀
  set c₁ := lorentzScale A u₁
  have hc₀ : 0 < c₀ := lorentzScale_pos A u₀
  have hc₁ : 0 < c₁ := lorentzScale_pos A u₁
  have e₀ : L (nullVec u₀) = c₀ • nullVec u₀ := lox_apply_nullVec_of_fix h₀
  have e₁ : L (nullVec u₁) = c₁ • nullVec u₁ := lox_apply_nullVec_of_fix h₁
  have hB := lox_minkB_nullVec_neg hne
  -- `c₀ c₁ = 1`
  have hcc : c₀ * c₁ = 1 := by
    have h := lorentz.minkB_apply A.2 (nullVec u₀) (nullVec u₁)
    rw [← hL, e₀, e₁, minkB_smul_left, minkB_smul_right, ← mul_assoc] at h
    have h' : (c₀ * c₁ - 1) * minkB (nullVec u₀) (nullVec u₁) = 0 := by linarith
    rcases mul_eq_zero.1 h' with h'' | h''
    · linarith
    · exact absurd h'' hB.ne
  refine ⟨Real.log c₁, ?_, ?_, ?_, ?_⟩
  · rw [Real.exp_neg, Real.exp_log hc₁, e₀, eq_inv_of_mul_eq_one_left hcc]
  · rw [Real.exp_log hc₁, e₁]
  · intro v hv₀ hv₁
    have key : ∀ (u : PenroseSphere d) (c : ℝ), 0 < c → L (nullVec u) = c • nullVec u →
        minkB (nullVec u) (L v) = c⁻¹ * minkB (nullVec u) v := by
      intro u c hc hu
      have h := lorentz.minkB_apply A.2 (nullVec u) v
      rw [← hL, hu, minkB_smul_left] at h
      rw [← h, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    rw [key u₀ c₀ hc₀ e₀, key u₁ c₁ hc₁ e₁, hv₀, hv₁]
    exact ⟨mul_zero _, mul_zero _⟩
  -- the dichotomy
  have hell : Real.log c₁ = 0 → IsElliptic L := by
    intro ha
    have hc₁1 : c₁ = 1 := by
      have := Real.exp_log hc₁; rw [ha, Real.exp_zero] at this; exact this.symm
    have hc₀1 : c₀ = 1 := by rw [hc₁1, mul_one] at hcc; exact hcc
    have hfix : L (nullVec u₀ + nullVec u₁) = nullVec u₀ + nullVec u₁ := by
      rw [map_add, e₀, e₁, hc₀1, hc₁1, one_smul, one_smul]
    have hq : minkQ (nullVec u₀ + nullVec u₁) < 0 := by
      rw [minkQ_add, minkQ_nullVec, minkQ_nullVec]; linarith
    exact isElliptic_of_fixed_timelike (fun w => lorentz.minkQ_apply A.2 w) hq hfix
  refine ⟨⟨fun hlox ha => hlox.not_isElliptic (hell ha), fun ha => ?_⟩, hell⟩
  have he : Real.exp (Real.log c₁) = c₁ := Real.exp_log hc₁
  refine isLoxodromic_of_null_eigen A.2 (nullVec_ne_zero u₁) (minkQ_nullVec u₁) hc₁
    (fun h => ha ?_) e₁
  rw [← he, Real.exp_eq_one_iff] at h
  exact h

end Causal.Flat.Lox
