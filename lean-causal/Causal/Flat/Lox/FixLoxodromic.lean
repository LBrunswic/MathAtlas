import CausalScaffold.Flat.Externals

/-!
# `CausalScaffold.Flat.Lox.FixLoxodromic` — [10.M], first step: a finite-index `Γ'` whose linear part fixes `Δ₀`, a fixed direction of a loxodromic `γ₀`, with `Δ₁` the other one

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §10,
subsection "The elementary case" (`misnerr`). No ledger label is certified here (no `**` mark):
this is the opening reduction of `loxo_elementary_misner` (`Flat/Loxodromic.lean`, [10.M]),
l.3237–3240 of `papers/barbot/legacy/labeled/GHFspace.tex`:

> Here, we consider the case where, up to
> finite index, $L(\Gamma)$ preserves some isotropic
> direction $\Delta_{0}$. Since $\gamma_{0}$ is loxodromic, it admits a second
> isotropic fixed direction: we denote this fixed direction by $\Delta_{1}$.

`exists_finiteIndex_fix_loxodromic`: if a finite-index `H ≤ L(Γ)` fixes `u ∈ 𝒮` (the unfolded
negation of `IsNonelementary Γ`) and `γ₀ ∈ Γ` is loxodromic, then `Γ' = Γ ⊓ L⁻¹(H)` has finite
index in `Γ`, contains a power `γ₀ᵏ`, `k > 0`, and `u` is one of the two (distinct) fixed points
`u₀ = u`, `u₁` of `L(γ₀)` on `𝒮` — Barbot's `Δ₀`, `Δ₁`. The paper's "Since γ₀ is loxodromic" is
read as: `γ₀ᵏ ∈ Γ'` fixes `Δ₀`, and a fixed point of a positive power of a loxodromic element is a
fixed point of the element itself (`minkB_eq_zero_of_fixed_pow_loxodromic`, `exists_fixed_pair_of_null_orth`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| up to finite index, `L(Γ)` preserves an isotropic direction `Δ₀` | ✓ carried (`helem`: `H ≤ L(Γ)`, finite relative index, fixing `u`) |
| `γ₀ ∈ Γ` loxodromic | ✓ carried (`hγ₀`, `hlox`) |

## SCOPE (disclosed)

* Not covered: that a further finite-index subgroup also fixes `Δ₁` (l.3286–3299, through
  `L(Γ₀)` finite); here only `L(Γ')` fixes `u₀`, and `L(γ₀)` fixes both.
* `Δ₀` of the statement is `u₀ = u`, the point `H` fixes: it is a fixed point of `L(γ₀)` itself,
  not only of its power.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Planner's statement
`/tmp/loxplan/M2_FixLoxodromic.lean`; the null-direction construction repeats
`Flat.Loxodromic.exists_nullVec_eq_smul` (not importable here).
-/

namespace Causal.Flat

open Set

variable {d : ℕ}

namespace Lox

/-- A nonzero null vector is a nonzero multiple of the null vector of a point of `𝒮`. -/
theorem exists_nullVec_eq_smul_of_null {e : Minkowski d} (he0 : e ≠ 0) (he : minkQ e = 0) :
    ∃ (u : PenroseSphere d) (c : ℝ), c ≠ 0 ∧ nullVec u = c • e := by
  have he1 : e.1 ≠ 0 := fun h0 => he0 (eq_zero_of_fst_eq_zero h0 he.le)
  have hnorm : ‖e.2‖ = |e.1| := by
    have h2 : ‖e.2‖ ^ 2 = |e.1| ^ 2 := by
      have := he; simp only [minkQ] at this; rw [sq_abs]; linarith
    exact (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).1 h2
  refine ⟨⟨e.1⁻¹ • e.2, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, hnorm,
      inv_mul_cancel₀ (abs_ne_zero.2 he1)]⟩, e.1⁻¹, inv_ne_zero he1, ?_⟩
  refine Prod.ext ?_ rfl
  simp [nullVec, inv_mul_cancel₀ he1]

/-- **Two fixed points from a null frame.** If `e`, `e'` are null eigenvectors of `A ∈ SO₀(1, d)`
with `⟨e | e'⟩ ≠ 0`, and `u ∈ 𝒮` has `(1, u)` orthogonal to `e`, then `u` (the direction of `e`)
and the direction `u₁` of `e'` are two distinct fixed points of `A` on `𝒮`. -/
theorem exists_fixed_pair_of_null_orth {A : lorentz d} {e e' : Minkowski d} {μ μ' : ℝ}
    (he0 : e ≠ 0) (he0' : e' ≠ 0) (hq : minkQ e = 0) (hq' : minkQ e' = 0)
    (hee' : minkB e e' ≠ 0) (hAe : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) e = μ • e)
    (hAe' : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) e' = μ' • e') {u : PenroseSphere d}
    (hu : minkB e (nullVec u) = 0) :
    ∃ u₁ : PenroseSphere d, u ≠ u₁ ∧ lorentzSphere A u = u ∧ lorentzSphere A u₁ = u₁ := by
  obtain ⟨a, ha⟩ := eq_smul_of_null_orth hq he0 (minkQ_nullVec u) hu
  obtain ⟨u₁, b, hb, hu₁⟩ := exists_nullVec_eq_smul_of_null he0' hq'
  refine ⟨u₁, fun h => ?_, lorentzSphere_eq_of_eigen (c := μ) ?_,
    lorentzSphere_eq_of_eigen (c := μ') ?_⟩
  · rw [h, hu₁, minkB_smul_right] at hu
    exact hee' ((mul_eq_zero.1 hu).resolve_left hb)
  · rw [ha, map_smul, hAe, smul_comm]
  · rw [hu₁, map_smul, hAe', smul_comm]

/-- **A point of `𝒮` fixed by a positive power of a loxodromic `A` is orthogonal to one of its two
null eigenvectors** `e`, `e'` (eigenvalues `l`, `l⁻¹`, `l ≠ 1`): if `Aᵏ(1,u) = c(1,u)`, then
`lᵏc⟨e|(1,u)⟩ = ⟨e|(1,u)⟩` and `l⁻ᵏc⟨e'|(1,u)⟩ = ⟨e'|(1,u)⟩`; both brackets nonzero would force
`c² = 1`, so `c = 1` and `lᵏ = 1`. -/
theorem minkB_eq_zero_of_fixed_pow_loxodromic {A : lorentz d} {e e' : Minkowski d} {l : ℝ}
    (hl : 0 < l) (hl1 : l ≠ 1) (hAe : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) e = l • e)
    (hAe' : (A : Minkowski d ≃ₗ[ℝ] Minkowski d) e' = l⁻¹ • e') {k : ℕ} (hk : 0 < k)
    {u : PenroseSphere d} (hfix : lorentzSphere (A ^ k) u = u) :
    minkB e (nullVec u) = 0 ∨ minkB e' (nullVec u) = 0 := by
  set c := lorentzScale (A ^ k) u with hc
  have hc0 : 0 < c := lorentzScale_pos _ u
  have hAkv : ((A ^ k : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) (nullVec u) =
      c • nullVec u := by
    have h := nullVec_lorentzSphere (A ^ k) u
    rw [hfix] at h
    conv_rhs => rw [h]
    rw [smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]
  have h1 : l ^ k * c * minkB e (nullVec u) = minkB e (nullVec u) := by
    have := lorentz.minkB_apply (A ^ k).2 e (nullVec u)
    rw [lorentz_pow_apply_of_eigen A hAe k, hAkv, minkB_smul_left, minkB_smul_right] at this
    linear_combination this
  have h2 : l⁻¹ ^ k * c * minkB e' (nullVec u) = minkB e' (nullVec u) := by
    have := lorentz.minkB_apply (A ^ k).2 e' (nullVec u)
    rw [lorentz_pow_apply_of_eigen A hAe' k, hAkv, minkB_smul_left, minkB_smul_right] at this
    linear_combination this
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨ha, hb⟩ := hcon
  have ea : l ^ k * c = 1 := by
    have : (l ^ k * c - 1) * minkB e (nullVec u) = 0 := by linear_combination h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right ha)
  have eb : l⁻¹ ^ k * c = 1 := by
    have : (l⁻¹ ^ k * c - 1) * minkB e' (nullVec u) = 0 := by linear_combination h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hb)
  have hlk : l ^ k * l⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hl.ne', one_pow]
  have hc2 : c ^ 2 = 1 := by linear_combination (-(c ^ 2)) * hlk + (l⁻¹ ^ k * c) * ea + eb
  have hc1 : c = 1 := (pow_eq_one_iff_of_nonneg hc0.le two_ne_zero).1 hc2
  rw [hc1, mul_one] at ea
  exact hl1 ((pow_eq_one_iff_of_nonneg hl.le hk.ne').1 ea)

/-- **[10.M], l.3237–3240: the finite-index reduction to `L(Γ')` fixing `Δ₀`, with `Δ₁` the second
fixed direction of `γ₀`.** If a finite-index `H ≤ L(Γ)` fixes `u ∈ 𝒮` (`¬IsNonelementary Γ`,
unfolded) and `γ₀ ∈ Γ` is loxodromic, then `Γ' = Γ ⊓ L⁻¹(H)` has finite index, contains `γ₀ᵏ` for
some `k > 0`, and `L(Γ')` fixes `u₀ = u`, which is one of the two distinct fixed points `u₀`, `u₁`
of `L(γ₀)` on `𝒮`. Consumer: `loxo_elementary_misner` (`Flat/Loxodromic.lean`). -/
theorem exists_finiteIndex_fix_loxodromic {Γ : Subgroup (isom d)} {γ₀ : isom d} (hγ₀ : γ₀ ∈ Γ)
    (hlox : IsLoxodromic (linOf γ₀))
    (helem : ∃ H : Subgroup (lorentz d), H ≤ linearImage Γ ∧ H.relIndex (linearImage Γ) ≠ 0 ∧
      ∃ u : PenroseSphere d, ∀ A ∈ H, lorentzSphere A u = u) :
    ∃ Γ' : Subgroup (isom d), Γ' ≤ Γ ∧ Γ'.relIndex Γ ≠ 0 ∧
      ∃ k : ℕ, 0 < k ∧ γ₀ ^ k ∈ Γ' ∧
      ∃ u₀ u₁ : PenroseSphere d, u₀ ≠ u₁ ∧ lorentzSphere (linearPart γ₀) u₀ = u₀ ∧
        lorentzSphere (linearPart γ₀) u₁ = u₁ ∧
        ∀ A ∈ linearImage Γ', lorentzSphere A u₀ = u₀ := by
  obtain ⟨H, -, hHi, u, hu⟩ := helem
  obtain ⟨-, e, e', l, -, -, -, he0, he0', hq, hq', hee', hl, hl1, hAe, hAe', -⟩ := hlox.frame
  have hAlin : linOf γ₀ = ((linearPart γ₀ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) :=
    linOf_eq_linearPart γ₀
  rw [hAlin] at hAe hAe'
  set Γ' : Subgroup (isom d) := Γ ⊓ H.comap linearPart with hΓ'
  have hi : Γ'.relIndex Γ ≠ 0 := by
    rw [hΓ', Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]; exact hHi
  obtain ⟨k, hk, -, hkmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hi hγ₀
  have hk' : γ₀ ^ k ∈ Γ' := hkmem.1
  have hAkH : linearPart γ₀ ^ k ∈ H := by
    have h : linearPart (γ₀ ^ k) ∈ H := hk'.2
    rwa [map_pow] at h
  have hfixk := hu _ hAkH
  have hall : ∀ A ∈ linearImage Γ', lorentzSphere A u = u := by
    rintro A hA
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hA
    exact hu _ hγ.2
  refine ⟨Γ', inf_le_left, hi, k, hk, hk', ?_⟩
  rcases minkB_eq_zero_of_fixed_pow_loxodromic hl hl1 hAe hAe' hk hfixk with h0 | h0
  · obtain ⟨u₁, hne, hf₀, hf₁⟩ :=
      exists_fixed_pair_of_null_orth he0 he0' hq hq' hee' hAe hAe' h0
    exact ⟨u, u₁, hne, hf₀, hf₁, hall⟩
  · obtain ⟨u₁, hne, hf₀, hf₁⟩ :=
      exists_fixed_pair_of_null_orth he0' he0 hq' hq (by rwa [minkB_comm]) hAe' hAe h0
    exact ⟨u, u₁, hne, hf₀, hf₁, hall⟩

end Lox

end Causal.Flat
