import Causal.Flat.TwistedProduct
import Causal.Flat.Externals

/-!
# A fixed isotropic direction of a finite-index subgroup of `L_U(Γ)` transports to `L(Γ)`

Transport step of Barbot's Prop 10.5 (`bprop:LU_discrete`, `GHFspace.tex` l.3367–3388), served to
`bprop_LU_discrete` (`Flat/Loxodromic.lean`): an isotropic direction of `U = range ι` fixed by a
finite-index subgroup of `L_U(Γ)` is an isotropic direction of `𝐌ⁿ` fixed by a finite-index
subgroup of `L(Γ)`, i.e. it contradicts `IsNonelementary Γ`. **No label is marked**: this is one
sentence of a proof, not a statement of the paper.

* `bprop:LU_discrete`, `GHFspace.tex:3382–3384`, partial (the transport step only; **no
  `sorry`**): `exists_finiteIndex_fix_of_restrictGroup`.

> If it contains a parabolic element $\gamma_{0}$, the unique
> isotropic direction of $\gamma_{0}$ is $L_{U}(\Gamma)$-invariant, and
> thus $L(\Gamma)$-invariant. Contradiction.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ` preserves `U`, restricting to isometries of `U` | ✓ carried (`hres`, `RestrictsIn`) |
| the direction is `L_U(Γ)`-invariant | ⚠ weakened: under a finite-index `H` (`hidx`, `hu`) |
| conclusion "`L(Γ)`-invariant" | ⚠ weakened: finite-index `H' ≤ L(Γ)`, i.e. `¬IsNonelementary Γ` |

## SCOPE (disclosed)

Only the transport `U → 𝐌ⁿ` is proved. The Lie-theoretic input of Prop 10.5 (a central parabolic
or hyperbolic element in the identity component of the closure of `L_U(Γ)`) is not treated here.
`hH` is not used by the proof (the comap of `H` along `Γ → L_U(Γ)` only sees `H ⊓ L_U(Γ)`); it is
kept because the statement is fixed by the caller.

Proof: `γ ↦` its unique restriction is a surjective hom `r : Γ →* ι.restrictGroup Γ`
(`Restricts.unique`); `K = (L ∘ r)⁻¹ H` has finite index in `Γ` (`Subgroup.index_comap`), so
`H' = L(K)` has finite index in `L(Γ)`. For `γ ∈ K`, `L(r γ)` has `(1,u₁)` as an eigenvector, so
`L(γ)` has `e = ι.lin (1,u₁)` as one (`Restricts.lin`); `e` is nonzero and null, a multiple of
`(1,u)` for some `u ∈ 𝒮`, and `lorentzSphere_eq_of_eigen` concludes.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
planner proof plan (`/tmp/loxplan/LU2_RestrictFix.lean`); `rfx_exists_nullVec_eq_smul` reproves
`exists_nullVec_eq_smul` (`Flat/Loxodromic.lean`), which this module may not import.
-/

namespace Causal.Flat.Lox
open Set
variable {d d₁ : ℕ}

/-- A nonzero null vector spans the null direction of a point of `𝒮` (a copy of
`Loxodromic.exists_nullVec_eq_smul`). -/
private theorem rfx_exists_nullVec_eq_smul {e : Minkowski d} (he0 : e ≠ 0) (he : minkQ e = 0) :
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

private theorem rfx_restricts (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) (γ : Γ) :
    ι.Restricts (γ : isom d) (Classical.choose (hres γ γ.2)) :=
  Classical.choose_spec (hres γ γ.2)

/-- The restriction hom `Γ →* ι.restrictGroup Γ`, `γ ↦ g` with `ι ∘ g = γ ∘ ι`. -/
private noncomputable def rfxHom (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) : Γ →* ι.restrictGroup Γ where
  toFun γ := ⟨Classical.choose (hres γ γ.2), γ, γ.2, rfx_restricts ι hres γ⟩
  map_one' := Subtype.ext ((rfx_restricts ι hres 1).unique AffineMinkEmbedding.Restricts.one)
  map_mul' γ γ' := Subtype.ext ((rfx_restricts ι hres (γ * γ')).unique
    ((rfx_restricts ι hres γ).mul (rfx_restricts ι hres γ')))

private theorem rfxHom_restricts (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) (γ : Γ) : ι.Restricts (γ : isom d) (rfxHom ι hres γ : isom d₁) :=
  rfx_restricts ι hres γ

private theorem rfxHom_surjective (ι : AffineMinkEmbedding d₁ d) {Γ : Subgroup (isom d)}
    (hres : ι.RestrictsIn Γ) : Function.Surjective (rfxHom ι hres) := by
  rintro ⟨g, γ, hγ, h⟩
  exact ⟨⟨γ, hγ⟩, Subtype.ext ((rfxHom_restricts ι hres ⟨γ, hγ⟩).unique h)⟩

/-- **Transport of a fixed isotropic direction from `U` to `𝐌ⁿ`** (`bprop:LU_discrete`,
l.3382–3384): a finite-index subgroup of `L_U(Γ)` fixing a point of `𝒮` for `U` yields a
finite-index subgroup of `L(Γ)` fixing a point of `𝒮`, i.e. `¬IsNonelementary Γ`. -/
theorem exists_finiteIndex_fix_of_restrictGroup (ι : AffineMinkEmbedding d₁ d)
    {Γ : Subgroup (isom d)} (hres : ι.RestrictsIn Γ) {H : Subgroup (lorentz d₁)}
    (hH : H ≤ linearImage (ι.restrictGroup Γ))
    (hidx : H.relIndex (linearImage (ι.restrictGroup Γ)) ≠ 0) {u₁ : PenroseSphere d₁}
    (hu : ∀ A ∈ H, lorentzSphere A u₁ = u₁) :
    ∃ H' : Subgroup (lorentz d), H' ≤ linearImage Γ ∧ H'.relIndex (linearImage Γ) ≠ 0 ∧
      ∃ u : PenroseSphere d, ∀ A ∈ H', lorentzSphere A u = u := by
  have _hH : H ≤ linearImage (ι.restrictGroup Γ) := hH  -- unused (SCOPE)
  set r := rfxHom ι hres
  set φ : Γ →* lorentz d₁ := linearPart.comp ((ι.restrictGroup Γ).subtype.comp r) with hφ
  set ψ : Γ →* lorentz d := linearPart.comp Γ.subtype with hψ
  have hφr : φ.range = linearImage (ι.restrictGroup Γ) := by
    rw [hφ, MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ (rfxHom_surjective ι hres), ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hψr : ψ.range = linearImage Γ := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  set K := H.comap φ with hK
  have hKi : K.index ≠ 0 := by rw [hK, Subgroup.index_comap, hφr]; exact hidx
  refine ⟨K.map ψ, ?_, ?_, ?_⟩
  · rw [← hψr]; exact Subgroup.map_le_range ψ K
  · rw [← hψr, ← Subgroup.index_comap]
    exact fun h0 => hKi (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le
      (Subgroup.le_comap_map ψ K)))
  · -- the null vector `e = ι.lin (1, u₁)` is an eigenvector of every `L(γ)`, `γ ∈ K`
    set e := ι.lin (nullVec u₁) with he
    have he0 : e ≠ 0 := fun h0 => nullVec_ne_zero u₁
      (ι.lin_injective (h0.trans (map_zero _).symm))
    have heq : minkQ e = 0 := by rw [he, ι.minkQ_lin, minkQ_nullVec]
    obtain ⟨u, c', hc', hue⟩ := rfx_exists_nullVec_eq_smul he0 heq
    refine ⟨u, ?_⟩
    rintro _ ⟨γ, hγ, rfl⟩
    have hfix := hu _ hγ
    have hA : ((φ γ : lorentz d₁) : Minkowski d₁ ≃ₗ[ℝ] Minkowski d₁) (nullVec u₁) =
        lorentzScale (φ γ) u₁ • nullVec u₁ := by
      have := nullVec_lorentzSphere (φ γ) u₁
      rw [hfix] at this
      conv_rhs => rw [this]
      rw [smul_smul, mul_inv_cancel₀ (lorentzScale_pos _ u₁).ne', one_smul]
    refine lorentzSphere_eq_of_eigen (c := lorentzScale (φ γ) u₁) ?_
    have hl := (rfxHom_restricts ι hres γ).lin (nullVec u₁)
    have hA' : ((r γ : isom d₁) : Minkowski d₁ ≃ᵃ[ℝ] Minkowski d₁).linear (nullVec u₁) =
        lorentzScale (φ γ) u₁ • nullVec u₁ := hA
    rw [hA', map_smul] at hl
    show ((γ : isom d) : Minkowski d ≃ᵃ[ℝ] Minkowski d).linear (nullVec u) = _
    rw [hue, map_smul, ← hl, smul_comm]

end Causal.Flat.Lox
