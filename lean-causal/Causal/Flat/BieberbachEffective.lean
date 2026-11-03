import Causal.Flat.Bieberbach

/-!
# `Causal.Flat.BieberbachEffective` — from an action by translations to Bieberbach's conclusion

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5.1,
the prose item **[5.B]** of `docs/BARBOT.md` (l.1720–1735). Package WP-Bieb-4 (DEC-110). **No
ledger label is certified here**: this is step (2b) of the proof of Bieberbach I through virtual
abelianity — making the action effective and the subspace invariant under all of `Γ`.

> […] `Γ_nd` is a finite index subgroup of `Γ`, and the kernel of the restriction morphism
> `Γ → Isom(U)` is a finite index subgroup of `Γ_nd`. (l.1730–1733)

The argument.
* `bieberbachConclusion_of_actsEffectivelyOn` (no discreteness) — a finite-index `Γ' ≤ Γ`
  acting effectively by translations on a nonempty `U` gives `BieberbachConclusion Γ`: pass to
  the normal core `N` of `Γ'` and to its translation locus `M = translationLocus N x₀ ⊇ U`, which
  `Γ` preserves (the argument of `bieberbachMaxConclusion_of_bieberbachConclusion`, whose
  `Γ`-invariance hypothesis is only spent on `γ x₀ ∈ U` for `γ ∈ N`, here a consequence of
  `ActsByTranslationsOn`).
* `finite_setOf_apply_eq` — a discrete `Γ` has finitely many elements fixing a point.
* `exists_finiteIndex_actsEffectivelyOn` — a commutative `A ≤ Γ` (discrete) acting by
  translations on `U ∋ x₀`: `φ(γ) = γ x₀ − x₀` is a morphism `Additive A →+ E` with finite kernel
  `K` (the elements fixing `x₀`) and discrete image `Λ`, a free `ℤ`-module; a section
  `s : Λ →+ Additive A` (`Module.projective_lifting_property`) has image `A'` of index `≤ |K|`
  meeting `K` trivially — so `A'` acts effectively.
* `bieberbachConclusion_of_commute_of_actsByTranslationsOn` — step (2b) assembled.

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| Γ discrete (l.1723) | ✓ carried (`IsDiscreteEucl`); spent on the finiteness of `K` and the discreteness of `Λ` |
| `E = ℝⁿ` | ⚠ weakened: any finite-dimensional real inner product space |

## SCOPE (disclosed)
* Step (2b) only; the assembly is `Flat/BieberbachProof`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-110.
-/

namespace Causal.Flat

open Set Function Module

section Effective

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `ActsByTranslationsOn` passes to subgroups. -/
theorem ActsByTranslationsOn.mono {Γ' Γ'' : Subgroup (E ≃ᵃⁱ[ℝ] E)} {U : AffineSubspace ℝ E}
    (h : ActsByTranslationsOn Γ' U) (hle : Γ'' ≤ Γ') : ActsByTranslationsOn Γ'' U :=
  fun γ hγ => h γ (hle hγ)

/-- **Invariance for free** (no discreteness): a finite-index `Γ' ≤ Γ` acting effectively by
translations on a nonempty `U` yields `BieberbachConclusion Γ` (normal core, translation locus). -/
theorem bieberbachConclusion_of_actsEffectivelyOn {Γ Γ' : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hle : Γ' ≤ Γ)
    (hfi : (Γ'.subgroupOf Γ).FiniteIndex) {U : AffineSubspace ℝ E} (hU : (U : Set E).Nonempty)
    (htr : ActsByTranslationsOn Γ' U) (heff : ActsEffectivelyOn Γ' U) :
    BieberbachConclusion Γ := by
  obtain ⟨x₀, hx₀⟩ := hU
  set H := Γ'.subgroupOf Γ with hH
  set N : Subgroup (E ≃ᵃⁱ[ℝ] E) := H.normalCore.map Γ.subtype with hNdef
  have hNΓ' : N ≤ Γ' := by
    rintro _ ⟨g, hg, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (H.normalCore_le hg)
  have hNΓ : N ≤ Γ := hNΓ'.trans hle
  have hNsub : N.subgroupOf Γ = H.normalCore :=
    Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective _
  have hnorm : (N.subgroupOf Γ).Normal := by rw [hNsub]; infer_instance
  have hfiN : (N.subgroupOf Γ).FiniteIndex := by rw [hNsub]; infer_instance
  set M := translationLocus N x₀ with hMdef
  have hγx₀ : ∀ γ ∈ N, γ x₀ ∈ U := by
    intro γ hγ
    obtain ⟨v, hv, hvx⟩ := htr γ (hNΓ' hγ)
    rw [hvx x₀ hx₀]
    exact AffineSubspace.vadd_mem_of_mem_direction hv hx₀
  have hUM : ∀ x ∈ U, x ∈ M := by
    intro x hx γ hγ
    obtain ⟨v, -, hv⟩ := htr γ (hNΓ' hγ)
    rw [hv x hx, hv x₀ hx₀, vadd_vsub]
  have hx₀M : x₀ ∈ M := hUM x₀ hx₀
  have hτM : ∀ γ ∈ N, γ x₀ -ᵥ x₀ ∈ M.direction := fun γ hγ =>
    AffineSubspace.vsub_mem_direction (hUM _ (hγx₀ γ hγ)) hx₀M
  have htrM : ActsByTranslationsOn N M := fun γ hγ => ⟨_, hτM γ hγ, fun x hx => hx γ hγ⟩
  have hmap : ∀ g ∈ Γ, ∀ x ∈ M, g x ∈ M := by
    intro g hg x hx γ hγ
    have hδ : g⁻¹ * γ * g⁻¹⁻¹ ∈ N := conj_mem_of_normal hNΓ hnorm (Γ.inv_mem hg) hγ
    rw [inv_inv] at hδ
    have hpow : ∀ k : ℕ, (γ ^ k) (g x) =
        (k • g.linearIsometryEquiv ((g⁻¹ * γ * g) x₀ -ᵥ x₀)) +ᵥ g x := by
      intro k
      have e : γ ^ k * g = g * (g⁻¹ * γ * g) ^ k := by
        have := conj_pow (a := g⁻¹) (b := γ) (i := k)
        rw [inv_inv] at this
        rw [this]
        group
      have : (γ ^ k) (g x) = (g * (g⁻¹ * γ * g) ^ k) x := by
        rw [← e, AffineIsometryEquiv.coe_mul, Function.comp_apply]
      rw [this, AffineIsometryEquiv.coe_mul, Function.comp_apply,
        pow_apply_of_translation (hτM _ hδ) (fun z hz => hz _ hδ) k x hx,
        AffineIsometryEquiv.map_vadd, map_nsmul]
    have hpow₀ := fun k => pow_apply_of_translation (hτM γ hγ) (fun z hz => hz γ hγ) k x₀ hx₀M
    have := eq_of_pow_apply hpow hpow₀
    have h1 := hpow 1
    simp only [pow_one, one_smul] at h1
    rw [h1, this]
  refine ⟨M, ⟨x₀, hx₀M⟩, ?_, N, hNΓ, hfiN, htrM, ?_⟩
  · intro g hg x
    refine ⟨fun hgx => ?_, hmap g hg x⟩
    have := hmap g⁻¹ (Γ.inv_mem hg) _ hgx
    rwa [AffineIsometryEquiv.coe_inv, AffineIsometryEquiv.symm_apply_apply] at this
  · intro γ hγ hfix
    exact heff γ (hNΓ' hγ) fun x hx => hfix x (hUM x hx)

/-- **Finitely many elements of a discrete `Γ` fix a point.** -/
theorem finite_setOf_apply_eq {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ) (x₀ : E) :
    {γ | γ ∈ Γ ∧ γ x₀ = x₀}.Finite :=
  (hΓ x₀ 0).subset fun γ ⟨hγ, hx⟩ => ⟨hγ, by rw [hx, dist_self]⟩

/-- **Effectiveness on a subgroup of finite index**: a commutative `A ≤ Γ`, `Γ` discrete, acting by
translations on a nonempty `U`, has a finite-index subgroup acting effectively on `U`. -/
theorem exists_finiteIndex_actsEffectivelyOn [FiniteDimensional ℝ E]
    {Γ A : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ) (hle : A ≤ Γ)
    (hA : ∀ g ∈ A, ∀ h ∈ A, Commute g h) {U : AffineSubspace ℝ E} (hU : (U : Set E).Nonempty)
    (htr : ActsByTranslationsOn A U) :
    ∃ A' : Subgroup (E ≃ᵃⁱ[ℝ] E), A' ≤ A ∧ (A'.subgroupOf A).FiniteIndex ∧
      ActsEffectivelyOn A' U := by
  classical
  obtain ⟨x₀, hx₀⟩ := hU
  letI : CommGroup A :=
    { (inferInstance : Group A) with
      mul_comm := fun a b => Subtype.ext (hA _ a.2 _ b.2).eq }
  -- every `γ ∈ A` moves all of `U` by `γ x₀ -ᵥ x₀`
  have hmove : ∀ γ ∈ A, ∀ x ∈ U, γ x = (γ x₀ -ᵥ x₀) +ᵥ x := by
    intro γ hγ x hx
    obtain ⟨v, -, hv⟩ := htr γ hγ
    rw [hv x hx, hv x₀ hx₀, vadd_vsub]
  -- the displacement of `x₀`, a morphism `Additive A →+ E`
  let φ : Additive A →+ E :=
    { toFun := fun a => ((Additive.toMul a : A) : E ≃ᵃⁱ[ℝ] E) x₀ -ᵥ x₀
      map_zero' := by simp
      map_add' := by
        intro a b
        have hb : ((Additive.toMul b : A) : E ≃ᵃⁱ[ℝ] E) x₀ ∈ U := by
          obtain ⟨v, hv, hvx⟩ := htr _ (Additive.toMul b).2
          rw [hvx x₀ hx₀]
          exact AffineSubspace.vadd_mem_of_mem_direction hv hx₀
        simp only [toMul_add, Subgroup.coe_mul, AffineIsometryEquiv.coe_mul, Function.comp_apply]
        rw [hmove _ (Additive.toMul a).2 _ hb]
        simp only [vsub_eq_sub, vadd_eq_add]
        abel }
  have hφ : ∀ a : Additive A, φ a = ((Additive.toMul a : A) : E ≃ᵃⁱ[ℝ] E) x₀ -ᵥ x₀ :=
    fun _ => rfl
  -- its image is a discrete subgroup, hence a free `ℤ`-module
  let L : Submodule ℤ E := AddSubgroup.toIntSubmodule φ.range
  haveI hLd : DiscreteTopology L := by
    refine discreteTopology_of_finite_ball φ.range ((((hΓ x₀ 1).image
      fun γ : E ≃ᵃⁱ[ℝ] E => γ x₀ -ᵥ x₀)).subset ?_)
    rintro v ⟨⟨a, rfl⟩, hv⟩
    refine ⟨((Additive.toMul a : A) : E ≃ᵃⁱ[ℝ] E), ⟨hle (Additive.toMul a).2, ?_⟩, rfl⟩
    rw [dist_eq_norm, ← vsub_eq_sub]
    exact hv
  haveI : Module.Free ℤ L := discreteSubmodule_free L
  -- the corestriction `ψ : Additive A → L` is onto; lift `id` along it
  let ψ : Additive A →ₗ[ℤ] L :=
    LinearMap.codRestrict L φ.toIntLinearMap fun a => AddMonoidHom.mem_range.mpr ⟨a, rfl⟩
  have hψ : ∀ a, (ψ a : E) = φ a := fun _ => rfl
  have hψs : Function.Surjective ψ := by
    rintro ⟨v, a, rfl⟩
    exact ⟨a, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property ψ LinearMap.id hψs
  have hψs' : ∀ v, ψ (s v) = v := fun v => LinearMap.congr_fun hs v
  -- `A'` is the image of the section
  let A' : Subgroup (E ≃ᵃⁱ[ℝ] E) :=
    { carrier := {γ | ∃ v : L, ((Additive.toMul (s v) : A) : E ≃ᵃⁱ[ℝ] E) = γ}
      one_mem' := ⟨0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
        exact ⟨v + w, by simp⟩
      inv_mem' := by
        rintro _ ⟨v, rfl⟩
        exact ⟨-v, by simp⟩ }
  have hA'A : A' ≤ A := by
    rintro _ ⟨v, rfl⟩
    exact (Additive.toMul (s v)).2
  refine ⟨A', hA'A, ?_, ?_⟩
  · -- finite index: every coset meets the finite kernel of `φ`
    set K : Set A := {a | ((a : A) : E ≃ᵃⁱ[ℝ] E) x₀ = x₀} with hKdef
    have hK : K.Finite :=
      ((finite_setOf_apply_eq hΓ x₀).preimage Subtype.val_injective.injOn).subset
        fun a ha => ⟨hle a.2, ha⟩
    haveI := hK.to_subtype
    let f : K → A ⧸ A'.subgroupOf A := fun k => (k : A)
    have hf : Function.Surjective f := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H a =>
        set σ : A := Additive.toMul (s (ψ (Additive.ofMul a))) with hσ
        have hσA' : σ ∈ A'.subgroupOf A :=
          Subgroup.mem_subgroupOf.mpr ⟨ψ (Additive.ofMul a), rfl⟩
        have hφσ : φ (Additive.ofMul σ) = φ (Additive.ofMul a) := by
          rw [hσ, ofMul_toMul, ← hψ, hψs', hψ]
        refine ⟨⟨a * σ⁻¹, ?_⟩, ?_⟩
        · have h0 : φ (Additive.ofMul (a * σ⁻¹)) = 0 := by
            rw [ofMul_mul, ofMul_inv, map_add, map_neg, hφσ, add_neg_cancel]
          rw [hφ, vsub_eq_zero_iff_eq] at h0
          exact h0
        · show ((a * σ⁻¹ : A) : A ⧸ A'.subgroupOf A) = (a : A ⧸ A'.subgroupOf A)
          rw [QuotientGroup.eq]
          simpa using hσA'
    haveI : Finite (A ⧸ A'.subgroupOf A) := Finite.of_surjective f hf
    exact Subgroup.finiteIndex_of_finite_quotient
  · -- effective: the section meets the kernel of `φ` trivially
    rintro _ ⟨v, rfl⟩ hfix
    have h0 : φ (s v) = 0 := by
      rw [hφ, vsub_eq_zero_iff_eq]
      exact hfix x₀ hx₀
    have hv : v = 0 := by
      apply Subtype.ext
      rw [← hψs' v, hψ]
      exact h0
    subst hv
    simp

/-- **Step (2b)**: a commutative finite-index `A` of a discrete `Γ` acting by translations on a
nonempty `U` gives `BieberbachConclusion Γ`. -/
theorem bieberbachConclusion_of_commute_of_actsByTranslationsOn [FiniteDimensional ℝ E]
    {Γ A : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ) (hle : A ≤ Γ)
    (hfi : (A.subgroupOf Γ).FiniteIndex) (hA : ∀ g ∈ A, ∀ h ∈ A, Commute g h)
    {U : AffineSubspace ℝ E} (hU : (U : Set E).Nonempty) (htr : ActsByTranslationsOn A U) :
    BieberbachConclusion Γ := by
  obtain ⟨A', hA'A, hfi', heff⟩ := exists_finiteIndex_actsEffectivelyOn hΓ hle hA hU htr
  exact bieberbachConclusion_of_actsEffectivelyOn (hA'A.trans hle)
    ⟨Subgroup.relIndex_ne_zero_trans hfi'.index_ne_zero hfi.index_ne_zero⟩ hU
    (htr.mono hA'A) heff

end Effective

end Causal.Flat
