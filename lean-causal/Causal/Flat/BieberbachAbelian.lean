import Causal.Flat.Bieberbach

/-!
# `Causal.Flat.BieberbachAbelian` — commuting linear parts give an abelian subgroup of finite index

T. Barbot, *Globally hyperbolic flat space-times* (`papers/barbot`, arXiv math/0402257), §5.1,
the prose item **[5.B]** of `docs/BARBOT.md` (l.1720–1725). Package WP-Bieb-2 (DEC-110). **No
ledger label is certified here**: this is step (1b) of the proof of Bieberbach I through virtual
abelianity.

> As an application of these theorems, it is easy for example to recover the following version
> of Bieberbach's Theorem: *If Γ is discrete group of isometries of the euclidean space of
> dimension n, it contains a finite index free abelian subgroup of finite rank.* (l.1720–1725)

The argument. Let `Γ₁` be discrete with pairwise commuting linear parts, `Λ` its translation
vectors (`translationVectors`, a discrete subgroup of `E`, finitely generated).
* `Γ₁` acts on `Λ` through its linear parts (`linearIsometryEquiv_mem_translationVectors`:
  `g ∘ (· + v) ∘ g⁻¹ = (· + L(g) v)`); each orbit lies in `Λ ∩ sphere(0, ‖v‖)`, finite; so the
  subgroup `fixTranslationsSubgroup Γ₁` of the elements whose linear part fixes `Λ` pointwise has
  finite index (`finiteIndex_fixTranslationsSubgroup`: for a finite ℤ-generating set `b` of `Λ`,
  `γ ↦ (L(γ) bᵢ)ᵢ` is constant exactly on the cosets of that subgroup and takes values in the
  finite set `∏ᵢ Λ ∩ closedBall(0, ‖bᵢ‖)`).
* For `g, h` with commuting linear parts, `[g, h]` is the translation by
  `c = g (h 0) − h (g 0) = (L(g) − 1) (h 0) − (L(h) − 1) (g 0)` (`commutator_eq_constVAdd`), so
  `c ∈ Λ`; if `L(g)`, `L(h)` fix `c`, then `c ⊥ c` (`⟪L(g) b − b, c⟫ = ⟪L(g) b, L(g) c⟫ − ⟪b, c⟫ =
  0`), so `c = 0` (`eq_zero_of_linearPart_fix`).
* Hence `fixTranslationsSubgroup Γ₁` is abelian (`exists_finiteIndex_commute_of_commute_linearPart`).

## Hypothesis checklist
| paper hypothesis | here |
|---|---|
| Γ discrete (l.1723) | ✓ carried, as `IsDiscreteEucl`; spent only on the finiteness of the orbits in `Λ` |
| `E = ℝⁿ` | ⚠ weakened: any finite-dimensional real inner product space |

## SCOPE (disclosed)
* Step (1b) only (see `Flat/BieberbachZassenhaus` for (1a), `Flat/BieberbachProof` for the
  assembly).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-110.
-/

namespace Causal.Flat

open Set Function Module AffineIsometryEquiv

section Abelian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Conjugation transports translation vectors by the linear part**: `g ∈ Γ`, `v` a translation
vector of `Γ` ⇒ `L(g) v` is one. -/
theorem linearIsometryEquiv_mem_translationVectors {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)}
    {g : E ≃ᵃⁱ[ℝ] E} (hg : g ∈ Γ) {v : E} (hv : v ∈ translationVectors Γ) :
    g.linearIsometryEquiv v ∈ translationVectors Γ := by
  have hconj : g * constVAdd ℝ E v * g⁻¹ = constVAdd ℝ E (g.linearIsometryEquiv v) := by
    ext x
    rw [coe_mul, coe_mul, coe_inv, Function.comp_apply, Function.comp_apply, coe_constVAdd,
      coe_constVAdd, AffineIsometryEquiv.map_vadd, apply_symm_apply]
  show constVAdd ℝ E (g.linearIsometryEquiv v) ∈ Γ
  rw [← hconj]
  exact Γ.mul_mem (Γ.mul_mem hg hv) (Γ.inv_mem hg)

/-- The elements of `Γ` whose linear part fixes every translation vector of `Γ`. -/
def fixTranslationsSubgroup (Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)) : Subgroup (E ≃ᵃⁱ[ℝ] E) where
  carrier := {γ | γ ∈ Γ ∧ ∀ v ∈ translationVectors Γ, γ.linearIsometryEquiv v = v}
  one_mem' := ⟨Γ.one_mem, fun _ _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Γ.mul_mem ha hb, fun v hv => ?_⟩
    show a.linearIsometryEquiv (b.linearIsometryEquiv v) = v
    rw [hb' v hv, ha' v hv]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Γ.inv_mem ha, fun v hv => ?_⟩
    show a.linearIsometryEquiv.symm v = v
    conv_lhs => rw [← ha' v hv]
    exact a.linearIsometryEquiv.symm_apply_apply v

theorem fixTranslationsSubgroup_le (Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)) : fixTranslationsSubgroup Γ ≤ Γ :=
  fun _ h => h.1

/-- **`fixTranslationsSubgroup Γ` has finite index in a discrete `Γ`.** -/
theorem finiteIndex_fixTranslationsSubgroup [FiniteDimensional ℝ E]
    {Γ : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ) :
    ((fixTranslationsSubgroup Γ).subgroupOf Γ).FiniteIndex := by
  classical
  letI : DiscreteTopology (AddSubgroup.toIntSubmodule (translationVectors Γ)) :=
    discreteTopology_translationVectors hΓ
  obtain ⟨s, hs⟩ : (AddSubgroup.toIntSubmodule (translationVectors Γ)).FG :=
    Module.Finite.iff_fg.mp (discreteSubmodule_finite _)
  have hsΛ : ∀ b ∈ s, b ∈ translationVectors Γ := fun b hb => by
    have : b ∈ Submodule.span ℤ (s : Set E) := Submodule.subset_span hb
    rw [hs] at this
    exact this
  -- fixing the finite generating set `s` is fixing `Λ`
  have hkey : ∀ γ : E ≃ᵃⁱ[ℝ] E, γ ∈ Γ → (∀ b ∈ s, γ.linearIsometryEquiv b = b) →
      γ ∈ fixTranslationsSubgroup Γ := by
    intro γ hγ hb
    refine ⟨hγ, fun v hv => ?_⟩
    have hv' : v ∈ Submodule.span ℤ (s : Set E) := by rw [hs]; exact hv
    clear hv
    induction hv' using Submodule.span_induction with
    | mem x hx => exact hb x hx
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul a x _ hx => rw [map_zsmul, hx]
  set H := (fixTranslationsSubgroup Γ).subgroupOf Γ with hH
  let F : Γ → (s → E) := fun γ b => (γ : E ≃ᵃⁱ[ℝ] E).linearIsometryEquiv b
  have hF : ∀ γ γ' : Γ, γ⁻¹ * γ' ∈ H ↔ F γ = F γ' := by
    intro γ γ'
    rw [hH, Subgroup.mem_subgroupOf]
    constructor
    · intro hm
      funext b
      have hb := hm.2 b (hsΛ b b.2)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hb
      show (γ : E ≃ᵃⁱ[ℝ] E).linearIsometryEquiv b = (γ' : E ≃ᵃⁱ[ℝ] E).linearIsometryEquiv b
      conv_lhs => rw [← hb]
      show (γ : E ≃ᵃⁱ[ℝ] E).linearIsometryEquiv
          ((γ : E ≃ᵃⁱ[ℝ] E).linearIsometryEquiv.symm
            ((γ' : E ≃ᵃⁱ[ℝ] E).linearIsometryEquiv b)) = _
      rw [LinearIsometryEquiv.apply_symm_apply]
    · intro hFe
      refine hkey _ (γ⁻¹ * γ').2 fun b hb => ?_
      have := congrFun hFe ⟨b, hb⟩
      simp only [F] at this
      show (γ : E ≃ᵃⁱ[ℝ] E).linearIsometryEquiv.symm
          ((γ' : E ≃ᵃⁱ[ℝ] E).linearIsometryEquiv b) = b
      rw [← this, LinearIsometryEquiv.symm_apply_apply]
  let G : Γ ⧸ H → (s → E) :=
    Quotient.lift F fun a b hab => (hF a b).1 (QuotientGroup.leftRel_apply.mp hab)
  have hGinj : Function.Injective G := by
    intro x y hxy
    induction x using Quotient.inductionOn with | h a => ?_
    induction y using Quotient.inductionOn with | h b => ?_
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hF a b).2 hxy))
  haveI hdΛ : DiscreteTopology (translationVectors Γ) := discreteTopology_translationVectors hΓ
  haveI hdΛ' : DiscreteTopology (translationVectors Γ : Set E) := hdΛ
  have hc : IsClosed (translationVectors Γ : Set E) :=
    AddSubgroup.isClosed_of_discrete (H := translationVectors Γ)
  have hpi : (Set.pi univ fun b : s =>
      Metric.closedBall (0 : E) ‖(b : E)‖ ∩ (translationVectors Γ : Set E)).Finite := by
    refine Set.Finite.pi fun b => ?_
    exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      Metric.isBounded_closedBall hc
  have hrange : (range G).Finite := by
    refine hpi.subset ?_
    rintro _ ⟨x, rfl⟩ b -
    induction x using Quotient.inductionOn with | h a => ?_
    refine ⟨?_, linearIsometryEquiv_mem_translationVectors a.2 (hsΛ b b.2)⟩
    show (a : E ≃ᵃⁱ[ℝ] E).linearIsometryEquiv b ∈ Metric.closedBall (0 : E) ‖(b : E)‖
    simp
  haveI : Finite (range G) := hrange.to_subtype
  haveI : Finite (Γ ⧸ H) := Finite.of_injective_finite_range hGinj
  exact Subgroup.finiteIndex_of_finite_quotient

/-- **The commutator of two isometries with commuting linear parts is a translation**, by
`g (h 0) − h (g 0)`. -/
theorem commutator_eq_constVAdd {g h : E ≃ᵃⁱ[ℝ] E}
    (hc : Commute g.linearIsometryEquiv h.linearIsometryEquiv) :
    g * h * g⁻¹ * h⁻¹ = constVAdd ℝ E (g (h 0) - h (g 0)) := by
  set c := g * h * g⁻¹ * h⁻¹ with hc_def
  have hL : c ∈ euclTranslations := by
    rw [euclTranslations, MonoidHom.mem_ker, hc_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      euclLinearPart_apply, euclLinearPart_apply, hc.eq]
    group
  have hc0 : c (h (g 0)) = g (h 0) := by
    simp only [hc_def, coe_mul, coe_inv, Function.comp_apply, symm_apply_apply]
  have h1 := apply_eq_add_of_mem_euclTranslations hL (h (g 0))
  rw [hc0] at h1
  have h2 : c 0 = g (h 0) - h (g 0) := by rw [h1]; abel
  ext x
  rw [apply_eq_add_of_mem_euclTranslations hL x, h2, coe_constVAdd]
  exact add_comm _ _

/-- **A translation vector of a commutator fixed by both linear parts vanishes**: with
`c = g (h 0) − h (g 0) = (L(g) − 1)(h 0) − (L(h) − 1)(g 0)`, `L(g) c = c` and `L(h) c = c` force
`⟪c, c⟫ = 0`. -/
theorem eq_zero_of_linearPart_fix {g h : E ≃ᵃⁱ[ℝ] E}
    (hg : g.linearIsometryEquiv (g (h 0) - h (g 0)) = g (h 0) - h (g 0))
    (hh : h.linearIsometryEquiv (g (h 0) - h (g 0)) = g (h 0) - h (g 0)) :
    g (h 0) - h (g 0) = 0 := by
  have hdecomp : ∀ (f : E ≃ᵃⁱ[ℝ] E) (x : E), f x = f.linearIsometryEquiv x + f 0 := by
    intro f x
    have := f.map_vadd 0 x
    simpa using this
  set c := g (h 0) - h (g 0) with hc_def
  have hc : c = (g.linearIsometryEquiv (h 0) - h 0) - (h.linearIsometryEquiv (g 0) - g 0) := by
    rw [hc_def, hdecomp g (h 0), hdecomp h (g 0)]; abel
  have hgi : ∀ b : E, inner ℝ (g.linearIsometryEquiv b - b) c = 0 := by
    intro b
    have hb := LinearIsometryEquiv.inner_map_map g.linearIsometryEquiv b c
    rw [hg] at hb
    rw [inner_sub_left, hb, sub_self]
  have hhi : ∀ b : E, inner ℝ (h.linearIsometryEquiv b - b) c = 0 := by
    intro b
    have hb := LinearIsometryEquiv.inner_map_map h.linearIsometryEquiv b c
    rw [hh] at hb
    rw [inner_sub_left, hb, sub_self]
  have hcc : inner ℝ c c = 0 := by
    conv_lhs => arg 2; rw [hc]
    rw [inner_sub_left, hgi, hhi, sub_self]
  exact inner_self_eq_zero.mp hcc

/-- **Step (1b)**: a discrete `Γ₁` with pairwise commuting linear parts has an **abelian** subgroup
of finite index (`fixTranslationsSubgroup Γ₁`). -/
theorem exists_finiteIndex_commute_of_commute_linearPart [FiniteDimensional ℝ E]
    {Γ₁ : Subgroup (E ≃ᵃⁱ[ℝ] E)} (hΓ : IsDiscreteEucl Γ₁)
    (hcomm : ∀ g ∈ Γ₁, ∀ h ∈ Γ₁, Commute g.linearIsometryEquiv h.linearIsometryEquiv) :
    ∃ Γ₂ : Subgroup (E ≃ᵃⁱ[ℝ] E), Γ₂ ≤ Γ₁ ∧ (Γ₂.subgroupOf Γ₁).FiniteIndex ∧
      ∀ g ∈ Γ₂, ∀ h ∈ Γ₂, Commute g h := by
  refine ⟨fixTranslationsSubgroup Γ₁, fixTranslationsSubgroup_le Γ₁,
    finiteIndex_fixTranslationsSubgroup hΓ, fun g hg h hh => ?_⟩
  have hcomm' := hcomm g hg.1 h hh.1
  have hgh := commutator_eq_constVAdd hcomm'
  have hmem : g (h 0) - h (g 0) ∈ translationVectors Γ₁ := by
    show constVAdd ℝ E (g (h 0) - h (g 0)) ∈ Γ₁
    rw [← hgh]
    exact Γ₁.mul_mem (Γ₁.mul_mem (Γ₁.mul_mem hg.1 hh.1) (Γ₁.inv_mem hg.1)) (Γ₁.inv_mem hh.1)
  have h0 := eq_zero_of_linearPart_fix (hg.2 _ hmem) (hh.2 _ hmem)
  rw [h0, constVAdd_zero] at hgh
  rw [Commute, SemiconjBy, ← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def]
  exact hgh

end Abelian

end Causal.Flat
