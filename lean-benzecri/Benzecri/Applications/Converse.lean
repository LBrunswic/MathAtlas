import Benzecri.Applications.Products

/-!
# `Benzecri.Applications.Converse` — § 3 Déf. 2 and Prop. 4: the partial converse

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 3, journal pp. 245–246; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`, checked against the scan (PDF pp. 18–19).
Package WP-45v (wave 5).

* `bzdef:c1s3d2_automorphisme_compatible` — `benzecri1960_ch1.tex:806` (l.806–821, p. 245). Not
  marked HERE (`p = 2`, factors of the same dimension); the general-`p`, unequal-dimension
  formalization of record, with the GROUP of compatible automorphisms and `G_I` of index `≤ p!`, is
  `ConverseGeneral` (`IsCompatibleAssocPi`, `compatibleSubgroup`, `relIndex_compatibleIdSubgroup_le`). `IsCompatibleAssoc σ f`, `IsCompatible
  f`: `f = μ ∘ F⁻¹(φ)` with `φ(m₁, m₂) = (φ₁ m_{σ(1)}, φ₂ m_{σ(2)})`, `φᵢ : F(B_{σ(i)}) ≅ F(B_i)`
  conical isomorphisms, `μ` in the torus; `σ ∈ Equiv.Perm (Fin 2)` (`perm_fin_two`).
* `bzprop:c1s3p4_reciproque` — `benzecri1960_ch1.tex:823` (l.823–868, pp. 245–246). Not marked
  HERE (`p = 2`, same dimension); general `p`: `ConverseGeneral.prop4_reciproque_pi`. `homogeneous_of_compatible` (first
  assertion: the composite along the cycle of `1`, here `θ₁ ∘ θ₂` for the transposition) and
  `balayable_of_compatible` (second assertion: `G_I` of index `≤ p! = 2`, made concrete as one
  transposition-type element `f₀` enlarging the generating domain by `θ₂⁰⁻¹(K₂)`).
  `IsCompatible.cases`: what a compatible automorphism does on `B₁ × B₂`.

> **Définition 2.** Soient $p$ variétés localement projectives $B_1$, …, $B_p$; un automorphisme
> projectif $f$ de $F^{-1}(F(B_1)\times\ldots\times F(B_p))$ est dit compatible s'il peut
> s'exprimer de la façon suivante : il existe une permutation $\sigma$ des entiers
> $(1, \ldots, p)$, un système $\{\varphi_i\}$ de $p$ isomorphismes coniques affins entre
> $F(B_{\sigma(i)})$ et $F(B_i)$, tels que, si l'on définit un automorphisme $\varphi$ de la
> structure conique affine du produit […] par la formule […] $m'_i=\varphi_i m_{\sigma(i)}$, on ait
> $f\in\{F^{-1}(\varphi)\}\times(\R^{+p}/\R^+)$. L'automorphisme $f$ sera dit associé à la
> permutation $\sigma$.
>
> **Proposition 4.** Soient $p$ variétés localement projectives $B_1$, …, $B_p$; si le groupe des
> automorphismes compatibles opère transitivement sur $F^{-1}(F(B_1)\times\ldots\times F(B_p))$,
> les $B_i$ sont projectivement homogènes. Si $F^{-1}(F(B_1)\times\ldots\times F(B_p))$ est
> balayable par le groupe de ces automorphismes compatibles, les $B_i$ sont projectivement
> balayables.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `p` locally projective manifolds | `p = 2`, `B₁`, `B₂` of the same dimension `a` (SCOPE) |
| « variété »: Hausdorff | ✓ carried (`[T2Space Bᵢ]`) |
| « variété »: nonempty | reading (`[Nonempty Bᵢ]`, ruled by DEC-128 as DEC-114 for an affine space): with one factor empty the product is empty and the hypotheses are vacuous |
| « le groupe des automorphismes compatibles opère transitivement » | `∀ p p', ∃ f compatible, f • p = p'` |
| « balayable par le groupe de ces automorphismes compatibles » | `∃ K compact, ∀ p, ∃ f compatible, ∃ k ∈ K, f • k = p` |
| `φᵢ` « isomorphismes coniques affins » | homeomorphisms `F(B_{σ(i)}) ≃ₜ F(B_i)` which are conical morphisms (their inverses are, `IsGXMorphism.homeomorph_symm`) |

## SCOPE (disclosed)

* **`p = 2`, equal dimensions.** A conical isomorphism `F(B_{σ(i)}) ≅ F(B_i)` forces `dim B_{σ(i)} =
  dim B_i`, so for two factors of different dimensions only `σ = id` is possible; this file treats
  two factors of one dimension `a`, where both permutations occur. Not formalized: general `p`,
  and the unequal-dimension `p = 2` case (where Prop. 4 reduces to its `G_I` part).
* **The group of compatible automorphisms.** Prop. 4 is stated HERE with « the compatible
  automorphisms » as a set: transitivity / sweeping by compatible automorphisms. The set is a group
  (closed under composition and inverse) — proved for every `p` in `ConverseGeneral`
  (`compatibleSubgroup`, `IsCompatibleAssocPi.mul`, `.inv`), where Prop. 4's hypotheses are stated
  for that subgroup with Déf. 15's own predicates, so the two readings coincide. Here the sweeping
  argument is carried out directly (one transposition-type element suffices), which is the content
  of the index bound.
* **The permutation.** `IsCompatibleAssoc σ` is written per case for `p = 2`; the general form
  `m'ᵢ = φᵢ m_{σ(i)}` through `σ` is `ConverseGeneral.IsCompatibleAssocPi`.
* **`F⁻¹(φ)` on the factors.** `coneBaseMap`, `coneBaseAut`, `coneBaseHomeomorph`: the base map of a
  conical morphism `F(B) → F(B')`, read on `B → B'` through `F(B)/ℝ₊* ≅ B`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Function
open scoped Pointwise

namespace Benzecri

universe u

attribute [local instance] t2Space_RnO

/-! ### The base map `F⁻¹(φ) : B → B'` of a conical morphism `φ : F(B) → F(B')` -/

section BaseMap

variable {n : ℕ} {B : Type u} [TopologicalSpace B] [ChartedSpace (S n) B]
  [HasGroupoid B (projGroupoid n)] [T2Space B]
  {B' : Type u} [TopologicalSpace B'] [ChartedSpace (S n) B'] [HasGroupoid B' (projGroupoid n)]
  [T2Space B']

/-- **`F⁻¹(φ)` read on `B`**: the base map of a conical morphism `φ : F(B) → F(B')`, through the
canonical identifications `F(B)/ℝ₊* ≅ B` (`FCone.baseProjHomeomorph`). -/
def coneBaseMap {φ : FCone n B → FCone n B'} (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ) :
    B → B' :=
  FCone.baseProj ∘ ConeBase.map hφ ∘ FCone.baseProjHomeomorph.symm

theorem coneBaseMap_proj {φ : FCone n B → FCone n B'}
    (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ) (x : FCone n B) :
    coneBaseMap hφ (FCone.proj x) = FCone.proj (φ x) := by
  have : FCone.baseProjHomeomorph.symm (FCone.proj x) = ConeBase.mk (n := n) x := by
    rw [Homeomorph.symm_apply_eq, FCone.baseProjHomeomorph_apply, FCone.baseProj_mk]
  simp only [coneBaseMap, Function.comp_apply, this, ConeBase.map_mk, FCone.baseProj_mk]

/-- **`F⁻¹(φ)` is a projective morphism.** -/
theorem isGXMorphism_coneBaseMap {φ : FCone n B → FCone n B'}
    (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ) :
    IsGXMorphism (GSR n) (S n) (coneBaseMap hφ) :=
  FCone.isGXMorphism_baseProj.comp ((ConeBase.isGXMorphism_map hφ).comp
    (IsGXMorphism.homeomorph_symm (e := FCone.baseProjHomeomorph)
      FCone.isGXMorphism_baseProj))

theorem coneBaseMap_comp {B'' : Type u} [TopologicalSpace B''] [ChartedSpace (S n) B'']
    [HasGroupoid B'' (projGroupoid n)] [T2Space B''] {φ : FCone n B → FCone n B'}
    {ψ : FCone n B' → FCone n B''} (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ)
    (hψ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) ψ) :
    coneBaseMap hψ ∘ coneBaseMap hφ = coneBaseMap (hψ.comp hφ) := by
  funext b
  obtain ⟨x, rfl⟩ := FCone.proj_surjective (n := n) b
  simp only [Function.comp_apply, coneBaseMap_proj]

/-- The base map of a conical isomorphism is bijective. -/
theorem coneBaseMap_bijective (φ : FCone n B ≃ₜ FCone n B')
    (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ) : Bijective (coneBaseMap hφ) := by
  have hφ' := IsGXMorphism.homeomorph_symm (e := φ) hφ
  refine bijective_iff_has_inverse.2 ⟨coneBaseMap hφ', fun b => ?_, fun b => ?_⟩
  · obtain ⟨x, rfl⟩ := FCone.proj_surjective (n := n) b
    rw [coneBaseMap_proj, coneBaseMap_proj, Homeomorph.symm_apply_apply]
  · obtain ⟨x, rfl⟩ := FCone.proj_surjective (n := n) b
    rw [coneBaseMap_proj, coneBaseMap_proj, Homeomorph.apply_symm_apply]

/-- **A conical automorphism of `F(B)` induces a projective automorphism of `B`.** -/
def coneBaseAut (φ : FCone n B ≃ₜ FCone n B) (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ) :
    GXAut (GSR n) (S n) B :=
  GXAut.ofBijective (isGXMorphism_coneBaseMap hφ) (coneBaseMap_bijective φ hφ)

@[simp] theorem coneBaseAut_smul (φ : FCone n B ≃ₜ FCone n B)
    (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ) (b : B) :
    coneBaseAut φ hφ • b = coneBaseMap hφ b := rfl


/-- The base map of a conical isomorphism `F(B) ≅ F(B')`, as a homeomorphism `B ≃ₜ B'` (a bijective
projective morphism). -/
def coneBaseHomeomorph (φ : FCone n B ≃ₜ FCone n B')
    (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ) : B ≃ₜ B' :=
  (Equiv.ofBijective _ (coneBaseMap_bijective φ hφ)).toHomeomorphOfContinuousOpen
    (isGXMorphism_coneBaseMap hφ).continuous (isGXMorphism_coneBaseMap hφ).isLocalHomeomorph.isOpenMap

@[simp] theorem coneBaseHomeomorph_apply (φ : FCone n B ≃ₜ FCone n B')
    (hφ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) φ) (b : B) :
    coneBaseHomeomorph φ hφ b = coneBaseMap hφ b := rfl

end BaseMap

/-! ### Déf. 2 — compatible automorphisms (`p = 2`) -/

section Def2

open ProdCone

variable {a : ℕ} {B₁ : Type u} [TopologicalSpace B₁] [ChartedSpace (S a) B₁]
  [HasGroupoid B₁ (projGroupoid a)] [T2Space B₁]
  {B₂ : Type u} [TopologicalSpace B₂] [ChartedSpace (S a) B₂]
  [HasGroupoid B₂ (projGroupoid a)] [T2Space B₂]

variable (σ : Equiv.Perm (Fin 2))

/-- **Déf. 2, for two factors of the same dimension** (`bzdef:c1s3d2_automorphisme_compatible`): a
projective automorphism `f` of `F⁻¹(F(B₁) × F(B₂))` is *compatible, associated with the permutation
`σ`* when there are conical isomorphisms `φᵢ : F(B_{σ(i)}) ≅ F(B_i)` and an element `μ` of the
torus `ℝ₊*²/ℝ₊*` with `f = μ ∘ F⁻¹(φ)`, `φ(m₁, m₂) = (φ₁ m_{σ(1)}, φ₂ m_{σ(2)})` (« $m'_i =
\varphi_i m_{\sigma(i)}$ … $f\in\{F^{-1}(\varphi)\}\times(\R^{+p}/\R^+)$ »). `Fin 2 = {0, 1}` indexes
`B₁, B₂`; `σ = 1` or `σ = swap 0 1`. -/
def IsCompatibleAssoc (f : GXAut (GSR (a + a + 1)) (S (a + a + 1)) (ProdBase a a B₁ B₂)) : Prop :=
  (σ = 1 ∧ ∃ φ₁ : FCone a B₁ ≃ₜ FCone a B₁, ∃ φ₂ : FCone a B₂ ≃ₜ FCone a B₂,
      IsGXMorphism (GUR (a + 1)) (RnO (a + 1)) φ₁ ∧ IsGXMorphism (GUR (a + 1)) (RnO (a + 1)) φ₂ ∧
      ∃ μ : RPos, ∀ x : FCone a B₁ × FCone a B₂, f • (ConeBase.mk x : ProdBase a a B₁ B₂) =
        torusMap a a (FCone a B₁) (FCone a B₂) μ (ConeBase.mk (φ₁ x.1, φ₂ x.2))) ∨
  (σ = Equiv.swap 0 1 ∧ ∃ φ₁ : FCone a B₂ ≃ₜ FCone a B₁, ∃ φ₂ : FCone a B₁ ≃ₜ FCone a B₂,
      IsGXMorphism (GUR (a + 1)) (RnO (a + 1)) φ₁ ∧ IsGXMorphism (GUR (a + 1)) (RnO (a + 1)) φ₂ ∧
      ∃ μ : RPos, ∀ x : FCone a B₁ × FCone a B₂, f • (ConeBase.mk x : ProdBase a a B₁ B₂) =
        torusMap a a (FCone a B₁) (FCone a B₂) μ (ConeBase.mk (φ₁ x.2, φ₂ x.1)))

/-- **Compatible** (Déf. 2): associated with some permutation. -/
def IsCompatible (f : GXAut (GSR (a + a + 1)) (S (a + a + 1)) (ProdBase a a B₁ B₂)) : Prop :=
  ∃ σ : Equiv.Perm (Fin 2), IsCompatibleAssoc σ f

/-- Every permutation of `Fin 2` is `1` or the transposition (Déf. 2's `σ` for `p = 2`). -/
theorem perm_fin_two (σ : Equiv.Perm (Fin 2)) : σ = 1 ∨ σ = Equiv.swap 0 1 := by
  revert σ; decide

/-- **What a compatible automorphism does on `B₁ × B₂`**: associated with the identity it acts as a
pair of projective automorphisms `(ψ₁, ψ₂)`; associated with the transposition, as
`(b₁, b₂) ↦ (θ₁ b₂, θ₂ b₁)` for projective isomorphisms `θ₁ : B₂ ≅ B₁`, `θ₂ : B₁ ≅ B₂` (the base maps
`F⁻¹(φᵢ)`). -/
theorem IsCompatible.cases {f : GXAut (GSR (a + a + 1)) (S (a + a + 1)) (ProdBase a a B₁ B₂)}
    (hf : IsCompatible f) :
    (∃ ψ₁ : GXAut (GSR a) (S a) B₁, ∃ ψ₂ : GXAut (GSR a) (S a) B₂, ∀ p : ProdBase a a B₁ B₂,
      prodBaseProj (f • p) = (ψ₁ • (prodBaseProj p).1, ψ₂ • (prodBaseProj p).2)) ∨
    (∃ θ₁ : B₂ ≃ₜ B₁, ∃ θ₂ : B₁ ≃ₜ B₂, IsGXMorphism (GSR a) (S a) θ₁ ∧
      IsGXMorphism (GSR a) (S a) θ₂ ∧ ∀ p : ProdBase a a B₁ B₂,
      prodBaseProj (f • p) = (θ₁ (prodBaseProj p).2, θ₂ (prodBaseProj p).1)) := by
  obtain ⟨σ, ⟨-, φ₁, φ₂, h₁, h₂, μ, hμ⟩ | ⟨-, φ₁, φ₂, h₁, h₂, μ, hμ⟩⟩ := hf
  · refine Or.inl ⟨coneBaseAut φ₁ h₁, coneBaseAut φ₂ h₂, fun p => ?_⟩
    obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
    rw [hμ, prodBaseProj_torusMap, prodBaseProj_mk, prodBaseProj_mk, coneBaseAut_smul,
      coneBaseAut_smul, coneBaseMap_proj, coneBaseMap_proj]
  · refine Or.inr ⟨coneBaseHomeomorph φ₁ h₁, coneBaseHomeomorph φ₂ h₂,
      isGXMorphism_coneBaseMap h₁, isGXMorphism_coneBaseMap h₂, fun p => ?_⟩
    obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
    rw [hμ, prodBaseProj_torusMap, prodBaseProj_mk, prodBaseProj_mk, coneBaseHomeomorph_apply,
      coneBaseHomeomorph_apply, coneBaseMap_proj, coneBaseMap_proj]

/-- An automorphism of `B₁` from two projective isomorphisms `B₁ ≅ B₂ ≅ B₁`. -/
def autOfIsos {X Y : Type u} [TopologicalSpace X] [ChartedSpace (S a) X] [TopologicalSpace Y]
    [ChartedSpace (S a) Y] (θ : Y ≃ₜ X) (θ' : X ≃ₜ Y) (h : IsGXMorphism (GSR a) (S a) θ)
    (h' : IsGXMorphism (GSR a) (S a) θ') : GXAut (GSR a) (S a) X :=
  GXAut.ofBijective (h.comp h') (θ.bijective.comp θ'.bijective)

@[simp] theorem autOfIsos_smul {X Y : Type u} [TopologicalSpace X] [ChartedSpace (S a) X]
    [TopologicalSpace Y] [ChartedSpace (S a) Y] (θ : Y ≃ₜ X) (θ' : X ≃ₜ Y)
    (h : IsGXMorphism (GSR a) (S a) θ) (h' : IsGXMorphism (GSR a) (S a) θ') (x : X) :
    autOfIsos θ θ' h h' • x = θ (θ' x) := rfl

theorem exists_prodBase_over (b₁ : B₁) (b₂ : B₂) :
    ∃ p : ProdBase a a B₁ B₂, prodBaseProj p = (b₁, b₂) :=
  ⟨ConeBase.mk (FCone.ofPoint b₁, FCone.ofPoint b₂), rfl⟩

/-- **§ 3 Prop. 4, first assertion, for two factors of the same dimension**
(`bzprop:c1s3p4_reciproque`): « si le groupe des automorphismes compatibles opère transitivement
sur $F^{-1}(F(B_1)\times\ldots\times F(B_p))$, les $B_i$ sont projectivement homogènes », for
nonempty `B_i` (the composite along the cycle of `1`, `h = 2` for the transposition). -/
theorem homogeneous_of_compatible [Nonempty B₁] [Nonempty B₂]
    (h : ∀ p p' : ProdBase a a B₁ B₂, ∃ f : GXAut (GSR (a + a + 1)) (S (a + a + 1))
      (ProdBase a a B₁ B₂), IsCompatible f ∧ f • p = p') :
    IsHomogeneous (GSR a) (S a) B₁ ∧ IsHomogeneous (GSR a) (S a) B₂ := by
  obtain ⟨c₁⟩ := ‹Nonempty B₁›
  obtain ⟨c₂⟩ := ‹Nonempty B₂›
  refine ⟨⟨fun b b' => ?_⟩, ⟨fun b b' => ?_⟩⟩
  · obtain ⟨p, hp⟩ := exists_prodBase_over (a := a) b c₂
    obtain ⟨p', hp'⟩ := exists_prodBase_over (a := a) b' c₂
    obtain ⟨f, hf, hfp⟩ := h p p'
    rcases hf.cases with ⟨ψ₁, ψ₂, hψ⟩ | ⟨θ₁, θ₂, h₁, h₂, hθ⟩
    · have := hψ p
      rw [hfp, hp', hp, Prod.mk.injEq] at this
      exact ⟨ψ₁, this.1.symm⟩
    · have := hθ p
      rw [hfp, hp', hp, Prod.mk.injEq] at this
      refine ⟨autOfIsos θ₁ θ₂ h₁ h₂, ?_⟩
      rw [autOfIsos_smul, ← this.2, ← this.1]
  · obtain ⟨p, hp⟩ := exists_prodBase_over (a := a) c₁ b
    obtain ⟨p', hp'⟩ := exists_prodBase_over (a := a) c₁ b'
    obtain ⟨f, hf, hfp⟩ := h p p'
    rcases hf.cases with ⟨ψ₁, ψ₂, hψ⟩ | ⟨θ₁, θ₂, h₁, h₂, hθ⟩
    · have := hψ p
      rw [hfp, hp', hp, Prod.mk.injEq] at this
      exact ⟨ψ₂, this.2.symm⟩
    · have := hθ p
      rw [hfp, hp', hp, Prod.mk.injEq] at this
      refine ⟨autOfIsos θ₂ θ₁ h₂ h₁, ?_⟩
      rw [autOfIsos_smul, ← this.1, ← this.2]

/-- **§ 3 Prop. 4, second assertion, for two factors of the same dimension**: « Si
$F^{-1}(F(B_1)\times\ldots\times F(B_p))$ est balayable par le groupe de ces automorphismes
compatibles, les $B_i$ sont projectivement balayables », for nonempty `B_i`. The proof is the
printed one made concrete: the compatible automorphisms associated with the identity (`G_I`) have
index `≤ 2 = p!`, so one transposition-type element `f₀` (if any) adds its translate
`t₂⁻¹(K₂)` to the generating domain. -/
theorem balayable_of_compatible [Nonempty B₁] [Nonempty B₂]
    (h : ∃ K : Set (ProdBase a a B₁ B₂), IsCompact K ∧
      ∀ p, ∃ f : GXAut (GSR (a + a + 1)) (S (a + a + 1)) (ProdBase a a B₁ B₂),
        IsCompatible f ∧ ∃ k ∈ K, f • k = p) :
    IsBalayable (GSR a) (S a) B₁ ∧ IsBalayable (GSR a) (S a) B₂ := by
  obtain ⟨c₁⟩ := ‹Nonempty B₁›
  obtain ⟨c₂⟩ := ‹Nonempty B₂›
  obtain ⟨K, hK, hKf⟩ := h
  have hpc : Continuous (prodBaseProj : ProdBase a a B₁ B₂ → B₁ × B₂) :=
    ((FCone.continuous_baseProj.comp continuous_fst).prodMk
      (FCone.continuous_baseProj.comp continuous_snd)).comp continuous_basePr
  set K₁ := Prod.fst '' (prodBaseProj '' K)
  set K₂ := Prod.snd '' (prodBaseProj '' K)
  have hK₁ : IsCompact K₁ := (hK.image hpc).image continuous_fst
  have hK₂ : IsCompact K₂ := (hK.image hpc).image continuous_snd
  have mem₁ : ∀ k ∈ K, (prodBaseProj k).1 ∈ K₁ := fun k hk => ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have mem₂ : ∀ k ∈ K, (prodBaseProj k).2 ∈ K₂ := fun k hk => ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  classical
  by_cases hs : ∃ θ₁ : B₂ ≃ₜ B₁, ∃ θ₂ : B₁ ≃ₜ B₂, IsGXMorphism (GSR a) (S a) θ₁ ∧
      IsGXMorphism (GSR a) (S a) θ₂
  · obtain ⟨t₁, t₂, ht₁, ht₂⟩ := hs
    refine ⟨⟨K₁ ∪ t₂.symm '' K₂, hK₁.union (hK₂.image t₂.symm.continuous),
      eq_univ_of_forall fun b => ?_⟩, ⟨K₂ ∪ t₁.symm '' K₁,
      hK₂.union (hK₁.image t₁.symm.continuous), eq_univ_of_forall fun b => ?_⟩⟩
    · obtain ⟨p, hp⟩ := exists_prodBase_over (a := a) b c₂
      obtain ⟨f, hf, k, hk, rfl⟩ := hKf p
      rcases hf.cases with ⟨ψ₁, ψ₂, hψ⟩ | ⟨θ₁, θ₂, h₁, h₂, hθ⟩
      · have := hψ k
        rw [hp, Prod.mk.injEq] at this
        exact mem_iUnion₂.2 ⟨ψ₁, Subgroup.mem_top _, _, Or.inl (mem₁ k hk), this.1.symm⟩
      · have := hθ k
        rw [hp, Prod.mk.injEq] at this
        refine mem_iUnion₂.2 ⟨autOfIsos θ₁ t₂ h₁ ht₂, Subgroup.mem_top _, t₂.symm (prodBaseProj k).2,
          Or.inr ⟨_, mem₂ k hk, rfl⟩, ?_⟩
        show autOfIsos θ₁ t₂ h₁ ht₂ • t₂.symm (prodBaseProj k).2 = b
        rw [autOfIsos_smul, Homeomorph.apply_symm_apply, this.1]
    · obtain ⟨p, hp⟩ := exists_prodBase_over (a := a) c₁ b
      obtain ⟨f, hf, k, hk, rfl⟩ := hKf p
      rcases hf.cases with ⟨ψ₁, ψ₂, hψ⟩ | ⟨θ₁, θ₂, h₁, h₂, hθ⟩
      · have := hψ k
        rw [hp, Prod.mk.injEq] at this
        exact mem_iUnion₂.2 ⟨ψ₂, Subgroup.mem_top _, _, Or.inl (mem₂ k hk), this.2.symm⟩
      · have := hθ k
        rw [hp, Prod.mk.injEq] at this
        refine mem_iUnion₂.2 ⟨autOfIsos θ₂ t₁ h₂ ht₁, Subgroup.mem_top _, t₁.symm (prodBaseProj k).1,
          Or.inr ⟨_, mem₁ k hk, rfl⟩, ?_⟩
        show autOfIsos θ₂ t₁ h₂ ht₁ • t₁.symm (prodBaseProj k).1 = b
        rw [autOfIsos_smul, Homeomorph.apply_symm_apply, this.2]
  · refine ⟨⟨K₁, hK₁, eq_univ_of_forall fun b => ?_⟩, ⟨K₂, hK₂, eq_univ_of_forall fun b => ?_⟩⟩
    · obtain ⟨p, hp⟩ := exists_prodBase_over (a := a) b c₂
      obtain ⟨f, hf, k, hk, rfl⟩ := hKf p
      rcases hf.cases with ⟨ψ₁, ψ₂, hψ⟩ | ⟨θ₁, θ₂, h₁, h₂, -⟩
      · have := hψ k
        rw [hp, Prod.mk.injEq] at this
        exact mem_iUnion₂.2 ⟨ψ₁, Subgroup.mem_top _, _, mem₁ k hk, this.1.symm⟩
      · exact absurd ⟨θ₁, θ₂, h₁, h₂⟩ hs
    · obtain ⟨p, hp⟩ := exists_prodBase_over (a := a) c₁ b
      obtain ⟨f, hf, k, hk, rfl⟩ := hKf p
      rcases hf.cases with ⟨ψ₁, ψ₂, hψ⟩ | ⟨θ₁, θ₂, h₁, h₂, -⟩
      · have := hψ k
        rw [hp, Prod.mk.injEq] at this
        exact mem_iUnion₂.2 ⟨ψ₂, Subgroup.mem_top _, _, mem₂ k hk, this.2.symm⟩
      · exact absurd ⟨θ₁, θ₂, h₁, h₂⟩ hs

end Def2

end Benzecri
