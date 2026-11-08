import BenzecriScaffold.Applications.Circle

/-!
# `BenzecriScaffold.Applications.Products` — § 3 Déf. 1, Props. 2–3 and the corollary: products

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 3, journal pp. 243–245; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`, checked against the scan (PDF pp. 16–18).
Package WP-45u (wave 5).

* **`bzcor:c1s3p3c_produit_projectif`** — `benzecri1960_ch1.tex:797` (l.797–801, p. 245).
  **MARKED.** `Benzecri.produit_projectif`: for `p = q + 1` Hausdorff σ-compact (« variété »)
  spaces `B i` carrying locally projective structures of dimensions `n i`,
  `(∀ i, B i) × (Fin q → S¹)` carries a locally projective structure, of dimension `Σ n i + q`.
  By induction on `q` from the two-factor case `produit_projectif_two` /
  `exists_proj_prod_circle` (the quotient of `F⁻¹(F(B₁) × F(B₂))` by a lattice `λ^ℤ` of the torus).
* `bzdef:c1s3d1_produit_cones` — `benzecri1960_ch1.tex:727` (l.727–739, p. 244). Not marked
  (`partial`: two factors). The product of two affine conical manifolds `V × W` of dimensions
  `a + 1`, `b + 1` is an affine conical manifold of dimension `a + b + 2`, charted on
  `(ℝ^{a+1} − {O}) × (ℝ^{b+1} − {O}) ⊂ ℝ^{a+b+2} − {O}` (`blockPt`, an open embedding;
  `prodConeChartedSpace`, scoped instances `ProdCone.instChartedSpace`, `instHasGroupoid`,
  `instHasConeCharts`), with `GU(a+1) × GU(b+1) ↪ GU(a+b+2)` block-diagonally (`blockGU`,
  `det_blockGL`); the `ℝ₊*²`-action `blockHom`; its diagonal is Déf. 3's (`posSMul_prod`).
* `bzprop:c1s3p2_fibre_produit` — `benzecri1960_ch1.tex:741` (l.741–759, p. 244). Not marked
  (`partial`: two factors; a FINDING against the proof). `prop2_fibre_produit`: `ℝ₊*²/ℝ₊*`
  (`torusMap`, the class of `(1, μ)`) acts on the base `F⁻¹(V × W)` by projective automorphisms,
  freely, with orbits the fibres of `basePr` onto the product of the bases; for `F(B₁) × F(B₂)`
  with paracompact `Bᵢ` the bundle is trivial (`exists_prodBase_homeomorph`).
  **Finding**: the printed lift « le sous-groupe … dont le produit est égal à 1 » consists of
  conical automorphisms only when the factors have equal dimension
  (`not_isGXMorphism_blockHom_of_ne`, `det_eq_one_of_isGXMorphism_blockHom`); the corrected lift is
  `λ₁^{a+1} λ₂^{b+1} = 1` (`torusPair`).
* `bzprop:c1s3p3_produit_homogene` — `benzecri1960_ch1.tex:761` (l.761–795, pp. 244–245). Not
  marked (`partial`: two factors; divisible for paracompact factors). `prop3_produit_homogene`.

> **Définition 1.** Soient $p$ variétés localement projectives $B_1$, …, $B_p$; et soit
> $F(B_1)\times\ldots\times F(B_p)$ le cône affin produit des cônes affins de bases les $B_i$. Nous
> munirons ce produit d'une structure d'espace fibré $\R^{+p}$ principal de base
> $B_1\times\ldots\times B_p$ en faisant opérer $\R^{+p}$ […] suivant la formule
> $(\lambda_1\ldots\lambda_p)\times(m_1\ldots m_p)=(\lambda_1 m_1, \ldots, \lambda_p m_p)$.
>
> **Proposition 2.** Le quotient $\R^{+p}/\R^+$ opère sur $F^{-1}(F(B_1)\times\ldots\times F(B_p))$
> et définit sur cette variété localement projective une structure d'espace fibré principal de base
> $(B_1\times\ldots\times B_p)$. […] On peut encore remarquer que $\R^{+p}/\R^+$ se relève suivant
> le sous-groupe de $\R^{+p}$ formé des systèmes de $p$ nombres réels positifs dont le produit est
> égal à 1. Un élément de ce sous-groupe définit un automorphisme de la structure conique affine du
> produit des $F(B_i)$ […]
>
> **Proposition 3.** Soient $B_1$, …, $B_p$ des variétés localement projectives homogènes (resp.
> balayables, resp. divisibles); la variété localement projective
> $F^{-1}(F(B_1)\times\ldots\times F(B_p))$ est homogène (resp. balayable, resp. divisible).
>
> **Corollaire.** Si $p$ variétés $B_i$ peuvent être munies chacune d'une structure localement
> projective, le produit $B_1\times\ldots\times B_p\times S_1^{(p-1)}$ peut être muni d'une
> structure localement projective.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `B_i` locally projective (any dimensions) | ✓ carried, dimensions `a`, `b` (resp. `n i`) unconstrained |
| « variété »: Hausdorff | ✓ carried (`[T2Space Bᵢ]`) |
| « variété »: second countable | as `[SigmaCompactSpace (B i)]` in the corollary (equivalent for manifolds, and stable under products, which the induction needs); `[ParacompactSpace Bᵢ]` where a section of `F(Bᵢ) → Bᵢ` is used |
| `p` factors | the corollary: every `p ≥ 1`; Déf. 1, Props. 2–3: `p = 2` (SCOPE) |
| `S₁^{(p−1)}` | `Fin q → Circle`, `p = q + 1` |
| `H ⊂ ℝ^{+p}/ℝ^+` discrete, `ℝ^{+p}/ℝ^+ / H ≅ S₁^{(p−1)}` (printed « $\R^{+p}/\R^p$ », `[sic]`, read `/\R^+`) | `p = 2`: `H = λ^ℤ`, any `λ ≠ 1` |

## SCOPE (disclosed)

* **Two factors.** Déf. 1 and Props. 2–3 are formalized for `p = 2`, for factors of arbitrary
  (possibly different) dimensions; the `p`-fold product cone `∏ (ℝ^{nᵢ} − {O}) ⊂ ℝ^{Σnᵢ} − {O}` is
  not built. The corollary is proved for every `p` by iterating the two-factor case, which needs
  only `B₁ × … × B_{q+2} × (S¹)^{q+1} ≅ (B₁ × … × B_{q+1} × (S¹)^q) × B_{q+2} × S¹`
  (`homeomorphInsertNth`) and the transport of a structure along a homeomorphism
  (`exists_hasGroupoid_of_homeomorph`). Props. 2–3 for general `p` would follow the same pattern
  only after identifying `F⁻¹` of an iterated product with `F⁻¹(∏ F(Bᵢ))`, not done.
* **The product cone's structure is scoped** (`open scoped Benzecri.ProdCone`): `V × W` is a
  Mathlib type, so no global instance is declared on it.
* **The torus.** `ℝ₊*²/ℝ₊* ≅ ℝ₊*` through `μ ↦ [(1, μ)]`; its action on the base is the base map of
  the unimodular block homothety `torusPair μ` (Prop. 2's lift, corrected).
* **Prop. 3, divisible.** The group is `F⁻¹(F(G₁) × F(G₂)) × H`, `H = λ^ℤ` (`divProdHom`), as
  printed; proper discontinuity uses the radial coordinate of `exists_prodBase_homeomorph`, hence
  paracompact factors. The printed proof announces the sweepable case and argues the divisible one
  (flagged in the transcription); both are proved, with the homogeneous case.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Function
open scoped Pointwise

namespace Benzecri

universe u v

attribute [local instance] t2Space_RnO

/-! ### Blocks: `ℝ^{a+1} × ℝ^{b+1} ≃ ℝ^{a+b+2}` and `GU(a+1) × GU(b+1) ↪ GU(a+b+2)` -/

section Block

variable (a b : ℕ)

theorem block_dim_eq : a + b + 1 + 1 = (a + 1) + (b + 1) := by omega

/-- The block decomposition `ℝ^{a+1} × ℝ^{b+1} ≃ₗ ℝ^{a+b+2}` (the first `a+1` coordinates, then the
last `b+1`). -/
def blockEquiv : ((Fin (a + 1) → ℝ) × (Fin (b + 1) → ℝ)) ≃ₗ[ℝ] (Fin (a + b + 1 + 1) → ℝ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin (a + 1)) (Fin (b + 1)) ℝ ℝ).symm ≪≫ₗ
    LinearEquiv.funCongrLeft ℝ ℝ ((finCongr (block_dim_eq a b)).trans finSumFinEquiv.symm)

variable {a b}

/-- **The block-diagonal automorphism** `diag(g₁, g₂)` of `ℝ^{a+b+2}`. -/
def blockGL (g₁ : GLR (a + 1)) (g₂ : GLR (b + 1)) : GLR (a + b + 1 + 1) :=
  ((blockEquiv a b).symm.trans (g₁.prodCongr g₂)).trans (blockEquiv a b)

theorem blockGL_apply (g₁ : GLR (a + 1)) (g₂ : GLR (b + 1)) (v : Fin (a + 1) → ℝ)
    (w : Fin (b + 1) → ℝ) : blockGL g₁ g₂ (blockEquiv a b (v, w)) = blockEquiv a b (g₁ v, g₂ w) := by
  simp [blockGL]

/-- **The determinant multiplies** (« $\prod GU(n_i) \hookrightarrow GU(\sum n_i)$ »). -/
theorem det_blockGL (g₁ : GLR (a + 1)) (g₂ : GLR (b + 1)) :
    ((LinearEquiv.det (blockGL g₁ g₂) : ℝˣ) : ℝ) =
      ((LinearEquiv.det g₁ : ℝˣ) : ℝ) * ((LinearEquiv.det g₂ : ℝˣ) : ℝ) := by
  rw [blockGL, LinearEquiv.det_conj, LinearEquiv.coe_det, LinearEquiv.coe_det,
    LinearEquiv.coe_det]
  exact LinearMap.det_prodMap _ _

theorem blockGL_mul (g₁ h₁ : GLR (a + 1)) (g₂ h₂ : GLR (b + 1)) :
    blockGL (g₁ * h₁) (g₂ * h₂) = blockGL g₁ g₂ * blockGL h₁ h₂ := by
  ext x : 1
  simp [blockGL]

theorem blockGL_one : blockGL (1 : GLR (a + 1)) (1 : GLR (b + 1)) = 1 := by
  ext x : 1
  simp [blockGL]

/-- **`GU(a+1) × GU(b+1) ↪ GU(a+b+2)`, block-diagonally.** -/
def blockGU : GUR (a + 1) × GUR (b + 1) →* GUR (a + b + 1 + 1) where
  toFun g := ⟨blockGL g.1 g.2, by
    rw [mem_GU, det_blockGL, abs_mul, mem_GU.1 g.1.2, mem_GU.1 g.2.2, one_mul]⟩
  map_one' := Subtype.ext blockGL_one
  map_mul' g h := Subtype.ext (blockGL_mul _ _ _ _)

@[simp] theorem coe_blockGU (g : GUR (a + 1) × GUR (b + 1)) :
    ((blockGU g : GUR (a + b + 1 + 1)) : GLR (a + b + 1 + 1)) = blockGL g.1 g.2 := rfl

theorem blockEquiv_ne_zero {v : Fin (a + 1) → ℝ} {w : Fin (b + 1) → ℝ} (hv : v ≠ 0) :
    blockEquiv a b (v, w) ≠ 0 := by
  intro h
  have := congrArg Prod.fst ((blockEquiv a b).injective (h.trans (map_zero _).symm))
  exact hv this

/-- **The inclusion `(ℝ^{a+1} − {O}) × (ℝ^{b+1} − {O}) ⊂ ℝ^{a+b+2} − {O}`** (Déf. 1, « le cône
affin produit », `∏ (ℝ^{n_i} − {O}) ⊂ ℝ^{Σ n_i} − {O}`). -/
def blockPt (p : RnO (a + 1) × RnO (b + 1)) : RnO (a + b + 1 + 1) :=
  ⟨blockEquiv a b (p.1.val, p.2.val), blockEquiv_ne_zero p.1.val_ne_zero⟩

@[simp] theorem val_blockPt (p : RnO (a + 1) × RnO (b + 1)) :
    (blockPt p).val = blockEquiv a b (p.1.val, p.2.val) := rfl

theorem blockPt_injective : Injective (blockPt : RnO (a + 1) × RnO (b + 1) → RnO (a + b + 1 + 1)) :=
  fun p q h => by
    have := (blockEquiv a b).injective (congrArg Punctured.val h)
    exact Prod.ext (Punctured.val_injective (congrArg Prod.fst this))
      (Punctured.val_injective (congrArg Prod.snd this))

/-- The diagonal homotheties: `(λv, λw) ↦ λ(v, w)`. -/
theorem blockPt_smul_pos (c : RPos) (p : RnO (a + 1) × RnO (b + 1)) :
    blockPt (c • p.1, c • p.2) = c • blockPt p := by
  refine Punctured.val_injective ?_
  simp only [val_blockPt, Punctured.val_smul_pos]
  rw [← Prod.smul_mk, map_smul]

/-- `blockPt` is equivariant through `blockGU`. -/
theorem blockPt_smul_GU (g : GUR (a + 1) × GUR (b + 1)) (p : RnO (a + 1) × RnO (b + 1)) :
    blockPt (g.1 • p.1, g.2 • p.2) = blockGU g • blockPt p := by
  refine Punctured.val_injective ?_
  simp only [val_blockPt, Punctured.val_smul_sub, coe_blockGU, blockGL_apply]

/-- The block homothety `(v, w) ↦ (λ₁v, λ₂w)` as an element of `GL(a+b+2)`. -/
theorem blockPt_smul_pos₂ (c₁ c₂ : RPos) (p : RnO (a + 1) × RnO (b + 1)) :
    blockPt (c₁ • p.1, c₂ • p.2) =
      blockGL (a := a) (b := b) (homothety _ (c₁ : ℝˣ)) (homothety _ (c₂ : ℝˣ)) • blockPt p := by
  refine Punctured.val_injective ?_
  simp only [val_blockPt, Punctured.val_smul_pos, Punctured.val_smul_lin, blockGL_apply,
    homothety_apply]

theorem continuous_blockPt :
    Continuous (blockPt : RnO (a + 1) × RnO (b + 1) → RnO (a + b + 1 + 1)) := by
  refine continuous_induced_rng.2 ?_
  exact (LinearMap.continuous_of_finiteDimensional (blockEquiv a b).toLinearMap).comp
    ((Punctured.continuous_val.comp continuous_fst).prodMk
      (Punctured.continuous_val.comp continuous_snd))

/-- **`blockPt` is an open embedding.** -/
theorem isOpenEmbedding_blockPt :
    IsOpenEmbedding (blockPt : RnO (a + 1) × RnO (b + 1) → RnO (a + b + 1 + 1)) := by
  have hL : IsOpenEmbedding (blockEquiv a b) :=
    ((blockEquiv a b).toContinuousLinearEquiv.toHomeomorph).isOpenEmbedding
  have h1 : IsOpenEmbedding (Prod.map (Punctured.val : RnO (a + 1) → _)
      (Punctured.val : RnO (b + 1) → _)) :=
    Punctured.isOpenEmbedding_val.prodMap Punctured.isOpenEmbedding_val
  have h2 : IsOpenEmbedding (Punctured.val ∘ blockPt (a := a) (b := b)) := hL.comp h1
  exact (IsOpenEmbedding.of_comp_iff _ Punctured.isOpenEmbedding_val).1 h2

end Block

/-! ### Déf. 1 — the product of two affine conical manifolds -/

section ProdConeDef

variable {a b : ℕ}

variable (a b) in
/-- `blockPt` as an open partial homeomorphism (source everything). -/
def blockOPH : OpenPartialHomeomorph (RnO (a + 1) × RnO (b + 1)) (RnO (a + b + 1 + 1)) :=
  isOpenEmbedding_blockPt.toOpenPartialHomeomorph _

@[simp] theorem blockOPH_apply (p : RnO (a + 1) × RnO (b + 1)) : blockOPH a b p = blockPt p := rfl

@[simp] theorem blockOPH_source : (blockOPH a b).source = univ := by
  simp [blockOPH]

@[simp] theorem blockOPH_target : (blockOPH a b).target = range blockPt := by
  simp [blockOPH]

theorem blockOPH_symm_blockPt (p : RnO (a + 1) × RnO (b + 1)) :
    (blockOPH a b).symm (blockPt p) = p :=
  (blockOPH a b).left_inv (by simp)

variable {V : Type*} [TopologicalSpace V] {W : Type*} [TopologicalSpace W]

/-- **The product chart** `(m₁, m₂) ↦ (e₁(m₁), e₂(m₂)) ∈ ℝ^{a+b+2} − {O}`. -/
def prodChart (e₁ : OpenPartialHomeomorph V (RnO (a + 1)))
    (e₂ : OpenPartialHomeomorph W (RnO (b + 1))) :
    OpenPartialHomeomorph (V × W) (RnO (a + b + 1 + 1)) :=
  (e₁.prod e₂).trans (blockOPH a b)

variable {e₁ : OpenPartialHomeomorph V (RnO (a + 1))} {e₂ : OpenPartialHomeomorph W (RnO (b + 1))}

@[simp] theorem prodChart_apply (x : V × W) : prodChart e₁ e₂ x = blockPt (e₁ x.1, e₂ x.2) := rfl

@[simp] theorem prodChart_source : (prodChart e₁ e₂).source = e₁.source ×ˢ e₂.source := by
  simp [prodChart]

theorem prodChart_target : (prodChart e₁ e₂).target = blockPt '' (e₁.target ×ˢ e₂.target) := by
  ext y
  simp only [prodChart, OpenPartialHomeomorph.trans_target, blockOPH_target,
    OpenPartialHomeomorph.prod_target, mem_inter_iff, mem_range, mem_preimage, mem_image]
  constructor
  · rintro ⟨⟨p, rfl⟩, hp⟩
    rw [blockOPH_symm_blockPt] at hp
    exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, rfl⟩, by rw [blockOPH_symm_blockPt]; exact hp⟩

theorem prodChart_symm_blockPt (p : RnO (a + 1) × RnO (b + 1)) :
    (prodChart e₁ e₂).symm (blockPt p) = (e₁.symm p.1, e₂.symm p.2) := by
  simp [prodChart, blockOPH_symm_blockPt]

variable [ChartedSpace (RnO (a + 1)) V] [ChartedSpace (RnO (b + 1)) W]

variable (a b V W) in
/-- **Déf. 1: the conical charted space of a product** (« le cône affin produit des cônes affins »):
the charts are the product charts `(e₁, e₂)` composed with `blockPt`, onto subsets of
`∏ (ℝ^{n_i} − {O}) ⊂ ℝ^{Σ n_i} − {O}`. A reducible `def`; it is a SCOPED instance below (namespace
`Benzecri.ProdCone`), since `V × W` is a Mathlib type. -/
@[reducible] def prodConeChartedSpace : ChartedSpace (RnO (a + b + 1 + 1)) (V × W) where
  atlas := {E | ∃ e₁ ∈ atlas (RnO (a + 1)) V, ∃ e₂ ∈ atlas (RnO (b + 1)) W, E = prodChart e₁ e₂}
  chartAt x := prodChart (chartAt (RnO (a + 1)) x.1) (chartAt (RnO (b + 1)) x.2)
  mem_chart_source x := by
    rw [prodChart_source]
    exact ⟨mem_chart_source _ x.1, mem_chart_source _ x.2⟩
  chart_mem_atlas x := ⟨_, chart_mem_atlas _ x.1, _, chart_mem_atlas _ x.2, rfl⟩


end ProdConeDef

namespace ProdCone

variable {a b : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (RnO (a + 1)) V]
  {W : Type*} [TopologicalSpace W] [ChartedSpace (RnO (b + 1)) W]

/-- The conical charted space of `V × W` (Déf. 1), scoped to `Benzecri.ProdCone`. -/
scoped instance instChartedSpace : ChartedSpace (RnO (a + b + 1 + 1)) (V × W) :=
  prodConeChartedSpace a b V W

theorem chartAt_eq (x : V × W) :
    chartAt (RnO (a + b + 1 + 1)) x =
      prodChart (chartAt (RnO (a + 1)) x.1) (chartAt (RnO (b + 1)) x.2) := rfl

variable [HasGroupoid V (coneGroupoid (a + 1))] [HasGroupoid W (coneGroupoid (b + 1))]

/-- **The product of affine conical manifolds is an affine conical manifold** (Déf. 1, « $\prod
GU(n_i) \hookrightarrow GU(\sum n_i)$ »): the transition between two product charts is, near every
point, `diag(g₁, g₂)` where the factors' transitions are `g₁`, `g₂`. -/
scoped instance instHasGroupoid : HasGroupoid (V × W) (coneGroupoid (a + b + 1 + 1)) where
  compatible {E E'} hE hE' := by
    obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := hE
    obtain ⟨e₁', he₁', e₂', he₂', rfl⟩ := hE'
    refine symm_trans_mem_gxGroupoid fun x hx => ?_
    rw [prodChart_source, prodChart_source] at hx
    obtain ⟨g₁, hg₁⟩ := eventually_smul_eq_of_mem_gxGroupoid
      (HasGroupoid.compatible (G := coneGroupoid (a + 1)) he₁ he₁') hx.1.1 hx.2.1
    obtain ⟨g₂, hg₂⟩ := eventually_smul_eq_of_mem_gxGroupoid
      (HasGroupoid.compatible (G := coneGroupoid (b + 1)) he₂ he₂') hx.1.2 hx.2.2
    refine ⟨blockGU (g₁, g₂), ?_⟩
    filter_upwards [continuous_fst.continuousAt.eventually hg₁,
      continuous_snd.continuousAt.eventually hg₂] with z h1 h2
    rw [prodChart_apply, prodChart_apply, h1, h2, ← blockPt_smul_GU]

/-- **A product of maximal-atlas charts is in the maximal atlas.** -/
theorem prodChart_mem_maximalAtlas {e₁ : OpenPartialHomeomorph V (RnO (a + 1))}
    {e₂ : OpenPartialHomeomorph W (RnO (b + 1))} (he₁ : e₁ ∈ (coneGroupoid (a + 1)).maximalAtlas V)
    (he₂ : e₂ ∈ (coneGroupoid (b + 1)).maximalAtlas W) :
    prodChart e₁ e₂ ∈ (coneGroupoid (a + b + 1 + 1)).maximalAtlas (V × W) := by
  rw [mem_maximalAtlas_iff_eventually]
  intro x hx
  rw [prodChart_source] at hx
  obtain ⟨g₁, hg₁⟩ := (mem_maximalAtlas_iff_eventually.1 he₁) x.1 hx.1
  obtain ⟨g₂, hg₂⟩ := (mem_maximalAtlas_iff_eventually.1 he₂) x.2 hx.2
  refine ⟨blockGU (g₁, g₂), ?_⟩
  filter_upwards [continuous_fst.continuousAt.eventually hg₁,
    continuous_snd.continuousAt.eventually hg₂] with z h1 h2
  rw [prodChart_apply, chartAt_eq, prodChart_apply, h1, h2, ← blockPt_smul_GU]

/-- **A product of cone charts is a cone chart.** -/
theorem isConeChart_prodChart {e₁ : OpenPartialHomeomorph V (RnO (a + 1))}
    {e₂ : OpenPartialHomeomorph W (RnO (b + 1))} (he₁ : IsConeChart (a + 1) e₁)
    (he₂ : IsConeChart (b + 1) e₂) : IsConeChart (a + b + 1 + 1) (prodChart e₁ e₂) := by
  refine ⟨prodChart_mem_maximalAtlas he₁.1 he₂.1, ?_, ?_⟩
  · rw [prodChart_target]
    exact isOpenEmbedding_blockPt.isOpenMap _ (he₁.2.1.prod he₂.2.1)
  · intro c v hv
    rw [prodChart_target] at hv ⊢
    obtain ⟨p, hp, rfl⟩ := hv
    exact ⟨(c • p.1, c • p.2), ⟨he₁.2.2 c _ hp.1, he₂.2.2 c _ hp.2⟩, blockPt_smul_pos c p⟩

variable [HasConeCharts (a + 1) V] [HasConeCharts (b + 1) W]

/-- **The product has cone charts** (Déf. 2, 3°). -/
scoped instance instHasConeCharts : HasConeCharts (a + b + 1 + 1) (V × W) where
  exists_isConeChart x := ⟨prodChart (coneChartAt (a + 1) x.1) (coneChartAt (b + 1) x.2),
    isConeChart_prodChart (isConeChart_coneChartAt x.1) (isConeChart_coneChartAt x.2),
    by rw [prodChart_source]; exact ⟨mem_coneChartAt_source x.1, mem_coneChartAt_source x.2⟩⟩

variable [T2Space V] [T2Space W]

/-- **The homotheties of the product are the diagonal ones** (Déf. 1, « $(\lambda_1\ldots\lambda_p)
\times(m_1\ldots m_p) = (\lambda_1 m_1, \ldots, \lambda_p m_p)$ » on the diagonal): Déf. 3's action
on `V × W` is `λ(m₁, m₂) = (λm₁, λm₂)`. -/
theorem posSMul_prod (c : RPos) (x : V × W) :
    posSMul (a + b + 1 + 1) c x = (posSMul (a + 1) c x.1, posSMul (b + 1) c x.2) := by
  have he₁ := isConeChart_coneChartAt (n := a + 1) x.1
  have he₂ := isConeChart_coneChartAt (n := b + 1) x.2
  have hx₁ := mem_coneChartAt_source (n := a + 1) x.1
  have hx₂ := mem_coneChartAt_source (n := b + 1) x.2
  have hE := isConeChart_prodChart he₁ he₂
  rw [posSMul_eq hE (by rw [prodChart_source]; exact ⟨hx₁, hx₂⟩), prodChart_apply,
    ← blockPt_smul_pos, prodChart_symm_blockPt, posSMul_eq he₁ hx₁, posSMul_eq he₂ hx₂]

omit [HasGroupoid V (coneGroupoid (a + 1))] [HasGroupoid W (coneGroupoid (b + 1))]
  [HasConeCharts (a + 1) V] [HasConeCharts (b + 1) W] [T2Space V] [T2Space W] in
/-- **A product of conical morphisms is a conical morphism of the products** (Prop. 3's proof,
« un automorphisme $F(\varphi_i)$ … qui définit un automorphisme … $F_i(\varphi_i)$ de la structure
conique affine du produit »): it reads as `diag(g₁, g₂)` in product charts. -/
theorem isGXMorphism_prodMap {V' : Type*} [TopologicalSpace V'] [ChartedSpace (RnO (a + 1)) V']
    {W' : Type*} [TopologicalSpace W'] [ChartedSpace (RnO (b + 1)) W'] {f₁ : V → V'}
    {f₂ : W → W'} (h₁ : IsGXMorphism (GUR (a + 1)) (RnO (a + 1)) f₁)
    (h₂ : IsGXMorphism (GUR (b + 1)) (RnO (b + 1)) f₂) :
    IsGXMorphism (GUR (a + b + 1 + 1)) (RnO (a + b + 1 + 1)) (Prod.map f₁ f₂) := by
  refine ⟨h₁.continuous.prodMap h₂.continuous, fun x => ?_⟩
  obtain ⟨g₁, hg₁⟩ := h₁.exists_smul_eq x.1
  obtain ⟨g₂, hg₂⟩ := h₂.exists_smul_eq x.2
  refine ⟨blockGU (g₁, g₂), ?_⟩
  filter_upwards [continuous_fst.continuousAt.eventually hg₁,
    continuous_snd.continuousAt.eventually hg₂] with y h1 h2
  rw [chartAt_eq, chartAt_eq, prodChart_apply, prodChart_apply, Prod.map_fst, Prod.map_snd,
    Prod.map_fst, Prod.map_snd, h1, h2, ← blockPt_smul_GU]

end ProdCone

/-! ### The block homotheties `(m₁, m₂) ↦ (λ₁m₁, λ₂m₂)` and the torus `ℝ₊*²/ℝ₊*` -/

section BlockHom

open ProdCone

variable {a b : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (RnO (a + 1)) V]
  [HasGroupoid V (coneGroupoid (a + 1))] [HasConeCharts (a + 1) V] [T2Space V]
  {W : Type*} [TopologicalSpace W] [ChartedSpace (RnO (b + 1)) W]
  [HasGroupoid W (coneGroupoid (b + 1))] [HasConeCharts (b + 1) W] [T2Space W]

variable (a b V W) in
/-- **The action of `(λ₁, λ₂) ∈ ℝ₊*²` on the product cone** (Déf. 1, « $(\lambda_1 \ldots
\lambda_p) \times (m_1 \ldots m_p) = (\lambda_1 m_1, \ldots, \lambda_p m_p)$ »). -/
def blockHom (c₁ c₂ : RPos) (x : V × W) : V × W := (posSMul (a + 1) c₁ x.1, posSMul (b + 1) c₂ x.2)

omit [HasGroupoid V (coneGroupoid (a + 1))] [HasGroupoid W (coneGroupoid (b + 1))] in
theorem continuous_blockHom (c₁ c₂ : RPos) : Continuous (blockHom a b V W c₁ c₂) :=
  ((continuous_posSMul (n := a + 1)).comp (continuous_const.prodMk continuous_fst)).prodMk
    ((continuous_posSMul (n := b + 1)).comp (continuous_const.prodMk continuous_snd))

/-- **A block homothety is a morphism of the conical structure of the product when
`λ₁^{a+1} λ₂^{b+1} = 1`** (`a + 1`, `b + 1` the dimensions of the factors): in product cone charts it
is `diag(λ₁, λ₂)`, of determinant `λ₁^{a+1} λ₂^{b+1}`. -/
theorem isGXMorphism_blockHom {c₁ c₂ : RPos}
    (h : (((c₁ : ℝˣ) : ℝ)) ^ (a + 1) * (((c₂ : ℝˣ) : ℝ)) ^ (b + 1) = 1) :
    IsGXMorphism (GUR (a + b + 1 + 1)) (RnO (a + b + 1 + 1)) (blockHom a b V W c₁ c₂) := by
  have hg : blockGL (homothety (Fin (a + 1) → ℝ) (c₁ : ℝˣ)) (homothety (Fin (b + 1) → ℝ) (c₂ : ℝˣ))
      ∈ GUR (a + b + 1 + 1) := by
    rw [mem_GU, det_blockGL, det_homothety, det_homothety, Module.finrank_fin_fun,
      Module.finrank_fin_fun, h, abs_one]
  refine isGXMorphism_of_mem_maximalAtlas (continuous_blockHom c₁ c₂) fun x => ?_
  have he₁ := isConeChart_coneChartAt (n := a + 1) x.1
  have he₂ := isConeChart_coneChartAt (n := b + 1) x.2
  have hx₁ := mem_coneChartAt_source (n := a + 1) x.1
  have hx₂ := mem_coneChartAt_source (n := b + 1) x.2
  have hE := isConeChart_prodChart he₁ he₂
  have hx : x ∈ (prodChart (coneChartAt (a + 1) x.1) (coneChartAt (b + 1) x.2)).source := by
    rw [prodChart_source]; exact ⟨hx₁, hx₂⟩
  refine ⟨_, hE.1, _, hE.1, hx, ?_, ⟨_, hg⟩, ?_⟩
  · rw [prodChart_source]
    exact ⟨he₁.smul_mem_source hx₁ c₁, he₂.smul_mem_source hx₂ c₂⟩
  · filter_upwards [(prodChart (coneChartAt (a + 1) x.1) (coneChartAt (b + 1) x.2)).open_source.mem_nhds
      hx] with y hy
    rw [prodChart_source] at hy
    simp only [blockHom, prodChart_apply]
    rw [he₁.map_smul hy.1, he₂.map_smul hy.2]
    exact blockPt_smul_pos₂ c₁ c₂ (_, _)

variable (a b) in
/-- The unimodular representative `(λ₁, λ₂)` of the class of `(1, μ)` in `ℝ₊*²/ℝ₊*`:
`λ₂/λ₁ = μ` and `λ₁^{a+1} λ₂^{b+1} = 1` (the CORRECTED lift of Prop. 2's proof; the printed one,
`λ₁λ₂ = 1`, is not conical unless `a = b`, `not_isGXMorphism_blockHom_of_ne`). -/
def torusPair (μ : RPos) : RPos × RPos :=
  (rposExp (-((b : ℝ) + 1) * rposLog μ / ((a : ℝ) + b + 2)),
    rposExp (((a : ℝ) + 1) * rposLog μ / ((a : ℝ) + b + 2)))

theorem coe_rposExp (t : ℝ) : (((rposExp t : RPos) : ℝˣ) : ℝ) = Real.exp t := rfl

theorem torusPair_det (μ : RPos) :
    ((((torusPair a b μ).1 : ℝˣ) : ℝ)) ^ (a + 1) * ((((torusPair a b μ).2 : ℝˣ) : ℝ)) ^ (b + 1) =
      1 := by
  simp only [torusPair, coe_rposExp, ← Real.exp_nat_mul, ← Real.exp_add]
  rw [Real.exp_eq_one_iff]
  have : (a : ℝ) + b + 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem torusPair_ratio (μ : RPos) : (torusPair a b μ).1 * μ = (torusPair a b μ).2 := by
  refine rposLog_injective ?_
  simp only [torusPair, rposLog_mul, rposLog_rposExp]
  have : (a : ℝ) + b + 2 ≠ 0 := by positivity
  field_simp
  ring

variable (a b V W) in
/-- **The torus `ℝ₊*²/ℝ₊*` acting on the base `F⁻¹(F(B₁) × F(B₂))`** (Prop. 2), the class of `(1, μ)`
acting by `[m₁, m₂] ↦ [m₁, μm₂]`: the base map of the unimodular block homothety `torusPair μ`. -/
def torusMap (μ : RPos) : ConeBase (a + b + 1) (V × W) → ConeBase (a + b + 1) (V × W) :=
  ConeBase.map (isGXMorphism_blockHom (a := a) (b := b) (V := V) (W := W) (torusPair_det μ))

/-- **The torus acts by projective automorphisms** (« Un élément de ce sous-groupe définit un
automorphisme de la structure conique affine du produit des $F(B_i)$ qui se projette donc suivant un
automorphisme projectif de la structure de la base »). -/
theorem isGXMorphism_torusMap (μ : RPos) :
    IsGXMorphism (GSR (a + b + 1)) (S (a + b + 1)) (torusMap a b V W μ) :=
  ConeBase.isGXMorphism_map _

theorem torusMap_mk (μ : RPos) (x : V × W) :
    torusMap a b V W μ (ConeBase.mk x) = ConeBase.mk (x.1, posSMul (b + 1) μ x.2) := by
  rw [torusMap, ConeBase.map_mk]
  refine ConeBase.mk_eq_mk_iff.2 ⟨(torusPair a b μ).1, ?_⟩
  rw [ProdCone.posSMul_prod, ← posSMul_mul, torusPair_ratio]
  rfl

theorem continuous_torusMap (μ : RPos) : Continuous (torusMap a b V W μ) :=
  ConeBase.continuous_map _

theorem torusMap_one : torusMap a b V W 1 = id := by
  funext p
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rw [torusMap_mk, posSMul_one]
  rfl

theorem torusMap_mul (μ ν : RPos) : torusMap a b V W (μ * ν) = torusMap a b V W μ ∘ torusMap a b V W ν := by
  funext p
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rw [Function.comp_apply, torusMap_mk, torusMap_mk, torusMap_mk, posSMul_mul]

variable (a b V W) in
/-- **The projection of the base of the product cone onto the product of the bases**,
`[m₁, m₂] ↦ ([m₁], [m₂])` (« structure d'espace fibré principal de base $B_1 \times \ldots \times
B_p$ »). -/
def basePr : ConeBase (a + b + 1) (V × W) → ConeBase a V × ConeBase b W :=
  Quotient.lift (fun x : V × W => (ConeBase.mk x.1, ConeBase.mk x.2)) fun x x' h => by
    obtain ⟨c, rfl⟩ := ConeBase.rel_iff.1 h
    rw [ProdCone.posSMul_prod]
    simp only [ConeBase.mk_posSMul]

@[simp] theorem basePr_mk (x : V × W) :
    basePr a b V W (ConeBase.mk x) = (ConeBase.mk x.1, ConeBase.mk x.2) := rfl

theorem continuous_basePr : Continuous (basePr a b V W) :=
  continuous_quot_lift _ ((ConeBase.continuous_mk.comp continuous_fst).prodMk
    (ConeBase.continuous_mk.comp continuous_snd))

theorem basePr_surjective : Surjective (basePr a b V W) := by
  rintro ⟨q₁, q₂⟩
  obtain ⟨x₁, rfl⟩ := ConeBase.mk_surjective q₁
  obtain ⟨x₂, rfl⟩ := ConeBase.mk_surjective q₂
  exact ⟨ConeBase.mk (x₁, x₂), rfl⟩

theorem basePr_torusMap (μ : RPos) (p : ConeBase (a + b + 1) (V × W)) :
    basePr a b V W (torusMap a b V W μ p) = basePr a b V W p := by
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rw [torusMap_mk, basePr_mk, basePr_mk, ConeBase.mk_posSMul]

/-- **The fibres of the projection are the orbits of the torus** (Prop. 2). -/
theorem basePr_eq_iff {p p' : ConeBase (a + b + 1) (V × W)} :
    basePr a b V W p = basePr a b V W p' ↔ ∃ μ : RPos, torusMap a b V W μ p = p' := by
  refine ⟨fun h => ?_, fun ⟨μ, hμ⟩ => hμ ▸ (basePr_torusMap μ p).symm⟩
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  obtain ⟨x', rfl⟩ := ConeBase.mk_surjective p'
  simp only [basePr_mk, Prod.mk.injEq] at h
  obtain ⟨c₁, hc₁⟩ := ConeBase.mk_eq_mk_iff.1 h.1.symm
  obtain ⟨c₂, hc₂⟩ := ConeBase.mk_eq_mk_iff.1 h.2.symm
  refine ⟨c₁⁻¹ * c₂, ?_⟩
  rw [torusMap_mk]
  refine (ConeBase.mk_eq_mk_iff.2 ⟨c₁, ?_⟩).symm
  rw [ProdCone.posSMul_prod, ← posSMul_mul, mul_inv_cancel_left, hc₁, hc₂]

/-- **The torus acts freely** (« espace fibré principal »). -/
theorem eq_one_of_torusMap_eq {μ : RPos} {p : ConeBase (a + b + 1) (V × W)}
    (h : torusMap a b V W μ p = p) : μ = 1 := by
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rw [torusMap_mk] at h
  obtain ⟨c, hc⟩ := ConeBase.mk_eq_mk_iff.1 h.symm
  rw [ProdCone.posSMul_prod, Prod.mk.injEq] at hc
  obtain rfl := eq_one_of_posSMul_eq hc.1
  have h2 : posSMul (b + 1) μ x.2 = x.2 := by simpa only [posSMul_one] using hc.2
  exact eq_one_of_posSMul_eq h2

/-- The torus acts by automorphisms: `torusMap μ` is a bijective projective morphism. -/
theorem torusMap_bijective (μ : RPos) : Bijective (torusMap a b V W μ) := by
  refine bijective_iff_has_inverse.2 ⟨torusMap a b V W μ⁻¹, fun p => ?_, fun p => ?_⟩
  · rw [← Function.comp_apply (f := torusMap a b V W μ⁻¹), ← torusMap_mul, inv_mul_cancel,
      torusMap_one]; rfl
  · rw [← Function.comp_apply (f := torusMap a b V W μ), ← torusMap_mul, mul_inv_cancel,
      torusMap_one]; rfl

/-- **§ 3 Prop. 2, for two factors** (`bzprop:c1s3p2_fibre_produit`): « Le quotient
$\R^{+p}/\R^+$ opère sur $F^{-1}(F(B_1)\times\ldots\times F(B_p))$ et définit sur cette variété
localement projective une structure d'espace fibré principal de base
$(B_1\times\ldots\times B_p)$ », for any two affine conical manifolds `V`, `W` (base `V/ℝ₊* ×
W/ℝ₊*`; for `V = F(B₁)`, `W = F(B₂)` it is `B₁ × B₂`, `FCone.baseProjHomeomorph`): `ℝ₊*²/ℝ₊* ≅ ℝ₊*`
(the class of `(1, μ)`) acts by projective automorphisms, freely, with orbits the fibres of the
continuous surjection `basePr`. Local triviality: `exists_prodBase_homeomorph` (global, for
paracompact bases). -/
theorem prop2_fibre_produit :
    (∀ μ, IsGXMorphism (GSR (a + b + 1)) (S (a + b + 1)) (torusMap a b V W μ) ∧
      Bijective (torusMap a b V W μ)) ∧
    torusMap a b V W 1 = id ∧
    (∀ μ ν, torusMap a b V W (μ * ν) = torusMap a b V W μ ∘ torusMap a b V W ν) ∧
    (∀ μ p, torusMap a b V W μ p = p → μ = 1) ∧
    Continuous (basePr a b V W) ∧ Surjective (basePr a b V W) ∧
    ∀ p p', basePr a b V W p = basePr a b V W p' ↔ ∃ μ : RPos, torusMap a b V W μ p = p' :=
  ⟨fun μ => ⟨isGXMorphism_torusMap μ, torusMap_bijective μ⟩, torusMap_one, torusMap_mul,
    fun _ _ h => eq_one_of_torusMap_eq h, continuous_basePr, basePr_surjective,
    fun _ _ => basePr_eq_iff⟩

/-- **A block homothety is a conical morphism ONLY IF `λ₁^{a+1} λ₂^{b+1} = 1`** (for a nonempty
product): in a product cone chart it reads as `diag(λ₁, λ₂)`, and an element of `GU(a+b+2)` agreeing
with it on an open set is it (rigidity), so `|det| = λ₁^{a+1} λ₂^{b+1} = 1`. -/
theorem det_eq_one_of_isGXMorphism_blockHom [Nonempty V] [Nonempty W] {c₁ c₂ : RPos}
    (hf : IsGXMorphism (GUR (a + b + 1 + 1)) (RnO (a + b + 1 + 1)) (blockHom a b V W c₁ c₂)) :
    (((c₁ : ℝˣ) : ℝ)) ^ (a + 1) * (((c₂ : ℝˣ) : ℝ)) ^ (b + 1) = 1 := by
  obtain ⟨x₁⟩ := ‹Nonempty V›
  obtain ⟨x₂⟩ := ‹Nonempty W›
  set x : V × W := (x₁, x₂)
  have he₁ := isConeChart_coneChartAt (n := a + 1) x.1
  have he₂ := isConeChart_coneChartAt (n := b + 1) x.2
  have hx₁ := mem_coneChartAt_source (n := a + 1) x.1
  have hx₂ := mem_coneChartAt_source (n := b + 1) x.2
  set E := prodChart (coneChartAt (a + 1) x.1) (coneChartAt (b + 1) x.2) with hEdef
  have hE := isConeChart_prodChart he₁ he₂
  have hx : x ∈ E.source := by rw [prodChart_source]; exact ⟨hx₁, hx₂⟩
  have hfx : blockHom a b V W c₁ c₂ x ∈ E.source := by
    rw [prodChart_source]
    exact ⟨he₁.smul_mem_source hx₁ c₁, he₂.smul_mem_source hx₂ c₂⟩
  obtain ⟨g, hg⟩ := hf.exists_smul_eq_of_mem_maximalAtlas hE.1 hE.1 hx hfx
  obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 (hg.and (E.open_source.mem_nhds hx))
  set D := blockGL (homothety (Fin (a + 1) → ℝ) (c₁ : ℝˣ)) (homothety (Fin (b + 1) → ℝ) (c₂ : ℝˣ))
  have hkey : (g : GLR (a + b + 1 + 1)) = D := by
    refine eq_of_eqOn (E.isOpen_image_of_subset_source hto fun z hz => (ht hz).2)
      ⟨E x, mem_image_of_mem E hxt⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    have h1 : E (blockHom a b V W c₁ c₂ y) = g • E y := (ht hy).1
    have hy' := (ht hy).2
    rw [hEdef, prodChart_source] at hy'
    have h2 : E (blockHom a b V W c₁ c₂ y) = D • E y := by
      simp only [hEdef, blockHom, prodChart_apply]
      rw [he₁.map_smul hy'.1, he₂.map_smul hy'.2]
      exact blockPt_smul_pos₂ c₁ c₂ (_, _)
    exact h1.symm.trans h2
  have hdet := mem_GU.1 g.2
  have hp₁ := Punctured.pos c₁
  have hp₂ := Punctured.pos c₂
  rw [hkey, det_blockGL, det_homothety, det_homothety, Module.finrank_fin_fun,
    Module.finrank_fin_fun, abs_of_pos (by positivity)] at hdet
  exact hdet

/-- **Finding (Prop. 2's proof, p. 244)**: the printed lift « le sous-groupe de $\R^{+p}$ formé des
systèmes de $p$ nombres réels positifs dont le produit est égal à $1$. Un élément de ce sous-groupe
définit un automorphisme de la structure conique affine du produit » is false when the factors'
dimensions differ: for `a ≠ b` the element `(2, 1/2)` (product `1`) is not a conical automorphism of
`V × W`. The corrected lift is `λ₁^{a+1} λ₂^{b+1} = 1` (`torusPair`), and Prop. 2 itself holds
(`prop2_fibre_produit`): every element of `ℝ₊*²` descends to a projective automorphism of the
base. -/
theorem not_isGXMorphism_blockHom_of_ne [Nonempty V] [Nonempty W] (hab : a ≠ b) :
    ∃ c₁ c₂ : RPos, c₁ * c₂ = 1 ∧
      ¬ IsGXMorphism (GUR (a + b + 1 + 1)) (RnO (a + b + 1 + 1)) (blockHom a b V W c₁ c₂) := by
  refine ⟨Punctured.posUnit 2 two_pos, (Punctured.posUnit 2 two_pos)⁻¹, mul_inv_cancel _,
    fun hf => ?_⟩
  have h := det_eq_one_of_isGXMorphism_blockHom hf
  simp only [Punctured.coe_posUnit, InvMemClass.coe_inv, Units.val_inv_eq_inv_val, inv_pow] at h
  rw [mul_inv_eq_one₀ (by positivity)] at h
  have h' : (2 : ℕ) ^ (a + 1) = 2 ^ (b + 1) := by exact_mod_cast h
  have := Nat.pow_right_injective (le_refl 2) h'
  omega

end BlockHom

/-! ### Radial coordinates on `F(B)` -/

namespace FCone

variable {n : ℕ} {B : Type u} [TopologicalSpace B] [ChartedSpace (S n) B]
  [HasGroupoid B (projGroupoid n)] [T2Space B]

/-- **A homogeneous norm and a section of `F(B) → B`** (`Cone/Section`, through `F(B)/ℝ₊* ≅ B`), for
`B` paracompact: `N(λx) = λN(x)`, `π ∘ σ = id`, `N ∘ σ = 1`, and `x = N(x)·σ(π(x))`. -/
theorem exists_radial [ParacompactSpace B] :
    ∃ N : FCone n B → RPos, ∃ σ : B → FCone n B, Continuous N ∧ Continuous σ ∧
      (∀ c x, N (posSMul (n + 1) c x) = c * N x) ∧ (∀ b, proj (σ b) = b) ∧ (∀ b, N (σ b) = 1) ∧
      ∀ x, posSMul (n + 1) (N x) (σ (proj x)) = x := by
  haveI := t2Space_coneBase (n := n) (B := B)
  haveI : ParacompactSpace (ConeBase n (FCone n B)) :=
    (baseProjHomeomorph.paracompactSpace_iff).2 inferInstance
  obtain ⟨T, hT1, hT2⟩ := ConeBase.exists_trivialization (n := n) (V := FCone n B)
  have hq : ∀ x : FCone n B, baseProjHomeomorph.symm (proj x) = (T x).1 := fun x => by
    rw [Homeomorph.symm_apply_eq, hT1, baseProjHomeomorph_apply, baseProj_mk]
  refine ⟨fun x => (T x).2, fun b => T.symm (baseProjHomeomorph.symm b, 1),
    continuous_snd.comp T.continuous,
    T.symm.continuous.comp (baseProjHomeomorph.symm.continuous.prodMk continuous_const),
    fun c x => by simp only [hT2], fun b => ?_, fun b => by simp, fun x => T.injective ?_⟩
  · have h1 := hT1 (T.symm (baseProjHomeomorph.symm b, 1))
    rw [T.apply_symm_apply] at h1
    rw [← baseProj_mk, ← h1, ← baseProjHomeomorph_apply, Homeomorph.apply_symm_apply]
  · rw [hT2, T.apply_symm_apply, hq, mul_one]

end FCone

/-! ### The corollary of Prop. 3 for two factors: `B₁ × B₂ × S¹` is locally projective -/

section Corollary

open ProdCone

variable {a b : ℕ} {B₁ : Type u} [TopologicalSpace B₁] [ChartedSpace (S a) B₁]
  [HasGroupoid B₁ (projGroupoid a)] [T2Space B₁]
  {B₂ : Type u} [TopologicalSpace B₂] [ChartedSpace (S b) B₂]
  [HasGroupoid B₂ (projGroupoid b)] [T2Space B₂]

/-- **The base of the product cone is `B₁ × B₂ × ℝ₊*`**, the last coordinate being `N₂(m₂)/N₁(m₁)`
(Prop. 2: « la base du produit des $F(B_i)$ n'est autre que le quotient de ce produit par la
diagonale de $\R^{+p}$ », trivialised), equivariantly for the torus. -/
theorem exists_prodBase_homeomorph [ParacompactSpace B₁] [ParacompactSpace B₂] :
    ∃ H : ConeBase (a + b + 1) (FCone a B₁ × FCone b B₂) ≃ₜ B₁ × B₂ × RPos,
      (∀ x : FCone a B₁ × FCone b B₂,
        (H (ConeBase.mk x)).1 = FCone.proj x.1 ∧ (H (ConeBase.mk x)).2.1 = FCone.proj x.2) ∧
      ∀ (μ : RPos) (p : ConeBase (a + b + 1) (FCone a B₁ × FCone b B₂)),
        H (torusMap a b (FCone a B₁) (FCone b B₂) μ p) = ((H p).1, (H p).2.1, μ * (H p).2.2) := by
  obtain ⟨N₁, σ₁, hN₁c, hσ₁c, hN₁, hσ₁p, hσ₁N, hσ₁⟩ := FCone.exists_radial (n := a) (B := B₁)
  obtain ⟨N₂, σ₂, hN₂c, hσ₂c, hN₂, hσ₂p, hσ₂N, hσ₂⟩ := FCone.exists_radial (n := b) (B := B₂)
  set r : FCone a B₁ × FCone b B₂ → RPos := fun x => N₂ x.2 * (N₁ x.1)⁻¹ with hr_def
  have hr : ∀ c x, r (posSMul (a + b + 1 + 1) c x) = r x := by
    intro c x
    simp only [hr_def, ProdCone.posSMul_prod, hN₁, hN₂]
    exact rposLog_injective (by simp only [rposLog_mul, rposLog_inv]; ring)
  let f : FCone a B₁ × FCone b B₂ → B₁ × B₂ × RPos :=
    fun x => (FCone.proj x.1, FCone.proj x.2, r x)
  have hf : ∀ x x', coneRel (a + b + 1) (FCone a B₁ × FCone b B₂) x x' → f x = f x' := by
    intro x x' h
    obtain ⟨c, rfl⟩ := ConeBase.rel_iff.1 h
    show (FCone.proj (posSMul _ c x').1, FCone.proj (posSMul _ c x').2,
      r (posSMul (a + b + 1 + 1) c x')) = _
    rw [hr, ProdCone.posSMul_prod]
    simp only [f, FCone.proj_posSMul]
  let F : ConeBase (a + b + 1) (FCone a B₁ × FCone b B₂) → B₁ × B₂ × RPos :=
    Quotient.lift f hf
  have hFc : Continuous F := continuous_quot_lift _
    ((FCone.continuous_proj.comp continuous_fst).prodMk ((FCone.continuous_proj.comp
      continuous_snd).prodMk ((hN₂c.comp continuous_snd).mul (hN₁c.comp continuous_fst).inv)))
  let G : B₁ × B₂ × RPos → ConeBase (a + b + 1) (FCone a B₁ × FCone b B₂) :=
    fun q => ConeBase.mk (σ₁ q.1, posSMul (b + 1) q.2.2 (σ₂ q.2.1))
  have hGc : Continuous G := ConeBase.continuous_mk.comp ((hσ₁c.comp continuous_fst).prodMk
    ((continuous_posSMul (n := b + 1)).comp ((continuous_snd.comp continuous_snd).prodMk
      (hσ₂c.comp (continuous_fst.comp continuous_snd)))))
  have hFmk : ∀ x, F (ConeBase.mk x) = f x := fun x => rfl
  have hFG : ∀ q, F (G q) = q := by
    rintro ⟨b₁, b₂, t⟩
    show f (σ₁ b₁, posSMul (b + 1) t (σ₂ b₂)) = (b₁, b₂, t)
    simp only [f, hr_def, hσ₁p, FCone.proj_posSMul, hσ₂p, hN₂, hσ₂N, hσ₁N, inv_one, mul_one]
  have hGF : ∀ p, G (F p) = p := by
    intro p
    obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
    rw [hFmk]
    refine (ConeBase.mk_eq_mk_iff.2 ⟨N₁ x.1, ?_⟩).symm
    rw [ProdCone.posSMul_prod]
    simp only [f, hr_def, ← posSMul_mul, hσ₁]
    have : N₁ x.1 * (N₂ x.2 * (N₁ x.1)⁻¹) = N₂ x.2 :=
      rposLog_injective (by simp only [rposLog_mul, rposLog_inv]; ring)
    rw [this, hσ₂]
  refine ⟨⟨⟨F, G, hGF, hFG⟩, hFc, hGc⟩, fun x => ⟨rfl, rfl⟩, fun μ p => ?_⟩
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  show F (torusMap a b (FCone a B₁) (FCone b B₂) μ (ConeBase.mk x)) =
    ((F (ConeBase.mk x)).1, (F (ConeBase.mk x)).2.1, μ * (F (ConeBase.mk x)).2.2)
  rw [torusMap_mk, hFmk, hFmk]
  simp only [f, hr_def, FCone.proj_posSMul, hN₂, mul_assoc]

/-- **The corollary of Prop. 3 for two factors, full form**: for `B₁`, `B₂` paracompact and any
ratio `λ ≠ 1` there is a surjective local homeomorphism `Ψ` from the base `F⁻¹(F(B₁) × F(B₂))` onto
`B₁ × B₂ × S¹`, over `B₁ × B₂`, whose fibres are exactly the orbits of `λ^ℤ ⊂ ℝ₊*²/ℝ₊*` (the lattice
`H` of the proof, `p = 2`), and `B₁ × B₂ × S¹` carries a locally projective structure for which `Ψ`
is a morphism — the quotient structure of `F⁻¹(F(B₁) × F(B₂))/H`, unique as such. -/
theorem exists_proj_prod_circle [ParacompactSpace B₁] [ParacompactSpace B₂] {lam : RPos}
    (hlam : lam ≠ 1) :
    ∃ Ψ : ConeBase (a + b + 1) (FCone a B₁ × FCone b B₂) → B₁ × B₂ × Circle,
      IsLocalHomeomorph Ψ ∧ Surjective Ψ ∧
      (∀ x : FCone a B₁ × FCone b B₂,
        (Ψ (ConeBase.mk x)).1 = FCone.proj x.1 ∧ (Ψ (ConeBase.mk x)).2.1 = FCone.proj x.2) ∧
      (∀ p p', Ψ p = Ψ p' ↔
        ∃ k : ℤ, torusMap a b (FCone a B₁) (FCone b B₂) (lam ^ k) p = p') ∧
      ∃ cs : ChartedSpace (S (a + b + 1)) (B₁ × B₂ × Circle),
        ∃ _ : @HasGroupoid _ _ (B₁ × B₂ × Circle) _ cs (projGroupoid (a + b + 1)),
        @IsGXMorphism (GSR (a + b + 1)) (S (a + b + 1)) _ _ _
          (ConeBase (a + b + 1) (FCone a B₁ × FCone b B₂)) _ (B₁ × B₂ × Circle) _ _ cs Ψ ∧
        ∀ cs' : ChartedSpace (S (a + b + 1)) (B₁ × B₂ × Circle),
          ∀ _ : @HasGroupoid _ _ (B₁ × B₂ × Circle) _ cs' (projGroupoid (a + b + 1)),
          @IsGXMorphism (GSR (a + b + 1)) (S (a + b + 1)) _ _ _
            (ConeBase (a + b + 1) (FCone a B₁ × FCone b B₂)) _ (B₁ × B₂ × Circle) _ _ cs' Ψ →
          @StructureGroupoid.maximalAtlas _ (B₁ × B₂ × Circle) _ _ cs'
              (projGroupoid (a + b + 1)) =
            @StructureGroupoid.maximalAtlas _ (B₁ × B₂ × Circle) _ _ cs
              (projGroupoid (a + b + 1)) := by
  obtain ⟨H, hH1, hH2⟩ := exists_prodBase_homeomorph (a := a) (b := b) (B₁ := B₁) (B₂ := B₂)
  set Ψ : ConeBase (a + b + 1) (FCone a B₁ × FCone b B₂) → B₁ × B₂ × Circle :=
    fun p => ((H p).1, (H p).2.1, circleCoord lam (H p).2.2) with hΨ
  have hΨeq : ∀ p p', Ψ p = Ψ p' ↔
      ∃ k : ℤ, torusMap a b (FCone a B₁) (FCone b B₂) (lam ^ k) p = p' := by
    intro p p'
    constructor
    · intro h
      simp only [hΨ, Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      obtain ⟨k, hk⟩ := (circleCoord_eq_iff hlam).1 h3.symm
      refine ⟨k, H.injective ?_⟩
      rw [hH2, h1, h2, ← hk]
    · rintro ⟨k, rfl⟩
      simp only [hΨ, hH2, circleCoord_zpow_mul]
  have hloc : IsLocalHomeomorph Ψ :=
    (isLocalHomeomorph_prodMap (Homeomorph.refl B₁).isLocalHomeomorph
      (isLocalHomeomorph_prodMap (Homeomorph.refl B₂).isLocalHomeomorph
        (isLocalHomeomorph_circleCoord hlam))).comp H.isLocalHomeomorph
  have hsurj : Surjective Ψ := by
    rintro ⟨b₁, b₂, z⟩
    obtain ⟨c, rfl⟩ := circleCoord_surjective hlam z
    exact ⟨H.symm (b₁, b₂, c), by simp only [hΨ, Homeomorph.apply_symm_apply]⟩
  have hdeck : IsGXDeck (GSR (a + b + 1)) (S (a + b + 1)) Ψ := by
    intro p p' h
    obtain ⟨k, rfl⟩ := (hΨeq p p').1 h
    obtain ⟨g, hg⟩ := (isGXMorphism_torusMap (V := FCone a B₁) (W := FCone b B₂)
      (lam ^ k)).exists_smul_eq p
    exact ⟨_, (continuous_torusMap _).continuousAt, rfl,
      Eventually.of_forall fun y => ((hΨeq y _).2 ⟨k, rfl⟩).symm, g, hg⟩
  obtain ⟨cs, hcs, hmor, huniq⟩ := existsUnique_pushforward hloc hsurj hdeck
  exact ⟨Ψ, hloc, hsurj, fun x => ⟨(hH1 x).1, (hH1 x).2⟩, hΨeq, cs, hcs, hmor, huniq⟩

end Corollary

/-! ### § 3 Prop. 3 for two factors — homogeneous, sweepable, divisible -/

section Prop3

open ProdCone

variable {a b : ℕ} {B₁ : Type u} [TopologicalSpace B₁] [ChartedSpace (S a) B₁]
  [HasGroupoid B₁ (projGroupoid a)] [T2Space B₁]
  {B₂ : Type u} [TopologicalSpace B₂] [ChartedSpace (S b) B₂]
  [HasGroupoid B₂ (projGroupoid b)] [T2Space B₂]

variable (a b B₁ B₂) in
/-- **The base `F⁻¹(F(B₁) × F(B₂))` of the product cone** (Prop. 2: a locally projective manifold of
dimension `a + b + 1`). -/
abbrev ProdBase : Type u := ConeBase (a + b + 1) (FCone a B₁ × FCone b B₂)

/-- The projection `F⁻¹(F(B₁) × F(B₂)) → B₁ × B₂`. -/
def prodBaseProj (p : ProdBase a b B₁ B₂) : B₁ × B₂ :=
  (FCone.baseProj (basePr a b (FCone a B₁) (FCone b B₂) p).1,
    FCone.baseProj (basePr a b (FCone a B₁) (FCone b B₂) p).2)

@[simp] theorem prodBaseProj_mk (x : FCone a B₁ × FCone b B₂) :
    prodBaseProj (ConeBase.mk x : ProdBase a b B₁ B₂) = (FCone.proj x.1, FCone.proj x.2) := rfl

theorem prodBaseProj_eq_iff {p p' : ProdBase a b B₁ B₂} :
    prodBaseProj p = prodBaseProj p' ↔
      ∃ μ : RPos, torusMap a b (FCone a B₁) (FCone b B₂) μ p = p' := by
  rw [← basePr_eq_iff]
  constructor
  · intro h
    simp only [prodBaseProj, Prod.mk.injEq] at h
    exact Prod.ext (FCone.baseProj_injective h.1) (FCone.baseProj_injective h.2)
  · intro h
    simp only [prodBaseProj, h]

theorem prodBaseProj_torusMap (μ : RPos) (p : ProdBase a b B₁ B₂) :
    prodBaseProj (torusMap a b (FCone a B₁) (FCone b B₂) μ p) = prodBaseProj p :=
  prodBaseProj_eq_iff.2 ⟨μ, rfl⟩ |>.symm

/-- The torus element `μ` as an automorphism of `F⁻¹(F(B₁) × F(B₂))`. -/
def torusAut (μ : RPos) : GXAut (GSR (a + b + 1)) (S (a + b + 1)) (ProdBase a b B₁ B₂) :=
  GXAut.ofBijective (isGXMorphism_torusMap μ) (torusMap_bijective μ)

@[simp] theorem torusAut_smul (μ : RPos) (p : ProdBase a b B₁ B₂) :
    torusAut (a := a) (b := b) (B₁ := B₁) (B₂ := B₂) μ • p = torusMap a b (FCone a B₁) (FCone b B₂) μ p := rfl

/-- `F⁻¹(F(φ₁) × F(φ₂))`: a pair of automorphisms of `B₁`, `B₂` as an automorphism of
`F⁻¹(F(B₁) × F(B₂))` (« $F^{-1}(F_i(\varphi_i))$ est un automorphisme de la structure localement
projective de $F^{-1}(F(B_1)\times\ldots\times F(B_p))$ »). -/
def prodAut (φ : GXAut (GSR a) (S a) B₁ × GXAut (GSR b) (S b) B₂) :
    GXAut (GSR (a + b + 1)) (S (a + b + 1)) (ProdBase a b B₁ B₂) :=
  GXAut.ofBijective (ConeBase.isGXMorphism_map (isGXMorphism_prodMap
      (FCone.isGXMorphism_map φ.1.isGXMorphism) (FCone.isGXMorphism_map φ.2.isGXMorphism)))
    (bijective_iff_has_inverse.2 ⟨ConeBase.map (isGXMorphism_prodMap
      (FCone.isGXMorphism_map φ.1⁻¹.isGXMorphism) (FCone.isGXMorphism_map φ.2⁻¹.isGXMorphism)),
      fun p => by
        obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
        simp only [ConeBase.map_mk, Prod.map]
        rw [← FCone.autMap_smul, ← FCone.autMap_smul, ← FCone.autMap_smul,
          ← FCone.autMap_smul, FCone.autMap_inv_smul_autMap_smul,
          FCone.autMap_inv_smul_autMap_smul],
      fun p => by
        obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
        simp only [ConeBase.map_mk, Prod.map]
        have h₁ := FCone.autMap_inv_smul_autMap_smul φ.1⁻¹ x.1
        have h₂ := FCone.autMap_inv_smul_autMap_smul φ.2⁻¹ x.2
        rw [inv_inv] at h₁ h₂
        rw [← FCone.autMap_smul, ← FCone.autMap_smul, ← FCone.autMap_smul,
          ← FCone.autMap_smul, h₁, h₂]⟩)

theorem prodAut_smul_mk (φ : GXAut (GSR a) (S a) B₁ × GXAut (GSR b) (S b) B₂)
    (x : FCone a B₁ × FCone b B₂) :
    prodAut φ • (ConeBase.mk x : ProdBase a b B₁ B₂) =
      ConeBase.mk (FCone.autMap φ.1 • x.1, FCone.autMap φ.2 • x.2) := rfl

theorem prodBaseProj_prodAut (φ : GXAut (GSR a) (S a) B₁ × GXAut (GSR b) (S b) B₂)
    (p : ProdBase a b B₁ B₂) :
    prodBaseProj (prodAut φ • p) = (φ.1 • (prodBaseProj p).1, φ.2 • (prodBaseProj p).2) := by
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rw [prodAut_smul_mk, prodBaseProj_mk, prodBaseProj_mk, FCone.proj_autMap_smul,
    FCone.proj_autMap_smul]

/-- **Prop. 3, homogeneous** (for two factors). -/
theorem isHomogeneous_prodBase (h₁ : IsHomogeneous (GSR a) (S a) B₁)
    (h₂ : IsHomogeneous (GSR b) (S b) B₂) :
    IsHomogeneous (GSR (a + b + 1)) (S (a + b + 1)) (ProdBase a b B₁ B₂) := by
  haveI : MulAction.IsPretransitive (GXAut (GSR a) (S a) B₁) B₁ := h₁
  haveI : MulAction.IsPretransitive (GXAut (GSR b) (S b) B₂) B₂ := h₂
  refine ⟨fun p p' => ?_⟩
  obtain ⟨φ₁, hφ₁⟩ := MulAction.exists_smul_eq (GXAut (GSR a) (S a) B₁) (prodBaseProj p).1
    (prodBaseProj p').1
  obtain ⟨φ₂, hφ₂⟩ := MulAction.exists_smul_eq (GXAut (GSR b) (S b) B₂) (prodBaseProj p).2
    (prodBaseProj p').2
  obtain ⟨μ, hμ⟩ := prodBaseProj_eq_iff.1 (show prodBaseProj (prodAut (φ₁, φ₂) • p) =
    prodBaseProj p' by rw [prodBaseProj_prodAut]; exact Prod.ext hφ₁ hφ₂)
  exact ⟨torusAut μ * prodAut (φ₁, φ₂), by rw [mul_smul, torusAut_smul, hμ]⟩

/-- **Prop. 3, sweepable** (for two factors, « Démontrons par exemple que, si les $B_i$ sont
projectivement balayables, … est projectivement balayable »). -/
theorem isBalayable_prodBase (h₁ : IsBalayable (GSR a) (S a) B₁)
    (h₂ : IsBalayable (GSR b) (S b) B₂) :
    IsBalayable (GSR (a + b + 1)) (S (a + b + 1)) (ProdBase a b B₁ B₂) := by
  obtain ⟨K₁, hK₁, hU₁⟩ := h₁
  obtain ⟨K₂, hK₂, hU₂⟩ := h₂
  obtain ⟨L₁, hL₁, hKL₁⟩ := FCone.exists_isCompact_subset_proj_image (n := a) hK₁
  obtain ⟨L₂, hL₂, hKL₂⟩ := FCone.exists_isCompact_subset_proj_image (n := b) hK₂
  refine ⟨ConeBase.mk '' (L₁ ×ˢ L₂), (hL₁.prod hL₂).image ConeBase.continuous_mk,
    eq_univ_of_forall fun p => ?_⟩
  have hp₁ : (prodBaseProj p).1 ∈ ⋃ g ∈ (⊤ : Subgroup (GXAut (GSR a) (S a) B₁)), g • K₁ :=
    hU₁ ▸ mem_univ _
  have hp₂ : (prodBaseProj p).2 ∈ ⋃ g ∈ (⊤ : Subgroup (GXAut (GSR b) (S b) B₂)), g • K₂ :=
    hU₂ ▸ mem_univ _
  obtain ⟨φ₁, -, k₁, hk₁, hk₁p⟩ := mem_iUnion₂.1 hp₁
  obtain ⟨φ₂, -, k₂, hk₂, hk₂p⟩ := mem_iUnion₂.1 hp₂
  obtain ⟨y₁, hy₁, rfl⟩ := hKL₁ hk₁
  obtain ⟨y₂, hy₂, rfl⟩ := hKL₂ hk₂
  obtain ⟨μ, hμ⟩ := prodBaseProj_eq_iff.1
    (show prodBaseProj (prodAut (φ₁, φ₂) • (ConeBase.mk (y₁, y₂) : ProdBase a b B₁ B₂)) =
      prodBaseProj p by rw [prodBaseProj_prodAut]; exact Prod.ext hk₁p hk₂p)
  exact mem_iUnion₂.2 ⟨torusAut μ * prodAut (φ₁, φ₂), Subgroup.mem_top _, _,
    ⟨(y₁, y₂), ⟨hy₁, hy₂⟩, rfl⟩, show (torusAut μ * prodAut (φ₁, φ₂)) • _ = p by
      rw [mul_smul, torusAut_smul, hμ]⟩

/-- `(φ₁, φ₂) ↦ F⁻¹(F(φ₁) × F(φ₂))` as a homomorphism. -/
def prodAutHom : GXAut (GSR a) (S a) B₁ × GXAut (GSR b) (S b) B₂ →*
    GXAut (GSR (a + b + 1)) (S (a + b + 1)) (ProdBase a b B₁ B₂) where
  toFun := prodAut
  map_one' := FaithfulSMul.eq_of_smul_eq_smul fun p : ProdBase a b B₁ B₂ => by
    obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
    rw [prodAut_smul_mk, one_smul, Prod.fst_one, Prod.snd_one, ← FCone.autMapHom_apply,
      ← FCone.autMapHom_apply, map_one, map_one, one_smul, one_smul]
  map_mul' φ ψ := FaithfulSMul.eq_of_smul_eq_smul fun p : ProdBase a b B₁ B₂ => by
    obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
    rw [mul_smul, prodAut_smul_mk, prodAut_smul_mk, prodAut_smul_mk, Prod.fst_mul, Prod.snd_mul,
      ← FCone.autMapHom_apply, ← FCone.autMapHom_apply, map_mul, map_mul, mul_smul, mul_smul]
    rfl

/-- `μ ↦ torusAut μ` as a homomorphism. -/
def torusAutHom : RPos →* GXAut (GSR (a + b + 1)) (S (a + b + 1)) (ProdBase a b B₁ B₂) where
  toFun := torusAut
  map_one' := FaithfulSMul.eq_of_smul_eq_smul fun p : ProdBase a b B₁ B₂ => by
    rw [torusAut_smul, torusMap_one, one_smul]; rfl
  map_mul' μ ν := FaithfulSMul.eq_of_smul_eq_smul fun p : ProdBase a b B₁ B₂ => by
    rw [mul_smul, torusAut_smul, torusAut_smul, torusAut_smul, torusMap_mul]; rfl

theorem commute_prodAut_torusAut (φ : GXAut (GSR a) (S a) B₁ × GXAut (GSR b) (S b) B₂)
    (μ : RPos) : Commute (prodAut φ) (torusAut (a := a) (b := b) (B₁ := B₁) (B₂ := B₂) μ) :=
  FaithfulSMul.eq_of_smul_eq_smul fun p : ProdBase a b B₁ B₂ => by
    obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
    rw [mul_smul, mul_smul, torusAut_smul, torusMap_mk, prodAut_smul_mk, prodAut_smul_mk,
      torusAut_smul, torusMap_mk, FCone.autMap_smul_posSMul]

/-- **The group `F⁻¹(F(G₁) × F(G₂)) × H`** of Prop. 3's proof (`p = 2`, `H = λ^ℤ ⊂ ℝ₊*²/ℝ₊*`). -/
def divProdHom (G₁ : Subgroup (GXAut (GSR a) (S a) B₁)) (G₂ : Subgroup (GXAut (GSR b) (S b) B₂))
    (lam : RPos) : (G₁ × G₂) × Multiplicative ℤ →*
      GXAut (GSR (a + b + 1)) (S (a + b + 1)) (ProdBase a b B₁ B₂) :=
  (prodAutHom.comp (G₁.subtype.prodMap G₂.subtype)).noncommCoprod
    (torusAutHom.comp (zpowersHom RPos lam)) fun _ _ => commute_prodAut_torusAut _ _

theorem divProdHom_smul (G₁ : Subgroup (GXAut (GSR a) (S a) B₁))
    (G₂ : Subgroup (GXAut (GSR b) (S b) B₂)) (lam : RPos) (q : (G₁ × G₂) × Multiplicative ℤ)
    (p : ProdBase a b B₁ B₂) :
    divProdHom G₁ G₂ lam q • p = prodAut ((q.1.1 : GXAut (GSR a) (S a) B₁),
      (q.1.2 : GXAut (GSR b) (S b) B₂)) •
        torusMap a b (FCone a B₁) (FCone b B₂) (lam ^ (Multiplicative.toAdd q.2)) p := by
  rw [divProdHom, MonoidHom.noncommCoprod_apply, mul_smul]
  rfl

theorem prodBaseProj_divProdHom_smul (G₁ : Subgroup (GXAut (GSR a) (S a) B₁))
    (G₂ : Subgroup (GXAut (GSR b) (S b) B₂)) (lam : RPos) (q : (G₁ × G₂) × Multiplicative ℤ)
    (p : ProdBase a b B₁ B₂) :
    prodBaseProj (divProdHom G₁ G₂ lam q • p) =
      (q.1.1 • (prodBaseProj p).1, q.1.2 • (prodBaseProj p).2) := by
  rw [divProdHom_smul, prodBaseProj_prodAut, prodBaseProj_torusMap]; rfl

/-- The radial coordinate of `F⁻¹(F(B₁) × F(B₂))` (paracompact factors): finitely many torus powers
move a compact set to meet another. -/
theorem finite_setOf_torus_inter_nonempty [ParacompactSpace B₁] [ParacompactSpace B₂] {lam : RPos}
    (hlam : lam ≠ 1) {K L : Set (ProdBase a b B₁ B₂)} (hK : IsCompact K) (hL : IsCompact L) :
    {k : ℤ | ((torusMap a b (FCone a B₁) (FCone b B₂) (lam ^ k)) '' K ∩ L).Nonempty}.Finite := by
  obtain ⟨H, -, hH2⟩ := exists_prodBase_homeomorph (a := a) (b := b) (B₁ := B₁) (B₂ := B₂)
  set ρ : ProdBase a b B₁ B₂ → ℝ := fun p => rposLog (H p).2.2
  have hρ : Continuous ρ := continuous_rposLog.comp (continuous_snd.comp (continuous_snd.comp
    H.continuous))
  obtain ⟨r₁, hr₁⟩ := ((hK.image hρ).isBounded).subset_closedBall 0
  obtain ⟨r₂, hr₂⟩ := ((hL.image hρ).isBounded).subset_closedBall 0
  have hl' : 0 < |rposLog lam| := abs_pos.2 (rposLog_ne_zero hlam)
  refine (Set.finite_Icc (-⌈(r₁ + r₂) / |rposLog lam|⌉) ⌈(r₁ + r₂) / |rposLog lam|⌉).subset
    fun k hk => ?_
  obtain ⟨_, ⟨p, hp, rfl⟩, hpL⟩ := hk
  have h1 : |ρ p| ≤ r₁ := by
    simpa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hr₁ ⟨p, hp, rfl⟩
  have h2 : |ρ (torusMap a b (FCone a B₁) (FCone b B₂) (lam ^ k) p)| ≤ r₂ := by
    simpa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hr₂ ⟨_, hpL, rfl⟩
  have h3 : ρ (torusMap a b (FCone a B₁) (FCone b B₂) (lam ^ k) p) = k * rposLog lam + ρ p := by
    simp only [ρ, hH2, rposLog_mul, rposLog_zpow]
  rw [h3] at h2
  have h4 : |(k : ℝ)| * |rposLog lam| ≤ r₁ + r₂ := by
    rw [← abs_mul]
    calc |(k : ℝ) * rposLog lam| = |(k * rposLog lam + ρ p) - ρ p| := by ring_nf
      _ ≤ |k * rposLog lam + ρ p| + |ρ p| := abs_sub _ _
      _ ≤ r₂ + r₁ := add_le_add h2 h1
      _ = r₁ + r₂ := add_comm _ _
  have hk' : |(k : ℝ)| ≤ (r₁ + r₂) / |rposLog lam| := (le_div_iff₀ hl').2 h4
  have hk'' : |k| ≤ ⌈(r₁ + r₂) / |rposLog lam|⌉ := by
    have := hk'.trans (Int.le_ceil _)
    exact_mod_cast this
  exact abs_le.1 hk''

/-- **Prop. 3, divisible** (for two factors; the proof printed): the group
`F⁻¹(F(G₁) × F(G₂)) × λ^ℤ` is properly discontinuous, free, and has compact quotient (« Le quotient …
est une variété localement projective compacte »). -/
theorem isDivisible_divProdHom [ParacompactSpace B₁] [ParacompactSpace B₂]
    (G₁ : Subgroup (GXAut (GSR a) (S a) B₁)) (G₂ : Subgroup (GXAut (GSR b) (S b) B₂))
    (h₁ : ProperlyDiscontinuousSMul G₁ B₁) (h₁' : IsCancelSMul G₁ B₁)
    (h₁'' : CompactSpace (MulAction.orbitRel.Quotient G₁ B₁))
    (h₂ : ProperlyDiscontinuousSMul G₂ B₂) (h₂' : IsCancelSMul G₂ B₂)
    (h₂'' : CompactSpace (MulAction.orbitRel.Quotient G₂ B₂)) {lam : RPos} (hlam : lam ≠ 1) :
    ProperlyDiscontinuousSMul (divProdHom G₁ G₂ lam).range (ProdBase a b B₁ B₂) ∧
      IsCancelSMul (divProdHom G₁ G₂ lam).range (ProdBase a b B₁ B₂) ∧
      CompactSpace (MulAction.orbitRel.Quotient (divProdHom G₁ G₂ lam).range
        (ProdBase a b B₁ B₂)) := by
  have hpc : Continuous (prodBaseProj : ProdBase a b B₁ B₂ → B₁ × B₂) :=
    ((FCone.continuous_baseProj.comp continuous_fst).prodMk
      (FCone.continuous_baseProj.comp continuous_snd)).comp continuous_basePr
  refine ⟨⟨fun {K L} hK hL => ?_⟩, ?_, ?_⟩
  · -- proper discontinuity
    set A₁ := {φ : G₁ | ((φ • ·) '' (Prod.fst '' (prodBaseProj '' K)) ∩
      Prod.fst '' (prodBaseProj '' L)).Nonempty}
    set A₂ := {φ : G₂ | ((φ • ·) '' (Prod.snd '' (prodBaseProj '' K)) ∩
      Prod.snd '' (prodBaseProj '' L)).Nonempty}
    have hA₁ : A₁.Finite := h₁.finite_disjoint_inter_image
      ((hK.image hpc).image continuous_fst) ((hL.image hpc).image continuous_fst)
    have hA₂ : A₂.Finite := h₂.finite_disjoint_inter_image
      ((hK.image hpc).image continuous_snd) ((hL.image hpc).image continuous_snd)
    set Z : G₁ × G₂ → Set ℤ := fun φ => {k : ℤ |
      ((torusMap a b (FCone a B₁) (FCone b B₂) (lam ^ k)) '' K ∩
        ((prodAut ((φ.1 : GXAut (GSR a) (S a) B₁), (φ.2 : GXAut (GSR b) (S b) B₂)))⁻¹ • ·) ''
          L).Nonempty}
    have hZ : ∀ φ, (Z φ).Finite := fun φ => finite_setOf_torus_inter_nonempty hlam hK
      (hL.image (continuous_const_smul _))
    set Pf : Set ((G₁ × G₂) × Multiplicative ℤ) :=
      ⋃ φ ∈ A₁ ×ˢ A₂, {φ} ×ˢ (Multiplicative.ofAdd '' Z φ)
    have hPf : Pf.Finite :=
      (hA₁.prod hA₂).biUnion fun φ _ => (finite_singleton φ).prod ((hZ φ).image _)
    refine (hPf.image fun q => (⟨divProdHom G₁ G₂ lam q, q, rfl⟩ :
      (divProdHom G₁ G₂ lam).range)).subset ?_
    rintro ⟨γ, q, rfl⟩ ⟨_, ⟨x, hx, rfl⟩, hxL⟩
    have hxL' : divProdHom G₁ G₂ lam q • x ∈ L := hxL
    have hpr := prodBaseProj_divProdHom_smul G₁ G₂ lam q x
    have hq₁ : q.1.1 ∈ A₁ := ⟨q.1.1 • (prodBaseProj x).1,
      ⟨(prodBaseProj x).1, ⟨prodBaseProj x, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩,
      ⟨prodBaseProj (divProdHom G₁ G₂ lam q • x), ⟨_, hxL', rfl⟩, by rw [hpr]⟩⟩
    have hq₂ : q.1.2 ∈ A₂ := ⟨q.1.2 • (prodBaseProj x).2,
      ⟨(prodBaseProj x).2, ⟨prodBaseProj x, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩,
      ⟨prodBaseProj (divProdHom G₁ G₂ lam q • x), ⟨_, hxL', rfl⟩, by rw [hpr]⟩⟩
    refine ⟨q, mem_iUnion₂.2 ⟨q.1, ⟨hq₁, hq₂⟩,
      mem_prod.2 ⟨rfl, ⟨Multiplicative.toAdd q.2, ⟨_, ⟨x, hx, rfl⟩, ⟨_, hxL', ?_⟩⟩, rfl⟩⟩⟩, rfl⟩
    show (prodAut ((q.1.1 : GXAut (GSR a) (S a) B₁), (q.1.2 : GXAut (GSR b) (S b) B₂)))⁻¹ •
      divProdHom G₁ G₂ lam q • x = _
    rw [divProdHom_smul, inv_smul_smul]
  · -- freeness
    refine isCancelSMul_iff_eq_one_of_smul_eq.2 ?_
    rintro ⟨γ, q, rfl⟩ x hx
    have hx' : divProdHom G₁ G₂ lam q • x = x := hx
    have hpr := prodBaseProj_divProdHom_smul G₁ G₂ lam q x
    rw [hx', Prod.ext_iff] at hpr
    have e₁ : q.1.1 = 1 := h₁'.eq_one_of_smul (x := (prodBaseProj x).1) hpr.1.symm
    have e₂ : q.1.2 = 1 := h₂'.eq_one_of_smul (x := (prodBaseProj x).2) hpr.2.symm
    rw [divProdHom_smul, e₁, e₂, OneMemClass.coe_one, OneMemClass.coe_one] at hx'
    have hone : prodAut ((1 : GXAut (GSR a) (S a) B₁), (1 : GXAut (GSR b) (S b) B₂)) = 1 :=
      map_one (prodAutHom (a := a) (b := b) (B₁ := B₁) (B₂ := B₂))
    have hx'' : torusMap a b (FCone a B₁) (FCone b B₂) (lam ^ (Multiplicative.toAdd q.2)) x = x := by
      rwa [hone, one_smul] at hx'
    have h2 := eq_one_of_torusMap_eq hx''
    have h3 : Multiplicative.toAdd q.2 = 0 := by
      have := congrArg rposLog h2
      rw [rposLog_zpow, rposLog_one, mul_eq_zero] at this
      exact_mod_cast this.resolve_right (rposLog_ne_zero hlam)
    have hq : q = 1 := Prod.ext (Prod.ext e₁ e₂) (by simpa using h3)
    exact Subtype.ext (show divProdHom G₁ G₂ lam q = 1 by rw [hq, map_one])
  · -- compact quotient
    haveI : ContinuousConstSMul G₁ B₁ :=
      ⟨fun g => continuous_const_smul (g : GXAut (GSR a) (S a) B₁)⟩
    haveI : ContinuousConstSMul G₂ B₂ :=
      ⟨fun g => continuous_const_smul (g : GXAut (GSR b) (S b) B₂)⟩
    haveI := ChartedSpace.locallyCompactSpace (S a) B₁
    haveI := ChartedSpace.locallyCompactSpace (S b) B₂
    obtain ⟨K₁, hK₁, hK₁m⟩ := exists_isCompact_forall_exists_smul_mem h₁''
    obtain ⟨K₂, hK₂, hK₂m⟩ := exists_isCompact_forall_exists_smul_mem h₂''
    obtain ⟨H, hH1, hH2⟩ := exists_prodBase_homeomorph (a := a) (b := b) (B₁ := B₁) (B₂ := B₂)
    set L := rposLog lam
    have hL := rposLog_ne_zero hlam
    set I : Set RPos := (fun t : ℝ => rposExp (t * L)) '' Icc 0 1
    have hI : IsCompact I := isCompact_Icc.image (continuous_rposExp.comp
      (continuous_id.mul continuous_const))
    set K := H.symm '' (K₁ ×ˢ K₂ ×ˢ I)
    have hK : IsCompact K := (hK₁.prod (hK₂.prod hI)).image H.symm.continuous
    have hHpr : ∀ p, ((H p).1, (H p).2.1) = prodBaseProj p := fun p => by
      obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
      rw [(hH1 x).1, (hH1 x).2]; rfl
    refine ⟨?_⟩
    have huniv : (univ : Set (MulAction.orbitRel.Quotient (divProdHom G₁ G₂ lam).range
        (ProdBase a b B₁ B₂))) = Quotient.mk _ '' K := by
      refine (eq_univ_of_forall fun Q => ?_).symm
      obtain ⟨p, rfl⟩ := Quotient.mk_surjective Q
      obtain ⟨γ₁, hγ₁⟩ := hK₁m (prodBaseProj p).1
      obtain ⟨γ₂, hγ₂⟩ := hK₂m (prodBaseProj p).2
      obtain ⟨p₁, hp₁⟩ : ∃ p₁, p₁ = divProdHom G₁ G₂ lam ((γ₁, γ₂), 1) • p := ⟨_, rfl⟩
      obtain ⟨r, hr₀⟩ : ∃ r, r = (H p₁).2.2 := ⟨_, rfl⟩
      obtain ⟨j, hj⟩ : ∃ j : ℤ, j = ⌊rposLog r / L⌋ := ⟨_, rfl⟩
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Int.fract (rposLog r / L) := ⟨_, rfl⟩
      have hr : r = lam ^ j * rposExp (t * L) := by
        refine rposLog_injective ?_
        rw [rposLog_mul, rposLog_zpow, rposLog_rposExp, ← add_mul, hj, ht, Int.floor_add_fract,
          div_mul_cancel₀ _ hL]
      have hp₂ : divProdHom G₁ G₂ lam ((γ₁, γ₂), Multiplicative.ofAdd (-j)) • p =
          torusMap a b (FCone a B₁) (FCone b B₂) (lam ^ (-j)) p₁ := by
        rw [hp₁, divProdHom_smul, divProdHom_smul, toAdd_ofAdd, toAdd_one, zpow_zero, torusMap_one,
          id, ← torusAut_smul, ← torusAut_smul, ← mul_smul, ← mul_smul,
          (commute_prodAut_torusAut _ _).eq]
      have hpp₁ : prodBaseProj p₁ = (γ₁ • (prodBaseProj p).1, γ₂ • (prodBaseProj p).2) := by
        rw [hp₁, prodBaseProj_divProdHom_smul]
      have hHp₂ : H (divProdHom G₁ G₂ lam ((γ₁, γ₂), Multiplicative.ofAdd (-j)) • p) =
          ((prodBaseProj p₁).1, (prodBaseProj p₁).2, rposExp (t * L)) := by
        rw [hp₂, hH2, ← hHpr, ← hr₀, hr, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero,
          one_mul]
      refine ⟨divProdHom G₁ G₂ lam ((γ₁, γ₂), Multiplicative.ofAdd (-j)) • p,
        ⟨H (divProdHom G₁ G₂ lam ((γ₁, γ₂), Multiplicative.ofAdd (-j)) • p), ?_,
          H.symm_apply_apply _⟩, ?_⟩
      · rw [hHp₂, hpp₁]
        exact ⟨hγ₁, hγ₂, ⟨t, ⟨ht ▸ Int.fract_nonneg _, ht ▸ (Int.fract_lt_one _).le⟩, rfl⟩⟩
      · exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨⟨_, _, rfl⟩, rfl⟩)
    rw [huniv]
    exact hK.image continuous_quotient_mk'

/-- **§ 3 Prop. 3, for two factors** (`bzprop:c1s3p3_produit_homogene`): « Soient $B_1, \ldots,
B_p$ des variétés localement projectives homogènes (resp. balayables, resp. divisibles); la variété
localement projective $F^{-1}(F(B_1)\times\ldots\times F(B_p))$ est homogène (resp. balayable, resp.
divisible) », `p = 2`; the divisible case for paracompact factors. -/
theorem prop3_produit_homogene :
    (IsHomogeneous (GSR a) (S a) B₁ → IsHomogeneous (GSR b) (S b) B₂ →
      IsHomogeneous (GSR (a + b + 1)) (S (a + b + 1)) (ProdBase a b B₁ B₂)) ∧
    (IsBalayable (GSR a) (S a) B₁ → IsBalayable (GSR b) (S b) B₂ →
      IsBalayable (GSR (a + b + 1)) (S (a + b + 1)) (ProdBase a b B₁ B₂)) ∧
    (∀ [ParacompactSpace B₁] [ParacompactSpace B₂], IsDivisible (GSR a) (S a) B₁ →
      IsDivisible (GSR b) (S b) B₂ →
      IsDivisible (GSR (a + b + 1)) (S (a + b + 1)) (ProdBase a b B₁ B₂)) := by
  refine ⟨isHomogeneous_prodBase, isBalayable_prodBase, fun h₁ h₂ => ?_⟩
  obtain ⟨G₁, hp₁, hc₁, hq₁⟩ := h₁
  obtain ⟨G₂, hp₂, hc₂, hq₂⟩ := h₂
  exact ⟨_, isDivisible_divProdHom G₁ G₂ hp₁ hc₁ hq₁ hp₂ hc₂ hq₂ rposExp_one_ne_one⟩

end Prop3

/-- **§ 3, corollary of Prop. 3, for two factors**: if `B₁`, `B₂` (Hausdorff, paracompact) carry
locally projective structures of dimensions `a`, `b`, then `B₁ × B₂ × S¹` carries a locally
projective structure (of dimension `a + b + 1`). -/
theorem produit_projectif_two {a b : ℕ} (B₁ B₂ : Type u) [TopologicalSpace B₁] [T2Space B₁]
    [ParacompactSpace B₁] [TopologicalSpace B₂] [T2Space B₂] [ParacompactSpace B₂]
    (h₁ : ∃ cs : ChartedSpace (S a) B₁, @HasGroupoid _ _ B₁ _ cs (projGroupoid a))
    (h₂ : ∃ cs : ChartedSpace (S b) B₂, @HasGroupoid _ _ B₂ _ cs (projGroupoid b)) :
    ∃ cs : ChartedSpace (S (a + b + 1)) (B₁ × B₂ × Circle),
      @HasGroupoid _ _ (B₁ × B₂ × Circle) _ cs (projGroupoid (a + b + 1)) := by
  obtain ⟨cs₁, hcs₁⟩ := h₁
  obtain ⟨cs₂, hcs₂⟩ := h₂
  obtain ⟨-, -, -, -, -, cs, hcs, -⟩ := exists_proj_prod_circle (a := a) (b := b) (B₁ := B₁)
    (B₂ := B₂) rposExp_one_ne_one
  exact ⟨cs, hcs⟩

/-! ### Transport of a structure along a homeomorphism; the general corollary -/

/-- **A `(G, X)`-structure transports along a homeomorphism** (the push-forward along `e`, whose
only deck transformation is the identity). -/
theorem exists_hasGroupoid_of_homeomorph {G : Type*} {X : Type*} [TopologicalSpace X] [Group G]
    [MulAction G X] [ContinuousConstSMul G X] {M : Type*} [TopologicalSpace M] [ChartedSpace X M]
    [HasGroupoid M (gxGroupoid G X)] {N : Type*} [TopologicalSpace N] (e : M ≃ₜ N) :
    ∃ cs : ChartedSpace X N, @HasGroupoid _ _ N _ cs (gxGroupoid G X) := by
  have hdeck : IsGXDeck G X e := by
    intro x x' h
    obtain rfl := e.injective h
    exact ⟨id, continuousAt_id, rfl, Eventually.of_forall fun _ => rfl, 1,
      Eventually.of_forall fun y => (one_smul G _).symm⟩
  obtain ⟨cs, hcs, -, -⟩ := existsUnique_pushforward e.isLocalHomeomorph e.surjective hdeck
  exact ⟨cs, hcs⟩

/-- A projective structure of dimension `d` is one of dimension `d'` when `d = d'`. -/
theorem exists_projStructure_congr {M : Type*} [TopologicalSpace M] {d d' : ℕ} (h : d = d')
    (hM : ∃ cs : ChartedSpace (S d) M, @HasGroupoid _ _ M _ cs (projGroupoid d)) :
    ∃ cs : ChartedSpace (S d') M, @HasGroupoid _ _ M _ cs (projGroupoid d') := by
  subst h; exact hM

/-- `(∀ j, α j) ≃ₜ α i × ∀ j, α (i.succAbove j)` (Mathlib's `Fin.insertNthEquiv`, as a
homeomorphism). -/
def homeomorphInsertNth {q : ℕ} (α : Fin (q + 1) → Type*) [∀ i, TopologicalSpace (α i)]
    (i : Fin (q + 1)) : (α i × ∀ j, α (i.succAbove j)) ≃ₜ ∀ j, α j where
  toEquiv := Fin.insertNthEquiv α i
  continuous_toFun := Continuous.finInsertNth i continuous_fst continuous_snd
  continuous_invFun := (continuous_apply i).prodMk (continuous_pi fun _ => continuous_apply _)

/-- **§ 3, corollary of Prop. 3** (`bzcor:c1s3p3c_produit_projectif`): « Si $p$ variétés $B_i$
peuvent être munies chacune d'une structure localement projective, le produit
$B_1\times\ldots\times B_p\times S_1^{(p-1)}$ peut être muni d'une structure localement
projective », for `p = q + 1` Hausdorff σ-compact (« variété ») factors of dimensions `n i`; the
product has dimension `Σ n i + q`. By induction on `q` from the two-factor case
(`produit_projectif_two`), since `B₁ × … × B_{q+2} × (S¹)^{q+1} ≅ (B₁ × … × B_{q+1} × (S¹)^q) ×
B_{q+2} × S¹`. -/
theorem produit_projectif {q : ℕ} (B : Fin (q + 1) → Type u) [∀ i, TopologicalSpace (B i)]
    [∀ i, T2Space (B i)] [∀ i, SigmaCompactSpace (B i)] (n : Fin (q + 1) → ℕ)
    (h : ∀ i, ∃ cs : ChartedSpace (S (n i)) (B i), @HasGroupoid _ _ (B i) _ cs (projGroupoid (n i))) :
    ∃ cs : ChartedSpace (S (∑ i, n i + q)) ((∀ i, B i) × (Fin q → Circle)),
      @HasGroupoid _ _ ((∀ i, B i) × (Fin q → Circle)) _ cs (projGroupoid (∑ i, n i + q)) := by
  induction q with
  | zero =>
    haveI : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    obtain ⟨cs, hcs⟩ := h (@default (Fin (0 + 1)) Unique.instInhabited)
    have e := (Homeomorph.piUnique B).symm.trans
      (Homeomorph.prodUnique (∀ i, B i) (Fin 0 → Circle)).symm
    refine exists_projStructure_congr (d := n (@default (Fin (0 + 1)) Unique.instInhabited)) ?_
      (exists_hasGroupoid_of_homeomorph e)
    rw [Fin.sum_univ_one, add_zero]
    exact congrArg n (Subsingleton.elim _ _)
  | succ q ih =>
    set i₀ := Fin.last (q + 1)
    set B' : Fin (q + 1) → Type u := fun j => B (i₀.succAbove j)
    obtain ⟨cs', hcs'⟩ := ih B' (fun j => n (i₀.succAbove j)) fun j => h _
    obtain ⟨csl, hcsl⟩ := h i₀
    haveI := ChartedSpace.locallyCompactSpace (S (∑ j, n (i₀.succAbove j) + q))
      ((∀ j, B' j) × (Fin q → Circle))
    haveI := ChartedSpace.locallyCompactSpace (S (n i₀)) (B i₀)
    obtain ⟨cs, hcs⟩ := produit_projectif_two (a := ∑ j, n (i₀.succAbove j) + q) (b := n i₀)
      ((∀ j, B' j) × (Fin q → Circle)) (B i₀) ⟨cs', hcs'⟩ ⟨csl, hcsl⟩
    have e : ((∀ j, B' j) × (Fin q → Circle)) × B i₀ × Circle ≃ₜ
        (∀ i, B i) × (Fin (q + 1) → Circle) :=
      (Homeomorph.prodProdProdComm _ _ _ _).trans
        (Homeomorph.prodCongr ((Homeomorph.prodComm _ _).trans (homeomorphInsertNth B i₀))
          ((Homeomorph.prodComm _ _).trans (homeomorphInsertNth (fun _ => Circle) (Fin.last q))))
    refine exists_projStructure_congr
      (d := (∑ j, n (i₀.succAbove j) + q) + n i₀ + 1) ?_ (exists_hasGroupoid_of_homeomorph e)
    rw [Fin.sum_univ_succAbove n i₀]
    omega

end Benzecri
