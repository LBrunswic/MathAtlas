import BenzecriScaffold.Applications.Products

/-!
# `BenzecriScaffold.Applications.ProductsGeneral` — § 3 Déf. 1, Props. 2–3 for general `p`

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 3, journal pp. 243–245; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`, checked against the scan (PDF pp. 16–18).
Package WP-45x (wave 5b, DEC-128: general `p`, flat block construction). `p = q + 1` factors
`B₀, …, B_q` of dimensions `nᵢ` (`dim F(Bᵢ) = nᵢ + 1`); the base of the product has dimension
`pdim n = Σ nᵢ + q`, the product cone `Σ (nᵢ + 1) = pdim n + 1` (`sum_succ_eq_pdim`).

* **`bzdef:c1s3d1_produit_cones`** — `benzecri1960_ch1.tex:727` (l.727–739, p. 244). **MARKED.**
  `Benzecri.def1_produit_cones_pi`: `F(B₀) × … × F(B_q)` is an affine conical manifold (`PiCone`:
  charts onto `∏ (ℝ^{nᵢ+1} − {O}) ⊂ ℝ^{Σ(nᵢ+1)} − {O}`, `piBlockPt` an open embedding; transitions
  in `∏ GU(nᵢ+1) ↪ GU(Σ(nᵢ+1))`, `piBlockGU`, `det_piBlockGL`), and `ℝ₊*^p` acts by
  `(λᵢ)·(mᵢ) = (λᵢmᵢ)` (`piSMul`) making it a principal bundle over `∏ Bᵢ`: an action, continuous,
  free, orbits = fibres of `piProj`, locally trivial equivariantly (Mathlib `Trivialization`),
  globally trivial for paracompact (e.g. σ-compact) factors; the diagonal is Déf. 3's homothety;
  every `(λᵢ)` is an affine automorphism, a conical one iff `∏ λᵢ^{dim F(Bᵢ)} = 1`.
* **`bzprop:c1s3p2_fibre_produit`** — `benzecri1960_ch1.tex:741` (l.741–759, p. 244). **MARKED**
  (DEC-128: the finding below is against a remark of the proof and does not block the mark).
  `Benzecri.prop2_fibre_produit_pi`: `ℝ^{+p}/ℝ^+` (`PiTorus q`) acts on `F⁻¹(∏ F(Bᵢ))` (`PiBase n B`)
  by projective automorphisms (`piTorusAut`), freely, with orbits the fibres of `piBaseProj` onto
  `∏ Bᵢ`, locally trivially and equivariantly (fibre `ℝ₊*^{p−1}` through `torusCoordEquiv`),
  globally trivially for paracompact factors. **FINDING against the proof's remark** (« On peut
  encore remarquer que $\R^{+p}/\R^+$ se relève suivant le sous-groupe … dont le produit est égal à
  1 »): `not_isGXMorphism_piSMul_of_ne` — when two factors have different dimensions some `(λᵢ)` with
  `∏ λᵢ = 1` is not conical; the corrected lift is `∏ λᵢ^{dim F(Bᵢ)} = 1` (`piLift`, a complement of
  the diagonal, `existsUnique_piLift`), and the printed one is right iff all `F(Bᵢ)` have one
  dimension (`isGXMorphism_piSMul_of_prod_eq_one`). The statement holds as printed.
* **`bzprop:c1s3p3_produit_homogene`** — `benzecri1960_ch1.tex:761` (l.761–795, pp. 244–245).
  **MARKED.** `Benzecri.prop3_produit_homogene_pi`: homogeneous, sweepable, and (paracompact
  factors) divisible, the last with the printed group `F⁻¹(F₁(G₁) × … × F_p(G_p)) × H`,
  `H = λ^{ℤ^{p−1}}` (`piDivHom`).

> **Définition 1.** Soient $p$ variétés localement projectives $B_1$, …, $B_p$; et soit
> $F(B_1)\times\ldots\times F(B_p)$ le cône affin produit des cônes affins de bases les $B_i$. Nous
> munirons ce produit d'une structure d'espace fibré $\R^{+p}$ principal de base
> $B_1\times\ldots\times B_p$ en faisant opérer $\R^{+p}$ sur $F(B_1)\times\ldots\times F(B_p)$
> suivant la formule $(\lambda_1\ldots\lambda_p)\times(m_1\ldots m_p)=(\lambda_1 m_1, \ldots,
> \lambda_p m_p)$, où $\lambda_i\in\R^+$, $m\in F(B_i)$ et $\lambda_i m_i$ désigne l'homothétique de
> $m_i$ dans le rapport $\lambda$.
>
> **Proposition 2.** Le quotient $\R^{+p}/\R^+$ opère sur $F^{-1}(F(B_1)\times\ldots\times F(B_p))$
> et définit sur cette variété localement projective une structure d'espace fibré principal de base
> $(B_1\times\ldots\times B_p)$. *Démonstration.* […] On peut encore remarquer que $\R^{+p}/\R^+$ se
> relève suivant le sous-groupe de $\R^{+p}$ formé des systèmes de $p$ nombres réels positifs dont le
> produit est égal à 1. Un élément de ce sous-groupe définit un automorphisme de la structure conique
> affine du produit des $F(B_i)$ […] Un élément quelconque de $\R^{+p}$ est seulement un
> automorphisme affin de la structure du cône produit.
>
> **Proposition 3.** Soient $B_1$, …, $B_p$ des variétés localement projectives homogènes (resp.
> balayables, resp. divisibles); la variété localement projective
> $F^{-1}(F(B_1)\times\ldots\times F(B_p))$ est homogène (resp. balayable, resp. divisible).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `p` locally projective manifolds, any dimensions | ✓ `p = q + 1 ≥ 1` (`Fin (q + 1)`), dimensions `n i` unconstrained |
| « variété »: Hausdorff | ✓ carried (`[∀ i, T2Space (B i)]`; Déf. 3's homotheties need it) |
| « variété »: second countable | as `[∀ i, ParacompactSpace (B i)]` (implied, strictly weaker), ONLY for global triviality (Déf. 1, Prop. 2) and the divisible case of Prop. 3; σ-compact suffices (`paracompactSpace_of_sigmaCompact`) |
| « variété »: nonempty (DEC-128) | only for « conical iff `∏ λᵢ^{dim F(Bᵢ)} = 1` » (an empty factor makes every map conical) |
| « espace fibré principal » | free action, orbits = fibres, equivariant Mathlib `Trivialization` at every base point |
| `ℝ^{+p}/ℝ^+` | `PiTorus q := (Fin (q+1) → ℝ₊*) ⧸ piDiag q`, `≃* ℝ₊*^{p−1}` (`torusCoordEquiv`) |
| `H` discrete, `(ℝ^{+p}/ℝ^+)/H ≅ S₁^{(p−1)}` (printed « $\R^{+p}/\R^p$ », `[sic]`, read `/\R^+`) | `H = λ^{ℤ^{p−1}}` in torus coordinates (`latticeHom`), any `λ ≠ 1` |

## SCOPE (disclosed)

* **Flat block construction** (DEC-128): one product cone over `Σᵢ Fin (nᵢ+1)` laid end to end
  (`piBlockIdx`, `finSigmaFinEquiv`), `ℝ^{+p}/ℝ^+` acting at once; no induction through binary
  products. The binary `Products` file is kept; its rows are carried here.
* **The product cone's structure is scoped** (`open scoped Benzecri.PiCone`): `∀ i, V i` is a
  Mathlib type, so no global instance is declared on it; `PiBase n B` (an `abbrev`) carries its
  instances, so consumers need not open the scope.
* **The torus action on the base** is `piBaseMap c` (`[m] ↦ [(λᵢmᵢ)]`), a projective morphism through
  the unimodular representative of `c` in `piLift` (`piBaseMap_eq_map`); it factors through
  `PiTorus q` (`piTorusAut`, a homomorphism to the projective automorphisms).
* **Prop. 3, divisible.** Proper discontinuity and the compact quotient use the global radial
  coordinates `exists_piBase_homeomorph` (paracompact factors). That `H` is discrete with compact
  quotient `≅ S₁^{(p−1)}` is the proof's device and is used, not stated separately
  (`finite_setOf_lattice_inter_nonempty` is its discreteness on compacta). The printed proof
  announces the sweepable case and argues the divisible one (flagged in the transcription); all three
  are proved.
* **Readings, not findings**: « $m\in F(B_i)$ » and « rapport $\lambda$ » read `mᵢ`, `λᵢ` (transcription
  comment); `nᵢ` in a product formula of the earlier wave means `dim F(Bᵢ)` (here `nᵢ = dim Bᵢ`).
* Generic lemmas (upstream candidates): `det_piCongrRight_fin` (determinant of a block-diagonal map,
  blocks of different sizes), `piProdHomeomorph`, `trivializationPi`, `trivializationCompHomeomorph`,
  `coneTrivialization_symm_mk`, `paracompactSpace_of_sigmaCompact`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Function Bundle
open scoped Pointwise

namespace Benzecri

universe u

attribute [local instance] t2Space_RnO

/-! ### The determinant of a block-diagonal map, any number of blocks -/

/-- **`det diag(g₀, …, g_{p−1}) = ∏ det gᵢ`**, blocks of arbitrary sizes `k i` (by induction on `p`,
splitting off the first block with `Fin.consLinearEquiv` and `LinearMap.det_prodMap`). -/
theorem det_piCongrRight_fin : ∀ {p : ℕ} {k : Fin p → ℕ}
    (g : ∀ i, (Fin (k i) → ℝ) ≃ₗ[ℝ] (Fin (k i) → ℝ)),
    ((LinearEquiv.det (LinearEquiv.piCongrRight g) : ℝˣ) : ℝ) =
      ∏ i, ((LinearEquiv.det (g i) : ℝˣ) : ℝ)
  | 0, k, g => by
    rw [LinearEquiv.coe_det, LinearMap.det_eq_one_of_subsingleton, Finset.univ_eq_empty,
      Finset.prod_empty]
  | p + 1, k, g => by
    set e := Fin.consLinearEquiv ℝ (fun i => Fin (k i) → ℝ)
    set f := (g 0).prodCongr (LinearEquiv.piCongrRight fun i : Fin p => g (Fin.succ i))
    have key : (e.symm.trans f).trans e = LinearEquiv.piCongrRight g := by
      refine LinearEquiv.ext fun x => funext fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [e, f]
      · simp [e, f]
        rfl
    have hf : f.toLinearMap = LinearMap.prodMap (g 0).toLinearMap
        (LinearEquiv.piCongrRight fun i : Fin p => g (Fin.succ i)).toLinearMap := rfl
    rw [← key, LinearEquiv.det_conj, LinearEquiv.coe_det, hf, LinearMap.det_prodMap, ← LinearEquiv.coe_det, ← LinearEquiv.coe_det,
      det_piCongrRight_fin (fun i : Fin p => g (Fin.succ i)), Fin.prod_univ_succ]

/-! ### Blocks: `∏ ℝ^{nᵢ+1} ≃ ℝ^{Σ(nᵢ+1)}` and `∏ GU(nᵢ+1) ↪ GU(Σ(nᵢ+1))` -/

section PiBlock

variable {q : ℕ} (n : Fin (q + 1) → ℕ)

/-- **The dimension of the base of the product of `p = q + 1` cones** `F(B₀), …, F(B_q)` with
`dim Bᵢ = nᵢ`: `Σ nᵢ + (p − 1)`; the product cone has dimension `Σ (nᵢ + 1) = pdim n + 1`
(`sum_succ_eq_pdim`). -/
def pdim : ℕ := ∑ i, n i + q

theorem sum_succ_eq_pdim : ∑ i, (n i + 1) = pdim n + 1 := by
  simp only [pdim, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]
  omega

/-- The coordinates of `ℝ^{Σ(nᵢ+1)}` as the disjoint union of the blocks. -/
def piBlockIdx : Fin (pdim n + 1) ≃ (Σ i, Fin (n i + 1)) :=
  (finCongr (sum_succ_eq_pdim n).symm).trans finSigmaFinEquiv.symm

/-- **The block decomposition `∏ᵢ ℝ^{nᵢ+1} ≃ₗ ℝ^{Σ(nᵢ+1)}`** (the blocks laid end to end). -/
def piBlockEquiv : (∀ i, Fin (n i + 1) → ℝ) ≃ₗ[ℝ] (Fin (pdim n + 1) → ℝ) :=
  (LinearEquiv.piCurry ℝ (fun (i : Fin (q + 1)) (_ : Fin (n i + 1)) => ℝ)).symm ≪≫ₗ
    LinearEquiv.funCongrLeft ℝ ℝ (piBlockIdx n)

variable {n}

/-- **The block-diagonal automorphism** `diag(g₀, …, g_q)` of `ℝ^{Σ(nᵢ+1)}`. -/
def piBlockGL (g : ∀ i, GLR (n i + 1)) : GLR (pdim n + 1) :=
  ((piBlockEquiv n).symm.trans (LinearEquiv.piCongrRight g)).trans (piBlockEquiv n)

theorem piBlockGL_apply (g : ∀ i, GLR (n i + 1)) (v : ∀ i, Fin (n i + 1) → ℝ) :
    piBlockGL g (piBlockEquiv n v) = piBlockEquiv n (fun i => g i (v i)) := by
  simp only [piBlockGL, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- **The determinant multiplies** (« $\prod GU(n_i) \hookrightarrow GU(\sum n_i)$ »). -/
theorem det_piBlockGL (g : ∀ i, GLR (n i + 1)) :
    ((LinearEquiv.det (piBlockGL g) : ℝˣ) : ℝ) = ∏ i, ((LinearEquiv.det (g i) : ℝˣ) : ℝ) := by
  rw [piBlockGL, LinearEquiv.det_conj]
  exact det_piCongrRight_fin g

theorem piBlockGL_mul (g h : ∀ i, GLR (n i + 1)) :
    piBlockGL (g * h) = piBlockGL g * piBlockGL h := by
  refine LinearEquiv.ext fun x => ?_
  simp only [piBlockGL, LinearEquiv.mul_apply, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  rfl

theorem piBlockGL_one : piBlockGL (1 : ∀ i, GLR (n i + 1)) = 1 := by
  refine LinearEquiv.ext fun x => ?_
  exact (piBlockEquiv n).apply_symm_apply x

/-- **`∏ GU(nᵢ+1) ↪ GU(Σ(nᵢ+1))`, block-diagonally.** -/
def piBlockGU : (∀ i, GUR (n i + 1)) →* GUR (pdim n + 1) where
  toFun g := ⟨piBlockGL fun i => (g i : GLR (n i + 1)), by
    rw [mem_GU, det_piBlockGL, Finset.abs_prod]
    exact Finset.prod_eq_one fun i _ => mem_GU.1 (g i).2⟩
  map_one' := Subtype.ext piBlockGL_one
  map_mul' g h := Subtype.ext (piBlockGL_mul (fun i => (g i : GLR (n i + 1))) fun i => h i)

@[simp] theorem coe_piBlockGU (g : ∀ i, GUR (n i + 1)) :
    ((piBlockGU g : GUR (pdim n + 1)) : GLR (pdim n + 1)) =
      piBlockGL fun i => (g i : GLR (n i + 1)) := rfl

/-- **`∏ GU(nᵢ+1) ↪ GU(Σ(nᵢ+1))` is injective** (« $\prod GU(n_i) \hookrightarrow GU(\sum n_i)$ »). -/
theorem piBlockGU_injective : Injective (piBlockGU (n := n)) := by
  intro g h hgh
  have hGL : piBlockGL (fun i => (g i : GLR (n i + 1))) = piBlockGL fun i => (h i : GLR (n i + 1)) :=
    congrArg Subtype.val hgh
  funext i
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  have key := congrArg (fun L : GLR (pdim n + 1) =>
    L (piBlockEquiv n (Pi.single (M := fun j => Fin (n j + 1) → ℝ) i v))) hGL
  simp only [piBlockGL_apply] at key
  have := congrFun ((piBlockEquiv n).injective key) i
  simpa using this

theorem piBlockEquiv_ne_zero {v : ∀ i, Fin (n i + 1) → ℝ} (i : Fin (q + 1)) (hv : v i ≠ 0) :
    piBlockEquiv n v ≠ 0 := by
  intro h
  apply hv
  rw [(piBlockEquiv n).injective (h.trans (map_zero _).symm)]
  rfl

/-- **The inclusion `∏ (ℝ^{nᵢ+1} − {O}) ⊂ ℝ^{Σ(nᵢ+1)} − {O}`** (Déf. 1, « le cône affin produit »). -/
def piBlockPt (x : ∀ i, RnO (n i + 1)) : RnO (pdim n + 1) :=
  ⟨piBlockEquiv n (fun i => (x i).val), piBlockEquiv_ne_zero 0 (x 0).val_ne_zero⟩

@[simp] theorem val_piBlockPt (x : ∀ i, RnO (n i + 1)) :
    (piBlockPt x).val = piBlockEquiv n (fun i => (x i).val) := rfl

theorem piBlockPt_injective : Injective (piBlockPt : (∀ i, RnO (n i + 1)) → RnO (pdim n + 1)) :=
  fun _ _ h => funext fun i => Punctured.val_injective
    (congrFun ((piBlockEquiv n).injective (congrArg Punctured.val h)) i)

/-- The diagonal homotheties: `(λmᵢ)ᵢ ↦ λ(mᵢ)ᵢ`. -/
theorem piBlockPt_smul_pos (c : RPos) (x : ∀ i, RnO (n i + 1)) :
    piBlockPt (fun i => c • x i) = c • piBlockPt x := by
  refine Punctured.val_injective ?_
  simp only [val_piBlockPt, Punctured.val_smul_pos]
  rw [← map_smul]
  rfl

/-- `piBlockPt` is equivariant through `piBlockGU`. -/
theorem piBlockPt_smul_GU (g : ∀ i, GUR (n i + 1)) (x : ∀ i, RnO (n i + 1)) :
    piBlockPt (fun i => g i • x i) = piBlockGU g • piBlockPt x := by
  refine Punctured.val_injective ?_
  simp only [val_piBlockPt, Punctured.val_smul_sub, coe_piBlockGU, piBlockGL_apply]

/-- The block homothety `(mᵢ) ↦ (λᵢmᵢ)` as an element of `GL(Σ(nᵢ+1))`. -/
theorem piBlockPt_smul_pos_pi (c : Fin (q + 1) → RPos) (x : ∀ i, RnO (n i + 1)) :
    piBlockPt (fun i => c i • x i) =
      piBlockGL (fun i => homothety (Fin (n i + 1) → ℝ) (c i : ℝˣ)) • piBlockPt x := by
  refine Punctured.val_injective ?_
  simp only [val_piBlockPt, Punctured.val_smul_pos, Punctured.val_smul_lin, piBlockGL_apply,
    homothety_apply]

theorem continuous_piBlockPt :
    Continuous (piBlockPt : (∀ i, RnO (n i + 1)) → RnO (pdim n + 1)) := by
  refine continuous_induced_rng.2 ?_
  exact (LinearMap.continuous_of_finiteDimensional (piBlockEquiv n).toLinearMap).comp
    (continuous_pi fun i => Punctured.continuous_val.comp (continuous_apply i))

/-- **`piBlockPt` is an open embedding.** -/
theorem isOpenEmbedding_piBlockPt :
    IsOpenEmbedding (piBlockPt : (∀ i, RnO (n i + 1)) → RnO (pdim n + 1)) := by
  have hL : IsOpenEmbedding (piBlockEquiv n) :=
    ((piBlockEquiv n).toContinuousLinearEquiv.toHomeomorph).isOpenEmbedding
  have h1 : IsOpenEmbedding (Pi.map fun i => (Punctured.val : RnO (n i + 1) → _)) :=
    IsOpenEmbedding.piMap fun _ => Punctured.isOpenEmbedding_val
  have h2 : IsOpenEmbedding (Punctured.val ∘ piBlockPt (n := n)) := hL.comp h1
  exact (IsOpenEmbedding.of_comp_iff _ Punctured.isOpenEmbedding_val).1 h2

end PiBlock

/-! ### Déf. 1 — the product of `p` affine conical manifolds -/

section PiConeDef

variable {q : ℕ} {n : Fin (q + 1) → ℕ}

variable (n) in
/-- `piBlockPt` as an open partial homeomorphism (source everything). -/
def piBlockOPH : OpenPartialHomeomorph (∀ i, RnO (n i + 1)) (RnO (pdim n + 1)) :=
  isOpenEmbedding_piBlockPt.toOpenPartialHomeomorph _

@[simp] theorem piBlockOPH_apply (x : ∀ i, RnO (n i + 1)) : piBlockOPH n x = piBlockPt x := rfl

@[simp] theorem piBlockOPH_source : (piBlockOPH n).source = univ := by
  simp [piBlockOPH]

@[simp] theorem piBlockOPH_target : (piBlockOPH n).target = range piBlockPt := by
  simp [piBlockOPH]

theorem piBlockOPH_symm_piBlockPt (x : ∀ i, RnO (n i + 1)) :
    (piBlockOPH n).symm (piBlockPt x) = x :=
  (piBlockOPH n).left_inv (by simp)

variable {V : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (V i)]

variable (n) in
/-- **The product chart** `(mᵢ) ↦ (eᵢ(mᵢ)) ∈ ℝ^{Σ(nᵢ+1)} − {O}`. -/
def piChart (e : ∀ i, OpenPartialHomeomorph (V i) (RnO (n i + 1))) :
    OpenPartialHomeomorph (∀ i, V i) (RnO (pdim n + 1)) :=
  (OpenPartialHomeomorph.pi e).trans (piBlockOPH n)

variable {e : ∀ i, OpenPartialHomeomorph (V i) (RnO (n i + 1))}

@[simp] theorem piChart_apply (x : ∀ i, V i) : piChart n e x = piBlockPt fun i => e i (x i) := rfl

@[simp] theorem piChart_source : (piChart n e).source = univ.pi fun i => (e i).source := by
  simp [piChart, OpenPartialHomeomorph.pi_toPartialEquiv]

theorem piChart_target :
    (piChart n e).target = piBlockPt '' (univ.pi fun i => (e i).target) := by
  ext y
  simp only [piChart, OpenPartialHomeomorph.trans_target, piBlockOPH_target, mem_inter_iff,
    mem_range, mem_preimage, mem_image]
  constructor
  · rintro ⟨⟨x, rfl⟩, hx⟩
    rw [piBlockOPH_symm_piBlockPt] at hx
    exact ⟨x, by simpa [OpenPartialHomeomorph.pi_toPartialEquiv] using hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, by rw [piBlockOPH_symm_piBlockPt]; simpa
      [OpenPartialHomeomorph.pi_toPartialEquiv] using hx⟩

theorem piChart_symm_piBlockPt (x : ∀ i, RnO (n i + 1)) :
    (piChart n e).symm (piBlockPt x) = fun i => (e i).symm (x i) := by
  simp only [piChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.coe_trans, comp_apply, piBlockOPH_symm_piBlockPt]
  rfl

variable [∀ i, ChartedSpace (RnO (n i + 1)) (V i)]

variable (n V) in
/-- **Déf. 1: the conical charted space of a product of `p` cones** (« le cône affin produit des
cônes affins »): the charts are the product charts `(eᵢ)` composed with `piBlockPt`, onto subsets of
`∏ (ℝ^{nᵢ+1} − {O}) ⊂ ℝ^{Σ(nᵢ+1)} − {O}`. A reducible `def`; a SCOPED instance below (namespace
`Benzecri.PiCone`), since `∀ i, V i` is a Mathlib type. -/
@[reducible] def piConeChartedSpace : ChartedSpace (RnO (pdim n + 1)) (∀ i, V i) where
  atlas := {E | ∃ e : ∀ i, OpenPartialHomeomorph (V i) (RnO (n i + 1)),
    (∀ i, e i ∈ atlas (RnO (n i + 1)) (V i)) ∧ E = piChart n e}
  chartAt x := piChart n fun i => chartAt (RnO (n i + 1)) (x i)
  mem_chart_source x := by
    rw [piChart_source]
    exact fun i _ => mem_chart_source _ (x i)
  chart_mem_atlas x := ⟨_, fun i => chart_mem_atlas _ (x i), rfl⟩

end PiConeDef

namespace PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {V : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (V i)]
  [∀ i, ChartedSpace (RnO (n i + 1)) (V i)]

/-- The conical charted space of `∏ V i` (Déf. 1), scoped to `Benzecri.PiCone`. -/
scoped instance instChartedSpace : ChartedSpace (RnO (pdim n + 1)) (∀ i, V i) :=
  piConeChartedSpace n V

theorem chartAt_eq (x : ∀ i, V i) :
    chartAt (RnO (pdim n + 1)) x = piChart n fun i => chartAt (RnO (n i + 1)) (x i) := rfl

variable [∀ i, HasGroupoid (V i) (coneGroupoid (n i + 1))]

/-- **The product of affine conical manifolds is an affine conical manifold** (Déf. 1, « $\prod
GU(n_i) \hookrightarrow GU(\sum n_i)$ »): the transition between two product charts is, near every
point, `diag(g₀, …, g_q)` where the factors' transitions are the `gᵢ`. -/
scoped instance instHasGroupoid : HasGroupoid (∀ i, V i) (coneGroupoid (pdim n + 1)) where
  compatible {E E'} hE hE' := by
    obtain ⟨e, he, rfl⟩ := hE
    obtain ⟨e', he', rfl⟩ := hE'
    refine symm_trans_mem_gxGroupoid fun x hx => ?_
    rw [piChart_source, piChart_source] at hx
    have key : ∀ i, ∃ g : GUR (n i + 1), ∀ᶠ z in 𝓝 (x i), e' i z = g • e i z := fun i =>
      eventually_smul_eq_of_mem_gxGroupoid
        (HasGroupoid.compatible (G := coneGroupoid (n i + 1)) (he i) (he' i))
        (hx.1 i trivial) (hx.2 i trivial)
    choose g hg using key
    refine ⟨piBlockGU g, ?_⟩
    filter_upwards [Filter.eventually_all.2 fun i => (continuous_apply i).continuousAt.eventually
      (hg i)] with z hz
    rw [piChart_apply, piChart_apply, ← piBlockPt_smul_GU]
    exact congrArg piBlockPt (funext hz)

/-- **A product of maximal-atlas charts is in the maximal atlas.** -/
theorem piChart_mem_maximalAtlas {e : ∀ i, OpenPartialHomeomorph (V i) (RnO (n i + 1))}
    (he : ∀ i, e i ∈ (coneGroupoid (n i + 1)).maximalAtlas (V i)) :
    piChart n e ∈ (coneGroupoid (pdim n + 1)).maximalAtlas (∀ i, V i) := by
  rw [mem_maximalAtlas_iff_eventually]
  intro x hx
  rw [piChart_source] at hx
  have key : ∀ i, ∃ g : GUR (n i + 1), ∀ᶠ z in 𝓝 (x i),
      e i z = g • chartAt (RnO (n i + 1)) (x i) z := fun i =>
    (mem_maximalAtlas_iff_eventually.1 (he i)) (x i) (hx i trivial)
  choose g hg using key
  refine ⟨piBlockGU g, ?_⟩
  filter_upwards [Filter.eventually_all.2 fun i => (continuous_apply i).continuousAt.eventually
    (hg i)] with z hz
  rw [piChart_apply, chartAt_eq, piChart_apply, ← piBlockPt_smul_GU]
  exact congrArg piBlockPt (funext hz)

/-- **A product of cone charts is a cone chart.** -/
theorem isConeChart_piChart {e : ∀ i, OpenPartialHomeomorph (V i) (RnO (n i + 1))}
    (he : ∀ i, IsConeChart (n i + 1) (e i)) : IsConeChart (pdim n + 1) (piChart n e) := by
  refine ⟨piChart_mem_maximalAtlas fun i => (he i).1, ?_, ?_⟩
  · rw [piChart_target]
    exact isOpenEmbedding_piBlockPt.isOpenMap _
      (isOpen_set_pi finite_univ fun i _ => (he i).2.1)
  · intro c v hv
    rw [piChart_target] at hv ⊢
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨fun i => c • x i, fun i _ => (he i).2.2 c _ (hx i trivial), piBlockPt_smul_pos c x⟩

variable [∀ i, HasConeCharts (n i + 1) (V i)]

/-- **The product has cone charts** (Déf. 2, 3°). -/
scoped instance instHasConeCharts : HasConeCharts (pdim n + 1) (∀ i, V i) where
  exists_isConeChart x := ⟨piChart n fun i => coneChartAt (n i + 1) (x i),
    isConeChart_piChart fun i => isConeChart_coneChartAt (x i),
    by rw [piChart_source]; exact fun i _ => mem_coneChartAt_source (x i)⟩

variable [∀ i, T2Space (V i)]

/-- **The homotheties of the product are the diagonal ones** (Déf. 1 on the diagonal): Déf. 3's
action on `∏ V i` is `λ(mᵢ) = (λmᵢ)`. -/
theorem posSMul_pi (c : RPos) (x : ∀ i, V i) :
    posSMul (pdim n + 1) c x = fun i => posSMul (n i + 1) c (x i) := by
  have he := fun i => isConeChart_coneChartAt (n := n i + 1) (x i)
  have hx := fun i => mem_coneChartAt_source (n := n i + 1) (x i)
  have hE := isConeChart_piChart he
  rw [posSMul_eq hE (by rw [piChart_source]; exact fun i _ => hx i), piChart_apply,
    ← piBlockPt_smul_pos, piChart_symm_piBlockPt]
  funext i
  rw [posSMul_eq (he i) (hx i)]

omit [∀ i, HasGroupoid (V i) (coneGroupoid (n i + 1))] [∀ i, HasConeCharts (n i + 1) (V i)]
  [∀ i, T2Space (V i)] in
/-- **A product of conical morphisms is a conical morphism of the products** (Prop. 3's proof): it
reads as `diag(g₀, …, g_q)` in product charts. -/
theorem isGXMorphism_piMap {W : Fin (q + 1) → Type*} [∀ i, TopologicalSpace (W i)]
    [∀ i, ChartedSpace (RnO (n i + 1)) (W i)] {f : ∀ i, V i → W i}
    (hf : ∀ i, IsGXMorphism (GUR (n i + 1)) (RnO (n i + 1)) (f i)) :
    IsGXMorphism (GUR (pdim n + 1)) (RnO (pdim n + 1)) (Pi.map f) := by
  refine ⟨continuous_pi fun i => (hf i).continuous.comp (continuous_apply i), fun x => ?_⟩
  have key := fun i => (hf i).exists_smul_eq (x i)
  choose g hg using key
  refine ⟨piBlockGU g, ?_⟩
  filter_upwards [Filter.eventually_all.2 fun i => (continuous_apply i).continuousAt.eventually
    (hg i)] with y hy
  rw [chartAt_eq, chartAt_eq, piChart_apply, piChart_apply, ← piBlockPt_smul_GU]
  exact congrArg piBlockPt (funext hy)

end PiCone

/-! ### Generic: products of trivialisations, and a change of base -/

section TrivGeneric

variable {ι : Type*} [Fintype ι] {Z B F : ι → Type*} [∀ i, TopologicalSpace (Z i)]
  [∀ i, TopologicalSpace (B i)] [∀ i, TopologicalSpace (F i)]

/-- `∏ (Bᵢ × Fᵢ) ≃ₜ (∏ Bᵢ) × (∏ Fᵢ)`. -/
def piProdHomeomorph : (∀ i, B i × F i) ≃ₜ (∀ i, B i) × (∀ i, F i) where
  toEquiv := Equiv.arrowProdEquivProdArrow ι B F
  continuous_toFun := (continuous_pi fun i => (continuous_apply i).fst).prodMk
    (continuous_pi fun i => (continuous_apply i).snd)
  continuous_invFun := continuous_pi fun i => ((continuous_apply i).comp continuous_fst).prodMk
    ((continuous_apply i).comp continuous_snd)

/-- **A finite product of local trivialisations is a local trivialisation of the product**
(fibre `∏ Fᵢ`, base set `∏ Uᵢ`). -/
def trivializationPi {proj : ∀ i, Z i → B i} (T : ∀ i, Trivialization (F i) (proj i)) :
    Trivialization (∀ i, F i) (fun (z : ∀ i, Z i) i => proj i (z i)) where
  toOpenPartialHomeomorph := (OpenPartialHomeomorph.pi fun i => (T i).toOpenPartialHomeomorph).trans
    (piProdHomeomorph (B := B) (F := F)).toOpenPartialHomeomorph
  baseSet := univ.pi fun i => (T i).baseSet
  open_baseSet := isOpen_set_pi finite_univ fun i _ => (T i).open_baseSet
  source_eq := by
    ext z
    simp [OpenPartialHomeomorph.pi_toPartialEquiv, Trivialization.mem_source]
  target_eq := by
    ext ⟨b, f⟩
    simp [OpenPartialHomeomorph.pi_toPartialEquiv, piProdHomeomorph, Trivialization.mem_target]
  proj_toFun z hz := by
    funext i
    have hz' : z i ∈ (T i).source :=
      (by simpa [OpenPartialHomeomorph.pi_toPartialEquiv] using hz : ∀ j, z j ∈ (T j).source) i
    exact (T i).proj_toFun _ hz'

theorem trivializationPi_apply {proj : ∀ i, Z i → B i} (T : ∀ i, Trivialization (F i) (proj i))
    (z : ∀ i, Z i) : trivializationPi T z = (fun i => (T i (z i)).1, fun i => (T i (z i)).2) := rfl

theorem mem_trivializationPi_source {proj : ∀ i, Z i → B i}
    (T : ∀ i, Trivialization (F i) (proj i)) {z : ∀ i, Z i} :
    z ∈ (trivializationPi T).source ↔ ∀ i, z i ∈ (T i).source := by
  simp [trivializationPi, OpenPartialHomeomorph.pi_toPartialEquiv]

end TrivGeneric

/-- **A local trivialisation composed with a homeomorphism of the base.** -/
def trivializationCompHomeomorph {Z B B' F : Type*} [TopologicalSpace Z] [TopologicalSpace B]
    [TopologicalSpace B'] [TopologicalSpace F] {proj : Z → B} (T : Trivialization F proj)
    (h : B ≃ₜ B') : Trivialization F (h ∘ proj) where
  toOpenPartialHomeomorph := T.toOpenPartialHomeomorph.trans
    (h.prodCongr (Homeomorph.refl F)).toOpenPartialHomeomorph
  baseSet := h.symm ⁻¹' T.baseSet
  open_baseSet := T.open_baseSet.preimage h.symm.continuous
  source_eq := by
    ext z
    simp [T.source_eq]
  target_eq := by
    ext ⟨b, f⟩
    simp [T.target_eq]
  proj_toFun z hz := by
    have hz' : z ∈ T.source := by simpa using hz
    simp only [OpenPartialHomeomorph.coe_trans, Homeomorph.toOpenPartialHomeomorph_apply,
      comp_apply]
    exact congrArg h (T.proj_toFun z hz')

theorem trivializationCompHomeomorph_apply {Z B B' F : Type*} [TopologicalSpace Z]
    [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace F] {proj : Z → B}
    (T : Trivialization F proj) (h : B ≃ₜ B') (z : Z) :
    trivializationCompHomeomorph T h z = (h (T z).1, (T z).2) := rfl

theorem trivializationCompHomeomorph_source {Z B B' F : Type*} [TopologicalSpace Z]
    [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace F] {proj : Z → B}
    (T : Trivialization F proj) (h : B ≃ₜ B') :
    (trivializationCompHomeomorph T h).source = T.source := by
  simp [trivializationCompHomeomorph]

/-! ### Déf. 1 — the `ℝ₊*^p`-action on the product cone and its principal-bundle structure -/

section PiAction

open PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {V : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (V i)]
  [∀ i, ChartedSpace (RnO (n i + 1)) (V i)] [∀ i, HasConeCharts (n i + 1) (V i)]
  [∀ i, T2Space (V i)]

variable (n) in
/-- **The action of `(λᵢ) ∈ ℝ₊*^p` on the product cone** (Déf. 1, « $(\lambda_1 \ldots \lambda_p)
\times (m_1 \ldots m_p) = (\lambda_1 m_1, \ldots, \lambda_p m_p)$ »). -/
def piSMul (c : Fin (q + 1) → RPos) (x : ∀ i, V i) : ∀ i, V i :=
  fun i => posSMul (n i + 1) (c i) (x i)

omit [∀ i, T2Space (V i)] in
@[simp] theorem piSMul_apply (c : Fin (q + 1) → RPos) (x : ∀ i, V i) (i : Fin (q + 1)) :
    piSMul n c x i = posSMul (n i + 1) (c i) (x i) := rfl

theorem piSMul_one (x : ∀ i, V i) : piSMul n 1 x = x := funext fun _ => posSMul_one _

theorem piSMul_mul (c d : Fin (q + 1) → RPos) (x : ∀ i, V i) :
    piSMul n (c * d) x = piSMul n c (piSMul n d x) := funext fun _ => posSMul_mul _ _ _

theorem continuous_piSMul :
    Continuous fun p : (Fin (q + 1) → RPos) × (∀ i, V i) => piSMul n p.1 p.2 :=
  continuous_pi fun i => (continuous_posSMul (n := n i + 1)).comp
    (((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd) :
      Continuous fun a : (Fin (q + 1) → RPos) × (∀ i, V i) => (a.1 i, a.2 i))

theorem continuous_piSMul_const (c : Fin (q + 1) → RPos) :
    Continuous (piSMul n c : (∀ i, V i) → ∀ i, V i) :=
  continuous_piSMul.comp (continuous_const.prodMk continuous_id)

/-- **The action is free** (« espace fibré principal »). -/
theorem eq_one_of_piSMul_eq {c : Fin (q + 1) → RPos} {x : ∀ i, V i} (h : piSMul n c x = x) :
    c = 1 :=
  funext fun i => eq_one_of_posSMul_eq (congrFun h i)

variable (n V) in
/-- **The projection of the product cone onto the product of the bases**, `(mᵢ) ↦ ([mᵢ])`. -/
def piMk (x : ∀ i, V i) : ∀ i, ConeBase (n i) (V i) := fun i => ConeBase.mk (x i)

theorem continuous_piMk : Continuous (piMk n V) :=
  continuous_pi fun i => ConeBase.continuous_mk.comp (continuous_apply i)

theorem piMk_surjective : Surjective (piMk n V) := fun b =>
  ⟨fun i => (ConeBase.mk_surjective (b i)).choose,
    funext fun i => (ConeBase.mk_surjective (b i)).choose_spec⟩

@[simp] theorem piMk_piSMul (c : Fin (q + 1) → RPos) (x : ∀ i, V i) :
    piMk n V (piSMul n c x) = piMk n V x :=
  funext fun _ => ConeBase.mk_posSMul _ _

/-- **The fibres of `piMk` are the orbits of `ℝ₊*^p`.** -/
theorem piMk_eq_iff {x x' : ∀ i, V i} :
    piMk n V x = piMk n V x' ↔ ∃ c : Fin (q + 1) → RPos, piSMul n c x = x' := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ => hc ▸ (piMk_piSMul c x).symm⟩
  have key : ∀ i, ∃ c : RPos, posSMul (n i + 1) c (x' i) = x i := fun i =>
    ConeBase.mk_eq_mk_iff.1 (congrFun h i)
  choose c hc using key
  exact ⟨c⁻¹, funext fun i => by
    rw [piSMul_apply, Pi.inv_apply, ← hc i, posSMul_inv_posSMul]⟩

variable [∀ i, HasGroupoid (V i) (coneGroupoid (n i + 1))]

/-- **The diagonal of `ℝ₊*^p` acts by Déf. 3's homotheties of the product cone.** -/
theorem piSMul_const (c : RPos) (x : ∀ i, V i) :
    piSMul n (fun _ => c) x = posSMul (pdim n + 1) c x := (posSMul_pi c x).symm

/-- **« Un élément quelconque de $\R^{+p}$ est seulement un automorphisme affin de la structure du
cône produit »**: every `piSMul n c` is a morphism of the canonical locally affine structure of the
product cone; in the charts `ι ∘ e` it is the block homothety `diag(λ₀, …, λ_q) ∈ GL ⊂ GA`. -/
theorem isGXMorphism_affine_piSMul (c : Fin (q + 1) → RPos) :
    @IsGXMorphism (GAR (pdim n + 1)) (Fin (pdim n + 1) → ℝ) _ _ _ (∀ i, V i) _ (∀ i, V i) _
      (affineChartedSpace (pdim n + 1) (∀ i, V i)) (affineChartedSpace (pdim n + 1) (∀ i, V i))
      (piSMul n c) := by
  letI := affineChartedSpace (pdim n + 1) (∀ i, V i)
  haveI := hasGroupoid_affineChartedSpace (pdim n + 1) (V := ∀ i, V i)
  refine isGXMorphism_of_mem_maximalAtlas (continuous_piSMul_const c) fun x => ?_
  have he := fun i => isConeChart_coneChartAt (n := n i + 1) (x i)
  have hx := fun i => mem_coneChartAt_source (n := n i + 1) (x i)
  have hE := isConeChart_piChart he
  have hxE : x ∈ (piChart n fun i => coneChartAt (n i + 1) (x i)).source := by
    rw [piChart_source]; exact fun i _ => hx i
  have hsrc : ∀ e : OpenPartialHomeomorph (∀ i, V i) (RnO (pdim n + 1)), (e.trans
      ((Punctured.isOpenEmbedding_val (E := Fin (pdim n + 1) → ℝ)).toOpenPartialHomeomorph _)).source =
      e.source := by
    intro e
    simp only [OpenPartialHomeomorph.trans_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
  refine ⟨_, trans_mem_maximalAtlas_affine (pdim n + 1) hE.1, _,
    trans_mem_maximalAtlas_affine (pdim n + 1) hE.1, by rw [hsrc]; exact hxE, by
      rw [hsrc, piChart_source]; exact fun i _ => (he i).smul_mem_source (hx i) (c i),
    (piBlockGL fun i => homothety (Fin (n i + 1) → ℝ) (c i : ℝˣ)).toAffineEquiv, ?_⟩
  filter_upwards [(piChart n fun i => coneChartAt (n i + 1) (x i)).open_source.mem_nhds hxE]
    with y hy
  rw [piChart_source] at hy
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply, affineEquiv_smul_def,
    LinearEquiv.coe_toAffineEquiv, piChart_apply, piSMul_apply]
  have : (fun i => coneChartAt (n i + 1) (x i) (posSMul (n i + 1) (c i) (y i))) =
      fun i => c i • coneChartAt (n i + 1) (x i) (y i) :=
    funext fun i => (he i).map_smul (hy i trivial) (c i)
  rw [this, piBlockPt_smul_pos_pi, Punctured.val_smul_lin]

/-- **A block homothety is a conical automorphism when `∏ λᵢ^{dim F(Bᵢ)} = 1`** (`dim = nᵢ + 1`):
in product cone charts it is `diag(λ₀, …, λ_q)`, of determinant `∏ λᵢ^{nᵢ+1}`. -/
theorem isGXMorphism_piSMul {c : Fin (q + 1) → RPos}
    (h : ∏ i, ((c i : ℝˣ) : ℝ) ^ (n i + 1) = 1) :
    IsGXMorphism (GUR (pdim n + 1)) (RnO (pdim n + 1)) (piSMul n c : (∀ i, V i) → ∀ i, V i) := by
  have hg : piBlockGL (fun i => homothety (Fin (n i + 1) → ℝ) (c i : ℝˣ)) ∈ GUR (pdim n + 1) := by
    rw [mem_GU, det_piBlockGL]
    simp only [det_homothety, Module.finrank_fin_fun]
    rw [h, abs_one]
  refine isGXMorphism_of_mem_maximalAtlas (continuous_piSMul_const c) fun x => ?_
  have he := fun i => isConeChart_coneChartAt (n := n i + 1) (x i)
  have hx := fun i => mem_coneChartAt_source (n := n i + 1) (x i)
  have hE := isConeChart_piChart he
  have hxE : x ∈ (piChart n fun i => coneChartAt (n i + 1) (x i)).source := by
    rw [piChart_source]; exact fun i _ => hx i
  refine ⟨_, hE.1, _, hE.1, hxE, ?_, ⟨_, hg⟩, ?_⟩
  · rw [piChart_source]
    exact fun i _ => (he i).smul_mem_source (hx i) (c i)
  · filter_upwards [(piChart n fun i => coneChartAt (n i + 1) (x i)).open_source.mem_nhds hxE]
      with y hy
    rw [piChart_source] at hy
    simp only [piChart_apply, piSMul_apply]
    have : (fun i => coneChartAt (n i + 1) (x i) (posSMul (n i + 1) (c i) (y i))) =
        fun i => c i • coneChartAt (n i + 1) (x i) (y i) :=
      funext fun i => (he i).map_smul (hy i trivial) (c i)
    rw [this, piBlockPt_smul_pos_pi]
    rfl

/-- **A block homothety is a conical morphism ONLY IF `∏ λᵢ^{nᵢ+1} = 1`** (nonempty factors): in a
product cone chart it reads as `diag(λ₀, …, λ_q)`, and an element of `GU` agreeing with it on an
open set is it (rigidity), so `|det| = ∏ λᵢ^{nᵢ+1} = 1`. -/
theorem prod_pow_eq_one_of_isGXMorphism_piSMul [∀ i, Nonempty (V i)] {c : Fin (q + 1) → RPos}
    (hf : IsGXMorphism (GUR (pdim n + 1)) (RnO (pdim n + 1))
      (piSMul n c : (∀ i, V i) → ∀ i, V i)) :
    ∏ i, ((c i : ℝˣ) : ℝ) ^ (n i + 1) = 1 := by
  let x : ∀ i, V i := fun i => Classical.arbitrary (V i)
  have he := fun i => isConeChart_coneChartAt (n := n i + 1) (x i)
  have hx := fun i => mem_coneChartAt_source (n := n i + 1) (x i)
  set E := piChart n fun i => coneChartAt (n i + 1) (x i) with hEdef
  have hE := isConeChart_piChart he
  have hxE : x ∈ E.source := by rw [piChart_source]; exact fun i _ => hx i
  have hfx : piSMul n c x ∈ E.source := by
    rw [piChart_source]; exact fun i _ => (he i).smul_mem_source (hx i) (c i)
  obtain ⟨g, hg⟩ := hf.exists_smul_eq_of_mem_maximalAtlas hE.1 hE.1 hxE hfx
  obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 (hg.and (E.open_source.mem_nhds hxE))
  set D := piBlockGL fun i => homothety (Fin (n i + 1) → ℝ) (c i : ℝˣ)
  have hkey : (g : GLR (pdim n + 1)) = D := by
    refine eq_of_eqOn (E.isOpen_image_of_subset_source hto fun z hz => (ht hz).2)
      ⟨E x, mem_image_of_mem E hxt⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    have h1 : E (piSMul n c y) = g • E y := (ht hy).1
    have hy' := (ht hy).2
    rw [hEdef, piChart_source] at hy'
    have h2 : E (piSMul n c y) = D • E y := by
      simp only [hEdef, piChart_apply, piSMul_apply]
      have : (fun i => coneChartAt (n i + 1) (x i) (posSMul (n i + 1) (c i) (y i))) =
          fun i => c i • coneChartAt (n i + 1) (x i) (y i) :=
        funext fun i => (he i).map_smul (hy' i trivial) (c i)
      rw [this, piBlockPt_smul_pos_pi]
    exact h1.symm.trans h2
  have hdet := mem_GU.1 g.2
  rw [hkey, det_piBlockGL] at hdet
  simp only [det_homothety, Module.finrank_fin_fun] at hdet
  rwa [abs_of_pos (Finset.prod_pos fun i _ => pow_pos (Punctured.pos (c i)) _)] at hdet

/-- **Conical iff `∏ λᵢ^{dim F(Bᵢ)} = 1`** (nonempty factors). -/
theorem isGXMorphism_piSMul_iff [∀ i, Nonempty (V i)] (c : Fin (q + 1) → RPos) :
    IsGXMorphism (GUR (pdim n + 1)) (RnO (pdim n + 1)) (piSMul n c : (∀ i, V i) → ∀ i, V i) ↔
      ∏ i, ((c i : ℝˣ) : ℝ) ^ (n i + 1) = 1 :=
  ⟨prod_pow_eq_one_of_isGXMorphism_piSMul, isGXMorphism_piSMul⟩

omit [∀ i, HasGroupoid (V i) (coneGroupoid (n i + 1))] in
/-- **The principal `ℝ₊*^p`-bundle is locally trivial** (Déf. 1, « une structure d'espace fibré
$\R^{+p}$ principal »): every point of `∏ (Vᵢ/ℝ₊*)` lies in the base of an equivariant local
trivialisation of `piMk`, the product of the cone trivialisations `ConeBase.coneTrivialization`. -/
theorem exists_trivialization_piMk (b : ∀ i, ConeBase (n i) (V i)) :
    ∃ T : Trivialization (Fin (q + 1) → RPos) (piMk n V), b ∈ T.baseSet ∧
      ∀ x ∈ T.source, ∀ c, piSMul n c x ∈ T.source ∧ T (piSMul n c x) = ((T x).1, c * (T x).2) := by
  have key := fun i => ConeBase.exists_coneTrivialization (b i)
  choose e he hb using key
  refine ⟨trivializationPi fun i => ConeBase.coneTrivialization (he i), fun i _ => hb i,
    fun x hx c => ?_⟩
  rw [mem_trivializationPi_source] at hx
  have hx' : ∀ i, x i ∈ (e i).source := fun i =>
    (ConeBase.mk_mem_baseChart_source_iff (he i)).1 (hx i)
  refine ⟨(mem_trivializationPi_source _).2 fun i => ?_, ?_⟩
  · have h : ConeBase.mk (n := n i) (posSMul (n i + 1) (c i) (x i)) = ConeBase.mk (x i) :=
      ConeBase.mk_posSMul _ _
    show ConeBase.mk (n := n i) (posSMul (n i + 1) (c i) (x i)) ∈
      (ConeBase.baseChart (he i)).source
    rw [h]
    exact hx i
  · have h := fun i => ConeBase.coneTrivialization_posSMul (he i) (hx' i) (c i)
    show (fun i => (ConeBase.coneTrivialization (he i) (piSMul n c x i)).1,
        fun i => (ConeBase.coneTrivialization (he i) (piSMul n c x i)).2) =
      ((fun i => (ConeBase.coneTrivialization (he i) (x i)).1),
        c * fun i => (ConeBase.coneTrivialization (he i) (x i)).2)
    exact Prod.ext (funext fun i => by simp only [piSMul_apply, h i])
      (funext fun i => by simp only [piSMul_apply, h i, Pi.mul_apply])

end PiAction

/-! ### Déf. 1 for `F(B₀) × … × F(B_q)`: base `B₀ × … × B_q` -/

section PiFCone

open PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {B : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (B i)]
  [∀ i, ChartedSpace (S (n i)) (B i)] [∀ i, HasGroupoid (B i) (projGroupoid (n i))]
  [∀ i, T2Space (B i)]

variable (n B) in
/-- **The projection `F(B₀) × … × F(B_q) → B₀ × … × B_q`.** -/
def piProj (x : ∀ i, FCone (n i) (B i)) : ∀ i, B i := fun i => FCone.proj (x i)

theorem piProj_eq_baseProj_piMk (x : ∀ i, FCone (n i) (B i)) :
    piProj n B x = fun i => FCone.baseProj (piMk n (fun i => FCone (n i) (B i)) x i) := rfl

omit [∀ i, T2Space (B i)] in
theorem continuous_piProj : Continuous (piProj n B) :=
  continuous_pi fun i => FCone.continuous_proj.comp (continuous_apply i)

omit [∀ i, T2Space (B i)] in
theorem piProj_surjective : Surjective (piProj n B) := fun b =>
  ⟨fun i => FCone.ofPoint (b i), rfl⟩

@[simp] theorem piProj_piSMul (c : Fin (q + 1) → RPos) (x : ∀ i, FCone (n i) (B i)) :
    piProj n B (piSMul n c x) = piProj n B x := funext fun _ => FCone.proj_posSMul _ _

/-- **The fibres of `F(B₀) × … × F(B_q) → B₀ × … × B_q` are the `ℝ₊*^p`-orbits.** -/
theorem piProj_eq_iff {x x' : ∀ i, FCone (n i) (B i)} :
    piProj n B x = piProj n B x' ↔ ∃ c : Fin (q + 1) → RPos, piSMul n c x = x' := by
  rw [← piMk_eq_iff]
  constructor
  · intro h
    exact funext fun i => FCone.baseProj_injective (congrFun h i)
  · intro h
    rw [piProj_eq_baseProj_piMk, piProj_eq_baseProj_piMk, h]

/-- The base homeomorphism `∏ F(Bᵢ)/ℝ₊* ≃ₜ ∏ Bᵢ`. -/
def piBaseProjHomeomorph : (∀ i, ConeBase (n i) (FCone (n i) (B i))) ≃ₜ ∀ i, B i :=
  Homeomorph.piCongrRight fun _ => FCone.baseProjHomeomorph

/-- **Local triviality over `B₀ × … × B_q`**, equivariantly (Déf. 1). -/
theorem exists_trivialization_piProj (b : ∀ i, B i) :
    ∃ T : Trivialization (Fin (q + 1) → RPos) (piProj n B), b ∈ T.baseSet ∧
      ∀ x ∈ T.source, ∀ c, piSMul n c x ∈ T.source ∧ T (piSMul n c x) = ((T x).1, c * (T x).2) := by
  obtain ⟨T, hb, hT⟩ := exists_trivialization_piMk (n := n) (V := fun i => FCone (n i) (B i))
    (piBaseProjHomeomorph.symm b)
  refine ⟨trivializationCompHomeomorph T piBaseProjHomeomorph, ?_, fun x hx c => ?_⟩
  · show piBaseProjHomeomorph.symm b ∈ T.baseSet
    exact hb
  · rw [trivializationCompHomeomorph_source] at hx ⊢
    obtain ⟨h1, h2⟩ := hT x hx c
    refine ⟨h1, ?_⟩
    erw [trivializationCompHomeomorph_apply, trivializationCompHomeomorph_apply, h2]

/-- **Global triviality for paracompact factors** (a « variété » is second countable, hence
paracompact): `F(B₀) × … × F(B_q) ≃ₜ (B₀ × … × B_q) × ℝ₊*^p` over the base, equivariantly. -/
theorem exists_piHomeomorph [∀ i, ParacompactSpace (B i)] :
    ∃ H : (∀ i, FCone (n i) (B i)) ≃ₜ (∀ i, B i) × (Fin (q + 1) → RPos),
      (∀ x, (H x).1 = piProj n B x) ∧ ∀ c x, H (piSMul n c x) = ((H x).1, c * (H x).2) := by
  have key := fun i => FCone.exists_radial (n := n i) (B := B i)
  choose N σ hNc hσc hN hσp hσN hσ using key
  refine ⟨{ toFun := fun x => (fun i => FCone.proj (x i), fun i => N i (x i))
            invFun := fun y i => posSMul (n i + 1) (y.2 i) (σ i (y.1 i))
            left_inv := fun x => funext fun i => hσ i (x i)
            right_inv := fun y => Prod.ext (funext fun i => by
                simp only [FCone.proj_posSMul, hσp])
              (funext fun i => by simp only [hN, hσN, mul_one])
            continuous_toFun := (continuous_pi fun i => FCone.continuous_proj.comp
              (continuous_apply i)).prodMk (continuous_pi fun i => (hNc i).comp (continuous_apply i))
            continuous_invFun := continuous_pi fun i => (continuous_posSMul (n := n i + 1)).comp
              ((((continuous_apply i).comp continuous_snd)).prodMk
                ((hσc i).comp ((continuous_apply i).comp continuous_fst)) :
                Continuous fun a : (∀ i, B i) × (Fin (q + 1) → RPos) => (a.2 i, σ i (a.1 i))) },
    fun x => rfl, fun c x => Prod.ext (funext fun i => FCone.proj_posSMul _ _)
      (funext fun i => hN i (c i) (x i))⟩

end PiFCone

/-! ### The printed lift of `ℝ^{+p}/ℝ^+` and its correction (Prop. 2's proof) -/

section Lift

variable {q : ℕ} (n : Fin (q + 1) → ℕ)

/-- **The corrected lift** of `ℝ^{+p}/ℝ^+` (Prop. 2's proof, DEC-128): the subgroup of `ℝ₊*^p` of
the `(λᵢ)` with `∏ λᵢ^{dim F(Bᵢ)} = 1`, `dim F(Bᵢ) = nᵢ + 1`. -/
def piLift : Subgroup (Fin (q + 1) → RPos) where
  carrier := {c | ∏ i, ((c i : ℝˣ) : ℝ) ^ (n i + 1) = 1}
  mul_mem' {c d} hc hd := by
    simp only [mem_setOf_eq, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul, mul_pow,
      Finset.prod_mul_distrib] at hc hd ⊢
    rw [hc, hd, one_mul]
  one_mem' := by simp
  inv_mem' {c} hc := by
    simp only [mem_setOf_eq, Pi.inv_apply, InvMemClass.coe_inv, Units.val_inv_eq_inv_val,
      inv_pow, Finset.prod_inv_distrib] at hc ⊢
    rw [hc, inv_one]

/-- **`ℝ^{+p}/ℝ^+` lifts to `piLift`** (it is a complement of the diagonal): every `(λᵢ)` is, up to
a unique diagonal factor, in `piLift`. -/
theorem existsUnique_piLift (c : Fin (q + 1) → RPos) :
    ∃! c' : Fin (q + 1) → RPos, c' ∈ piLift n ∧ ∃ t : RPos, c' = c * fun _ => t := by
  set P : ℝ := ∏ i, ((c i : ℝˣ) : ℝ) ^ (n i + 1) with hP
  have hPpos : 0 < P := Finset.prod_pos fun i _ => pow_pos (Punctured.pos (c i)) _
  have hK : ∀ t : ℝ, ∏ i, (((c i : ℝˣ) : ℝ) * t) ^ (n i + 1) = P * t ^ (pdim n + 1) := by
    intro t
    rw [hP, ← sum_succ_eq_pdim, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => mul_pow _ _ _
  have hmem : ∀ t : RPos, (c * fun _ => t) ∈ piLift n ↔
      P * (((t : ℝˣ) : ℝ)) ^ (pdim n + 1) = 1 := by
    intro t
    show ∏ i, (((c i * t : RPos) : ℝˣ) : ℝ) ^ (n i + 1) = 1 ↔ _
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hK]
  set t₀ : RPos := Punctured.posUnit (P ^ (-(1 / ((pdim n : ℝ) + 1)))) (Real.rpow_pos_of_pos hPpos _)
  have ht₀ : P * (((t₀ : ℝˣ) : ℝ)) ^ (pdim n + 1) = 1 := by
    simp only [t₀, Punctured.coe_posUnit]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hPpos.le]
    have : (-(1 / ((pdim n : ℝ) + 1)) * ((pdim n + 1 : ℕ) : ℝ)) = -1 := by
      push_cast; field_simp
    rw [this, Real.rpow_neg_one, mul_inv_cancel₀ hPpos.ne']
  refine ⟨c * fun _ => t₀, ⟨(hmem t₀).2 ht₀, t₀, rfl⟩, ?_⟩
  rintro c' ⟨hc', t, rfl⟩
  have h1 := (hmem t).1 hc'
  have h2 : (((t : ℝˣ) : ℝ)) ^ (pdim n + 1) = (((t₀ : ℝˣ) : ℝ)) ^ (pdim n + 1) :=
    mul_left_cancel₀ hPpos.ne' (h1.trans ht₀.symm)
  have h3 : t = t₀ := Subtype.ext (Units.ext ((pow_left_inj₀ (Punctured.pos t).le
    (Punctured.pos t₀).le (Nat.succ_ne_zero _)).1 h2))
  rw [h3]

end Lift

/-- `∏ₖ (mulSingle i a k)^{m k} = a^{m i}` in `ℝ`. -/
theorem prod_coe_mulSingle_pow {q : ℕ} (m : Fin (q + 1) → ℕ) (i : Fin (q + 1)) (a : RPos) :
    ∏ k, (((Pi.mulSingle i a : Fin (q + 1) → RPos) k : RPos) : ℝˣ).val ^ (m k) =
      ((a : ℝˣ) : ℝ) ^ (m i) := by
  rw [Finset.prod_eq_single i (fun k _ hk => by simp [Pi.mulSingle_eq_of_ne hk]) (by simp)]
  simp

section Finding

open PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {V : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (V i)]
  [∀ i, ChartedSpace (RnO (n i + 1)) (V i)] [∀ i, HasConeCharts (n i + 1) (V i)]
  [∀ i, T2Space (V i)] [∀ i, HasGroupoid (V i) (coneGroupoid (n i + 1))]

/-- **FINDING (Prop. 2's proof, p. 244; DEC-128), general `p`**: the printed lift « le sous-groupe
de $\R^{+p}$ formé des systèmes de $p$ nombres réels positifs dont le produit est égal à $1$. Un
élément de ce sous-groupe définit un automorphisme de la structure conique affine du produit » is
false as soon as two factors have different dimensions: then some `(λᵢ)` with `∏ λᵢ = 1` (namely
`2` at `i`, `1/2` at `j`, `1` elsewhere) is not a conical automorphism of the product. The
statement of Prop. 2 is unaffected (`prop2_fibre_produit_pi`); the corrected lift is `piLift`. -/
theorem not_isGXMorphism_piSMul_of_ne [∀ i, Nonempty (V i)] {i j : Fin (q + 1)}
    (hij : n i ≠ n j) :
    ∃ c : Fin (q + 1) → RPos, ∏ k, c k = 1 ∧
      ¬ IsGXMorphism (GUR (pdim n + 1)) (RnO (pdim n + 1))
        (piSMul n c : (∀ i, V i) → ∀ i, V i) := by
  have hne : i ≠ j := fun h => hij (h ▸ rfl)
  set two : RPos := Punctured.posUnit 2 two_pos
  refine ⟨Pi.mulSingle i two * Pi.mulSingle j two⁻¹, ?_, fun hf => ?_⟩
  · simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle' i, Finset.prod_pi_mulSingle' j]
    simp
  · have h := prod_pow_eq_one_of_isGXMorphism_piSMul hf
    simp only [Pi.mul_apply, Subgroup.coe_mul, Units.val_mul, mul_pow,
      Finset.prod_mul_distrib, prod_coe_mulSingle_pow] at h
    simp only [two, Punctured.coe_posUnit, InvMemClass.coe_inv, Units.val_inv_eq_inv_val,
      inv_pow] at h
    rw [mul_inv_eq_one₀ (by positivity)] at h
    have h' : (2 : ℕ) ^ (n i + 1) = 2 ^ (n j + 1) := by exact_mod_cast h
    have := Nat.pow_right_injective (le_refl 2) h'
    omega

/-- **The printed lift is right exactly when the factors have one dimension**: then every `(λᵢ)`
with `∏ λᵢ = 1` is a conical automorphism. -/
theorem isGXMorphism_piSMul_of_prod_eq_one {d : ℕ} (hd : ∀ i, n i = d)
    {c : Fin (q + 1) → RPos} (hc : ∏ k, c k = 1) :
    IsGXMorphism (GUR (pdim n + 1)) (RnO (pdim n + 1)) (piSMul n c : (∀ i, V i) → ∀ i, V i) := by
  refine isGXMorphism_piSMul ?_
  simp only [hd]
  rw [Finset.prod_pow]
  have : ∏ k, ((c k : ℝˣ) : ℝ) = (((∏ k, c k : RPos) : ℝˣ) : ℝ) := by
    push_cast; rfl
  rw [this, hc]
  simp

end Finding

/-! ### Prop. 2 — `ℝ^{+p}/ℝ^+` acting on the base of the product cone -/

/-- **The diagonal `ℝ₊* ⊂ ℝ₊*^p`.** -/
def piDiag (q : ℕ) : Subgroup (Fin (q + 1) → RPos) where
  carrier := {c | ∀ i, c i = c 0}
  mul_mem' {c d} hc hd i := by simp only [Pi.mul_apply, hc i, hd i]
  one_mem' _ := rfl
  inv_mem' {c} hc i := by simp only [Pi.inv_apply, hc i]

instance (q : ℕ) : (piDiag q).Normal := Subgroup.normal_of_isMulCommutative _

/-- **`ℝ^{+p}/ℝ^+`**, the quotient of `ℝ₊*^p` by its diagonal. -/
abbrev PiTorus (q : ℕ) : Type := (Fin (q + 1) → RPos) ⧸ piDiag q

/-- The ratios `(λ_{j+1}/λ₀)_j`, `ℝ₊*^p → ℝ₊*^{p−1}`. -/
def piRatioHom (q : ℕ) : (Fin (q + 1) → RPos) →* (Fin q → RPos) where
  toFun c j := c j.succ * (c 0)⁻¹
  map_one' := by funext j; simp
  map_mul' c d := by funext j; simp only [Pi.mul_apply, mul_inv_rev]; ac_rfl

theorem map_continuous_piRatio (q : ℕ) : Continuous (piRatioHom q) :=
  continuous_pi fun j => (continuous_apply j.succ).mul (continuous_apply 0).inv

/-- **The torus coordinates `ℝ^{+p}/ℝ^+ → ℝ₊*^{p−1}`**, `[λ] ↦ (λ_{j+1}/λ₀)_j`. -/
def torusCoord (q : ℕ) : PiTorus q →* (Fin q → RPos) :=
  QuotientGroup.lift (piDiag q) (piRatioHom q) fun c hc => by
    funext j
    simp only [piRatioHom, MonoidHom.coe_mk, OneHom.coe_mk, Pi.one_apply]
    rw [hc j.succ, mul_inv_cancel]

theorem torusCoord_mk (c : Fin (q + 1) → RPos) :
    torusCoord q (c : PiTorus q) = fun j => c j.succ * (c 0)⁻¹ := rfl

/-- `t ↦ [(1, t₀, …, t_{q−1})]`. -/
def torusOfCoord (q : ℕ) : (Fin q → RPos) →* PiTorus q where
  toFun t := ((Fin.cons 1 t : Fin (q + 1) → RPos) : PiTorus q)
  map_one' := by
    rw [← QuotientGroup.mk_one]
    congr 1
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  map_mul' s t := by
    rw [← QuotientGroup.mk_mul]
    congr 1
    funext i
    refine Fin.cases (by simp) (fun j => by simp) i

/-- **`ℝ^{+p}/ℝ^+ ≅ ℝ₊*^{p−1}`** (the fibre of Prop. 2 is a torus `(ℝ₊*)^{p−1}`). -/
def torusCoordEquiv (q : ℕ) : PiTorus q ≃* (Fin q → RPos) :=
  { torusCoord q with
    invFun := torusOfCoord q
    left_inv := fun t => by
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective t
      show ((Fin.cons 1 (fun j => c j.succ * (c 0)⁻¹) : Fin (q + 1) → RPos) : PiTorus q) = c
      refine QuotientGroup.eq.2 fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp
    right_inv := fun t => by
      funext j
      show ((Fin.cons 1 t : Fin (q + 1) → RPos) j.succ) * ((Fin.cons 1 t : Fin (q + 1) → RPos) 0)⁻¹
        = t j
      simp }

section PiBase

open PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {V : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (V i)]
  [∀ i, ChartedSpace (RnO (n i + 1)) (V i)] [∀ i, HasConeCharts (n i + 1) (V i)]
  [∀ i, T2Space (V i)] [∀ i, HasGroupoid (V i) (coneGroupoid (n i + 1))]

theorem piSMul_comm_const (c : Fin (q + 1) → RPos) (d : RPos) (x : ∀ i, V i) :
    piSMul n c (posSMul (pdim n + 1) d x) = posSMul (pdim n + 1) d (piSMul n c x) := by
  rw [← piSMul_const, ← piSMul_const, ← piSMul_mul, ← piSMul_mul, mul_comm]

variable (n V) in
/-- **The base map of `(λᵢ) ∈ ℝ₊*^p`** on `F⁻¹(∏ Vᵢ)`, `[m] ↦ [(λᵢmᵢ)]` (well defined: `(λᵢ)`
commutes with the diagonal). -/
def piBaseMap (c : Fin (q + 1) → RPos) :
    ConeBase (pdim n) (∀ i, V i) → ConeBase (pdim n) (∀ i, V i) :=
  Quotient.lift (fun x => ConeBase.mk (piSMul n c x)) fun x x' h => by
    obtain ⟨d, rfl⟩ := ConeBase.rel_iff.1 h
    show ConeBase.mk (piSMul n c (posSMul (pdim n + 1) d x')) = ConeBase.mk (piSMul n c x')
    rw [piSMul_comm_const, ConeBase.mk_posSMul]

@[simp] theorem piBaseMap_mk (c : Fin (q + 1) → RPos) (x : ∀ i, V i) :
    piBaseMap n V c (ConeBase.mk x) = ConeBase.mk (piSMul n c x) := rfl

theorem piBaseMap_eq_map {c : Fin (q + 1) → RPos} (t : RPos) (hc : (c * fun _ => t) ∈ piLift n) :
    piBaseMap n V c = ConeBase.map (V := ∀ i, V i) (W := ∀ i, V i)
      (isGXMorphism_piSMul (n := n) (V := V) hc) := by
  funext p
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rw [piBaseMap_mk, ConeBase.map_mk, piSMul_mul, piSMul_const, piSMul_comm_const,
    ConeBase.mk_posSMul]

/-- **Every `(λᵢ)` acts on the base by a projective morphism** (through its unimodular
representative in `piLift`, the corrected lift). -/
theorem isGXMorphism_piBaseMap (c : Fin (q + 1) → RPos) :
    IsGXMorphism (GSR (pdim n)) (S (pdim n)) (piBaseMap n V c) := by
  obtain ⟨c', ⟨hc', t, rfl⟩, -⟩ := existsUnique_piLift n c
  rw [piBaseMap_eq_map t hc']
  exact ConeBase.isGXMorphism_map _

theorem piBaseMap_one : piBaseMap n V 1 = id := by
  funext p
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rw [piBaseMap_mk, piSMul_one]
  rfl

theorem piBaseMap_mul (c d : Fin (q + 1) → RPos) :
    piBaseMap n V (c * d) = piBaseMap n V c ∘ piBaseMap n V d := by
  funext p
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rw [comp_apply, piBaseMap_mk, piBaseMap_mk, piBaseMap_mk, piSMul_mul]

theorem piBaseMap_bijective (c : Fin (q + 1) → RPos) : Bijective (piBaseMap n V c) := by
  refine bijective_iff_has_inverse.2 ⟨piBaseMap n V c⁻¹, fun p => ?_, fun p => ?_⟩
  · rw [← comp_apply (f := piBaseMap n V c⁻¹), ← piBaseMap_mul, inv_mul_cancel, piBaseMap_one]; rfl
  · rw [← comp_apply (f := piBaseMap n V c), ← piBaseMap_mul, mul_inv_cancel, piBaseMap_one]; rfl

/-- The diagonal acts trivially on the base. -/
theorem piBaseMap_of_mem_piDiag {c : Fin (q + 1) → RPos} (hc : c ∈ piDiag q) :
    piBaseMap n V c = id := by
  funext p
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  have : c = fun _ => c 0 := funext hc
  rw [piBaseMap_mk, this, piSMul_const, ConeBase.mk_posSMul]
  rfl

variable (n V) in
/-- `(λᵢ) ↦` its base map, as a homomorphism to the projective automorphisms of `F⁻¹(∏ Vᵢ)`. -/
def piBaseAutHom : (Fin (q + 1) → RPos) →*
    GXAut (GSR (pdim n)) (S (pdim n)) (ConeBase (pdim n) (∀ i, V i)) where
  toFun c := GXAut.ofBijective (isGXMorphism_piBaseMap c) (piBaseMap_bijective c)
  map_one' := FaithfulSMul.eq_of_smul_eq_smul fun p : ConeBase (pdim n) (∀ i, V i) => by
    rw [GXAut.ofBijective_smul, piBaseMap_one, one_smul]; rfl
  map_mul' c d := FaithfulSMul.eq_of_smul_eq_smul fun p : ConeBase (pdim n) (∀ i, V i) => by
    rw [mul_smul, GXAut.ofBijective_smul, GXAut.ofBijective_smul, GXAut.ofBijective_smul,
      piBaseMap_mul]; rfl

@[simp] theorem piBaseAutHom_smul (c : Fin (q + 1) → RPos) (p : ConeBase (pdim n) (∀ i, V i)) :
    piBaseAutHom n V c • p = piBaseMap n V c p := rfl

variable (n V) in
/-- **Prop. 2: `ℝ^{+p}/ℝ^+` operates on `F⁻¹(V₀ × … × V_q)` by projective automorphisms.** -/
def piTorusAut : PiTorus q →* GXAut (GSR (pdim n)) (S (pdim n)) (ConeBase (pdim n) (∀ i, V i)) :=
  QuotientGroup.lift (piDiag q) (piBaseAutHom n V) fun c hc =>
    FaithfulSMul.eq_of_smul_eq_smul fun p : ConeBase (pdim n) (∀ i, V i) => by
      rw [piBaseAutHom_smul, piBaseMap_of_mem_piDiag hc, one_smul]; rfl

@[simp] theorem piTorusAut_mk_smul (c : Fin (q + 1) → RPos) (x : ∀ i, V i) :
    piTorusAut n V (c : PiTorus q) • (ConeBase.mk x : ConeBase (pdim n) (∀ i, V i)) =
      ConeBase.mk (piSMul n c x) := rfl

variable (n V) in
/-- **The projection of the base of the product cone onto the product of the bases**,
`[m] ↦ ([mᵢ])`. -/
def piBasePr : ConeBase (pdim n) (∀ i, V i) → ∀ i, ConeBase (n i) (V i) :=
  Quotient.lift (piMk n V) fun x x' h => by
    obtain ⟨d, rfl⟩ := ConeBase.rel_iff.1 h
    show piMk n V (posSMul (pdim n + 1) d x') = piMk n V x'
    rw [← piSMul_const, piMk_piSMul]

@[simp] theorem piBasePr_mk (x : ∀ i, V i) :
    piBasePr n V (ConeBase.mk x) = piMk n V x := rfl

theorem continuous_piBasePr : Continuous (piBasePr n V) :=
  continuous_quot_lift _ continuous_piMk

theorem piBasePr_surjective : Surjective (piBasePr n V) := fun b => by
  obtain ⟨x, rfl⟩ := piMk_surjective (n := n) (V := V) b
  exact ⟨ConeBase.mk x, rfl⟩

theorem piBasePr_piBaseMap (c : Fin (q + 1) → RPos) (p : ConeBase (pdim n) (∀ i, V i)) :
    piBasePr n V (piBaseMap n V c p) = piBasePr n V p := by
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rw [piBaseMap_mk, piBasePr_mk, piBasePr_mk, piMk_piSMul]

/-- **The fibres of `piBasePr` are the `ℝ^{+p}/ℝ^+`-orbits** (Prop. 2). -/
theorem piBasePr_eq_iff {p p' : ConeBase (pdim n) (∀ i, V i)} :
    piBasePr n V p = piBasePr n V p' ↔ ∃ t : PiTorus q, piTorusAut n V t • p = p' := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
    obtain ⟨x', rfl⟩ := ConeBase.mk_surjective p'
    obtain ⟨c, rfl⟩ := piMk_eq_iff.1 h
    exact ⟨c, rfl⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective t
    exact (piBasePr_piBaseMap c p).symm

/-- **`ℝ^{+p}/ℝ^+` acts freely** (« espace fibré principal »). -/
theorem eq_one_of_piTorusAut_smul_eq {t : PiTorus q} {p : ConeBase (pdim n) (∀ i, V i)}
    (h : piTorusAut n V t • p = p) : t = 1 := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective t
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rw [piTorusAut_mk_smul] at h
  obtain ⟨d, hd⟩ := ConeBase.mk_eq_mk_iff.1 h
  rw [← piSMul_const] at hd
  have h2 : piSMul n (c⁻¹ * fun _ => d) x = x := by
    rw [piSMul_mul, hd, ← piSMul_mul, inv_mul_cancel, piSMul_one]
  have h1 := eq_one_of_piSMul_eq h2
  have hc : ∀ i, c i = d := fun i => by
    have := congrFun h1 i
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply] at this
    exact inv_mul_eq_one.1 this
  rw [← QuotientGroup.mk_one, QuotientGroup.eq]
  intro i
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply, mul_one, hc]

end PiBase

/-- **The inverse of a cone trivialisation**: `T⁻¹([m], s) = (s / ‖m‖_T)·m`. -/
theorem coneTrivialization_symm_mk {k : ℕ} {W : Type*} [TopologicalSpace W]
    [ChartedSpace (RnO (k + 1)) W] [HasConeCharts (k + 1) W] [T2Space W]
    {e : OpenPartialHomeomorph W (RnO (k + 1))} (he : IsConeChart (k + 1) e) {m : W}
    (hm : m ∈ e.source) (s : RPos) :
    (ConeBase.coneTrivialization he).toOpenPartialHomeomorph.symm (ConeBase.mk m, s) =
      posSMul (k + 1) (s * ((ConeBase.coneTrivialization he m).2)⁻¹) m := by
  set T := ConeBase.coneTrivialization he
  have hm' : posSMul (k + 1) (s * (T m).2⁻¹) m ∈ T.source := by
    show ConeBase.mk (n := k) (posSMul (k + 1) (s * (T m).2⁻¹) m) ∈ (ConeBase.baseChart he).source
    rw [ConeBase.mk_posSMul]
    exact ⟨m, hm, rfl⟩
  have h := ConeBase.coneTrivialization_posSMul he hm (s * (T m).2⁻¹)
  have h2 : ((T m).1, s * (T m).2⁻¹ * (T m).2) = (ConeBase.mk m, s) := by
    rw [inv_mul_cancel_right]
    rfl
  rw [h2] at h
  rw [← h]
  exact T.toOpenPartialHomeomorph.left_inv hm'

section PiBaseTriv

open PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {V : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (V i)]
  [∀ i, ChartedSpace (RnO (n i + 1)) (V i)] [∀ i, HasConeCharts (n i + 1) (V i)]
  [∀ i, T2Space (V i)] [∀ i, HasGroupoid (V i) (coneGroupoid (n i + 1))]

/-- **Prop. 2, local triviality** (« une structure d'espace fibré principal »): every point of
`∏ (Vᵢ/ℝ₊*)` lies in the base of a local trivialisation of `piBasePr`, with fibre the torus
coordinates `ℝ₊*^{p−1}`, equivariant: `(λᵢ)` acts on the fibre by `(λ_{j+1}/λ₀)_j`. Built from the
cone trivialisations of the factors: `[m] ↦ ([mᵢ], (‖m_{j+1}‖/‖m₀‖)_j)`. -/
theorem exists_trivialization_piBasePr (b : ∀ i, ConeBase (n i) (V i)) :
    ∃ T : Trivialization (Fin q → RPos) (piBasePr n V), b ∈ T.baseSet ∧
      ∀ p ∈ T.source, ∀ c, piBaseMap n V c p ∈ T.source ∧
        T (piBaseMap n V c p) = ((T p).1, piRatioHom q c * (T p).2) := by
  have key := fun i => ConeBase.exists_coneTrivialization (b i)
  choose e he hb using key
  set Tr := fun i => ConeBase.coneTrivialization (he i) with hTr
  set r : ∀ i, V i → RPos := fun i m => (Tr i m).2 with hr_def
  set S : Set (∀ i, V i) := univ.pi fun i => (e i).source with hS
  set U : Set (∀ i, ConeBase (n i) (V i)) := univ.pi fun i => (Tr i).baseSet with hU
  set R : (∀ i, V i) → (Fin q → RPos) := fun x j => r j.succ (x j.succ) * (r 0 (x 0))⁻¹
    with hR_def
  have hSU : ∀ x, x ∈ S ↔ piMk n V x ∈ U := fun x => by
    simp only [hS, hU, mem_univ_pi]
    exact forall_congr' fun i => (ConeBase.mk_mem_baseChart_source_iff (he i)).symm
  have hr : ∀ i m, m ∈ (e i).source → ∀ c, r i (posSMul (n i + 1) c m) = c * r i m :=
    fun i m hm c => congrArg Prod.snd (ConeBase.coneTrivialization_posSMul (he i) hm c)
  have hRc : ∀ x ∈ S, ∀ c, R (piSMul n c x) = piRatioHom q c * R x := by
    intro x hx c
    rw [mem_univ_pi] at hx
    funext j
    simp only [hR_def, piSMul_apply, hr _ _ (hx _), piRatioHom, MonoidHom.coe_mk, OneHom.coe_mk,
      Pi.mul_apply, mul_inv_rev]
    ac_rfl
  have hSc : ∀ x ∈ S, ∀ c, piSMul n c x ∈ S := fun x hx c => by
    rw [mem_univ_pi] at hx ⊢
    exact fun i => (he i).smul_mem_source (hx i) (c i)
  have hRd : ∀ x ∈ S, ∀ d, R (posSMul (pdim n + 1) d x) = R x := by
    intro x hx d
    rw [← piSMul_const, hRc x hx]
    funext j
    simp [piRatioHom]
  have hout : ∀ x ∈ S, R (Quotient.out (ConeBase.mk x : ConeBase (pdim n) (∀ i, V i))) = R x := by
    intro x hx
    obtain ⟨d, hd⟩ := ConeBase.mk_eq_mk_iff.1
      (Quotient.out_eq (ConeBase.mk x : ConeBase (pdim n) (∀ i, V i)))
    rw [← hd, hRd x hx]
  have hTt : ∀ i (z : ConeBase (n i) (V i) × RPos), z.1 ∈ (Tr i).baseSet → z ∈ (Tr i).target :=
    fun i z hz => (Tr i).mem_target.2 hz
  have hsymm_mk : ∀ i (z : ConeBase (n i) (V i) × RPos), z.1 ∈ (Tr i).baseSet →
      ConeBase.mk ((Tr i).toOpenPartialHomeomorph.symm z) = z.1 := fun i z hz =>
    (Tr i).proj_symm_apply (hTt i z hz)
  have hsymm_r : ∀ i (z : ConeBase (n i) (V i) × RPos), z.1 ∈ (Tr i).baseSet →
      r i ((Tr i).toOpenPartialHomeomorph.symm z) = z.2 := fun i z hz =>
    congrArg Prod.snd ((Tr i).apply_symm_apply (hTt i z hz))
  have hsymm_src : ∀ i (z : ConeBase (n i) (V i) × RPos), z.1 ∈ (Tr i).baseSet →
      (Tr i).toOpenPartialHomeomorph.symm z ∈ (e i).source := fun i z hz =>
    (ConeBase.mk_mem_baseChart_source_iff (he i)).1
      ((Tr i).toOpenPartialHomeomorph.map_target (hTt i z hz))
  have hrc : ∀ i m, m ∈ (e i).source → ContinuousAt (r i) m := fun i m hm => by
    have hm' : m ∈ (Tr i).toOpenPartialHomeomorph.source :=
      (ConeBase.mk_mem_baseChart_source_iff (he i)).2 hm
    exact ((Tr i).toOpenPartialHomeomorph.continuousOn.continuousAt
      ((Tr i).toOpenPartialHomeomorph.open_source.mem_nhds hm')).snd
  have hRcont : ∀ x ∈ S, ContinuousAt R x := fun x hx => by
    rw [mem_univ_pi] at hx
    exact continuousAt_pi.2 fun j => ((hrc _ _ (hx j.succ)).comp
      (continuous_apply j.succ).continuousAt).mul
      (((hrc _ _ (hx 0)).comp (continuous_apply 0).continuousAt).inv)
  have hSo : IsOpen S := isOpen_set_pi finite_univ fun i _ => (e i).open_source
  have hUo : IsOpen U := isOpen_set_pi finite_univ fun i _ => (Tr i).open_baseSet
  let Φ : ConeBase (pdim n) (∀ i, V i) → (∀ i, ConeBase (n i) (V i)) × (Fin q → RPos) :=
    fun p => (piBasePr n V p, R (Quotient.out p))
  let Ψ : (∀ i, ConeBase (n i) (V i)) × (Fin q → RPos) → ConeBase (pdim n) (∀ i, V i) :=
    fun z => ConeBase.mk (fun i => (Tr i).toOpenPartialHomeomorph.symm
      (z.1 i, (Fin.cons 1 z.2 : Fin (q + 1) → RPos) i))
  have hΦ : ∀ x ∈ S, Φ (ConeBase.mk x) = (piMk n V x, R x) := fun x hx => by
    simp only [Φ, piBasePr_mk, hout x hx]
  have hconsC : Continuous fun z : (∀ i, ConeBase (n i) (V i)) × (Fin q → RPos) =>
      (Fin.cons 1 z.2 : Fin (q + 1) → RPos) :=
    continuous_const.finCons continuous_snd
  let T : Trivialization (Fin q → RPos) (piBasePr n V) :=
    { toFun := Φ
      invFun := Ψ
      source := piBasePr n V ⁻¹' U
      target := U ×ˢ univ
      map_source' := fun p hp => ⟨hp, trivial⟩
      map_target' := fun z hz => by
        show piBasePr n V (ConeBase.mk _) ∈ U
        rw [piBasePr_mk, hU, mem_univ_pi]
        intro i
        show ConeBase.mk ((Tr i).toOpenPartialHomeomorph.symm _) ∈ _
        rw [hsymm_mk i _ ((mem_univ_pi.1 hz.1) i)]
        exact (mem_univ_pi.1 hz.1) i
      left_inv' := fun p hp => by
        obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
        have hx : x ∈ S := (hSU x).2 hp
        have hx' := mem_univ_pi.1 hx
        show Ψ (Φ (ConeBase.mk x)) = ConeBase.mk x
        rw [hΦ x hx]
        show ConeBase.mk (fun i => (Tr i).toOpenPartialHomeomorph.symm
          (ConeBase.mk (x i), (Fin.cons 1 (R x) : Fin (q + 1) → RPos) i)) = ConeBase.mk x
        have hpt : (fun i => (Tr i).toOpenPartialHomeomorph.symm
            (ConeBase.mk (x i), (Fin.cons 1 (R x) : Fin (q + 1) → RPos) i)) =
            piSMul n (fun _ => (r 0 (x 0))⁻¹) x := by
          funext i
          rw [coneTrivialization_symm_mk (he i) (hx' i), piSMul_apply]
          congr 1
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [hr_def, hTr]
          · simp only [Fin.cons_succ, hR_def, hr_def, hTr]
            rw [mul_right_comm, mul_inv_cancel, one_mul]
        rw [hpt, piSMul_const, ConeBase.mk_posSMul]
      right_inv' := fun z hz => by
        have hz1 := mem_univ_pi.1 hz.1
        set y : ∀ i, V i := fun i => (Tr i).toOpenPartialHomeomorph.symm
          (z.1 i, (Fin.cons 1 z.2 : Fin (q + 1) → RPos) i) with hy
        have hyS : y ∈ S := mem_univ_pi.2 fun i => hsymm_src i _ (hz1 i)
        show Φ (ConeBase.mk y) = z
        rw [hΦ y hyS]
        refine Prod.ext (funext fun i => hsymm_mk i _ (hz1 i)) (funext fun j => ?_)
        show r j.succ (y j.succ) * (r 0 (y 0))⁻¹ = z.2 j
        rw [hy, hsymm_r _ _ (hz1 _), hsymm_r _ _ (hz1 _)]
        simp
      open_source := hUo.preimage continuous_piBasePr
      open_target := hUo.prod isOpen_univ
      continuousOn_toFun := fun p hp => by
        obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
        have hx : x ∈ S := (hSU x).2 hp
        refine ContinuousAt.continuousWithinAt (continuous_piBasePr.continuousAt.prodMk ?_)
        refine Filter.tendsto_def.2 fun O hO => ?_
        have hO' : O ∈ 𝓝 (R x) := by rw [← hout x hx]; exact hO
        have hW : S ∩ R ⁻¹' O ∈ 𝓝 x := inter_mem (hSo.mem_nhds hx) (hRcont x hx hO')
        refine mem_of_superset (ConeBase.mk_image_mem_nhds hW) ?_
        rintro _ ⟨y, ⟨hyS, hyO⟩, rfl⟩
        show R (Quotient.out (ConeBase.mk y : ConeBase (pdim n) (∀ i, V i))) ∈ O
        rw [hout y hyS]
        exact hyO
      continuousOn_invFun := ConeBase.continuous_mk.comp_continuousOn
        (continuousOn_pi.2 fun i => (Tr i).toOpenPartialHomeomorph.continuousOn_symm.comp
          ((((continuous_apply i).comp continuous_fst).prodMk
            ((continuous_apply i).comp hconsC)).continuousOn)
          fun z hz => hTt i _ ((mem_univ_pi.1 hz.1) i))
      baseSet := U
      open_baseSet := hUo
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ => rfl }
  refine ⟨T, mem_univ_pi.2 hb, fun p hp c => ⟨?_, ?_⟩⟩
  · show piBasePr n V (piBaseMap n V c p) ∈ U
    rw [piBasePr_piBaseMap]
    exact hp
  · obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
    have hx : x ∈ S := (hSU x).2 hp
    show Φ (piBaseMap n V c (ConeBase.mk x)) = ((Φ (ConeBase.mk x)).1, _ * (Φ (ConeBase.mk x)).2)
    rw [piBaseMap_mk, hΦ _ (hSc x hx c), hΦ x hx, piMk_piSMul, hRc x hx]

end PiBaseTriv

theorem piRatioHom_const {q : ℕ} (d : RPos) : piRatioHom q (fun _ => d) = 1 := by
  funext j
  simp [piRatioHom]

theorem piRatioHom_cons {q : ℕ} (t : Fin q → RPos) :
    piRatioHom q (Fin.cons 1 t : Fin (q + 1) → RPos) = t := by
  funext j
  simp [piRatioHom]

theorem cons_piRatioHom {q : ℕ} (a : Fin (q + 1) → RPos) :
    (Fin.cons 1 (piRatioHom q a) : Fin (q + 1) → RPos) = a * fun _ => (a 0)⁻¹ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [piRatioHom]

section PiFBase

open PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {B : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (B i)]
  [∀ i, ChartedSpace (S (n i)) (B i)] [∀ i, HasGroupoid (B i) (projGroupoid (n i))]
  [∀ i, T2Space (B i)]

variable (n B) in
/-- **`F⁻¹(F(B₀) × … × F(B_q))`**, the base of the product cone (Prop. 2: a locally projective
manifold of dimension `Σ nᵢ + q`). -/
abbrev PiBase : Type u := ConeBase (pdim n) (∀ i, FCone (n i) (B i))

variable (n B) in
/-- **The projection `F⁻¹(F(B₀) × … × F(B_q)) → B₀ × … × B_q`.** -/
def piBaseProj (p : PiBase n B) : ∀ i, B i :=
  fun i => FCone.baseProj (piBasePr n (fun i => FCone (n i) (B i)) p i)

@[simp] theorem piBaseProj_mk (x : ∀ i, FCone (n i) (B i)) :
    piBaseProj n B (ConeBase.mk x) = piProj n B x := rfl

theorem continuous_piBaseProj : Continuous (piBaseProj n B) :=
  continuous_pi fun i => FCone.continuous_baseProj.comp
    ((continuous_apply i).comp continuous_piBasePr)

theorem piBaseProj_surjective : Surjective (piBaseProj n B) := fun b =>
  ⟨ConeBase.mk fun i => FCone.ofPoint (b i), rfl⟩

theorem piBaseProj_eq_iff {p p' : PiBase n B} :
    piBaseProj n B p = piBaseProj n B p' ↔
      ∃ t : PiTorus q, piTorusAut n (fun i => FCone (n i) (B i)) t • p = p' := by
  rw [← piBasePr_eq_iff]
  constructor
  · intro h
    exact funext fun i => FCone.baseProj_injective (congrFun h i)
  · intro h
    funext i
    show FCone.baseProj (piBasePr n (fun i => FCone (n i) (B i)) p i) =
      FCone.baseProj (piBasePr n (fun i => FCone (n i) (B i)) p' i)
    rw [h]

theorem piBaseProj_piBaseMap (c : Fin (q + 1) → RPos) (p : PiBase n B) :
    piBaseProj n B (piBaseMap n (fun i => FCone (n i) (B i)) c p) = piBaseProj n B p := by
  funext i
  show FCone.baseProj (piBasePr n (fun i => FCone (n i) (B i))
      (piBaseMap n (fun i => FCone (n i) (B i)) c p) i) =
    FCone.baseProj (piBasePr n (fun i => FCone (n i) (B i)) p i)
  rw [piBasePr_piBaseMap]

/-- **Prop. 2, local triviality over `B₀ × … × B_q`**, equivariantly. -/
theorem exists_trivialization_piBaseProj (b : ∀ i, B i) :
    ∃ T : Trivialization (Fin q → RPos) (piBaseProj n B), b ∈ T.baseSet ∧
      ∀ p ∈ T.source, ∀ c, piBaseMap n (fun i => FCone (n i) (B i)) c p ∈ T.source ∧
        T (piBaseMap n (fun i => FCone (n i) (B i)) c p) = ((T p).1, piRatioHom q c * (T p).2) := by
  obtain ⟨T, hb, hT⟩ := exists_trivialization_piBasePr (n := n) (V := fun i => FCone (n i) (B i))
    (piBaseProjHomeomorph.symm b)
  refine ⟨trivializationCompHomeomorph T piBaseProjHomeomorph, ?_, fun x hx c => ?_⟩
  · show piBaseProjHomeomorph.symm b ∈ T.baseSet
    exact hb
  · rw [trivializationCompHomeomorph_source] at hx ⊢
    obtain ⟨h1, h2⟩ := hT x hx c
    refine ⟨h1, ?_⟩
    erw [trivializationCompHomeomorph_apply, trivializationCompHomeomorph_apply, h2]

/-- **Prop. 2, global triviality for paracompact factors**: `F⁻¹(∏ F(Bᵢ)) ≃ₜ (∏ Bᵢ) × ℝ₊*^{p−1}`
over the base, `(λᵢ)` acting on the fibre by `(λ_{j+1}/λ₀)_j`. -/
theorem exists_piBase_homeomorph [∀ i, ParacompactSpace (B i)] :
    ∃ H : PiBase n B ≃ₜ (∀ i, B i) × (Fin q → RPos), (∀ p, (H p).1 = piBaseProj n B p) ∧
      ∀ c p, H (piBaseMap n (fun i => FCone (n i) (B i)) c p) =
        ((H p).1, piRatioHom q c * (H p).2) := by
  obtain ⟨H₀, hH₀1, hH₀2⟩ := exists_piHomeomorph (n := n) (B := B)
  have hH₀s : ∀ c y, H₀.symm ((H₀ y).1, c * (H₀ y).2) = piSMul n c y := fun c y => by
    rw [← hH₀2, Homeomorph.symm_apply_apply]
  let f : (∀ i, FCone (n i) (B i)) → (∀ i, B i) × (Fin q → RPos) :=
    fun x => ((H₀ x).1, piRatioHom q (H₀ x).2)
  have hf : ∀ x x', coneRel (pdim n) (∀ i, FCone (n i) (B i)) x x' → f x = f x' := by
    intro x x' h
    obtain ⟨d, rfl⟩ := ConeBase.rel_iff.1 h
    show ((H₀ (posSMul (pdim n + 1) d x')).1, piRatioHom q (H₀ (posSMul (pdim n + 1) d x')).2) =
      ((H₀ x').1, piRatioHom q (H₀ x').2)
    rw [← piSMul_const, hH₀2, map_mul, piRatioHom_const, one_mul]
  let F : PiBase n B → (∀ i, B i) × (Fin q → RPos) := Quotient.lift f hf
  let G : (∀ i, B i) × (Fin q → RPos) → PiBase n B :=
    fun z => ConeBase.mk (H₀.symm (z.1, (Fin.cons 1 z.2 : Fin (q + 1) → RPos)))
  have hFmk : ∀ x, F (ConeBase.mk x) = f x := fun _ => rfl
  have hFc : Continuous F := continuous_quot_lift _
    ((continuous_fst.comp H₀.continuous).prodMk
      ((map_continuous_piRatio q).comp (continuous_snd.comp H₀.continuous)))
  have hGc : Continuous G := ConeBase.continuous_mk.comp (H₀.symm.continuous.comp
    (continuous_fst.prodMk (continuous_const.finCons continuous_snd)))
  have hFG : ∀ z, F (G z) = z := by
    rintro ⟨b, t⟩
    show f (H₀.symm (b, (Fin.cons 1 t : Fin (q + 1) → RPos))) = (b, t)
    simp only [f, Homeomorph.apply_symm_apply, piRatioHom_cons]
  have hGF : ∀ p, G (F p) = p := by
    intro p
    obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
    rw [hFmk]
    show ConeBase.mk (H₀.symm ((H₀ x).1, (Fin.cons 1 (piRatioHom q (H₀ x).2) :
      Fin (q + 1) → RPos))) = ConeBase.mk x
    rw [cons_piRatioHom, mul_comm, hH₀s, piSMul_const, ConeBase.mk_posSMul]
  refine ⟨⟨⟨F, G, hGF, hFG⟩, hFc, hGc⟩, fun p => ?_, fun c p => ?_⟩
  · obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
    show (H₀ x).1 = _
    rw [hH₀1]
    rfl
  · obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
    show F (piBaseMap n (fun i => FCone (n i) (B i)) c (ConeBase.mk x)) =
      ((F (ConeBase.mk x)).1, piRatioHom q c * (F (ConeBase.mk x)).2)
    rw [piBaseMap_mk, hFmk, hFmk]
    simp only [f, hH₀2, map_mul]

/-- **§ 3 Prop. 2 for general `p`** (`bzprop:c1s3p2_fibre_produit`): « Le quotient
$\R^{+p}/\R^+$ opère sur $F^{-1}(F(B_1)\times\ldots\times F(B_p))$ et définit sur cette variété
localement projective une structure d'espace fibré principal de base
$(B_1\times\ldots\times B_p)$ ». `PiTorus q = ℝ₊*^p/diagonal` acts on `PiBase n B` by projective
automorphisms (`piTorusAut`, the class of `(λᵢ)` acting by `[m] ↦ [(λᵢmᵢ)]`), freely, with orbits
the fibres of the continuous surjection `piBaseProj` onto `∏ Bᵢ`, locally trivially and
equivariantly (fibre coordinates `torusCoord`, an isomorphism `ℝ^{+p}/ℝ^+ ≃* ℝ₊*^{p−1}`,
`torusCoordEquiv`), and globally trivially for paracompact factors. -/
theorem prop2_fibre_produit_pi :
    (∀ (c : Fin (q + 1) → RPos) (x : ∀ i, FCone (n i) (B i)),
      piTorusAut n (fun i => FCone (n i) (B i)) (c : PiTorus q) • (ConeBase.mk x : PiBase n B) =
        ConeBase.mk (piSMul n c x)) ∧
    (∀ (t : PiTorus q) (p : PiBase n B), piTorusAut n (fun i => FCone (n i) (B i)) t • p = p →
      t = 1) ∧
    Continuous (piBaseProj n B) ∧ Surjective (piBaseProj n B) ∧
    (∀ p p' : PiBase n B, piBaseProj n B p = piBaseProj n B p' ↔
      ∃ t : PiTorus q, piTorusAut n (fun i => FCone (n i) (B i)) t • p = p') ∧
    (∀ b : ∀ i, B i, ∃ T : Trivialization (Fin q → RPos) (piBaseProj n B), b ∈ T.baseSet ∧
      ∀ p ∈ T.source, ∀ t : PiTorus q,
        piTorusAut n (fun i => FCone (n i) (B i)) t • p ∈ T.source ∧
        T (piTorusAut n (fun i => FCone (n i) (B i)) t • p) = ((T p).1, torusCoord q t * (T p).2)) ∧
    (∀ [∀ i, ParacompactSpace (B i)], ∃ H : PiBase n B ≃ₜ (∀ i, B i) × (Fin q → RPos),
      (∀ p, (H p).1 = piBaseProj n B p) ∧
      ∀ (t : PiTorus q) (p : PiBase n B), H (piTorusAut n (fun i => FCone (n i) (B i)) t • p) =
        ((H p).1, torusCoord q t * (H p).2)) := by
  refine ⟨fun c x => rfl, fun t p h => eq_one_of_piTorusAut_smul_eq h, continuous_piBaseProj,
    piBaseProj_surjective, fun _ _ => piBaseProj_eq_iff, fun b => ?_, fun {_} => ?_⟩
  · obtain ⟨T, hb, hT⟩ := exists_trivialization_piBaseProj (n := n) (B := B) b
    refine ⟨T, hb, fun p hp t => ?_⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective t
    exact hT p hp c
  · obtain ⟨H, hH1, hH2⟩ := exists_piBase_homeomorph (n := n) (B := B)
    refine ⟨H, hH1, fun t p => ?_⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective t
    exact hH2 c p

end PiFBase

/-- A σ-compact locally projective manifold is paracompact (Hausdorff, locally compact). -/
theorem paracompactSpace_of_sigmaCompact {k : ℕ} (M : Type*) [TopologicalSpace M]
    [ChartedSpace (S k) M] [T2Space M] [SigmaCompactSpace M] : ParacompactSpace M := by
  haveI := ChartedSpace.locallyCompactSpace (S k) M
  infer_instance

section Def1Pi

open PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {B : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (B i)]
  [∀ i, ChartedSpace (S (n i)) (B i)] [∀ i, HasGroupoid (B i) (projGroupoid (n i))]
  [∀ i, T2Space (B i)]

/-- **§ 3 Déf. 1 for general `p`** (`bzdef:c1s3d1_produit_cones`): the product
`F(B₀) × … × F(B_q)` is an affine conical manifold of dimension `Σ (nᵢ + 1)` (`PiCone`, charts onto
`∏ (ℝ^{nᵢ+1} − {O}) ⊂ ℝ^{Σ(nᵢ+1)} − {O}`, transitions in `∏ GU(nᵢ+1) ↪ GU(Σ(nᵢ+1))`), and « Nous
munirons ce produit d'une structure d'espace fibré $\R^{+p}$ principal de base
$B_1\times\ldots\times B_p$ en faisant opérer $\R^{+p}$ … suivant la formule $(\lambda_i) \times
(m_i) = (\lambda_i m_i)$ »: `piSMul` is a continuous action of `ℝ₊*^p`, free, whose orbits are the
fibres of the continuous surjection `piProj` onto `∏ Bᵢ`, locally trivial and equivariantly so
(`Trivialization` in Mathlib's sense, at every point of the base), globally trivial for paracompact
(e.g. σ-compact, `paracompactSpace_of_sigmaCompact`) factors; its diagonal is Déf. 3's homothety of
the product cone; every `(λᵢ)` is an automorphism of the locally affine structure (« Un élément
quelconque de $\R^{+p}$ est seulement un automorphisme affin »), and of the conical one iff
`∏ λᵢ^{dim F(Bᵢ)} = 1` (nonempty factors). -/
theorem def1_produit_cones_pi :
    (∀ x : ∀ i, FCone (n i) (B i), piSMul n 1 x = x) ∧
    (∀ (c d : Fin (q + 1) → RPos) (x : ∀ i, FCone (n i) (B i)),
      piSMul n (c * d) x = piSMul n c (piSMul n d x)) ∧
    Continuous (fun p : (Fin (q + 1) → RPos) × (∀ i, FCone (n i) (B i)) => piSMul n p.1 p.2) ∧
    (∀ (c : Fin (q + 1) → RPos) (x : ∀ i, FCone (n i) (B i)), piSMul n c x = x → c = 1) ∧
    Continuous (piProj n B) ∧ Surjective (piProj n B) ∧
    (∀ x x' : ∀ i, FCone (n i) (B i),
      piProj n B x = piProj n B x' ↔ ∃ c : Fin (q + 1) → RPos, piSMul n c x = x') ∧
    (∀ b : ∀ i, B i, ∃ T : Trivialization (Fin (q + 1) → RPos) (piProj n B), b ∈ T.baseSet ∧
      ∀ x ∈ T.source, ∀ c, piSMul n c x ∈ T.source ∧ T (piSMul n c x) = ((T x).1, c * (T x).2)) ∧
    (∀ [∀ i, ParacompactSpace (B i)],
      ∃ H : (∀ i, FCone (n i) (B i)) ≃ₜ (∀ i, B i) × (Fin (q + 1) → RPos),
        (∀ x, (H x).1 = piProj n B x) ∧ ∀ c x, H (piSMul n c x) = ((H x).1, c * (H x).2)) ∧
    (∀ (c : RPos) (x : ∀ i, FCone (n i) (B i)),
      piSMul n (fun _ => c) x = posSMul (pdim n + 1) c x) ∧
    (∀ c : Fin (q + 1) → RPos,
      @IsGXMorphism (GAR (pdim n + 1)) (Fin (pdim n + 1) → ℝ) _ _ _ (∀ i, FCone (n i) (B i)) _
        (∀ i, FCone (n i) (B i)) _ (affineChartedSpace (pdim n + 1) (∀ i, FCone (n i) (B i)))
        (affineChartedSpace (pdim n + 1) (∀ i, FCone (n i) (B i))) (piSMul n c)) ∧
    (∀ [∀ i, Nonempty (B i)] (c : Fin (q + 1) → RPos),
      IsGXMorphism (GUR (pdim n + 1)) (RnO (pdim n + 1))
        (piSMul n c : (∀ i, FCone (n i) (B i)) → ∀ i, FCone (n i) (B i)) ↔
      ∏ i, ((c i : ℝˣ) : ℝ) ^ (n i + 1) = 1) := by
  refine ⟨piSMul_one, piSMul_mul, continuous_piSMul, fun _ _ h => eq_one_of_piSMul_eq h,
    continuous_piProj, piProj_surjective, fun _ _ => piProj_eq_iff, exists_trivialization_piProj,
    fun {_} => exists_piHomeomorph, piSMul_const, isGXMorphism_affine_piSMul, fun {_} c => ?_⟩
  haveI : ∀ i, Nonempty (FCone (n i) (B i)) := fun i => ⟨FCone.ofPoint (Classical.arbitrary _)⟩
  exact isGXMorphism_piSMul_iff c

end Def1Pi

/-! ### § 3 Prop. 3 for general `p` — homogeneous, sweepable, divisible -/

section Prop3Pi

open PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {B : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (B i)]
  [∀ i, ChartedSpace (S (n i)) (B i)] [∀ i, HasGroupoid (B i) (projGroupoid (n i))]
  [∀ i, T2Space (B i)]

/-- **`F⁻¹(F₀(φ₀) ∘ … ∘ F_q(φ_q))`**: automorphisms `φᵢ` of the `Bᵢ` as an automorphism of
`F⁻¹(F(B₀) × … × F(B_q))` (Prop. 3's proof, « $F^{-1}(F_i(\varphi_i))$ est un automorphisme de la
structure localement projective »). -/
def piAut (φ : ∀ i, GXAut (GSR (n i)) (S (n i)) (B i)) :
    GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B) :=
  GXAut.ofBijective (ConeBase.isGXMorphism_map (isGXMorphism_piMap fun i =>
      FCone.isGXMorphism_map (φ i).isGXMorphism))
    (bijective_iff_has_inverse.2 ⟨ConeBase.map (isGXMorphism_piMap fun i =>
      FCone.isGXMorphism_map (φ i)⁻¹.isGXMorphism),
      fun p => by
        obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
        simp only [ConeBase.map_mk]
        congr 1
        funext i
        simp only [Pi.map_apply]
        rw [← FCone.autMap_smul, ← FCone.autMap_smul, FCone.autMap_inv_smul_autMap_smul],
      fun p => by
        obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
        simp only [ConeBase.map_mk]
        congr 1
        funext i
        simp only [Pi.map_apply]
        have h := FCone.autMap_inv_smul_autMap_smul (φ i)⁻¹ (x i)
        rw [inv_inv] at h
        rw [← FCone.autMap_smul, ← FCone.autMap_smul, h]⟩)

theorem piAut_smul_mk (φ : ∀ i, GXAut (GSR (n i)) (S (n i)) (B i)) (x : ∀ i, FCone (n i) (B i)) :
    piAut φ • (ConeBase.mk x : PiBase n B) =
      ConeBase.mk (fun i => FCone.autMap (φ i) • x i) := rfl

theorem piBaseProj_piAut (φ : ∀ i, GXAut (GSR (n i)) (S (n i)) (B i)) (p : PiBase n B) :
    piBaseProj n B (piAut φ • p) = fun i => φ i • piBaseProj n B p i := by
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rw [piAut_smul_mk, piBaseProj_mk, piBaseProj_mk]
  funext i
  exact FCone.proj_autMap_smul _ _

/-- **Prop. 3, homogeneous**, for every `p`. -/
theorem isHomogeneous_piBase (h : ∀ i, IsHomogeneous (GSR (n i)) (S (n i)) (B i)) :
    IsHomogeneous (GSR (pdim n)) (S (pdim n)) (PiBase n B) := by
  refine ⟨fun p p' => ?_⟩
  have key : ∀ i, ∃ φ : GXAut (GSR (n i)) (S (n i)) (B i),
      φ • piBaseProj n B p i = piBaseProj n B p' i := fun i => by
    haveI : MulAction.IsPretransitive (GXAut (GSR (n i)) (S (n i)) (B i)) (B i) := h i
    exact MulAction.exists_smul_eq _ _ _
  choose φ hφ using key
  obtain ⟨t, ht⟩ := piBaseProj_eq_iff.1 (show piBaseProj n B (piAut φ • p) = piBaseProj n B p' by
    rw [piBaseProj_piAut]; exact funext hφ)
  exact ⟨piTorusAut n _ t * piAut φ, by rw [mul_smul, ht]⟩

/-- **Prop. 3, sweepable**, for every `p` (« Démontrons par exemple que, si les $B_i$ sont
projectivement balayables, … est projectivement balayable »). -/
theorem isBalayable_piBase (h : ∀ i, IsBalayable (GSR (n i)) (S (n i)) (B i)) :
    IsBalayable (GSR (pdim n)) (S (pdim n)) (PiBase n B) := by
  choose K hK hU using h
  have key := fun i => FCone.exists_isCompact_subset_proj_image (n := n i) (hK i)
  choose L hL hKL using key
  refine ⟨ConeBase.mk '' (univ.pi L), (isCompact_univ_pi hL).image ConeBase.continuous_mk,
    eq_univ_of_forall fun p => ?_⟩
  have key2 : ∀ i, ∃ φ : GXAut (GSR (n i)) (S (n i)) (B i), ∃ y ∈ L i,
      φ • FCone.proj y = piBaseProj n B p i := fun i => by
    have hp : piBaseProj n B p i ∈ ⋃ g ∈ (⊤ : Subgroup (GXAut (GSR (n i)) (S (n i)) (B i))),
        g • K i := (hU i) ▸ mem_univ _
    obtain ⟨φ, -, k, hk, hkp⟩ := mem_iUnion₂.1 hp
    obtain ⟨y, hy, rfl⟩ := hKL i hk
    exact ⟨φ, y, hy, hkp⟩
  choose φ y hy hyp using key2
  obtain ⟨t, ht⟩ := piBaseProj_eq_iff.1
    (show piBaseProj n B (piAut φ • (ConeBase.mk y : PiBase n B)) = piBaseProj n B p by
      rw [piBaseProj_piAut, piBaseProj_mk]; exact funext hyp)
  exact mem_iUnion₂.2 ⟨piTorusAut n _ t * piAut φ, Subgroup.mem_top _, _,
    ⟨y, fun i _ => hy i, rfl⟩, show (piTorusAut n _ t * piAut φ) • _ = p by rw [mul_smul, ht]⟩

/-- `φ ↦ F⁻¹(∏ F(φᵢ))` as a homomorphism. -/
def piAutHom : (∀ i, GXAut (GSR (n i)) (S (n i)) (B i)) →*
    GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B) where
  toFun := piAut
  map_one' := FaithfulSMul.eq_of_smul_eq_smul fun p : PiBase n B => by
    obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
    rw [piAut_smul_mk, one_smul]
    congr 1
    funext i
    rw [Pi.one_apply, ← FCone.autMapHom_apply, map_one, one_smul]
  map_mul' φ ψ := FaithfulSMul.eq_of_smul_eq_smul fun p : PiBase n B => by
    obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
    rw [mul_smul, piAut_smul_mk, piAut_smul_mk, piAut_smul_mk]
    congr 1
    funext i
    rw [Pi.mul_apply, ← FCone.autMapHom_apply, map_mul, mul_smul]
    rfl

theorem commute_piAut_piTorusAut (φ : ∀ i, GXAut (GSR (n i)) (S (n i)) (B i)) (t : PiTorus q) :
    Commute (piAut φ) (piTorusAut n (fun i => FCone (n i) (B i)) t) := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective t
  refine FaithfulSMul.eq_of_smul_eq_smul fun p : PiBase n B => ?_
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rw [mul_smul, mul_smul, piTorusAut_mk_smul, piAut_smul_mk, piAut_smul_mk, piTorusAut_mk_smul]
  congr 1
  funext i
  exact FCone.autMap_smul_posSMul _ _ _

variable (n B) in
/-- **The lattice `H = λ^{ℤ^{p−1}} ⊂ ℝ^{+p}/ℝ^+`** of Prop. 3's proof (« un sous-groupe discret de
$\R^{+p}/\R^+$ tel que le quotient … par $H$ soit compact et topologiquement isomorphe à
$S_1^{(p-1)}$ »), acting on `F⁻¹(∏ F(Bᵢ))`. -/
def latticeHom (lam : RPos) :
    (Fin q → Multiplicative ℤ) →* GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B) :=
  (piTorusAut n (fun i => FCone (n i) (B i))).comp
    ((torusOfCoord q).comp (MonoidHom.compLeft (zpowersHom RPos lam) (Fin q)))

theorem latticeHom_smul (lam : RPos) (k : Fin q → Multiplicative ℤ) (p : PiBase n B) :
    latticeHom n B lam k • p = piBaseMap n (fun i => FCone (n i) (B i))
      (Fin.cons 1 (fun j => lam ^ Multiplicative.toAdd (k j)) : Fin (q + 1) → RPos) p := by
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  rfl

theorem commute_piAut_latticeHom (φ : ∀ i, GXAut (GSR (n i)) (S (n i)) (B i)) (lam : RPos)
    (k : Fin q → Multiplicative ℤ) : Commute (piAut φ) (latticeHom n B lam k) :=
  commute_piAut_piTorusAut _ _

/-- **The group `F⁻¹(F₀(G₀) × … × F_q(G_q)) × H`** of Prop. 3's proof. -/
def piDivHom (G : ∀ i, Subgroup (GXAut (GSR (n i)) (S (n i)) (B i))) (lam : RPos) :
    (∀ i, G i) × (Fin q → Multiplicative ℤ) →* GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B) :=
  (piAutHom.comp
    { toFun := fun g i => (g i : GXAut (GSR (n i)) (S (n i)) (B i))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }).noncommCoprod (latticeHom n B lam)
    fun _ _ => commute_piAut_latticeHom _ _ _

theorem piDivHom_smul (G : ∀ i, Subgroup (GXAut (GSR (n i)) (S (n i)) (B i))) (lam : RPos)
    (γ : (∀ i, G i) × (Fin q → Multiplicative ℤ)) (p : PiBase n B) :
    piDivHom G lam γ • p =
      piAut (fun i => (γ.1 i : GXAut (GSR (n i)) (S (n i)) (B i))) • latticeHom n B lam γ.2 • p := by
  rw [piDivHom, MonoidHom.noncommCoprod_apply, mul_smul]
  rfl

theorem piBaseProj_latticeHom_smul (lam : RPos) (k : Fin q → Multiplicative ℤ)
    (p : PiBase n B) : piBaseProj n B (latticeHom n B lam k • p) = piBaseProj n B p := by
  rw [latticeHom_smul, piBaseProj_piBaseMap]

theorem piBaseProj_piDivHom_smul (G : ∀ i, Subgroup (GXAut (GSR (n i)) (S (n i)) (B i)))
    (lam : RPos) (γ : (∀ i, G i) × (Fin q → Multiplicative ℤ)) (p : PiBase n B) :
    piBaseProj n B (piDivHom G lam γ • p) = fun i => γ.1 i • piBaseProj n B p i := by
  rw [piDivHom_smul, piBaseProj_piAut, piBaseProj_latticeHom_smul]
  rfl

variable [∀ i, ParacompactSpace (B i)]

theorem exists_piBase_homeomorph_lattice :
    ∃ H : PiBase n B ≃ₜ (∀ i, B i) × (Fin q → RPos), (∀ p, (H p).1 = piBaseProj n B p) ∧
      ∀ (lam : RPos) (k : Fin q → Multiplicative ℤ) (p : PiBase n B),
        H (latticeHom n B lam k • p) =
          ((H p).1, (fun j => lam ^ Multiplicative.toAdd (k j)) * (H p).2) := by
  obtain ⟨H, hH1, hH2⟩ := exists_piBase_homeomorph (n := n) (B := B)
  exact ⟨H, hH1, fun lam k p => by rw [latticeHom_smul, hH2, piRatioHom_cons]⟩

/-- **The lattice is discrete**: finitely many lattice elements move a compact set to meet
another (through the radial coordinates of `exists_piBase_homeomorph`). -/
theorem finite_setOf_lattice_inter_nonempty {lam : RPos} (hlam : lam ≠ 1)
    {K L : Set (PiBase n B)} (hK : IsCompact K) (hL : IsCompact L) :
    {k : Fin q → Multiplicative ℤ | ((latticeHom n B lam k • ·) '' K ∩ L).Nonempty}.Finite := by
  obtain ⟨H, -, hH2⟩ := exists_piBase_homeomorph_lattice (n := n) (B := B)
  set ρ : PiBase n B → (Fin q → ℝ) := fun p j => rposLog ((H p).2 j)
  have hρ : Continuous ρ := continuous_pi fun j => continuous_rposLog.comp
    ((continuous_apply j).comp (continuous_snd.comp H.continuous))
  obtain ⟨r₁, hr₁⟩ := ((hK.image hρ).isBounded).subset_closedBall 0
  obtain ⟨r₂, hr₂⟩ := ((hL.image hρ).isBounded).subset_closedBall 0
  have hl' : 0 < |rposLog lam| := abs_pos.2 (rposLog_ne_zero hlam)
  set M : ℤ := ⌈(r₁ + r₂) / |rposLog lam|⌉
  refine ((Set.Finite.pi fun _ : Fin q => (Set.finite_Icc (-M) M).preimage
    Multiplicative.toAdd.injective.injOn)).subset fun k hk => ?_
  obtain ⟨_, ⟨p, hp, rfl⟩, hpL⟩ := hk
  rw [mem_univ_pi]
  intro j
  have h1 : |ρ p j| ≤ r₁ := by
    have := hr₁ ⟨p, hp, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact (norm_le_pi_norm (ρ p) j).trans this
  have h2 : |ρ (latticeHom n B lam k • p) j| ≤ r₂ := by
    have := hr₂ ⟨_, hpL, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact (norm_le_pi_norm _ j).trans this
  have h3 : ρ (latticeHom n B lam k • p) j =
      ((Multiplicative.toAdd (k j) : ℤ) : ℝ) * rposLog lam + ρ p j := by
    simp only [ρ, hH2, Pi.mul_apply, rposLog_mul, rposLog_zpow]
  rw [h3] at h2
  have h4 : |((Multiplicative.toAdd (k j) : ℤ) : ℝ)| * |rposLog lam| ≤ r₁ + r₂ := by
    rw [← abs_mul]
    calc |((Multiplicative.toAdd (k j) : ℤ) : ℝ) * rposLog lam|
        = |((Multiplicative.toAdd (k j) : ℤ) * rposLog lam + ρ p j) - ρ p j| := by ring_nf
      _ ≤ |(Multiplicative.toAdd (k j) : ℤ) * rposLog lam + ρ p j| + |ρ p j| := abs_sub _ _
      _ ≤ r₂ + r₁ := add_le_add h2 h1
      _ = r₁ + r₂ := add_comm _ _
  have hk' : |((Multiplicative.toAdd (k j) : ℤ) : ℝ)| ≤ (r₁ + r₂) / |rposLog lam| :=
    (le_div_iff₀ hl').2 h4
  have hk'' : |Multiplicative.toAdd (k j)| ≤ M := by
    have := hk'.trans (Int.le_ceil _)
    exact_mod_cast this
  exact abs_le.1 hk''

/-- **Prop. 3, divisible**, for every `p` (the proof printed): the group
`F⁻¹(F₀(G₀) × … × F_q(G_q)) × λ^{ℤ^{p−1}}` is properly discontinuous, free, and has compact
quotient (« Le quotient … est une variété localement projective compacte »). -/
theorem isDivisible_piDivHom (G : ∀ i, Subgroup (GXAut (GSR (n i)) (S (n i)) (B i)))
    (h₁ : ∀ i, ProperlyDiscontinuousSMul (G i) (B i)) (h₂ : ∀ i, IsCancelSMul (G i) (B i))
    (h₃ : ∀ i, CompactSpace (MulAction.orbitRel.Quotient (G i) (B i))) {lam : RPos}
    (hlam : lam ≠ 1) :
    ProperlyDiscontinuousSMul (piDivHom G lam).range (PiBase n B) ∧
      IsCancelSMul (piDivHom G lam).range (PiBase n B) ∧
      CompactSpace (MulAction.orbitRel.Quotient (piDivHom G lam).range (PiBase n B)) := by
  refine ⟨⟨fun {K L} hK hL => ?_⟩, ?_, ?_⟩
  · -- proper discontinuity
    set A : ∀ i, Set (G i) := fun i => {φ : G i | ((φ • ·) '' ((fun p => piBaseProj n B p i) '' K) ∩
      (fun p => piBaseProj n B p i) '' L).Nonempty}
    have hA : ∀ i, (A i).Finite := fun i => (h₁ i).finite_disjoint_inter_image
      (hK.image ((continuous_apply i).comp continuous_piBaseProj))
      (hL.image ((continuous_apply i).comp continuous_piBaseProj))
    set Z : (∀ i, G i) → Set (Fin q → Multiplicative ℤ) := fun φ => {k |
      ((latticeHom n B lam k • ·) '' K ∩
        ((piAut fun i => (φ i : GXAut (GSR (n i)) (S (n i)) (B i)))⁻¹ • ·) '' L).Nonempty}
    have hZ : ∀ φ, (Z φ).Finite := fun φ => finite_setOf_lattice_inter_nonempty hlam hK
      (hL.image (continuous_const_smul _))
    set Pf : Set ((∀ i, G i) × (Fin q → Multiplicative ℤ)) :=
      ⋃ φ ∈ univ.pi A, {φ} ×ˢ Z φ
    have hPf : Pf.Finite :=
      (Set.Finite.pi hA).biUnion fun φ _ => (finite_singleton φ).prod (hZ φ)
    refine (hPf.image fun γ => (⟨piDivHom G lam γ, γ, rfl⟩ : (piDivHom G lam).range)).subset ?_
    rintro ⟨γ', γ, rfl⟩ ⟨_, ⟨x, hx, rfl⟩, hxL⟩
    have hxL' : piDivHom G lam γ • x ∈ L := hxL
    have hpr := piBaseProj_piDivHom_smul G lam γ x
    have hγ : γ.1 ∈ univ.pi A := mem_univ_pi.2 fun i =>
      ⟨γ.1 i • piBaseProj n B x i, ⟨piBaseProj n B x i, ⟨x, hx, rfl⟩, rfl⟩,
        ⟨piDivHom G lam γ • x, hxL', congrFun hpr i⟩⟩
    refine ⟨γ, mem_iUnion₂.2 ⟨γ.1, hγ, mem_prod.2 ⟨rfl, ⟨_, ⟨x, hx, rfl⟩, ⟨_, hxL', ?_⟩⟩⟩⟩, rfl⟩
    show (piAut fun i => (γ.1 i : GXAut (GSR (n i)) (S (n i)) (B i)))⁻¹ •
      piDivHom G lam γ • x = _
    rw [piDivHom_smul, inv_smul_smul]
  · -- freeness
    refine isCancelSMul_iff_eq_one_of_smul_eq.2 ?_
    rintro ⟨γ', γ, rfl⟩ x hx
    have hx' : piDivHom G lam γ • x = x := hx
    have hpr := piBaseProj_piDivHom_smul G lam γ x
    rw [hx'] at hpr
    have e₁ : γ.1 = 1 := funext fun i => (h₂ i).eq_one_of_smul (x := piBaseProj n B x i)
      (congrFun hpr i).symm
    rw [piDivHom_smul, e₁] at hx'
    have hone : piAut (fun i => ((1 : ∀ i, G i) i : GXAut (GSR (n i)) (S (n i)) (B i))) = 1 :=
      map_one (piAutHom (n := n) (B := B))
    rw [hone, one_smul] at hx'
    have h2 := eq_one_of_piTorusAut_smul_eq hx'
    have h3 := congrArg (torusCoord q) h2
    rw [map_one] at h3
    have e₂ : γ.2 = 1 := by
      funext j
      have hj := congrFun h3 j
      simp only [torusOfCoord, MonoidHom.coe_comp, comp_apply, MonoidHom.coe_mk, OneHom.coe_mk,
        torusCoord_mk, Fin.cons_succ, Fin.cons_zero, inv_one, mul_one, Pi.one_apply,
        MonoidHom.compLeft_apply, zpowersHom_apply] at hj
      have := congrArg rposLog hj
      rw [rposLog_zpow, rposLog_one, mul_eq_zero] at this
      have h0 : Multiplicative.toAdd (γ.2 j) = 0 := by
        exact_mod_cast this.resolve_right (rposLog_ne_zero hlam)
      exact h0
    have hγ : γ = 1 := Prod.ext e₁ e₂
    exact Subtype.ext (show piDivHom G lam γ = 1 by rw [hγ, map_one])
  · -- compact quotient
    have hcs : ∀ i, ContinuousConstSMul (G i) (B i) := fun i =>
      ⟨fun g => continuous_const_smul (g : GXAut (GSR (n i)) (S (n i)) (B i))⟩
    have hlc : ∀ i, LocallyCompactSpace (B i) := fun i =>
      ChartedSpace.locallyCompactSpace (S (n i)) (B i)
    have key := fun i => exists_isCompact_forall_exists_smul_mem (hQ := h₃ i)
    choose K hK hKm using key
    obtain ⟨H, hH1, hH2⟩ := exists_piBase_homeomorph_lattice (n := n) (B := B)
    set Lg := rposLog lam
    have hL := rposLog_ne_zero hlam
    set I : Set RPos := (fun t : ℝ => rposExp (t * Lg)) '' Icc 0 1
    have hI : IsCompact I := isCompact_Icc.image (continuous_rposExp.comp
      (continuous_id.mul continuous_const))
    set Kt := H.symm '' (univ.pi K ×ˢ univ.pi fun _ : Fin q => I)
    have hKt : IsCompact Kt := ((isCompact_univ_pi hK).prod (isCompact_univ_pi fun _ => hI)).image
      H.symm.continuous
    refine ⟨?_⟩
    have huniv : (univ : Set (MulAction.orbitRel.Quotient (piDivHom G lam).range (PiBase n B))) =
        Quotient.mk _ '' Kt := by
      refine (eq_univ_of_forall fun Q => ?_).symm
      obtain ⟨p, rfl⟩ := Quotient.mk_surjective Q
      have key2 := fun i => hKm i (piBaseProj n B p i)
      choose γ hγ using key2
      set p₁ := piDivHom G lam (γ, 1) • p with hp₁
      set rr := (H p₁).2 with hrr
      set m : Fin q → ℤ := fun j => ⌊rposLog (rr j) / Lg⌋
      set t : Fin q → ℝ := fun j => Int.fract (rposLog (rr j) / Lg)
      have hr : ∀ j, rr j = lam ^ m j * rposExp (t j * Lg) := fun j => by
        refine rposLog_injective ?_
        rw [rposLog_mul, rposLog_zpow, rposLog_rposExp, ← add_mul, Int.floor_add_fract,
          div_mul_cancel₀ _ hL]
      set k : Fin q → Multiplicative ℤ := fun j => Multiplicative.ofAdd (-m j)
      have hp₂ : piDivHom G lam (γ, k) • p = latticeHom n B lam k • p₁ := by
        rw [hp₁, piDivHom_smul, piDivHom_smul, map_one, one_smul,
          ← mul_smul, ← mul_smul, (commute_piAut_latticeHom _ _ _).eq]
      have hpp₁ : piBaseProj n B p₁ = fun i => γ i • piBaseProj n B p i := by
        rw [hp₁, piBaseProj_piDivHom_smul]
      have hHp₂ : H (piDivHom G lam (γ, k) • p) =
          (piBaseProj n B p₁, fun j => rposExp (t j * Lg)) := by
        rw [hp₂, hH2, hH1]
        refine Prod.ext rfl (funext fun j => ?_)
        simp only [Pi.mul_apply, k, toAdd_ofAdd]
        rw [← hrr, hr j, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
      refine ⟨piDivHom G lam (γ, k) • p,
        ⟨H (piDivHom G lam (γ, k) • p), ?_, H.symm_apply_apply _⟩, ?_⟩
      · rw [hHp₂, hpp₁]
        exact ⟨mem_univ_pi.2 fun i => hγ i, mem_univ_pi.2 fun j =>
          ⟨t j, ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩⟩
      · exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨⟨_, _, rfl⟩, rfl⟩)
    rw [huniv]
    exact hKt.image continuous_quotient_mk'

end Prop3Pi

section Prop3PiStatement

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {B : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (B i)]
  [∀ i, ChartedSpace (S (n i)) (B i)] [∀ i, HasGroupoid (B i) (projGroupoid (n i))]
  [∀ i, T2Space (B i)]

/-- **§ 3 Prop. 3 for general `p`** (`bzprop:c1s3p3_produit_homogene`): « Soient $B_1, \ldots,
B_p$ des variétés localement projectives homogènes (resp. balayables, resp. divisibles); la variété
localement projective $F^{-1}(F(B_1)\times\ldots\times F(B_p))$ est homogène (resp. balayable,
resp. divisible) », the « variété » factors Hausdorff, and paracompact (implied by second
countability) in the divisible case, where the group is the printed
`F⁻¹(F₁(G₁) × … × F_p(G_p)) × H`, `H = λ^{ℤ^{p−1}}` (`piDivHom`, any `λ ≠ 1`). -/
theorem prop3_produit_homogene_pi :
    ((∀ i, IsHomogeneous (GSR (n i)) (S (n i)) (B i)) →
      IsHomogeneous (GSR (pdim n)) (S (pdim n)) (PiBase n B)) ∧
    ((∀ i, IsBalayable (GSR (n i)) (S (n i)) (B i)) →
      IsBalayable (GSR (pdim n)) (S (pdim n)) (PiBase n B)) ∧
    (∀ [∀ i, ParacompactSpace (B i)], (∀ i, IsDivisible (GSR (n i)) (S (n i)) (B i)) →
      IsDivisible (GSR (pdim n)) (S (pdim n)) (PiBase n B)) := by
  refine ⟨isHomogeneous_piBase, isBalayable_piBase, fun {_} h => ?_⟩
  choose G hG₁ hG₂ hG₃ using h
  exact ⟨_, isDivisible_piDivHom G hG₁ hG₂ hG₃ rposExp_one_ne_one⟩

end Prop3PiStatement

end Benzecri
