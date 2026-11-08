import Benzecri.Applications.ProductsGeneral
import Benzecri.Applications.Converse

/-!
# `Benzecri.Applications.ConverseGeneral` — § 3 Déf. 2 and Prop. 4 for general `p`

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 3, journal pp. 245–246; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`, checked against the scan (PDF pp. 18–19).
Package WP-45y (wave 5b, DEC-128: general `p`, unequal dimensions), over the flat product cone of
`ProductsGeneral`.

* **`bzdef:c1s3d2_automorphisme_compatible`** — `benzecri1960_ch1.tex:806` (l.806–821, p. 245).
  **MARKED.** `Benzecri.IsCompatibleAssocPi σ f` / `IsCompatiblePi f`: `f • [m] = t • [(φᵢ m_{σ(i)})ᵢ]`
  with `φᵢ : F(B_{σ(i)}) ≅ F(Bᵢ)` conical affine isomorphisms (`IsConeIso`, which forces
  `dim B_{σ(i)} = dim Bᵢ`) and `t ∈ ℝ^{+p}/ℝ^+`. The compatible automorphisms form a GROUP
  (`compatibleSubgroup`; `isCompatibleAssocPi_one`, `IsCompatibleAssocPi.mul` — associated with
  `τ * σ` —, `.inv` — with `σ⁻¹`), `G_I` (`compatibleIdSubgroup`) is a subgroup of index `≤ p!`
  (`relIndex_compatibleIdSubgroup_le`: finite and `≤ (q+1)!`). The clause « si l'on définit un
  automorphisme φ de la structure conique affine du produit par la formule » is proved: the permuted
  map `(mᵢ) ↦ (φᵢ m_{σ(i)})` is a conical automorphism of the product cone
  (`isGXMorphism_piPermMap`: a block permutation of equal-size blocks after `diag(gᵢ)`, `|det| = 1`),
  so every printed `(σ, φ, t)` gives a compatible automorphism (`exists_isCompatibleAssocPi`). For
  nonempty factors the permutation is determined by `f` (`IsCompatibleAssocPi.perm_unique`, through the
  free torus action), `f ↦ σ_f⁻¹` is a homomorphism `compatiblePerm : G →* Perm (Fin p)` with kernel
  `G_I` (`ker_compatiblePerm`).
* **`bzprop:c1s3p4_reciproque`** — `benzecri1960_ch1.tex:823` (l.823–868, pp. 245–246).
  **MARKED.** `Benzecri.prop4_reciproque_pi`: both assertions, the hypotheses stated for the group
  `G` with Déf. 15's predicates (`MulAction.IsPretransitive G _`, `IsBalayableFor _ _ _ G`), for
  nonempty (« variété », DEC-128) factors of arbitrary dimensions: `homogeneous_of_compatible_pi`
  (the composite along the cycle of `i₀`, `h` its length, as printed),
  `balayable_of_compatible_pi`.

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
> balayables. *Démonstration.* […] Mais $G_I$ est un sous-groupe de $G$ d'indice fini au plus égal à
> $p\,!$ […]

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `p` locally projective manifolds | ✓ `p = q + 1 ≥ 1`, dimensions `n i` arbitrary and unequal |
| « variété »: Hausdorff | ✓ carried (`[∀ i, T2Space (B i)]`) |
| « variété »: nonempty | reading (DEC-128, as DEC-114): `[∀ i, Nonempty (B i)]` for Prop. 4 and for the extras `perm_unique` / `compatiblePerm` / `ker_compatiblePerm` only |
| « si l'on définit un automorphisme φ … par la formule » | ✓ `isGXMorphism_piPermMap`, `exists_isCompatibleAssocPi` |
| « isomorphismes coniques affins entre $F(B_{\sigma(i)})$ et $F(B_i)$ » | `IsConeIso`: homeomorphisms with `dim` equality and the conical-morphism property (inverse conical too) |
| « le groupe des automorphismes compatibles » | ✓ `compatibleSubgroup`, proved closed under `*`, `⁻¹` |
| « $G_I$ … d'indice fini au plus égal à $p\,!$ » | ✓ `relIndex ≠ 0 ∧ relIndex ≤ (q+1)!` |

## SCOPE (disclosed)

* **Dimensions.** A conical (resp. projective) isomorphism between structures of different
  dimensions does not exist; `IsConeIso k k' φ` / `IsProjIso k k' θ` carry `k = k'` and the morphism
  property after identification. So `σ` permutes only factors of equal dimension, by construction.
* **The permutation of `f`** is determined by `f` for nonempty factors (`perm_unique`): `f` conjugates
  the torus element `[c]` to `[c ∘ σ]` (`smul_torus`) and the torus acts freely. The index bound is
  proved without it (cosets of `G_I` inject into `Perm (Fin p)`); the homomorphism to `Perm` and its
  kernel are stated for nonempty factors (DEC-128's reading of « variété »).
* **The second assertion** is proved directly with finitely many fixed isomorphisms `B_j ≅ B_{i₀}`
  (one per index class), which is the content of « balayable par $G$ entraîne balayable par $G_I$ »;
  the index bound is proved separately as Déf. 2/Prop. 4's printed device.
* `piFConeCast`: `F(B_j) ≃ₜ F(B_i)` along `j = i` (dependent-type bookkeeping for `σ⁻¹`); `castRnO`:
  `ℝ^{k+1} − {O} → ℝ^{k'+1} − {O}` along `k = k'` (the same for the charts of `IsConeIso`).
* Generic lemma (upstream candidate): `abs_det_funCongrLeft`, a permutation of coordinates has
  `|det| = 1`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Function
open scoped Pointwise

namespace Benzecri

universe u

attribute [local instance] t2Space_RnO

/-! ### Isomorphisms between structures whose dimensions are indexed differently -/

section Cast

/-- **A conical affine isomorphism between `V` (dimension `k + 1`) and `W` (dimension `k' + 1`)**
(Déf. 2's « isomorphismes coniques affins entre $F(B_{\sigma(i)})$ et $F(B_i)$ »): the dimensions
agree and, once identified, `φ` is a conical morphism (its inverse is one too,
`IsGXMorphism.homeomorph_symm`). A conical isomorphism between cones of different dimensions does
not exist, so the equality is part of the notion. -/
def IsConeIso (k k' : ℕ) {V W : Type*} [TopologicalSpace V] [cV : ChartedSpace (RnO (k + 1)) V]
    [TopologicalSpace W] [cW : ChartedSpace (RnO (k' + 1)) W] (φ : V ≃ₜ W) : Prop :=
  ∃ h : k = k', @IsGXMorphism (GUR (k' + 1)) (RnO (k' + 1)) _ _ _ V _ W _ (h ▸ cV) cW φ

/-- **A projective isomorphism between `X` (dimension `k`) and `Y` (dimension `k'`)**: the
dimensions agree and, once identified, `θ` is a projective morphism. -/
def IsProjIso (k k' : ℕ) {X Y : Type*} [TopologicalSpace X] [cX : ChartedSpace (S k) X]
    [TopologicalSpace Y] [cY : ChartedSpace (S k') Y] (θ : X ≃ₜ Y) : Prop :=
  ∃ h : k = k', @IsGXMorphism (GSR k') (S k') _ _ _ X _ Y _ (h ▸ cX) cY θ

theorem IsProjIso.refl {k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (S k) X] :
    IsProjIso k k (Homeomorph.refl X) :=
  ⟨rfl, isGXMorphism_id⟩

theorem IsProjIso.trans {k k' k'' : ℕ} {X Y Z : Type*} [TopologicalSpace X]
    [ChartedSpace (S k) X] [TopologicalSpace Y] [ChartedSpace (S k') Y] [TopologicalSpace Z]
    [ChartedSpace (S k'') Z] {θ : X ≃ₜ Y} {θ' : Y ≃ₜ Z} (h : IsProjIso k k' θ) (h' : IsProjIso k' k'' θ') :
    IsProjIso k k'' (θ.trans θ') := by
  obtain ⟨rfl, h⟩ := h
  obtain ⟨rfl, h'⟩ := h'
  exact ⟨rfl, h'.comp h⟩

theorem IsProjIso.symm {k k' : ℕ} {X Y : Type*} [TopologicalSpace X] [ChartedSpace (S k) X]
    [TopologicalSpace Y] [ChartedSpace (S k') Y] {θ : X ≃ₜ Y} (h : IsProjIso k k' θ) :
    IsProjIso k' k θ.symm := by
  obtain ⟨rfl, h⟩ := h
  exact ⟨rfl, IsGXMorphism.homeomorph_symm (e := θ) h⟩

/-- A projective isomorphism of `X` onto itself is a projective automorphism. -/
def IsProjIso.toAut {k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (S k) X] {θ : X ≃ₜ X}
    (h : IsProjIso k k θ) : GXAut (GSR k) (S k) X :=
  GXAut.ofBijective (h.choose_spec) θ.bijective

@[simp] theorem IsProjIso.toAut_smul {k : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (S k) X] {θ : X ≃ₜ X} (h : IsProjIso k k θ) (x : X) : h.toAut • x = θ x := rfl

theorem IsConeIso.refl {k : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (RnO (k + 1)) V] :
    IsConeIso k k (Homeomorph.refl V) :=
  ⟨rfl, isGXMorphism_id⟩

theorem IsConeIso.trans {k k' k'' : ℕ} {U V W : Type*} [TopologicalSpace U]
    [ChartedSpace (RnO (k + 1)) U] [TopologicalSpace V] [ChartedSpace (RnO (k' + 1)) V]
    [TopologicalSpace W] [ChartedSpace (RnO (k'' + 1)) W] {φ : U ≃ₜ V} {ψ : V ≃ₜ W}
    (h : IsConeIso k k' φ) (h' : IsConeIso k' k'' ψ) : IsConeIso k k'' (φ.trans ψ) := by
  obtain ⟨rfl, h⟩ := h
  obtain ⟨rfl, h'⟩ := h'
  exact ⟨rfl, h'.comp h⟩

theorem IsConeIso.symm {k k' : ℕ} {V W : Type*} [TopologicalSpace V]
    [ChartedSpace (RnO (k + 1)) V] [TopologicalSpace W] [ChartedSpace (RnO (k' + 1)) W]
    {φ : V ≃ₜ W} (h : IsConeIso k k' φ) : IsConeIso k' k φ.symm := by
  obtain ⟨rfl, h⟩ := h
  exact ⟨rfl, IsGXMorphism.homeomorph_symm (e := φ) h⟩

/-- **A conical isomorphism commutes with the homotheties** (Déf. 3 on both sides). -/
theorem IsConeIso.map_posSMul {k k' : ℕ} {V W : Type*} [TopologicalSpace V]
    [ChartedSpace (RnO (k + 1)) V] [HasConeCharts (k + 1) V] [T2Space V]
    [HasGroupoid V (coneGroupoid (k + 1))] [TopologicalSpace W] [ChartedSpace (RnO (k' + 1)) W]
    [HasConeCharts (k' + 1) W] [T2Space W] [HasGroupoid W (coneGroupoid (k' + 1))]
    {φ : V ≃ₜ W} (h : IsConeIso k k' φ) (c : RPos) (v : V) :
    φ (posSMul (k + 1) c v) = posSMul (k' + 1) c (φ v) := by
  obtain ⟨rfl, h⟩ := h
  exact IsGXMorphism.map_posSMul h c v

/-- **The base map of a conical isomorphism `F(X) ≅ F(Y)` is a projective isomorphism `X ≅ Y`**
(`F⁻¹(φ)`, read on the bases). -/
theorem IsConeIso.exists_base {k k' : ℕ} {X Y : Type u} [TopologicalSpace X]
    [ChartedSpace (S k) X] [HasGroupoid X (projGroupoid k)] [T2Space X] [TopologicalSpace Y]
    [ChartedSpace (S k') Y] [HasGroupoid Y (projGroupoid k')] [T2Space Y]
    {φ : FCone k X ≃ₜ FCone k' Y} (h : IsConeIso k k' φ) :
    ∃ θ : X ≃ₜ Y, IsProjIso k k' θ ∧ ∀ x, θ (FCone.proj x) = FCone.proj (φ x) := by
  obtain ⟨rfl, h⟩ := h
  exact ⟨coneBaseHomeomorph φ h, ⟨rfl, isGXMorphism_coneBaseMap h⟩, fun x =>
    coneBaseMap_proj h x⟩

/-- `ℝ^{k+1} − {O} → ℝ^{k'+1} − {O}` along `k = k'` (dependent-type bookkeeping). -/
def castRnO {k k' : ℕ} (h : k = k') (v : RnO (k + 1)) : RnO (k' + 1) := h ▸ v

@[simp] theorem castRnO_rfl {k : ℕ} (v : RnO (k + 1)) : castRnO rfl v = v := rfl

theorem val_castRnO {k k' : ℕ} (h : k = k') (v : RnO (k + 1)) (a : Fin (k' + 1)) :
    (castRnO h v).val a = v.val (Fin.cast (congrArg (· + 1) h).symm a) := by
  subst h
  rfl

/-- **A conical isomorphism read in charts**, the dimensions identified: near every point it is an
element of `GU` after `castRnO`. -/
theorem IsConeIso.exists_smul_eq {k k' : ℕ} {V W : Type*} [TopologicalSpace V]
    [ChartedSpace (RnO (k + 1)) V] [TopologicalSpace W] [ChartedSpace (RnO (k' + 1)) W]
    {φ : V ≃ₜ W} (h : IsConeIso k k' φ) (x : V) :
    ∃ hk : k = k', ∃ g : GUR (k' + 1), ∀ᶠ y in 𝓝 x,
      chartAt (RnO (k' + 1)) (φ x) (φ y) = g • castRnO hk (chartAt (RnO (k + 1)) x y) := by
  obtain ⟨rfl, h⟩ := h
  obtain ⟨g, hg⟩ := h.exists_smul_eq x
  exact ⟨rfl, g, hg⟩

end Cast

/-! ### Block permutations of equal-size blocks (Déf. 2's « automorphisme φ ») -/

section PermBlock

/-- **A permutation of coordinates has `|det| = 1`** (`det^m = 1` for `m` the order of the
permutation). -/
theorem abs_det_funCongrLeft {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Equiv.Perm ι) :
    |((LinearEquiv.det (LinearEquiv.funCongrLeft ℝ ℝ e) : ℝˣ) : ℝ)| = 1 := by
  have hpow : ∀ k : ℕ, LinearEquiv.funCongrLeft ℝ ℝ e ^ k =
      LinearEquiv.funCongrLeft ℝ ℝ (e ^ k) := by
    intro k
    induction k with
    | zero => exact LinearEquiv.ext fun v => rfl
    | succ k ih =>
      rw [pow_succ', ih, pow_succ]
      exact LinearEquiv.ext fun v => rfl
  have h1 : ((LinearEquiv.det (LinearEquiv.funCongrLeft ℝ ℝ e) : ℝˣ) : ℝ) ^ orderOf e = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hpow, pow_orderOf_eq_one]
    have : LinearEquiv.funCongrLeft ℝ ℝ (1 : Equiv.Perm ι) = 1 := LinearEquiv.ext fun v => rfl
    rw [this, map_one, Units.val_one]
  have h2 : |((LinearEquiv.det (LinearEquiv.funCongrLeft ℝ ℝ e) : ℝˣ) : ℝ)| ^ orderOf e = 1 := by
    rw [← abs_pow, h1, abs_one]
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) (orderOf_pos e).ne').1 h2

variable {q : ℕ} {n : Fin (q + 1) → ℕ}

theorem piBlockEquiv_apply (v : ∀ i, Fin (n i + 1) → ℝ) (k : Fin (pdim n + 1)) :
    piBlockEquiv n v k = v (piBlockIdx n k).1 (piBlockIdx n k).2 := rfl

/-- **The block permutation of coordinates** `⟨i, a⟩ ↦ ⟨σ i, a⟩` of `ℝ^{Σ(nᵢ+1)}`, for a
permutation `σ` of factors of equal dimensions (`n (σ i) = n i`). -/
def piBlockPerm (σ : Equiv.Perm (Fin (q + 1))) (hn : ∀ i, n (σ i) = n i) :
    Equiv.Perm (Fin (pdim n + 1)) :=
  (piBlockIdx n).trans (((Equiv.sigmaCongrRight fun i =>
      finCongr (congrArg (· + 1) (hn i)).symm).trans
    (Equiv.sigmaCongrLeft (β := fun j => Fin (n j + 1)) σ)).trans (piBlockIdx n).symm)

/-- **The block permutation matrix** `(vᵢ) ↦ (v_{σ(i)})`, an element of `GU(Σ(nᵢ+1))`
(`|det| = 1`, `abs_det_funCongrLeft`). -/
def piPermGU (σ : Equiv.Perm (Fin (q + 1))) (hn : ∀ i, n (σ i) = n i) : GUR (pdim n + 1) :=
  ⟨LinearEquiv.funCongrLeft ℝ ℝ (piBlockPerm σ hn), by
    rw [mem_GU]; exact abs_det_funCongrLeft _⟩

theorem piPermGU_apply (σ : Equiv.Perm (Fin (q + 1))) (hn : ∀ i, n (σ i) = n i)
    (v : ∀ i, Fin (n i + 1) → ℝ) :
    (piPermGU σ hn : GLR (pdim n + 1)) (piBlockEquiv n v) =
      piBlockEquiv n fun i a => v (σ i) (Fin.cast (congrArg (· + 1) (hn i)).symm a) := by
  funext k
  show piBlockEquiv n v (piBlockPerm σ hn k) = _
  rw [piBlockEquiv_apply, piBlockEquiv_apply]
  simp only [piBlockPerm, Equiv.trans_apply]
  erw [Equiv.apply_symm_apply]
  generalize piBlockIdx n k = s
  obtain ⟨i, a⟩ := s
  rfl

/-- `piBlockPt` intertwines the block permutation: `P • (wᵢ) = (w_{σ(i)})`. -/
theorem piBlockPt_perm (σ : Equiv.Perm (Fin (q + 1))) (hn : ∀ i, n (σ i) = n i)
    (w : ∀ i, RnO (n i + 1)) :
    piPermGU σ hn • piBlockPt w = piBlockPt fun i => castRnO (hn i) (w (σ i)) := by
  refine Punctured.val_injective ?_
  rw [Punctured.val_smul_sub, val_piBlockPt, val_piBlockPt, piPermGU_apply]
  congr 1
  funext i a
  rw [val_castRnO]

end PermBlock

section PermMap

open PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {V : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (V i)]
  [∀ i, ChartedSpace (RnO (n i + 1)) (V i)]

/-- **Déf. 2, « si l'on définit un automorphisme φ de la structure conique affine du produit par
la formule $m'_i=\varphi_i m_{\sigma(i)}$ »**: for conical isomorphisms `φᵢ : V_{σ(i)} ≅ Vᵢ` the
permuted map `(mᵢ) ↦ (φᵢ m_{σ(i)})` is a conical morphism of the product cone. In product charts it
is the block permutation `piPermGU σ` (equal-size blocks, `n (σ i) = n i`) followed by
`diag(gᵢ)` (`piBlockGU`), of `|det| = 1`. -/
theorem isGXMorphism_piPermMap {σ : Equiv.Perm (Fin (q + 1))} {φ : ∀ i, V (σ i) ≃ₜ V i}
    (hφ : ∀ i, IsConeIso (n (σ i)) (n i) (φ i)) :
    IsGXMorphism (GUR (pdim n + 1)) (RnO (pdim n + 1))
      (fun x : ∀ i, V i => fun i => φ i (x (σ i))) := by
  refine ⟨continuous_pi fun i => (φ i).continuous.comp (continuous_apply (σ i)), fun x => ?_⟩
  have key := fun i => (hφ i).exists_smul_eq (x (σ i))
  choose hn g hg using key
  refine ⟨piBlockGU g * piPermGU σ hn, ?_⟩
  filter_upwards [Filter.eventually_all.2 fun i =>
    (continuous_apply (σ i)).continuousAt.eventually (hg i)] with y hy
  rw [chartAt_eq, chartAt_eq, piChart_apply, piChart_apply, mul_smul, piBlockPt_perm,
    ← piBlockPt_smul_GU]
  exact congrArg piBlockPt (funext hy)

/-- The permuted map `(mᵢ) ↦ (φᵢ m_{σ(i)})` is bijective. -/
theorem bijective_piPermMap (σ : Equiv.Perm (Fin (q + 1))) (φ : ∀ i, V (σ i) ≃ₜ V i) :
    Bijective (fun x : ∀ i, V i => fun i => φ i (x (σ i))) := by
  refine ⟨fun x x' h => funext fun j => ?_, fun y => ?_⟩
  · have h1 := (φ (σ.symm j)).injective (congrFun h (σ.symm j))
    rwa [σ.apply_symm_apply] at h1
  · have key : ∀ (i k : Fin (q + 1)) (hk : k = i) (h : σ k = σ i),
        φ i (h ▸ (φ k).symm (y k)) = y i := by
      intro i k hk h
      subst hk
      exact (φ k).apply_symm_apply (y k)
    exact ⟨fun j => σ.apply_symm_apply j ▸ (φ (σ.symm j)).symm (y (σ.symm j)), funext fun i =>
      key i (σ.symm (σ i)) (σ.symm_apply_apply i) (σ.apply_symm_apply (σ i))⟩

end PermMap

/-! ### Déf. 2 — compatible automorphisms, for general `p` and arbitrary dimensions -/

section Def2Pi

open PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {B : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (B i)]
  [∀ i, ChartedSpace (S (n i)) (B i)] [∀ i, HasGroupoid (B i) (projGroupoid (n i))]
  [∀ i, T2Space (B i)]

/-- **§ 3 Déf. 2** (`bzdef:c1s3d2_automorphisme_compatible`), for `p = q + 1` factors of arbitrary
dimensions `n i`: a projective automorphism `f` of `F⁻¹(F(B₀) × … × F(B_q))` is *compatible,
associated with the permutation `σ`*, when there are conical affine isomorphisms
`φᵢ : F(B_{σ(i)}) ≅ F(Bᵢ)` (`IsConeIso`: they force `dim B_{σ(i)} = dim Bᵢ`) and an element `t` of
`ℝ^{+p}/ℝ^+` with `f = t ∘ F⁻¹(φ)`, `φ(m)ᵢ = φᵢ m_{σ(i)}` (« $m'_i=\varphi_i m_{\sigma(i)}$ … on ait
$f\in\{F^{-1}(\varphi)\}\times(\R^{+p}/\R^+)$ »). -/
def IsCompatibleAssocPi (σ : Equiv.Perm (Fin (q + 1)))
    (f : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)) : Prop :=
  ∃ φ : ∀ i, FCone (n (σ i)) (B (σ i)) ≃ₜ FCone (n i) (B i), (∀ i, IsConeIso (n (σ i)) (n i) (φ i)) ∧
    ∃ t : PiTorus q, ∀ x : ∀ i, FCone (n i) (B i),
      f • (ConeBase.mk x : PiBase n B) =
        piTorusAut n (fun i => FCone (n i) (B i)) t • ConeBase.mk fun i => φ i (x (σ i))

/-- **Compatible** (Déf. 2): associated with some permutation. -/
def IsCompatiblePi (f : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)) : Prop :=
  ∃ σ : Equiv.Perm (Fin (q + 1)), IsCompatibleAssocPi σ f

/-- `F(B_j) ≃ₜ F(B_i)` along an equality of indices. -/
def piFConeCast {j i : Fin (q + 1)} (h : j = i) : FCone (n j) (B j) ≃ₜ FCone (n i) (B i) :=
  h ▸ Homeomorph.refl _

omit [∀ i, T2Space (B i)] in
theorem isConeIso_piFConeCast {j i : Fin (q + 1)} (h : j = i) :
    IsConeIso (n j) (n i) (piFConeCast (n := n) (B := B) h) := by
  subst h
  exact IsConeIso.refl

/-- **A compatible automorphism moves the torus by the permutation**:
`f ∘ [λ] = [λ ∘ σ] ∘ f`. -/
theorem IsCompatibleAssocPi.smul_torus {σ : Equiv.Perm (Fin (q + 1))}
    {f : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)} (hf : IsCompatibleAssocPi σ f)
    (c : Fin (q + 1) → RPos) (p : PiBase n B) :
    f • piTorusAut n (fun i => FCone (n i) (B i)) (c : PiTorus q) • p =
      piTorusAut n (fun i => FCone (n i) (B i)) ((c ∘ σ : Fin (q + 1) → RPos) : PiTorus q) •
        f • p := by
  obtain ⟨φ, hφ, t, ht⟩ := hf
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  have hφc : (fun i => φ i (piSMul n c x (σ i))) =
      piSMul n (c ∘ σ) (fun i => φ i (x (σ i))) :=
    funext fun i => (hφ i).map_posSMul _ _
  rw [piTorusAut_mk_smul, ht, ht, hφc, ← piTorusAut_mk_smul, ← mul_smul, ← mul_smul, ← map_mul,
    ← map_mul, mul_comm t]

/-- The identity is compatible, associated with the identity. -/
theorem isCompatibleAssocPi_one : IsCompatibleAssocPi (n := n) (B := B) 1 1 :=
  ⟨fun i => Homeomorph.refl _, fun _ => IsConeIso.refl, 1, fun x => by
    rw [map_one, one_smul, one_smul]
    rfl⟩

/-- **Every printed `(σ, φ, t)` is a compatible automorphism** (Déf. 2's « si l'on définit un
automorphisme φ … par la formule … on ait $f\in\{F^{-1}(\varphi)\}\times(\R^{+p}/\R^+)$ »): the
permuted map is a conical automorphism of the product cone (`isGXMorphism_piPermMap`), its base
`F⁻¹(φ)` a projective automorphism of `F⁻¹(∏ F(Bᵢ))`, and `t ∘ F⁻¹(φ)` is compatible, associated
with `σ`. -/
theorem exists_isCompatibleAssocPi (σ : Equiv.Perm (Fin (q + 1)))
    {φ : ∀ i, FCone (n (σ i)) (B (σ i)) ≃ₜ FCone (n i) (B i)}
    (hφ : ∀ i, IsConeIso (n (σ i)) (n i) (φ i)) (t : PiTorus q) :
    ∃ f : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B), IsCompatibleAssocPi σ f ∧
      ∀ x : ∀ i, FCone (n i) (B i), f • (ConeBase.mk x : PiBase n B) =
        piTorusAut n (fun i => FCone (n i) (B i)) t • ConeBase.mk fun i => φ i (x (σ i)) := by
  have hΦ := isGXMorphism_piPermMap (V := fun i => FCone (n i) (B i)) hφ
  let e : (∀ i, FCone (n i) (B i)) ≃ₜ ∀ i, FCone (n i) (B i) :=
    (Equiv.ofBijective (fun x : ∀ i, FCone (n i) (B i) => fun i => φ i (x (σ i)))
      (bijective_piPermMap (V := fun i => FCone (n i) (B i)) σ φ)).toHomeomorphOfContinuousOpen
      hΦ.continuous hΦ.isLocalHomeomorph.isOpenMap
  have he : IsGXMorphism (GUR (pdim n + 1)) (RnO (pdim n + 1)) e := hΦ
  have he' := IsGXMorphism.homeomorph_symm (e := e) he
  have hb : Bijective
      (ConeBase.map (V := ∀ i, FCone (n i) (B i)) (W := ∀ i, FCone (n i) (B i)) hΦ) := by
    refine bijective_iff_has_inverse.2 ⟨ConeBase.map he', fun p => ?_, fun p => ?_⟩
    · obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
      rw [ConeBase.map_mk, ConeBase.map_mk]
      exact congrArg ConeBase.mk (e.symm_apply_apply x)
    · obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
      rw [ConeBase.map_mk, ConeBase.map_mk]
      exact congrArg ConeBase.mk (e.apply_symm_apply x)
  set F₀ : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B) :=
    GXAut.ofBijective (ConeBase.isGXMorphism_map hΦ) hb
  have hF : ∀ x : ∀ i, FCone (n i) (B i), (piTorusAut n (fun i => FCone (n i) (B i)) t * F₀) •
      (ConeBase.mk x : PiBase n B) = piTorusAut n (fun i => FCone (n i) (B i)) t •
        ConeBase.mk fun i => φ i (x (σ i)) := fun x => by
    rw [mul_smul]; rfl
  exact ⟨_, ⟨φ, hφ, t, hF⟩, hF⟩

/-- **Compatible automorphisms compose**: `f` (with `σ`) after `g` (with `τ`) is associated with
`τ * σ` (`i ↦ τ (σ i)`). -/
theorem IsCompatibleAssocPi.mul {σ τ : Equiv.Perm (Fin (q + 1))}
    {f g : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)} (hf : IsCompatibleAssocPi σ f)
    (hg : IsCompatibleAssocPi τ g) : IsCompatibleAssocPi (τ * σ) (f * g) := by
  obtain ⟨ψ, hψ, s, hs⟩ := hg
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective s
  have hf' := hf
  obtain ⟨φ, hφ, t, ht⟩ := hf
  refine ⟨(fun i => (ψ (σ i)).trans (φ i) :
      ∀ i, FCone (n ((τ * σ) i)) (B ((τ * σ) i)) ≃ₜ FCone (n i) (B i)),
    fun i => (hψ (σ i)).trans (hφ i), t * ((c ∘ σ : Fin (q + 1) → RPos) : PiTorus q),
    fun x => ?_⟩
  rw [mul_smul, hs, hf'.smul_torus, ht, ← mul_smul, ← map_mul,
    mul_comm ((c ∘ σ : Fin (q + 1) → RPos) : PiTorus q) t]
  rfl

/-- **The inverse of a compatible automorphism is compatible**, associated with `σ⁻¹`. -/
theorem IsCompatibleAssocPi.inv {σ : Equiv.Perm (Fin (q + 1))}
    {f : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)} (hf : IsCompatibleAssocPi σ f) :
    IsCompatibleAssocPi σ⁻¹ f⁻¹ := by
  have hf' := hf
  obtain ⟨φ, hφ, t, ht⟩ := hf
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective t
  set φ' : ∀ j, FCone (n (σ⁻¹ j)) (B (σ⁻¹ j)) ≃ₜ FCone (n j) (B j) := fun j =>
    (φ (σ.symm j)).symm.trans (piFConeCast (σ.apply_symm_apply j))
  set c' : Fin (q + 1) → RPos := fun j => (c (σ.symm j))⁻¹
  refine ⟨φ', fun j => (hφ (σ.symm j)).symm.trans (isConeIso_piFConeCast _),
    (c' : PiTorus q), fun x => ?_⟩
  rw [inv_smul_eq_iff, hf'.smul_torus, ht, ← mul_smul, ← map_mul, ← QuotientGroup.mk_mul,
    piTorusAut_mk_smul]
  have key : ∀ (i k : Fin (q + 1)) (hk : k = i) (h : σ k = σ i),
      φ i (piFConeCast h ((φ k).symm (x k))) = x i := by
    intro i k hk h
    subst hk
    cases h
    exact (φ k).apply_symm_apply (x k)
  have h1 : (fun i => φ i (φ' (σ i) (x (σ⁻¹ (σ i))))) = x := by
    funext i
    exact key i (σ.symm (σ i)) (σ.symm_apply_apply i) (σ.apply_symm_apply (σ i))
  have h2 : ((c' ∘ σ) * c : Fin (q + 1) → RPos) = 1 := by
    funext i
    simp [c', Equiv.symm_apply_apply]
  rw [h2, piSMul_one]
  exact (congrArg ConeBase.mk h1).symm

variable (n B) in
/-- **The group `G` of compatible automorphisms** (Prop. 4's « le groupe des automorphismes
compatibles »): the compatible automorphisms form a subgroup. -/
def compatibleSubgroup : Subgroup (GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)) where
  carrier := {f | IsCompatiblePi f}
  one_mem' := ⟨1, isCompatibleAssocPi_one⟩
  mul_mem' := fun ⟨σ, hf⟩ ⟨τ, hg⟩ => ⟨τ * σ, hf.mul hg⟩
  inv_mem' := fun ⟨σ, hf⟩ => ⟨σ⁻¹, hf.inv⟩

variable (n B) in
/-- **`G_I`, the compatible automorphisms associated with the identity permutation.** -/
def compatibleIdSubgroup : Subgroup (GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)) where
  carrier := {f | IsCompatibleAssocPi 1 f}
  one_mem' := isCompatibleAssocPi_one
  mul_mem' := fun hf hg => (mul_one (1 : Equiv.Perm (Fin (q + 1)))) ▸ hf.mul hg
  inv_mem' := fun hf => (inv_one (G := Equiv.Perm (Fin (q + 1)))) ▸ hf.inv

theorem compatibleIdSubgroup_le : compatibleIdSubgroup n B ≤ compatibleSubgroup n B :=
  fun _ hf => ⟨1, hf⟩

/-- **`G_I` has finite index `≤ p!` in `G`** (Prop. 4's proof, « $G_I$ est un sous-groupe de $G$
d'indice fini au plus égal à $p\,!$ »): two compatible automorphisms associated with the same
permutation lie in one coset of `G_I`. -/
theorem relIndex_compatibleIdSubgroup_le :
    (compatibleIdSubgroup n B).relIndex (compatibleSubgroup n B) ≠ 0 ∧
      (compatibleIdSubgroup n B).relIndex (compatibleSubgroup n B) ≤ (q + 1).factorial := by
  set G := compatibleSubgroup n B
  set H := (compatibleIdSubgroup n B).subgroupOf G
  have hperm : ∀ f : G, ∃ σ, IsCompatibleAssocPi σ
      (f : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)) := fun f => f.2
  choose χ hχ using hperm
  let ψ : G ⧸ H → Equiv.Perm (Fin (q + 1)) := fun Q => χ (Quotient.out Q)
  have hψ : Injective ψ := by
    intro Q Q' h
    rw [← Quotient.out_eq Q, ← Quotient.out_eq Q']
    refine Quotient.sound (QuotientGroup.leftRel_apply.2 ?_)
    have h1 := (hχ (Quotient.out Q)).inv.mul (hχ (Quotient.out Q'))
    simp only [ψ] at h
    rw [h, mul_inv_cancel] at h1
    exact h1
  haveI : Finite (G ⧸ H) := Finite.of_injective ψ hψ
  refine ⟨Subgroup.index_ne_zero_of_finite, ?_⟩
  show Nat.card (G ⧸ H) ≤ (q + 1).factorial
  have := Nat.card_le_card_of_injective ψ hψ
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin (q + 1))), Fintype.card_perm,
    Fintype.card_fin] at this
  exact this

/-! ### What a compatible automorphism does on `B₀ × … × B_q` -/

/-- **A compatible automorphism acts on the base `∏ Bᵢ` through projective isomorphisms
`θᵢ : B_{σ(i)} ≅ Bᵢ`**: `(bᵢ) ↦ (θᵢ b_{σ(i)})` (the base maps `F⁻¹(φᵢ)`). -/
theorem IsCompatibleAssocPi.exists_base {σ : Equiv.Perm (Fin (q + 1))}
    {f : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)} (hf : IsCompatibleAssocPi σ f) :
    ∃ θ : ∀ i, B (σ i) ≃ₜ B i, (∀ i, IsProjIso (n (σ i)) (n i) (θ i)) ∧
      ∀ p : PiBase n B, ∀ i, piBaseProj n B (f • p) i = θ i (piBaseProj n B p (σ i)) := by
  obtain ⟨φ, hφ, t, ht⟩ := hf
  have key := fun i => (hφ i).exists_base
  choose θ hθ hθp using key
  refine ⟨θ, hθ, fun p i => ?_⟩
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective p
  have h1 : piBaseProj n B (f • (ConeBase.mk x : PiBase n B)) =
      piBaseProj n B (ConeBase.mk fun i => φ i (x (σ i)) : PiBase n B) := by
    rw [ht]
    exact (piBaseProj_eq_iff.2 ⟨t, rfl⟩).symm
  rw [h1, piBaseProj_mk, piBaseProj_mk]
  exact (hθp i (x (σ i))).symm

/-- **The permutation of a compatible automorphism is determined by it**, for nonempty factors (no
other hypothesis): `f` conjugates the torus element `[c]` to `[c ∘ σ]` and to `[c ∘ σ']`
(`smul_torus`), the torus acts freely (`eq_one_of_piTorusAut_smul_eq`), so `(c ∘ σ')⁻¹ (c ∘ σ)` is
diagonal for every `c`; with `c = 2` at `σ i` and `1` elsewhere, `σ i ≠ σ' i` makes it `2` at `i` and
`1/2` at `σ'⁻¹(σ i) ≠ i`. -/
theorem IsCompatibleAssocPi.perm_unique [∀ i, Nonempty (B i)] {σ σ' : Equiv.Perm (Fin (q + 1))}
    {f : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)} (hf : IsCompatibleAssocPi σ f)
    (hf' : IsCompatibleAssocPi σ' f) : σ = σ' := by
  classical
  obtain ⟨p, -⟩ := piBaseProj_surjective (n := n) (B := B) (fun i => Classical.arbitrary _)
  refine Equiv.ext fun i => ?_
  by_contra hne
  set two : RPos := Punctured.posUnit 2 two_pos
  set c : Fin (q + 1) → RPos := Pi.mulSingle (σ i) two
  have h1 := hf.smul_torus c (f⁻¹ • p)
  have h2 := hf'.smul_torus c (f⁻¹ • p)
  rw [smul_inv_smul] at h1 h2
  have h3 : piTorusAut n (fun i => FCone (n i) (B i))
      (((c ∘ σ' : Fin (q + 1) → RPos) : PiTorus q)⁻¹ * ((c ∘ σ : Fin (q + 1) → RPos) : PiTorus q))
      • p = p := by
    rw [map_mul, mul_smul, ← h1, h2, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have h4 := eq_one_of_piTorusAut_smul_eq h3
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at h4
  set j := σ'.symm (σ i)
  have hji : j ≠ i := fun h => hne ((Equiv.symm_apply_eq σ').1 h)
  have hi := h4 i
  have hj := h4 j
  have e1 : (((c ∘ σ')⁻¹ * (c ∘ σ)) i) = two := by
    simp [c, Pi.mulSingle_eq_of_ne (Ne.symm hne)]
  have e2 : (((c ∘ σ')⁻¹ * (c ∘ σ)) j) = two⁻¹ := by
    have : σ j ≠ σ i := fun h => hji (σ.injective h)
    simp [c, j, Pi.mulSingle_eq_of_ne this]
  rw [e1, ← hj, e2] at hi
  have := congrArg (fun x : RPos => ((x : ℝˣ) : ℝ)) hi
  simp [two] at this
  norm_num at this

variable (n B) in
/-- **The homomorphism `G → Perm(1, …, p)`**, `f ↦ σ_f⁻¹` (nonempty factors, so that `σ_f` is
determined by `f`, `perm_unique`; `σ_{f∘g} = σ_g σ_f`). -/
def compatiblePerm [∀ i, Nonempty (B i)] :
    compatibleSubgroup n B →* Equiv.Perm (Fin (q + 1)) where
  toFun f := (Classical.choose f.2)⁻¹
  map_one' := by
    have h : IsCompatibleAssocPi (n := n) (B := B) (Classical.choose (1 : compatibleSubgroup n B).2)
      ((1 : compatibleSubgroup n B) : GXAut (GSR (pdim n)) (S (pdim n)) (PiBase n B)) :=
      Classical.choose_spec (1 : compatibleSubgroup n B).2
    rw [IsCompatibleAssocPi.perm_unique h isCompatibleAssocPi_one, inv_one]
  map_mul' f g := by
    have hf := Classical.choose_spec f.2
    have hg := Classical.choose_spec g.2
    have hfg := Classical.choose_spec (f * g).2
    rw [IsCompatibleAssocPi.perm_unique hfg (hf.mul hg), mul_inv_rev]

/-- **`G_I` is the kernel of `G → Perm(1, …, p)`** (nonempty factors). -/
theorem ker_compatiblePerm [∀ i, Nonempty (B i)] :
    (compatiblePerm n B).ker = (compatibleIdSubgroup n B).subgroupOf (compatibleSubgroup n B) := by
  ext f
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hf := Classical.choose_spec f.2
  constructor
  · intro h
    have h' : Classical.choose f.2 = 1 := inv_eq_one.1 h
    show IsCompatibleAssocPi 1 _
    rw [← h']
    exact hf
  · intro h
    show (Classical.choose f.2)⁻¹ = 1
    rw [IsCompatibleAssocPi.perm_unique hf h, inv_one]

end Def2Pi

/-! ### § 3 Prop. 4 for general `p` -/

section Prop4Pi

open PiCone

variable {q : ℕ} {n : Fin (q + 1) → ℕ} {B : Fin (q + 1) → Type u} [∀ i, TopologicalSpace (B i)]
  [∀ i, ChartedSpace (S (n i)) (B i)] [∀ i, HasGroupoid (B i) (projGroupoid (n i))]
  [∀ i, T2Space (B i)]

/-- **§ 3 Prop. 4, first assertion, for general `p`** (`bzprop:c1s3p4_reciproque`): « si le groupe
des automorphismes compatibles opère transitivement sur $F^{-1}(F(B_1)\times\ldots\times F(B_p))$,
les $B_i$ sont projectivement homogènes », for nonempty (« variété ») factors. The printed proof:
`φ = F⁻¹(φ_{σ'^h(1)}) ∘ … ∘ F⁻¹(φ_{σ'(1)})` along the cycle of `i₀`, `h` its length. -/
theorem homogeneous_of_compatible_pi [∀ i, Nonempty (B i)]
    (h : MulAction.IsPretransitive (compatibleSubgroup n B) (PiBase n B)) :
    ∀ i, IsHomogeneous (GSR (n i)) (S (n i)) (B i) := by
  classical
  intro i₀
  refine ⟨fun b b' => ?_⟩
  let c : ∀ i, B i := fun i => Classical.arbitrary (B i)
  obtain ⟨m, hm⟩ := piBaseProj_surjective (n := n) (B := B) (Function.update c i₀ b)
  obtain ⟨m', hm'⟩ := piBaseProj_surjective (n := n) (B := B) (Function.update c i₀ b')
  obtain ⟨⟨f, σ, hf⟩, hfm⟩ := h.exists_smul_eq m m'
  have hfm' : f • m = m' := hfm
  obtain ⟨θ, hθ, hθp⟩ := hf.exists_base
  have hβ' : ∀ i, θ i (piBaseProj n B m (σ i)) = piBaseProj n B m' i := fun i => by
    rw [← hfm', hθp]
  have hother : ∀ j, j ≠ i₀ → θ j (piBaseProj n B m (σ j)) = piBaseProj n B m j := fun j hj => by
    rw [hβ', hm', hm, Function.update_of_ne hj, Function.update_of_ne hj]
  -- the cycle of `i₀`
  have hex : ∃ k, 0 < k ∧ (σ ^ k) i₀ = i₀ :=
    ⟨orderOf σ, orderOf_pos σ, by rw [pow_orderOf_eq_one]; rfl⟩
  set h₀ := Nat.find hex with hh₀
  have hh₀pos : 0 < h₀ := (Nat.find_spec hex).1
  have hh₀eq : (σ ^ h₀) i₀ = i₀ := (Nat.find_spec hex).2
  have hmin : ∀ k, 0 < k → k < h₀ → (σ ^ k) i₀ ≠ i₀ := fun k hk hkh hki =>
    Nat.find_min hex hkh ⟨hk, hki⟩
  let R : Fin (q + 1) → Prop := fun j =>
    ∃ ψ : B j ≃ₜ B i₀, IsProjIso (n j) (n i₀) ψ ∧ ψ (piBaseProj n B m j) = b'
  have hR : ∀ k, 1 ≤ k → k ≤ h₀ → R ((σ ^ k) i₀) := by
    intro k hk1
    induction k, hk1 using Nat.le_induction with
    | base =>
      intro _
      refine ⟨θ i₀, hθ i₀, ?_⟩
      show θ i₀ (piBaseProj n B m (σ i₀)) = b'
      rw [hβ' i₀, hm', Function.update_self]
    | succ k hk ih =>
      intro hkh
      obtain ⟨ψ, hψ, hψb⟩ := ih (Nat.le_of_succ_le hkh)
      have hj : (σ ^ k) i₀ ≠ i₀ := hmin k (by omega) (by omega)
      have hsucc : (σ ^ (k + 1)) i₀ = σ ((σ ^ k) i₀) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [hsucc]
      refine ⟨(θ ((σ ^ k) i₀)).trans ψ, (hθ ((σ ^ k) i₀)).trans hψ, ?_⟩
      rw [Homeomorph.trans_apply, hother _ hj, hψb]
  have hRi₀ : R i₀ := hh₀eq ▸ hR h₀ hh₀pos le_rfl
  obtain ⟨ψ, hψ, hψb⟩ := hRi₀
  refine ⟨hψ.toAut, ?_⟩
  rw [IsProjIso.toAut_smul]
  have : piBaseProj n B m i₀ = b := by rw [hm, Function.update_self]
  rw [← this]
  exact hψb

/-- **§ 3 Prop. 4, second assertion, for general `p`**: « Si
$F^{-1}(F(B_1)\times\ldots\times F(B_p))$ est balayable par le groupe de ces automorphismes
compatibles, les $B_i$ sont projectivement balayables », for nonempty factors. The printed proof
passes to `G_I` (finite index, `relIndex_compatibleIdSubgroup_le`); here the finitely many index
classes are absorbed directly: for each `j` admitting a projective isomorphism `B_j ≅ B_{i₀}` one
is fixed, and the generating domain of `B_{i₀}` is the union of the images of the `j`-th
projections of `K`. -/
theorem balayable_of_compatible_pi [∀ i, Nonempty (B i)]
    (h : IsBalayableFor (GSR (pdim n)) (S (pdim n)) (PiBase n B) (compatibleSubgroup n B)) :
    ∀ i, IsBalayable (GSR (n i)) (S (n i)) (B i) := by
  classical
  intro i₀
  obtain ⟨K, hK, hKU⟩ := h
  let c : ∀ i, B i := fun i => Classical.arbitrary (B i)
  let Kj : ∀ j, Set (B j) := fun j => (fun p => piBaseProj n B p j) '' K
  have hKj : ∀ j, IsCompact (Kj j) := fun j =>
    hK.image ((continuous_apply j).comp continuous_piBaseProj)
  let T : Fin (q + 1) → Set (B i₀) := fun j =>
    if hj : ∃ θ : B j ≃ₜ B i₀, IsProjIso (n j) (n i₀) θ then hj.choose '' Kj j else ∅
  have hT : ∀ j, IsCompact (T j) := fun j => by
    by_cases hj : ∃ θ : B j ≃ₜ B i₀, IsProjIso (n j) (n i₀) θ
    · simp only [T, dif_pos hj]
      exact (hKj j).image hj.choose.continuous
    · simp only [T, dif_neg hj]
      exact isCompact_empty
  refine ⟨⋃ j, T j, isCompact_iUnion hT, eq_univ_of_forall fun b => ?_⟩
  obtain ⟨p, hp⟩ := piBaseProj_surjective (n := n) (B := B) (Function.update c i₀ b)
  have hpK : p ∈ ⋃ g ∈ compatibleSubgroup n B, g • K := hKU ▸ mem_univ p
  obtain ⟨f, ⟨σ, hf⟩, k, hk, hkp⟩ := mem_iUnion₂.1 hpK
  obtain ⟨θ, hθ, hθp⟩ := hf.exists_base
  have hb : θ i₀ (piBaseProj n B k (σ i₀)) = b := by
    have hkp' : f • k = p := hkp
    rw [← hθp, hkp', hp, Function.update_self]
  have hj : ∃ θ' : B (σ i₀) ≃ₜ B i₀, IsProjIso (n (σ i₀)) (n i₀) θ' := ⟨θ i₀, hθ i₀⟩
  set t := hj.choose
  have ht : IsProjIso (n (σ i₀)) (n i₀) t := hj.choose_spec
  have hmem : t (piBaseProj n B k (σ i₀)) ∈ T (σ i₀) := by
    simp only [T, dif_pos hj]
    exact ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have hiso : IsProjIso (n i₀) (n i₀) (t.symm.trans (θ i₀)) := ht.symm.trans (hθ i₀)
  refine mem_iUnion₂.2 ⟨hiso.toAut, Subgroup.mem_top _, t (piBaseProj n B k (σ i₀)),
    mem_iUnion.2 ⟨σ i₀, hmem⟩, ?_⟩
  show hiso.toAut • t (piBaseProj n B k (σ i₀)) = b
  rw [IsProjIso.toAut_smul, Homeomorph.trans_apply, Homeomorph.symm_apply_apply, hb]

/-- **§ 3 Prop. 4 for general `p`** (`bzprop:c1s3p4_reciproque`): both assertions, for nonempty
(« variété », DEC-128) factors of arbitrary dimensions. -/
theorem prop4_reciproque_pi [∀ i, Nonempty (B i)] :
    (MulAction.IsPretransitive (compatibleSubgroup n B) (PiBase n B) →
      ∀ i, IsHomogeneous (GSR (n i)) (S (n i)) (B i)) ∧
    (IsBalayableFor (GSR (pdim n)) (S (pdim n)) (PiBase n B) (compatibleSubgroup n B) →
      ∀ i, IsBalayable (GSR (n i)) (S (n i)) (B i)) :=
  ⟨homogeneous_of_compatible_pi, balayable_of_compatible_pi⟩

end Prop4Pi

end Benzecri
