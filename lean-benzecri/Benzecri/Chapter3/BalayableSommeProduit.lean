import Benzecri.Chapter3.BalayableSomme
import Benzecri.Applications.ConverseGeneral

/-!
# Chapter 3 § 2, Proposition 4 in the notation of Chapter 1: `w ≅ F⁻¹(F(v₁) × … × F(v_p))`

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 3 § 2, journal p. 268; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch3.tex` (TO BE CHECKED BY THE AUTHOR).
Targets T-bz-c3-balayable-somme (statement) and T-bz-c3-prop4-produit (proof).

* `bzprop:c3s2p4_automorphisme_compatible` — `benzecri1960_ch3.tex:599` (Prop. 4, l.599–611),
  NOT marked (OQ-168: the added hypothesis `¬ ContientDroite (F w)`; OQ-171: the torus factor):
  `Benzecri.Sphere.prop4_produit`, the Chapter 1 form, PROVED with no `sorry`: for bases
  `bᵢ : lᵢ ≅ ℝ^{nᵢ+1}` and `Bᵢ = s(bᵢ(F(vᵢ)))` (open in `S(nᵢ)`), a projective isomorphism
  `Ψ : F⁻¹(F(B₀) × … × F(B_q)) ≃ₜ w` (`PiBase`, Ch. 1 § 3; `IsProjIso`, which forces
  `pdim n = m`, `Produit.pdim_eq`), under which every projective automorphism of `w` is
  compatible (Ch. 1 § 3 Déf. 2, `IsCompatiblePi`). The intrinsic forms are `prop4_somme` and
  `prop4_automorphisme_compatible` (`BalayableSomme.lean`). Bases always exist
  (`exists_bases_simplesS`); the instance is the open simplex (`simplexO_prop4_produit`).

> **Proposition 4.** Soient $w$ un ouvert convexe de $S(\R^{n+1})=S(n)$, de noyau vide, $l_i$
> les $p$ sous-variétés distinguées simples relatives à $w$, $v_i$ les convexes de $l_i$ dont
> $w$ est la somme; on peut écrire avec les notations du chapitre 1, paragraphes 1 et 2
> $$ w=F^{-1}(F(v_1)\times\ldots\times F(v_p)) $$
> tout automorphisme projectif de $w$ est un automorphisme compatible au sens du chapitre 1,
> paragraphe 3, définition 2.
>
> *Démonstration.* En effet, un automorphisme projectif de $w$ est un élément de $GP(n, \R)$ qui
> permute entre elles les variétés distinguées simples.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `w` ouvert, convexe, de noyau vide | ✓ carried |
| (not printed) `F(w)` contains no line | ⚠ ADDED (OQ-168), as in `BalayableSomme.lean`; without it the statement is false (`not_prop4_simplesS_finite`) |
| (not printed) `w ≠ ∅` | ⚠ reading: `w.Nonempty` |
| « avec les notations du chapitre 1 » | reading: bases `bᵢ : lᵢ ≅ ℝ^{nᵢ+1}` (any; they exist, `exists_bases_simplesS`), `Bᵢ = s(bᵢ(F(vᵢ)))` open in `S(nᵢ)` |
| « $w=F^{-1}(F(v_1)\times\ldots\times F(v_p))$ » | a projective isomorphism `PiBase n B ≃ₜ w` (`IsProjIso (pdim n) m`) |
| « automorphisme compatible » | `IsCompatiblePi` of the transported automorphism, with the torus factor `t ≠ 1` in general (OQ-171) |

## SCOPE (disclosed)

* **The transport** (no `sorry`): (i) for an open `B ⊆ S(k)`, the cone chart of `F(B)` over
  the inclusion chart is global (`OpensCone.gcc`, source everything, target `s⁻¹(B)`); (ii)
  the product of these charts is a cone chart of `∏ F(Bᵢ)` and its base chart is a global chart
  of `PiBase` onto `s(∏ s⁻¹(Bᵢ))`; composed with the linear isomorphism
  `ℝ^{pdim n + 1} ≅ ℝ^{m+1}`, `(yᵢ) ↦ ∑ bᵢ⁻¹ yᵢ` (`Produit.linL`, the decomposition
  `E = ⊕ lᵢ` of `BalayableSomme.lean`), it maps `PiBase` onto `w` (`Produit.mem_F_iff_linL`:
  `F(w) = ∑ F(vᵢ)`), a projective morphism (`isProjIso_of_chart`); (iii) an automorphism `f` of
  `w` is a linear `g` permuting the `lᵢ` (`prop4_automorphisme_compatible`); the maps
  `Aᵢ = bᵢ g b_{τ(i)}⁻¹` are NORMALISED to `|det| = 1` by `cᵢ = |det Aᵢ|^{1/(nᵢ+1)}`
  (`OpensCone.exists_coneIso_of_linearEquiv`: the cone groupoid is `GU`), and the torus element
  `t = [(cᵢ)]` absorbs the normalisation (`isCompatiblePi_of_transport`).
* **The torus factor is needed** (OQ-171): the printed proof's « élément de $GP(n, \R)$ » reads,
  in Chapter 1's notation, as `φᵢ = cᵢ⁻¹ g|` and `t = [(cᵢ)]`, not `t = 1`; e.g. on the open
  segment of `S(1)` (two factors of dimension `0`, `F(Bᵢ) = ℝ₊*`, whose only conical
  automorphism is the identity), `g = diag(1, 2)` forces `t = [(1, 2)] ≠ 1`; formalized, for every `Ψ`, as
  `BooleProjectifInstance.simplexO_one_prop4_tore` (`Prop4Tore.lean`).
* Not marked for OQ-168 (added hypothesis) and OQ-171, see `BalayableSomme.lean`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Function Filter Topology
open scoped Pointwise

namespace Benzecri

attribute [local instance] t2Space_RnO

namespace OpensCone

variable {k : ℕ} {B : TopologicalSpace.Opens (S k)} (x₀ : B)

/-- The inclusion chart of an open `B ⊆ S(k)` (the preferred chart of the `Opens`) is compatible. -/
theorem incl_mem : chartAt (S k) x₀ ∈ (projGroupoid k).maximalAtlas B :=
  (projGroupoid k).chart_mem_maximalAtlas x₀

/-- The inclusion chart is global. -/
theorem incl_source : (chartAt (S k) x₀).source = univ := by
  simp [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]

/-- The inclusion chart is the inclusion. -/
theorem incl_apply (y : B) : chartAt (S k) x₀ y = (y : S k) := by
  simp [TopologicalSpace.Opens.chartAt_eq]

/-- The inclusion chart is onto `B`. -/
theorem incl_target : (chartAt (S k) x₀).target = (B : Set (S k)) := by
  rw [← (chartAt (S k) x₀).image_source_eq_target]
  simp [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_source]

/-- **The global cone chart of `F(B)`**, `B` open in `S(k)`: Chapter 1's cone chart over the
inclusion chart (`FCone.coneChart`). -/
def gcc : OpenPartialHomeomorph (FCone k B) (RnO (k + 1)) := FCone.coneChart (incl_mem x₀)

/-- The global cone chart is defined on all of `F(B)`. -/
theorem gcc_source : (gcc x₀).source = univ := by
  rw [gcc, FCone.coneChart_source, incl_source, preimage_univ]

/-- The global cone chart is onto the open cone `s⁻¹(B)`. -/
theorem gcc_target : (gcc x₀).target = Punctured.toSphere ⁻¹' (B : Set (S k)) := by
  rw [gcc, FCone.coneChart_target, incl_target]

/-- The global cone chart is a cone chart. -/
theorem isConeChart_gcc : IsConeChart (k + 1) (gcc x₀) := FCone.isConeChart_coneChart _

/-- The global cone chart is in the maximal atlas. -/
theorem gcc_mem : gcc x₀ ∈ (coneGroupoid (k + 1)).maximalAtlas (FCone k B) :=
  (isConeChart_gcc x₀).1

/-- **`F(B) ≃ₜ s⁻¹(B)`**, the global cone chart as a homeomorphism. -/
def gccH : FCone k B ≃ₜ (Punctured.toSphere ⁻¹' (B : Set (S k)) : Set (RnO (k + 1))) :=
  (Homeomorph.Set.univ _).symm.trans ((Homeomorph.setCongr (gcc_source x₀).symm).trans
    ((gcc x₀).toHomeomorphSourceTarget.trans (Homeomorph.setCongr (gcc_target x₀))))

/-- `gccH` is the global cone chart. -/
@[simp] theorem gccH_apply (x : FCone k B) : (gccH x₀ x : RnO (k + 1)) = gcc x₀ x := rfl

/-- `gccH.symm` is the inverse of the global cone chart. -/
theorem gccH_symm_apply (v : (Punctured.toSphere ⁻¹' (B : Set (S k)) : Set (RnO (k + 1)))) :
    (gccH x₀).symm v = (gcc x₀).symm v := rfl


/-- `s(v) ∈ B ↔ v ∈ F(B)`. -/
theorem toSphere_mem_iff {k : ℕ} {B : Set (S k)} (v : RnO (k + 1)) :
    Punctured.toSphere v ∈ B ↔ v.val ∈ Sphere.F B :=
  Sphere.mk_mem_iff_mem_F v.val_ne_zero

/-- **A linear isomorphism matching the cones of two open sets of spheres gives a conical
isomorphism of their cones `F(B)`, up to a positive normalisation.** -/
theorem exists_coneIso_of_linearEquiv {k k' : ℕ} {B : TopologicalSpace.Opens (S k)}
    {B' : TopologicalSpace.Opens (S k')} (x₀ : B) (x₀' : B')
    (A : (Fin (k + 1) → ℝ) ≃ₗ[ℝ] (Fin (k' + 1) → ℝ))
    (hA : ∀ v, v ∈ Sphere.F (B : Set (S k)) ↔ A v ∈ Sphere.F (B' : Set (S k'))) :
    ∃ φ : FCone k B ≃ₜ FCone k' B', IsConeIso k k' φ ∧ ∃ c : RPos, ∀ x,
      (gcc x₀' (posSMul (k' + 1) c (φ x))).val = A (gcc x₀ x).val := by
  have hk : k = k' := by
    have := A.finrank_eq
    simp only [Module.finrank_fin_fun] at this
    omega
  subst hk
  set d : ℝ := |((LinearEquiv.det A : ℝˣ) : ℝ)| with hd
  have hd0 : 0 < d := abs_pos.2 (Units.ne_zero _)
  set c : ℝ := d ^ (((k + 1 : ℕ) : ℝ)⁻¹) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hd0 _
  have hck : c ^ (k + 1) = d := Real.rpow_inv_natCast_pow hd0.le (Nat.succ_ne_zero k)
  set A' : GLR (k + 1) := homothety _ (Units.mk0 c⁻¹ (inv_ne_zero hc0.ne')) * A with hA'
  have hA'v : ∀ v, A' v = c⁻¹ • A v := fun v => rfl
  have hdet : |((LinearEquiv.det A' : ℝˣ) : ℝ)| = 1 := by
    rw [hA', map_mul, Units.val_mul, det_homothety, Module.finrank_fin_fun, abs_mul, ← hd,
      Units.val_mk0, abs_pow, abs_inv, abs_of_pos hc0, inv_pow, hck, inv_mul_cancel₀ hd0.ne']
  set g : GUR (k + 1) := ⟨A', mem_GU.2 hdet⟩
  have hgv : ∀ v : RnO (k + 1), (g • v).val = c⁻¹ • A v.val := fun v => rfl
  have hiff : ∀ v : RnO (k + 1), Punctured.toSphere v ∈ (B : Set (S k)) ↔
      Punctured.toSphere (g • v) ∈ (B' : Set (S k)) := fun v => by
    rw [toSphere_mem_iff, toSphere_mem_iff, hgv, hA]
    refine ⟨fun h => Sphere.smul_mem_F h (inv_pos.2 hc0), fun h => ?_⟩
    have := Sphere.smul_mem_F h hc0
    rwa [smul_smul, mul_inv_cancel₀ hc0.ne', one_smul] at this
  let φ : FCone k B ≃ₜ FCone k B' :=
    (gccH x₀).trans (((Homeomorph.smul g).subtype hiff).trans (gccH x₀').symm)
  have hφ : ∀ x, gcc x₀' (φ x) = g • gcc x₀ x := fun x => by
    show gcc x₀' ((gcc x₀').symm (g • gcc x₀ x)) = _
    refine (gcc x₀').right_inv ?_
    rw [gcc_target]
    have h1 := (gcc x₀).map_source (x := x) (by rw [gcc_source]; trivial)
    rw [gcc_target] at h1
    exact (hiff _).1 h1
  refine ⟨φ, ⟨rfl, isGXMorphism_of_mem_maximalAtlas φ.continuous fun x =>
    ⟨gcc x₀, gcc_mem x₀, gcc x₀', gcc_mem x₀', by rw [gcc_source]; trivial,
      by rw [gcc_source]; trivial, g, Eventually.of_forall fun y => hφ y⟩⟩,
    Punctured.posUnit c hc0, fun x => ?_⟩
  rw [(isConeChart_gcc x₀').map_smul (by rw [gcc_source]; trivial), hφ, Punctured.val_smul_pos,
    hgv, Punctured.coe_posUnit, smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]

end OpensCone

namespace Sphere

namespace Produit

variable {m : ℕ} {w : Set (S m)} {q : ℕ} (l : Fin (q + 1) ≃ simplesS w) (n : Fin (q + 1) → ℕ)
  (b : ∀ i, (l i : Submodule ℝ (Fin (m + 1) → ℝ)) ≃ₗ[ℝ] (Fin (n i + 1) → ℝ))

/-- `bᵢ(F(vᵢ))`, the cone of `Bᵢ` in `ℝ^{nᵢ+1}`. -/
abbrev cset (i : Fin (q + 1)) : Set (Fin (n i + 1) → ℝ) :=
  b i '' (Subtype.val ⁻¹' sommandeS w (l i))

/-- `bᵢ(F(vᵢ))` is a positive cone. -/
theorem isPosCone_cset (i : Fin (q + 1)) :
    ∀ c : ℝ, 0 < c → ∀ v ∈ cset l n b i, c • v ∈ cset l n b i := by
  rintro c hc _ ⟨u, hu, rfl⟩
  refine ⟨c • u, ?_, map_smul _ _ _⟩
  exact Hyps4.isPosCone_sommande _ c hc _ hu

variable {l n b}

/-- `v ∈ bᵢ(F(vᵢ)) ↔ bᵢ⁻¹ v ∈ F(vᵢ)`. -/
theorem mem_cset_iff {i : Fin (q + 1)} {v : Fin (n i + 1) → ℝ} :
    v ∈ cset l n b i ↔
      (((b i).symm v : ↥(l i : Submodule ℝ (Fin (m + 1) → ℝ))) : Fin (m + 1) → ℝ) ∈
        sommandeS w (l i) := by
  rw [cset, LinearEquiv.image_eq_preimage_symm]
  rfl

variable (H : Hyps4 w)
include H

/-- `O ∉ bᵢ(F(vᵢ))`. -/
theorem zero_notMem_cset (i : Fin (q + 1)) : (0 : Fin (n i + 1) → ℝ) ∉ cset l n b i := by
  rw [mem_cset_iff, map_zero]
  exact H.zero_notMem_sommande (l i).2

/-- `F(Bᵢ) = bᵢ(F(vᵢ))`. -/
theorem F_ofCone_cset (i : Fin (q + 1)) : F (ofCone (cset l n b i)) = cset l n b i := by
  rw [F_ofCone (isPosCone_cset l n b i)]
  exact sdiff_singleton_eq_self (zero_notMem_cset H i)

/-- `bᵢ(F(vᵢ))` is open in `ℝ^{nᵢ+1}` (`vᵢ` is open in `lᵢ`). -/
theorem isOpen_cset (i : Fin (q + 1)) : IsOpen (cset l n b i) := by
  have h := H.isOpen_sommande (l i).2
  rw [cset]
  exact ((b i).toContinuousLinearEquiv.toHomeomorph.isOpenMap) _ h

/-- `Bᵢ` is open in `S(nᵢ)`. -/
theorem isOpen_ofCone_cset (i : Fin (q + 1)) : IsOpen (ofCone (cset l n b i) : Set (S (n i))) :=
  isOpen_ofCone (isPosCone_cset l n b i) (isOpen_cset H i)

/-- `Bᵢ` is nonempty. -/
theorem nonempty_cset (i : Fin (q + 1)) : (ofCone (cset l n b i) : Set (S (n i))).Nonempty := by
  obtain ⟨u, hu⟩ := H.exists_mem_F
  have h1 : projS w (l i) u ∈ sommandeS w (l i) := ⟨u, hu, rfl⟩
  have hv : b i ⟨projS w (l i) u, H.projS_mem (l i).2 u⟩ ∈ cset l n b i := ⟨_, h1, rfl⟩
  exact ⟨_, mk_mem_ofCone (fun h => zero_notMem_cset H i (h ▸ hv)) hv⟩

omit H in
variable (l n b) in
/-- `(yᵢ) ↦ ∑ bᵢ⁻¹ yᵢ`, read through the block decomposition of `ℝ^{pdim n + 1}`. -/
def linFun : (Fin (pdim n + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
  ∑ i, (l i : Submodule ℝ (Fin (m + 1) → ℝ)).subtype ∘ₗ (b i).symm.toLinearMap ∘ₗ
    LinearMap.proj (R := ℝ) (φ := fun j => Fin (n j + 1) → ℝ) i ∘ₗ (piBlockEquiv n).symm.toLinearMap

variable (l n b) in
/-- The inverse of `linFun`: `x ↦ (bᵢ(Pᵢ x))`. -/
def linInv : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin (pdim n + 1) → ℝ) :=
  (piBlockEquiv n).toLinearMap ∘ₗ LinearMap.pi fun i =>
    ((b i).toLinearMap ∘ₗ (projS w (l i)).codRestrict (l i : Submodule ℝ _) (H.projS_mem (l i).2))

omit H in
/-- `linFun` in coordinates. -/
theorem linFun_apply (v) : linFun l n b v = ∑ i, (((b i).symm ((piBlockEquiv n).symm v i) :
    ↥(l i : Submodule ℝ (Fin (m + 1) → ℝ))) : Fin (m + 1) → ℝ) := by
  simp [linFun]

variable (l n b) in
/-- **The linear isomorphism `ℝ^{pdim n + 1} ≅ ℝ^{m+1}`**, `(yᵢ) ↦ ∑ bᵢ⁻¹ yᵢ` (`E = ⊕ lᵢ`). -/
def linL : (Fin (pdim n + 1) → ℝ) ≃ₗ[ℝ] (Fin (m + 1) → ℝ) :=
  LinearEquiv.ofLinear (linFun l n b) (linInv l n b H)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.id_apply, linFun_apply]
      simp only [linInv, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        LinearMap.pi_apply, LinearEquiv.symm_apply_apply, LinearMap.codRestrict_apply]
      exact H.sum_projS l x)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, LinearMap.id_apply, linFun_apply]
      simp only [linInv, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← LinearEquiv.eq_symm_apply]
      funext i
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← LinearEquiv.eq_symm_apply]
      exact Subtype.ext (H.projS_sum l (fun j => ((b j).symm ((piBlockEquiv n).symm v j)).2) i))

/-- `linL` in coordinates. -/
theorem linL_apply (v) : linL l n b H v = ∑ i, (((b i).symm ((piBlockEquiv n).symm v i) :
    ↥(l i : Submodule ℝ (Fin (m + 1) → ℝ))) : Fin (m + 1) → ℝ) :=
  linFun_apply v

/-- `linL` on the blocks: `(yᵢ) ↦ ∑ bᵢ⁻¹ yᵢ`. -/
theorem linL_piBlockEquiv (y : ∀ i, Fin (n i + 1) → ℝ) :
    linL l n b H (piBlockEquiv n y) =
      ∑ i, (((b i).symm (y i) : ↥(l i : Submodule ℝ (Fin (m + 1) → ℝ))) : Fin (m + 1) → ℝ) := by
  rw [linL_apply, LinearEquiv.symm_apply_apply]

/-- **`F(w) = ∑ F(vᵢ)` through the bases**: `u ∈ F(w)` iff `u = ∑ bᵢ⁻¹ yᵢ` with `yᵢ ∈ bᵢ(F(vᵢ))`. -/
theorem mem_F_iff_linL (u : Fin (m + 1) → ℝ) : u ∈ F w ↔
    ∃ y : ∀ i, Fin (n i + 1) → ℝ, (∀ i, y i ∈ cset l n b i) ∧
      u = linL l n b H (piBlockEquiv n y) := by
  constructor
  · intro hu
    refine ⟨fun i => b i ⟨projS w (l i) u, H.projS_mem (l i).2 u⟩, fun i => ?_, ?_⟩
    · rw [mem_cset_iff, LinearEquiv.symm_apply_apply]
      exact ⟨u, hu, rfl⟩
    · rw [linL_piBlockEquiv]
      simp only [LinearEquiv.symm_apply_apply]
      exact (H.sum_projS l u).symm
  · rintro ⟨y, hy, rfl⟩
    rw [linL_piBlockEquiv]
    have hz : ∀ i, ∃ z ∈ F w, projS w (l i) z =
        (((b i).symm (y i) : ↥(l i : Submodule ℝ (Fin (m + 1) → ℝ))) : Fin (m + 1) → ℝ) :=
      fun i => mem_cset_iff.1 (hy i)
    choose z hzF hz using hz
    have := H.sum_mem l hzF
    simp_rw [hz] at this
    exact this

include l b in
/-- **The dimensions add up**: `∑ (nᵢ + 1) = m + 1`, i.e. `pdim n = m`. -/
theorem pdim_eq : pdim n = m := by
  have := (linL l n b H).finrank_eq
  simp only [Module.finrank_fin_fun] at this
  omega

end Produit

end Sphere

/-- **A projective isomorphism criterion**: a homeomorphism `Ψ : X ≃ₜ W` onto an open `W` of
`S(m')` which reads as a linear isomorphism after a global compatible chart `β` of `X` is a
projective isomorphism (and the dimensions agree). -/
theorem isProjIso_of_chart {k m' : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (S k) X]
    [HasGroupoid X (projGroupoid k)] {W : TopologicalSpace.Opens (S m')} (Ψ : X ≃ₜ W)
    {β : OpenPartialHomeomorph X (S k)} (hβ : β ∈ (projGroupoid k).maximalAtlas X)
    (hs : β.source = univ) (L : (Fin (k + 1) → ℝ) ≃ₗ[ℝ] (Fin (m' + 1) → ℝ))
    (hΨ : ∀ x, (Ψ x : S m') = Sphere.map L.toContinuousLinearEquiv (β x)) :
    IsProjIso k m' Ψ := by
  have hk : k = m' := by
    have := L.finrank_eq
    simp only [Module.finrank_fin_fun] at this
    omega
  subst hk
  refine ⟨rfl, isGXMorphism_of_mem_maximalAtlas Ψ.continuous fun x => ⟨β, hβ, chartAt (S k) (Ψ x),
    (projGroupoid k).chart_mem_maximalAtlas _, by rw [hs]; trivial, mem_chart_source _ _,
    (QuotientGroup.mk L : GSR k), Eventually.of_forall fun y => ?_⟩⟩
  rw [OpensCone.incl_apply, hΨ, GSE.mk_smul]
  rfl

section Compat
open PiCone
variable {q : ℕ} {n : Fin (q + 1) → ℕ} {B : Fin (q + 1) → Type*} [∀ i, TopologicalSpace (B i)]
  [∀ i, ChartedSpace (S (n i)) (B i)] [∀ i, HasGroupoid (B i) (projGroupoid (n i))]
  [∀ i, T2Space (B i)]

/-- Transport criterion: if `f` read through `Ψ` is `[x] ↦ [c · (φᵢ x_{τ(i)})]`, the transported
automorphism is compatible. -/
theorem isCompatiblePi_of_transport {m' : ℕ} {W : TopologicalSpace.Opens (S m')}
    (Ψ : PiBase n B ≃ₜ W) (hΨ : IsProjIso (pdim n) m' Ψ) (f : GXAut (GSR m') (S m') W)
    (τ : Equiv.Perm (Fin (q + 1))) (φ : ∀ i, FCone (n (τ i)) (B (τ i)) ≃ₜ FCone (n i) (B i))
    (hφ : ∀ i, IsConeIso (n (τ i)) (n i) (φ i)) (c : Fin (q + 1) → RPos)
    (hx : ∀ x : ∀ i, FCone (n i) (B i), f • Ψ (ConeBase.mk x) =
      Ψ (ConeBase.mk (piSMul n c fun i => φ i (x (τ i))))) :
    IsCompatiblePi ((hΨ.trans (⟨rfl, f.isGXMorphism⟩ : IsProjIso m' m' f.toHomeomorph)).trans
      hΨ.symm).toAut := by
  refine ⟨τ, φ, hφ, (c : PiTorus q), fun x => ?_⟩
  rw [IsProjIso.toAut_smul, piTorusAut_mk_smul]
  apply Ψ.injective
  rw [Homeomorph.trans_apply, Homeomorph.apply_symm_apply, Homeomorph.trans_apply]
  exact hx x

end Compat

namespace Sphere
open Produit PiCone

variable {m : ℕ}


/-- **Prop. 4, the Chapter 1 form** (`bzprop:c3s2p4_automorphisme_compatible`, NOT marked:
OQ-168, OQ-171): with `n i + 1 = dim lᵢ` and bases `bᵢ : lᵢ ≅ ℝ^{nᵢ+1}`, each `vᵢ` is an open
subset `Bᵢ` of `S(nᵢ)`; `w` is projectively isomorphic to `F⁻¹(F(B₀) × … × F(B_q))` (`PiBase`,
Ch. 1 § 3), and every projective automorphism of `w`, transported, is compatible (Ch. 1 § 3
Déf. 2, `IsCompatiblePi`). -/
theorem prop4_produit {w : Set (S m)} (hw : IsConvexPart w) (hopen : IsOpen w)
    (hne : w.Nonempty) (hn : noyau w = ∅) (hd : ¬ ContientDroite (F w)) {q : ℕ}
    (l : Fin (q + 1) ≃ simplesS w) (n : Fin (q + 1) → ℕ)
    (b : ∀ i, (l i : Submodule ℝ (Fin (m + 1) → ℝ)) ≃ₗ[ℝ] (Fin (n i + 1) → ℝ)) :
    ∃ hB : ∀ i, IsOpen (ofCone (b i '' (Subtype.val ⁻¹' sommandeS w (l i))) : Set (S (n i))),
      ∃ Ψ : PiBase n (fun i => (⟨_, hB i⟩ : TopologicalSpace.Opens (S (n i)))) ≃ₜ
          (⟨w, hopen⟩ : TopologicalSpace.Opens (S m)),
        IsProjIso (pdim n) m Ψ ∧
        ∀ f : GXAut (GSR m) (S m) (⟨w, hopen⟩ : TopologicalSpace.Opens (S m)),
          ∃ h : IsProjIso (pdim n) (pdim n) ((Ψ.trans f.toHomeomorph).trans Ψ.symm),
            IsCompatiblePi h.toAut := by
  have H : Hyps4 w := ⟨hw, hopen, hne, hn, hd⟩
  refine ⟨fun i => isOpen_ofCone_cset H i, ?_⟩
  let Bo : ∀ i, TopologicalSpace.Opens (S (n i)) := fun i =>
    ⟨ofCone (cset l n b i), isOpen_ofCone_cset (l := l) (b := b) H i⟩
  let x₀ : ∀ i, Bo i := fun i => ⟨_, (nonempty_cset (l := l) (b := b) H i).some_mem⟩
  let P := piChart n (fun i => OpensCone.gcc (x₀ i))
  have hP : IsConeChart (pdim n + 1) P := isConeChart_piChart fun i => OpensCone.isConeChart_gcc _
  let β := ConeBase.baseChart hP
  have hβs : β.source = univ := by
    rw [ConeBase.baseChart_source, piChart_source]
    simp only [OpensCone.gcc_source, pi_univ, image_univ]
    exact ConeBase.mk_surjective.range_eq
  have hβ : β ∈ (projGroupoid (pdim n)).maximalAtlas (PiBase n fun i => Bo i) :=
    ConeBase.baseChart_mem_maximalAtlas hP
  let L := linL l n b H
  have hiff : ∀ x : S (pdim n), x ∈ β.target ↔
      Sphere.map L.toContinuousLinearEquiv x ∈ (⟨w, hopen⟩ : TopologicalSpace.Opens (S m)) := by
    intro x
    induction x using Sphere.ind with
    | h v hv =>
    rw [ConeBase.baseChart_target, piChart_target, Sphere.map_mk]
    show _ ↔ _ ∈ w
    rw [Sphere.mk_mem_iff_mem_F (A := w)]
    simp only [OpensCone.gcc_target]
    constructor
    · rintro ⟨_, ⟨Y, hY, rfl⟩, hYv⟩
      have hYc : ∀ i, (Y i).val ∈ cset l n b i := fun i => by
        have := (OpensCone.toSphere_mem_iff (B := ofCone (cset l n b i)) (Y i)).1 (hY i trivial)
        rwa [F_ofCone_cset H i] at this
      have h1 : L (piBlockEquiv n fun i => (Y i).val) ∈ F w :=
        (mem_F_iff_linL H _).2 ⟨_, hYc, rfl⟩
      obtain ⟨c, hc, hcv⟩ := (Sphere.mk_eq_mk_iff_exists_pos (piBlockPt Y).val_ne_zero hv).1 hYv
      rw [← hcv]
      show L (c • _) ∈ F w
      rw [map_smul]
      exact Sphere.smul_mem_F h1 hc
    · intro h
      obtain ⟨y, hy, hyv⟩ := (mem_F_iff_linL H _).1 h
      have hv' : v = piBlockEquiv n y := L.injective hyv
      subst hv'
      refine ⟨piBlockPt fun i => ⟨y i, fun h0 => zero_notMem_cset H i (h0 ▸ hy i)⟩,
        ⟨_, fun i _ => ?_, rfl⟩, rfl⟩
      show Punctured.toSphere _ ∈ (ofCone (cset l n b i) : Set (S (n i)))
      rw [OpensCone.toSphere_mem_iff]
      show y i ∈ F (ofCone (cset l n b i))
      rw [F_ofCone_cset H i]
      exact hy i
  let Ψ : PiBase n (fun i => Bo i) ≃ₜ (⟨w, hopen⟩ : TopologicalSpace.Opens (S m)) :=
    (Homeomorph.Set.univ _).symm.trans ((Homeomorph.setCongr hβs.symm).trans
      (β.toHomeomorphSourceTarget.trans ((Sphere.map L.toContinuousLinearEquiv).subtype hiff)))
  have hΨ : ∀ x, (Ψ x : S m) = Sphere.map L.toContinuousLinearEquiv (β x) := fun x => rfl
  have hΨiso : IsProjIso (pdim n) m Ψ := isProjIso_of_chart Ψ hβ hβs L hΨ
  have hΨmk : ∀ z, (Ψ (ConeBase.mk z) : S m) = Sphere.map L.toContinuousLinearEquiv
      (Punctured.toSphere (piBlockPt fun i => OpensCone.gcc (x₀ i) (z i))) := fun z => by
    rw [hΨ]
    show Sphere.map _ (ConeBase.baseChart hP (ConeBase.mk z)) = _
    rw [ConeBase.baseChart_mk hP (by rw [piChart_source]; simp [OpensCone.gcc_source])]
    rfl
  clear_value Ψ
  refine ⟨Ψ, hΨiso, fun f => ⟨(hΨiso.trans ⟨rfl, f.isGXMorphism⟩).trans hΨiso.symm, ?_⟩⟩
  obtain ⟨g, hfg, τ, hτ, -⟩ := prop4_automorphisme_compatible (w := ⟨w, hopen⟩) hw hne hn hd l f
  let gres : ∀ i, ↥(l (τ i) : Submodule ℝ (Fin (m + 1) → ℝ)) ≃ₗ[ℝ]
      ↥(l i : Submodule ℝ (Fin (m + 1) → ℝ)) := fun i =>
    (g.submoduleMap (l (τ i) : Submodule ℝ (Fin (m + 1) → ℝ))).trans (LinearEquiv.ofEq _ _ (hτ i).1)
  have hgres : ∀ i u, ((gres i u : ↥(l i : Submodule ℝ (Fin (m + 1) → ℝ))) : Fin (m + 1) → ℝ) =
      g (u : Fin (m + 1) → ℝ) := fun i u => rfl
  let A : ∀ i, (Fin (n (τ i) + 1) → ℝ) ≃ₗ[ℝ] (Fin (n i + 1) → ℝ) := fun i =>
    ((b (τ i)).symm.trans (gres i)).trans (b i)
  have hA : ∀ i, ∃ φ : FCone (n (τ i)) (Bo (τ i)) ≃ₜ FCone (n i) (Bo i),
      IsConeIso (n (τ i)) (n i) φ ∧ ∃ c : RPos, ∀ x, (OpensCone.gcc (x₀ i)
        (posSMul (n i + 1) c (φ x))).val = A i (OpensCone.gcc (x₀ (τ i)) x).val := fun i => by
    refine OpensCone.exists_coneIso_of_linearEquiv (x₀ (τ i)) (x₀ i) (A i) fun v => ?_
    show v ∈ F (ofCone (cset l n b (τ i))) ↔ A i v ∈ F (ofCone (cset l n b i))
    rw [F_ofCone_cset H, F_ofCone_cset H, mem_cset_iff, mem_cset_iff]
    simp only [A, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hgres]
    have h2 : (g : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) '' sommandeS w (l (τ i)) =
        sommandeS w (l i) := (hτ i).2
    rw [← h2]
    exact (g.injective.mem_set_image).symm
  choose φ hφ c hc using hA
  refine isCompatiblePi_of_transport Ψ hΨiso f τ φ hφ c fun x => ?_
  apply Subtype.ext
  show ((f • Ψ (ConeBase.mk x) : (⟨w, hopen⟩ : TopologicalSpace.Opens (S m))) : S m) = _
  rw [hfg, hΨmk, hΨmk]
  simp only [Punctured.toSphere, Sphere.map_mk, Sphere.smul_mk]
  congr 1
  simp only [LinearEquiv.coe_toContinuousLinearEquiv', val_piBlockPt, piSMul_apply, hc]
  show g (linL l n b H _) = linL l n b H _
  rw [linL_piBlockEquiv, linL_piBlockEquiv, map_sum]
  simp only [A, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hgres]
  exact (Equiv.sum_comp τ (fun j => g (((b j).symm (OpensCone.gcc (x₀ j) (x j)).val :
    ↥(l j : Submodule ℝ (Fin (m + 1) → ℝ))) : Fin (m + 1) → ℝ))).symm


variable {m : ℕ}

/-- **Chapter 1's notation is always available**: every simple distinguished subvariety `lᵢ` is
nonzero, so it has a basis `bᵢ : lᵢ ≅ ℝ^{nᵢ+1}` (`nᵢ + 1 = dim lᵢ`); `prop4_produit` applies to
every `w` satisfying its hypotheses. -/
theorem exists_bases_simplesS {w : Set (S m)} {p : ℕ} (l : Fin p ≃ simplesS w) :
    ∃ n : Fin p → ℕ,
      Nonempty (∀ i, (l i : Submodule ℝ (Fin (m + 1) → ℝ)) ≃ₗ[ℝ] (Fin (n i + 1) → ℝ)) := by
  have hpos : ∀ i, 0 < Module.finrank ℝ (l i : Submodule ℝ (Fin (m + 1) → ℝ)) := fun i =>
    Nat.pos_of_ne_zero fun h => (l i).2.2.1 (Submodule.finrank_eq_zero.1 h)
  refine ⟨fun i => Module.finrank ℝ (l i : Submodule ℝ (Fin (m + 1) → ℝ)) - 1, ⟨fun i =>
    LinearEquiv.ofFinrankEq _ _ ?_⟩⟩
  rw [Module.finrank_fin_fun]
  have := hpos i
  show _ = Module.finrank ℝ (l i : Submodule ℝ (Fin (m + 1) → ℝ)) - 1 + 1
  omega

end Sphere

namespace BooleProjectifInstance

open Sphere

/-- **The instance of `prop4_produit`: the open `n`-simplex** of `S(n)` (`p = n + 1` simple
subvarieties, every `lᵢ` a line, so `nᵢ = 0` and each `Bᵢ` a point of `S(0)`) is projectively
isomorphic to `F⁻¹(F(B₀) × … × F(B_n))`, and its automorphisms are compatible. -/
theorem simplexO_prop4_produit {n : ℕ} :
    ∃ (l : Fin (n + 1) ≃ simplesS (simplexO n)) (k : Fin (n + 1) → ℕ)
      (b : ∀ i, (l i : Submodule ℝ (Fin (n + 1) → ℝ)) ≃ₗ[ℝ] (Fin (k i + 1) → ℝ))
      (hB : ∀ i, IsOpen (ofCone (b i '' (Subtype.val ⁻¹' sommandeS (simplexO n) (l i))) :
        Set (S (k i)))),
      ∃ Ψ : PiBase k (fun i => (⟨_, hB i⟩ : TopologicalSpace.Opens (S (k i)))) ≃ₜ
          (⟨simplexO n, simplexO_hyps4.2.1⟩ : TopologicalSpace.Opens (S n)),
        IsProjIso (pdim k) n Ψ ∧
        ∀ f : GXAut (GSR n) (S n) (⟨simplexO n, simplexO_hyps4.2.1⟩ : TopologicalSpace.Opens (S n)),
          ∃ h : IsProjIso (pdim k) (pdim k) ((Ψ.trans f.toHomeomorph).trans Ψ.symm),
            IsCompatiblePi h.toAut := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := simplexO_hyps4 (n := n)
  refine (simplexO_prop4 (n := n)).elim fun l _ => ?_
  refine (exists_bases_simplesS l).elim fun k hk => hk.elim fun b => ?_
  exact ⟨l, k, b, prop4_produit h1 h2 h3 h4 h5 l k b⟩

end BooleProjectifInstance

end Benzecri
