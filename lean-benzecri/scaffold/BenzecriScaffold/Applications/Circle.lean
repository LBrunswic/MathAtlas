import Benzecri.Cone.Functor
import Benzecri.Structure.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.GroupTheory.NoncommCoprod

/-!
# `BenzecriScaffold.Applications.Circle` — § 3 Prop. 1 and its corollary: `F(B)` and `B × S¹`

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 3, journal pp. 242–243; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`, checked against the scan (PDF pp. 15–16).
Package WP-45t (wave 5). Indexing as in `Cone/Lift`: `B` has dimension `n` (model `S n`), `F(B)`
dimension `n + 1` (model `RnO (n + 1)` for the cone, `Fin (n + 1) → ℝ` for the affine structure).

* **`bzprop:c1s3p1_F_homogene`** — `benzecri1960_ch1.tex:657` (statement l.657–661, p. 242; proof
  l.664–697, p. 243). **MARKED.** `Benzecri.FCone.prop1_F_homogene`: for `B` locally projective
  (Hausdorff, « variété »), `F(B)` with its canonical locally affine structure
  (`FCone.instChartedSpaceAff`) is homogeneous (resp. sweepable, resp. divisible) when `B` is —
  `isHomogeneous_of_isHomogeneous`, `isBalayable_of_isBalayable`, `isDivisible_of_isDivisible`;
  the divisible case for the printed group `F(G) × λ^ℤ` and every ratio `λ ≠ 1`
  (`isDivisible_divHom`).
* **`bzcor:c1s3p1c_produit_cercle`** — `benzecri1960_ch1.tex:701` (l.701–704, p. 243; with the
  proof's last paragraph, l.692–696). **MARKED.** `Benzecri.produit_cercle`: if a Hausdorff
  paracompact `B` carries a locally projective structure, `B × S¹` carries a locally affine one
  (`S¹` = Mathlib's `Circle`); no compactness is printed and none is used. The proof's sentence is
  formalized in full: `FCone.exists_affine_prod_circle` (a surjective local homeomorphism
  `F(B) → B × S¹` over `B` whose fibres are the `λ^ℤ`-orbits — `IsCoveringMap` is not stated —
  with the unique quotient structure making it a morphism),
  `FCone.hasGroupoid_quotient_lamHom` (`F(B)/λ^ℤ` is locally affine, Mathlib's quotient charts) and
  `FCone.exists_quotient_lamHom_homeomorph` (`F(B)/λ^ℤ ≃ₜ B × S¹` over `B`).

> **Proposition 1.** Si $B$ est une variété localement projective homogène (resp. balayable, resp.
> divisible), $F(B)$ considérée comme variété localement affine est homogène (resp. balayable,
> resp. divisible).
>
> *Démonstration.* A tout automorphisme projectif $\varphi$ de $B$ correspond un automorphisme
> $F(\varphi)$ de la structure conique affine de $F(B)$, donc aussi de sa structure localement
> affine. De plus, $\R^+$, groupe des homothéties de $F(B)$, est un groupe d'automorphismes de sa
> structure localement affine. […] L'automorphisme cherché qui transforme $m$ en $m'$ s'obtiendra
> en composant $F(\varphi)$ et une homothétie de rapport convenable. […] Soit $K$ un domaine
> générateur (cf. § 1, déf. 2 [sic]). Soit $K_1$ un compact section de $F(B)$ au-dessus de $K$. Il
> est clair que $K_1$ est un domaine générateur pour $F(B)$ […]. On construira une variété
> localement affine compacte, quotient de $F(B)$, en prenant le quotient de $F(B)$ par un groupe
> d'automorphismes, produit de $F(G)$ par un sous-groupe cyclique infini du groupe $\R^+$ des
> homothéties. En particulier, si $B$ est une variété localement projective compacte, le quotient
> de $F(B)$ par un sous-groupe infini discret du groupe $\R^+$ est une variété localement affine
> topologiqnement [sic] isomorphe au produit de $B$ par le cercle $S_1$.
>
> **Corollaire.** Si $B$ peut être muni d'une structure localement projective, $B\times S_1$ peut
> être muni d'une structure localement affine.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `B` a locally projective manifold | ✓ carried: `[ChartedSpace (S n) B] [HasGroupoid B (projGroupoid n)]` |
| « variété »: Hausdorff | ✓ carried (`[T2Space B]`: `F(B)` Hausdorff, Déf. 3's homotheties) |
| « variété »: second countable | weakened to `[ParacompactSpace B]` (implied by second countability; the reading DEC-128 certifies), and only for the corollary (the section of `F(B) → B`); Prop. 1 needs none |
| « variété »: connected | not needed anywhere |
| homogeneous / sweepable / divisible (Déf. 15) | ✓ carried: `IsHomogeneous`, `IsBalayable`, `IsDivisible` of `Structure/Classes` |
| `B` compact (the proof's last paragraph) | dropped: not needed (the corollary prints none) |
| « un sous-groupe infini discret » of `ℝ₊*` | `λ^ℤ` for any `λ ≠ 1` (`lamHom`) |
| `S₁`, « le cercle » | ✓ Mathlib's `Circle` (the unit circle of `ℂ`) |

## SCOPE (disclosed)

* **`F(B)` as a locally affine manifold** is the canonical affine charted space of the affine
  conical manifold `F(B)` (`Cone/Basic`'s `affineChartedSpace`, charts `ι ∘ e`), made a GLOBAL
  instance on the package's own type `FCone` (`instChartedSpaceAff`; kept global by DEC-128). Two
  charted spaces on one type are safe here because Mathlib's `ChartedSpace H M` takes the model `H`
  as an explicit, non-`outParam` argument (several models per space are intended,
  `Mathlib/Geometry/Manifold/ChartedSpace.lean`), so every use names its model and `chartAt _ x` is
  stuck rather than ambiguous; only Prop-valued instances derive from either. **Never generalise
  this instance to all affine conical manifolds** (a generic `[HasConeCharts n V] → ChartedSpace
  (Fin n → ℝ) V` would duplicate it along a second instance path): use `affineChartedSpace` with
  `letI` there, as the strict library does. « Automorphisme » is `GXAut` of that structure.
  `IsGXMorphism.affine_of_cone`: a conical morphism is an affine one.
* **Sweepable.** The printed « compact section $K_1$ au-dessus de $K$ » is used in the form the
  argument needs, a compact `K₁` with `π(K₁) ⊇ K` (`exists_isCompact_subset_proj_image`, from the
  openness of `π`); no global section is needed. The cross-reference « § 1, déf. 2 » is read
  Déf. 15 (`[sic]`, DEC-113).
* **Divisible.** `F(G₁) × λ^ℤ` is realised as the range of `divHom G₁ λ`
  (`MonoidHom.noncommCoprod`; the factors commute, `commute_autMap_homAut`); proper
  discontinuity uses the properness of the `ℝ₊*`-action on `F(B)` (`FCone.properSMul`,
  DEC-122/124), compactness of the quotient a compact fundamental set of `G₁` lifted to `F(B)`.
* **The corollary.** `B × S¹` is reached by Mathlib's push-forward of a structure along a
  surjective local homeomorphism with `(G, X)` deck transformations (`existsUnique_pushforward`),
  `Φ(x) = (π(x), θ_λ(N(x)))`, `N` the homogeneous norm of `Cone/Section` (`exists_trivialization`,
  which needs `F(B)/ℝ₊* ≅ B` paracompact). « Variété » is read paracompact (implied by second
  countability; DEC-128).
* **REMARK (DEC-128), the non-paracompact case** — outside the paper, not a finding. The bundle
  route genuinely uses paracompactness (a principal `ℝ₊*`-bundle over a non-paracompact Hausdorff
  manifold need not be trivial). But a Hausdorff manifold containing an embedded long ray carries
  no locally projective (nor locally affine) structure at all: every continuous map from a long ray
  to the compact metric `Sⁿ` is eventually constant, so no developing map (a local homeomorphism on
  the universal cover, which still contains a lifted long ray) can exist. A counterexample would
  therefore have to be non-paracompact without long rays (Prüfer/Moore-type surfaces), with
  `F(B) → B` non-trivial and `B × S¹` admitting no affine structure by any other construction
  (`F(B)/λ^ℤ` is still locally affine, a principal `S¹`-bundle over `B`). That case is open; none of
  this is formalized.
* The literal quotient `F(B)/λ^ℤ` (Mathlib's quotient charted space) is a locally affine manifold
  and is homeomorphic to `B × S¹` over `B`; that this homeomorphism is an affine isomorphism (it
  is, by `maximalAtlas_quotient_unique` and the uniqueness clause of
  `exists_affine_prod_circle`) is not stated separately.
* Generic lemmas proved here (REPORT `upstream_moves`): `rposLog`/`rposExp`/`rposLogHomeomorph`,
  `IsGXMorphism.affine_of_cone`, `exists_isCompact_forall_exists_smul_mem`,
  `isLocalHomeomorph_prodMap`, `FCone.map_congr_fun`, `FCone.locallyCompactSpace`,
  `FCone.baseProjHomeomorph`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Function
open scoped Pointwise

namespace Benzecri

universe u v

attribute [local instance] t2Space_RnO

/-! ### `ℝ₊*` and the logarithm -/

section RPosLog

/-- The logarithm of a positive real, `ℝ₊* → ℝ`. -/
def rposLog (c : RPos) : ℝ := Real.log ((c : ℝˣ) : ℝ)

/-- The exponential, `ℝ → ℝ₊*`. -/
def rposExp (t : ℝ) : RPos := Punctured.posUnit (Real.exp t) (Real.exp_pos t)

@[simp] theorem rposLog_rposExp (t : ℝ) : rposLog (rposExp t) = t := Real.log_exp t

@[simp] theorem rposExp_rposLog (c : RPos) : rposExp (rposLog c) = c :=
  Subtype.ext (Units.ext (Real.exp_log (Punctured.pos c)))

theorem rposLog_injective : Injective rposLog := fun a b h => by
  rw [← rposExp_rposLog a, h, rposExp_rposLog]

theorem rposLog_mul (a b : RPos) : rposLog (a * b) = rposLog a + rposLog b :=
  Real.log_mul (Punctured.pos a).ne' (Punctured.pos b).ne'

@[simp] theorem rposLog_one : rposLog 1 = 0 := Real.log_one

theorem rposLog_inv (c : RPos) : rposLog c⁻¹ = -rposLog c := by
  have := rposLog_mul c c⁻¹
  rw [mul_inv_cancel, rposLog_one] at this
  linarith

theorem rposLog_zpow (c : RPos) (k : ℤ) : rposLog (c ^ k) = k * rposLog c := by
  have : (((c ^ k : RPos) : ℝˣ) : ℝ) = (((c : ℝˣ) : ℝ)) ^ k := by
    rw [SubgroupClass.coe_zpow, Units.val_zpow_eq_zpow_val]
  rw [rposLog, this, Real.log_zpow, rposLog]

@[simp] theorem rposExp_zero : rposExp 0 = 1 :=
  rposLog_injective (by rw [rposLog_rposExp, rposLog_one])

theorem rposExp_add (s t : ℝ) : rposExp (s + t) = rposExp s * rposExp t :=
  rposLog_injective (by rw [rposLog_mul, rposLog_rposExp, rposLog_rposExp, rposLog_rposExp])

theorem continuous_rposLog : Continuous rposLog :=
  Real.continuousOn_log.comp_continuous (Units.continuous_val.comp continuous_subtype_val)
    fun c => (Punctured.pos c).ne'

theorem continuous_rposExp : Continuous rposExp :=
  continuous_RPos_iff.2 Real.continuous_exp

/-- `ℝ₊* ≃ₜ ℝ` by the logarithm. -/
def rposLogHomeomorph : RPos ≃ₜ ℝ where
  toFun := rposLog
  invFun := rposExp
  left_inv := rposExp_rposLog
  right_inv := rposLog_rposExp
  continuous_toFun := continuous_rposLog
  continuous_invFun := continuous_rposExp

theorem rposExp_one_ne_one : rposExp 1 ≠ 1 := fun h => by
  have := congrArg rposLog h
  rw [rposLog_rposExp, rposLog_one] at this
  exact one_ne_zero this

theorem rposLog_ne_zero {lam : RPos} (hlam : lam ≠ 1) : rposLog lam ≠ 0 := fun h =>
  hlam (by rw [← rposExp_rposLog lam, h, rposExp_zero])

end RPosLog

/-! ### A conical morphism is a morphism of the canonical locally affine structures -/

section ConeAffine

variable {n : ℕ} [NeZero n] {V : Type*} [TopologicalSpace V] [ChartedSpace (RnO n) V]
  {W : Type*} [TopologicalSpace W] [ChartedSpace (RnO n) W]

/-- **A morphism of affine conical manifolds is a morphism of their canonical locally affine
structures** (§ 3 Prop. 1's proof, « un automorphisme $F(\varphi)$ de la structure conique affine de
$F(B)$, donc aussi de sa structure localement affine »): where `f` reads as `g ∈ GU(n, ℝ)` in cone
charts, it reads as `g ∈ GA(n, ℝ)` in the charts `ι ∘ e`. -/
theorem IsGXMorphism.affine_of_cone {f : V → W} (hf : IsGXMorphism (GUR n) (RnO n) f) :
    @IsGXMorphism (GAR n) (Fin n → ℝ) _ _ _ V _ W _ (affineChartedSpace n V)
      (affineChartedSpace n W) f := by
  refine @IsGXMorphism.mk _ _ _ _ _ V _ W _ (affineChartedSpace n V) (affineChartedSpace n W) f
    hf.continuous fun x => ?_
  obtain ⟨g, hg⟩ := hf.exists_smul_eq x
  refine ⟨guToGA n g, hg.mono fun y hy => ?_⟩
  rw [transport_chartAt, transport_chartAt]
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply, hy, val_smul_guToGA]

end ConeAffine

/-! ### `F(B)` as a locally affine manifold; the automorphisms `F(φ)` and the homotheties -/

namespace FCone

variable {n : ℕ} {B : Type u} [TopologicalSpace B] [ChartedSpace (S n) B]
  [HasGroupoid B (projGroupoid n)]

/-- **`F(B)` considered as a locally affine manifold** (« $F(B)$ considérée comme variété localement
affine »): the canonical affine charted space of an affine conical manifold (`Cone/Basic`,
`affineChartedSpace`), as a global instance on the package's own type `F(B)` (DEC-128). It coexists
with the cone charted space `FCone.chartedSpace` because Mathlib's `ChartedSpace H M` takes the
model `H` as an explicit, non-`outParam` argument: every use names its model, so `chartAt _ x` is
stuck, never a silent pick. Do not generalise it to all affine conical manifolds (use
`affineChartedSpace` with `letI` there). -/
instance instChartedSpaceAff : ChartedSpace (Fin (n + 1) → ℝ) (FCone n B) :=
  affineChartedSpace (n + 1) (FCone n B)

instance instHasGroupoidAff : HasGroupoid (FCone n B) (affGroupoid (n + 1)) :=
  hasGroupoid_affineChartedSpace (n + 1)

/-- `F(B)` is locally compact. -/
theorem locallyCompactSpace : LocallyCompactSpace (FCone n B) :=
  ChartedSpace.locallyCompactSpace (Fin (n + 1) → ℝ) _

/-- `F(φ)` depends on `φ` only (named `map_congr_fun`, not `map_congr`, which would shadow the
root `map_congr` after `open Benzecri.FCone`). -/
theorem map_congr_fun {B₂ : Type v} [TopologicalSpace B₂] [ChartedSpace (S n) B₂]
    [HasGroupoid B₂ (projGroupoid n)] {φ ψ : B → B₂} (h : φ = ψ)
    (hφ : IsGXMorphism (GSR n) (S n) φ) (hψ : IsGXMorphism (GSR n) (S n) ψ) :
    map hφ = map hψ := by
  subst h; rfl

/-- `F(φ)` is a morphism of the locally affine structures. -/
theorem isGXMorphism_aff_map {B₂ : Type v} [TopologicalSpace B₂] [ChartedSpace (S n) B₂]
    [HasGroupoid B₂ (projGroupoid n)] {φ : B → B₂} (hφ : IsGXMorphism (GSR n) (S n) φ) :
    IsGXMorphism (GAR (n + 1)) (Fin (n + 1) → ℝ) (map hφ) :=
  (isGXMorphism_map hφ).affine_of_cone

theorem map_aut_mul (φ ψ : GXAut (GSR n) (S n) B) :
    map (φ * ψ).isGXMorphism = map φ.isGXMorphism ∘ map ψ.isGXMorphism := by
  rw [← map_comp]
  exact map_congr_fun (funext fun x => mul_smul φ ψ x) _ _

theorem map_aut_one : map (1 : GXAut (GSR n) (S n) B).isGXMorphism = id :=
  (map_congr_fun (funext fun x => one_smul _ x) _ isGXMorphism_id).trans map_id

theorem map_aut_bijective (φ : GXAut (GSR n) (S n) B) : Bijective (map φ.isGXMorphism) := by
  refine bijective_iff_has_inverse.2 ⟨map φ⁻¹.isGXMorphism, fun x => ?_, fun x => ?_⟩
  · have := congrFun (map_aut_mul φ⁻¹ φ) x
    rw [inv_mul_cancel, map_aut_one] at this
    exact this.symm
  · have := congrFun (map_aut_mul φ φ⁻¹) x
    rw [mul_inv_cancel, map_aut_one] at this
    exact this.symm

/-- **`F(φ)` as an automorphism of the locally affine structure of `F(B)`** (« A tout automorphisme
projectif $\varphi$ de $B$ correspond un automorphisme $F(\varphi)$ de la structure conique affine de
$F(B)$, donc aussi de sa structure localement affine »). -/
def autMap (φ : GXAut (GSR n) (S n) B) : GXAut (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B) :=
  GXAut.ofBijective (isGXMorphism_aff_map φ.isGXMorphism) (map_aut_bijective φ)

@[simp] theorem autMap_smul (φ : GXAut (GSR n) (S n) B) (x : FCone n B) :
    autMap φ • x = map φ.isGXMorphism x := rfl

/-- `φ ↦ F(φ)` as a homomorphism `Aut_proj(B) → Aut_aff(F(B))`. -/
def autMapHom : GXAut (GSR n) (S n) B →* GXAut (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B) where
  toFun := autMap
  map_one' := FaithfulSMul.eq_of_smul_eq_smul fun x : FCone n B => by
    rw [autMap_smul, map_aut_one, one_smul]; rfl
  map_mul' φ ψ := FaithfulSMul.eq_of_smul_eq_smul fun x : FCone n B => by
    rw [mul_smul, autMap_smul, autMap_smul, autMap_smul, map_aut_mul]; rfl

@[simp] theorem autMapHom_apply (φ : GXAut (GSR n) (S n) B) :
    autMapHom φ = autMap φ := rfl

@[simp] theorem proj_autMap_smul (φ : GXAut (GSR n) (S n) B) (x : FCone n B) :
    proj (autMap φ • x) = φ • proj x := by
  rw [autMap_smul, proj_map]

variable [T2Space B]

/-- **The homothety of ratio `λ` as an automorphism of the locally affine structure of `F(B)`**
(« $\R^+$, groupe des homothéties de $F(B)$, est un groupe d'automorphismes de sa structure localement
affine »). -/
def homAut (c : RPos) : GXAut (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B) :=
  GXAut.ofBijective (isGXMorphism_affine_smul (n := n + 1) (V := FCone n B) c)
    (bijective_iff_has_inverse.2 ⟨posSMul (n + 1) c⁻¹, posSMul_inv_posSMul c, fun x => by
      simpa using posSMul_inv_posSMul c⁻¹ x⟩)

@[simp] theorem homAut_smul (c : RPos) (x : FCone n B) :
    homAut (n := n) (B := B) c • x = posSMul (n + 1) c x := rfl

theorem homAut_mul (a b : RPos) :
    homAut (n := n) (B := B) (a * b) = homAut a * homAut b :=
  FaithfulSMul.eq_of_smul_eq_smul fun x : FCone n B => by
    rw [mul_smul, homAut_smul, homAut_smul, homAut_smul, posSMul_mul]

/-- `λ ↦ (m ↦ λm)` as a homomorphism `ℝ₊* → Aut_aff(F(B))`. -/
def homAutHom : RPos →* GXAut (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B) where
  toFun := homAut
  map_one' := FaithfulSMul.eq_of_smul_eq_smul fun x : FCone n B => by
    rw [homAut_smul, posSMul_one, one_smul]
  map_mul' := homAut_mul

@[simp] theorem homAutHom_apply (c : RPos) :
    homAutHom (n := n) (B := B) c = homAut c := rfl

/-- **`F(φ)` commutes with the homotheties** (it is a conical morphism, `IsGXMorphism.map_posSMul`). -/
theorem commute_autMap_homAut (φ : GXAut (GSR n) (S n) B) (c : RPos) :
    Commute (autMap φ) (homAut (n := n) (B := B) c) :=
  FaithfulSMul.eq_of_smul_eq_smul fun x : FCone n B => by
    rw [mul_smul, mul_smul, autMap_smul, homAut_smul, homAut_smul, autMap_smul]
    exact IsGXMorphism.map_posSMul (isGXMorphism_map φ.isGXMorphism) c x

theorem autMap_smul_posSMul (φ : GXAut (GSR n) (S n) B) (c : RPos) (x : FCone n B) :
    autMap φ • posSMul (n + 1) c x = posSMul (n + 1) c (autMap φ • x) :=
  IsGXMorphism.map_posSMul (isGXMorphism_map φ.isGXMorphism) c x

@[simp] theorem proj_homAut_smul (c : RPos) (x : FCone n B) :
    proj (homAut (n := n) (B := B) c • x) = proj x := by
  rw [homAut_smul, proj_posSMul]

/-! ### § 3 Prop. 1 — homogeneous, sweepable, divisible -/

/-- **`F(B)` is homogeneous when `B` is** (« L'automorphisme cherché qui transforme $m$ en $m'$
s'obtiendra en composant $F(\varphi)$ et une homothétie de rapport convenable »). -/
theorem isHomogeneous_of_isHomogeneous (h : IsHomogeneous (GSR n) (S n) B) :
    IsHomogeneous (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B) := by
  haveI : MulAction.IsPretransitive (GXAut (GSR n) (S n) B) B := h
  refine ⟨fun x x' => ?_⟩
  obtain ⟨φ, hφ⟩ := MulAction.exists_smul_eq (GXAut (GSR n) (S n) B) (proj x) (proj x')
  obtain ⟨c, hc⟩ := exists_posSMul_eq_of_proj_eq (x := autMap φ • x) (x' := x')
    (by rw [proj_autMap_smul, hφ])
  exact ⟨homAut c * autMap φ, by rw [mul_smul, homAut_smul, hc]⟩

omit [T2Space B] in
/-- **A compact set of `B` is covered by the projection of a compact set of `F(B)`** (the « compact
section $K_1$ de $F(B)$ au-dessus de $K$ » of the proof, in the form the proof uses: `π(K₁) ⊇ K`;
`π` is open and `F(B)` locally compact, so no global section is needed). -/
theorem exists_isCompact_subset_proj_image {K : Set B} (hK : IsCompact K) :
    ∃ K₁ : Set (FCone n B), IsCompact K₁ ∧ K ⊆ proj '' K₁ := by
  haveI := locallyCompactSpace (n := n) (B := B)
  choose C hC hCx using fun x : FCone n B => exists_compact_mem_nhds x
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun b : B => proj '' interior (C (ofPoint b)))
    (fun b => isOpenMap_proj _ isOpen_interior)
    (fun b _ => mem_iUnion.2 ⟨b, ofPoint b, mem_interior_iff_mem_nhds.2 (hCx _), rfl⟩)
  refine ⟨⋃ b ∈ t, C (ofPoint b), t.isCompact_biUnion fun b _ => hC _, fun b hb => ?_⟩
  obtain ⟨b', hb', y, hy, rfl⟩ := mem_iUnion₂.1 (ht hb)
  exact ⟨y, mem_iUnion₂.2 ⟨b', hb', interior_subset hy⟩, rfl⟩

/-- **`F(B)` is sweepable when `B` is** (« Soit $K$ un domaine générateur … Soit $K_1$ un compact
section de $F(B)$ au-dessus de $K$. Il est clair que $K_1$ est un domaine générateur pour $F(B)$ »,
the cross-reference « § 1, déf. 2 » read Déf. 15, `[sic]`, DEC-113). -/
theorem isBalayable_of_isBalayable (h : IsBalayable (GSR n) (S n) B) :
    IsBalayable (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B) := by
  obtain ⟨K, hK, hU⟩ := h
  obtain ⟨K₁, hK₁, hKK₁⟩ := exists_isCompact_subset_proj_image (n := n) hK
  refine ⟨K₁, hK₁, eq_univ_of_forall fun x => ?_⟩
  have hx : proj x ∈ ⋃ g ∈ (⊤ : Subgroup (GXAut (GSR n) (S n) B)), g • K := hU ▸ mem_univ _
  obtain ⟨φ, -, k, hk, hkx⟩ := mem_iUnion₂.1 hx
  obtain ⟨y, hy, rfl⟩ := hKK₁ hk
  obtain ⟨c, hc⟩ := exists_posSMul_eq_of_proj_eq (x := autMap φ • y) (x' := x)
    (by rw [proj_autMap_smul]; exact hkx)
  exact mem_iUnion₂.2 ⟨homAut c * autMap φ, Subgroup.mem_top _, y, hy,
    show (homAut c * autMap φ) • y = x by rw [mul_smul, homAut_smul, hc]⟩

end FCone

/-- **A compact fundamental set for a cocompact action** (used for « divisible »): if `Γ` acts by
homeomorphisms on a locally compact `M` with compact orbit space, some compact `K` meets every orbit. -/
theorem exists_isCompact_forall_exists_smul_mem {Γ : Type*} [Group Γ] {M : Type*}
    [TopologicalSpace M] [MulAction Γ M] [ContinuousConstSMul Γ M] [LocallyCompactSpace M]
    (hQ : CompactSpace (MulAction.orbitRel.Quotient Γ M)) :
    ∃ K : Set M, IsCompact K ∧ ∀ x : M, ∃ γ : Γ, γ • x ∈ K := by
  set π : M → MulAction.orbitRel.Quotient Γ M := Quotient.mk _
  have hπo : IsOpenMap π := isOpenMap_quotient_mk'_mul
  choose K hK hKx using fun x : M => exists_compact_mem_nhds x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => π '' interior (K x))
    (fun x => hπo _ isOpen_interior)
    (fun q _ => by
      obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
      exact mem_iUnion.2 ⟨x, x, mem_interior_iff_mem_nhds.2 (hKx x), rfl⟩)
  refine ⟨⋃ x ∈ t, K x, t.isCompact_biUnion fun x _ => hK x, fun y => ?_⟩
  obtain ⟨x, hxt, k, hk, hky⟩ := mem_iUnion₂.1 (ht (mem_univ (π y)))
  obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.1 (Quotient.exact hky)
  exact ⟨γ, mem_iUnion₂.2 ⟨x, hxt, by
    rw [show γ • y = k from hγ]; exact interior_subset hk⟩⟩

namespace FCone

variable {n : ℕ} {B : Type u} [TopologicalSpace B] [ChartedSpace (S n) B]
  [HasGroupoid B (projGroupoid n)] [T2Space B]

/-- **Finitely many powers of a homothety move a compact set to meet another** (the action of
`ℝ₊*` on `F(B)` is proper, `FCone.properSMul`, and `λ^ℤ` is discrete in `ℝ₊*`). -/
theorem finite_setOf_zpow_inter_nonempty {lam : RPos} (hlam : lam ≠ 1) {K L : Set (FCone n B)}
    (hK : IsCompact K) (hL : IsCompact L) :
    {k : ℤ | ((posSMul (n + 1) (lam ^ k)) '' K ∩ L).Nonempty}.Finite := by
  letI := coneMulAction (n + 1) (FCone n B)
  haveI := properSMul (n := n) (B := B)
  have hC : IsCompact {c : RPos | (c • K ∩ L).Nonempty} :=
    ProperSMul.isCompact_setOf_inter_nonempty hK hL
  obtain ⟨r, hr⟩ := ((hC.image continuous_rposLog).isBounded).subset_closedBall 0
  have hl : rposLog lam ≠ 0 := fun h => hlam (by rw [← rposExp_rposLog lam, h, rposExp_zero])
  have hl' : 0 < |rposLog lam| := abs_pos.2 hl
  refine (Set.finite_Icc (-⌈r / |rposLog lam|⌉) ⌈r / |rposLog lam|⌉).subset fun k hk => ?_
  have hmem : rposLog (lam ^ k) ∈ Metric.closedBall (0 : ℝ) r := hr ⟨_, hk, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, rposLog_zpow, abs_mul] at hmem
  have hk' : |(k : ℝ)| ≤ r / |rposLog lam| := (le_div_iff₀ hl').2 hmem
  have hk'' : |k| ≤ ⌈r / |rposLog lam|⌉ := by
    have := hk'.trans (Int.le_ceil _)
    exact_mod_cast this
  exact abs_le.1 hk''

/-- **The group `F(G₁) × λ^ℤ`** of the divisible case (« un groupe d'automorphismes, produit de
$F(G)$ par un sous-groupe cyclique infini du groupe $\R^+$ des homothéties »), as the homomorphism
`(φ, k) ↦ F(φ) ∘ λ^k` (the two factors commute, `commute_autMap_homAut`). -/
def divHom (G₁ : Subgroup (GXAut (GSR n) (S n) B)) (lam : RPos) :
    G₁ × Multiplicative ℤ →* GXAut (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B) :=
  (autMapHom.comp G₁.subtype).noncommCoprod (homAutHom.comp (zpowersHom RPos lam))
    fun φ _ => commute_autMap_homAut (φ : GXAut (GSR n) (S n) B) _

theorem divHom_smul (G₁ : Subgroup (GXAut (GSR n) (S n) B)) (lam : RPos)
    (p : G₁ × Multiplicative ℤ) (x : FCone n B) :
    divHom G₁ lam p • x = autMap (p.1 : GXAut (GSR n) (S n) B) •
      posSMul (n + 1) (lam ^ (Multiplicative.toAdd p.2)) x := by
  rw [divHom, MonoidHom.noncommCoprod_apply, mul_smul]
  rfl

omit [T2Space B] in
/-- `F(φ⁻¹) ∘ F(φ) = id`. -/
theorem autMap_inv_smul_autMap_smul (φ : GXAut (GSR n) (S n) B) (x : FCone n B) :
    autMap φ⁻¹ • autMap φ • x = x := by
  rw [← mul_smul, ← autMapHom_apply, ← autMapHom_apply, ← map_mul, inv_mul_cancel, map_one,
    one_smul]

theorem proj_divHom_smul (G₁ : Subgroup (GXAut (GSR n) (S n) B)) (lam : RPos)
    (p : G₁ × Multiplicative ℤ) (x : FCone n B) :
    proj (divHom G₁ lam p • x) = p.1 • proj x := by
  rw [divHom_smul, proj_autMap_smul, proj_posSMul]; rfl

/-- **`F(G₁) × λ^ℤ` is properly discontinuous** when `G₁` is: its elements moving a compact `K` to
meet a compact `L` project to elements of `G₁` moving `π(K)` to meet `π(L)` (finitely many), and
for each of those only finitely many powers of `λ` occur (`finite_setOf_zpow_inter_nonempty`). -/
theorem properlyDiscontinuousSMul_divHom (G₁ : Subgroup (GXAut (GSR n) (S n) B))
    [hG : ProperlyDiscontinuousSMul G₁ B] {lam : RPos} (hlam : lam ≠ 1) :
    ProperlyDiscontinuousSMul (divHom G₁ lam).range (FCone n B) := by
  refine ⟨fun {K L} hK hL => ?_⟩
  set A := {φ : G₁ | ((φ • ·) '' (proj '' K) ∩ proj '' L).Nonempty}
  have hA : A.Finite := hG.finite_disjoint_inter_image (hK.image continuous_proj)
    (hL.image continuous_proj)
  set Z : G₁ → Set ℤ := fun φ => {k : ℤ | ((posSMul (n + 1) (lam ^ k)) '' K ∩
    (autMap (φ : GXAut (GSR n) (S n) B)⁻¹ • ·) '' L).Nonempty}
  have hZ : ∀ φ, (Z φ).Finite := fun φ => finite_setOf_zpow_inter_nonempty hlam hK
    (hL.image (continuous_const_smul _))
  set P : Set (G₁ × Multiplicative ℤ) := ⋃ φ ∈ A, {φ} ×ˢ (Multiplicative.ofAdd '' Z φ)
  have hS : P.Finite := hA.biUnion fun φ _ => (finite_singleton φ).prod ((hZ φ).image _)
  refine (hS.image fun p => (⟨divHom G₁ lam p, p, rfl⟩ : (divHom G₁ lam).range)).subset ?_
  rintro ⟨γ, p, rfl⟩ ⟨_, ⟨x, hx, rfl⟩, hxL⟩
  have hxL' : divHom G₁ lam p • x ∈ L := hxL
  refine ⟨p, ?_, rfl⟩
  refine mem_iUnion₂.2 ⟨p.1, ⟨_, ⟨proj x, ⟨x, hx, rfl⟩, rfl⟩,
    ⟨_, hxL', by rw [proj_divHom_smul]⟩⟩, mem_prod.2 ⟨rfl, ⟨Multiplicative.toAdd p.2, ?_, rfl⟩⟩⟩
  refine ⟨_, ⟨x, hx, rfl⟩, ⟨_, hxL', ?_⟩⟩
  show autMap (p.1 : GXAut (GSR n) (S n) B)⁻¹ • divHom G₁ lam p • x = _
  rw [divHom_smul, autMap_inv_smul_autMap_smul]

/-- **`F(G₁) × λ^ℤ` acts freely** when `G₁` does (« sans point fixe »): an element fixing `x`
projects to an element of `G₁` fixing `π(x)`, hence is a homothety fixing `x`, hence `1`. -/
theorem isCancelSMul_divHom (G₁ : Subgroup (GXAut (GSR n) (S n) B)) [hG : IsCancelSMul G₁ B]
    {lam : RPos} (hlam : lam ≠ 1) :
    IsCancelSMul (divHom G₁ lam).range (FCone n B) := by
  refine isCancelSMul_iff_eq_one_of_smul_eq.2 ?_
  rintro ⟨γ, p, rfl⟩ x hx
  have hx' : divHom G₁ lam p • x = x := hx
  have h1 : p.1 = 1 := IsCancelSMul.eq_one_of_smul (x := proj x) (by
    rw [← proj_divHom_smul G₁ lam p x, hx'])
  rw [divHom_smul, h1, OneMemClass.coe_one, ← autMapHom_apply, map_one, one_smul] at hx'
  have h2 := eq_one_of_posSMul_eq hx'
  have hl : rposLog lam ≠ 0 := fun h => hlam (by rw [← rposExp_rposLog lam, h, rposExp_zero])
  have h3 : Multiplicative.toAdd p.2 = 0 := by
    have := congrArg rposLog h2
    rw [rposLog_zpow, rposLog_one, mul_eq_zero] at this
    exact_mod_cast this.resolve_right hl
  have hp : p = 1 := Prod.ext h1 (by simpa using h3)
  exact Subtype.ext (show divHom G₁ lam p = 1 by rw [hp, map_one])

/-- **The quotient of `F(B)` by `F(G₁) × λ^ℤ` is compact** when `B/G₁` is: a compact `K ⊆ B` meets
every `G₁`-orbit, a compact `K₁ ⊆ F(B)` projects onto `K`, and `{μ y | y ∈ K₁, μ between 1 and λ}`
meets every orbit. -/
theorem compactSpace_quotient_divHom (G₁ : Subgroup (GXAut (GSR n) (S n) B))
    (hQ : CompactSpace (MulAction.orbitRel.Quotient G₁ B)) {lam : RPos} (hlam : lam ≠ 1) :
    CompactSpace (MulAction.orbitRel.Quotient (divHom G₁ lam).range (FCone n B)) := by
  haveI : ContinuousConstSMul G₁ B :=
    ⟨fun g => continuous_const_smul (g : GXAut (GSR n) (S n) B)⟩
  haveI := ChartedSpace.locallyCompactSpace (S n) B
  obtain ⟨K, hK, hKmem⟩ := exists_isCompact_forall_exists_smul_mem hQ
  obtain ⟨K₁, hK₁, hKK₁⟩ := exists_isCompact_subset_proj_image (n := n) hK
  set L := rposLog lam
  set f : ℝ × FCone n B → FCone n B := fun q => posSMul (n + 1) (rposExp (q.1 * L)) q.2
  have hf : Continuous f := (continuous_posSMul (n := n + 1)).comp
    ((continuous_rposExp.comp (continuous_fst.mul continuous_const)).prodMk continuous_snd)
  set K₂ := f '' (Icc (0 : ℝ) 1 ×ˢ K₁)
  have hK₂ : IsCompact K₂ := (isCompact_Icc.prod hK₁).image hf
  refine ⟨?_⟩
  have huniv : (univ : Set (MulAction.orbitRel.Quotient (divHom G₁ lam).range (FCone n B))) =
      Quotient.mk _ '' K₂ := by
    refine (eq_univ_of_forall fun q => ?_).symm
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨γ, hγ⟩ := hKmem (proj x)
    obtain ⟨y, hy, hyx⟩ := hKK₁ hγ
    obtain ⟨c, hc⟩ := exists_posSMul_eq_of_proj_eq
      (x := autMap ((γ : GXAut (GSR n) (S n) B)⁻¹) • y) (x' := x) (by
        rw [proj_autMap_smul, hyx, Subgroup.smul_def, inv_smul_smul])
    set a := rposLog c
    have hL : L ≠ 0 := fun h => hlam (by rw [← rposExp_rposLog lam, show rposLog lam = 0 from h,
      rposExp_zero])
    set j : ℤ := ⌊a / L⌋
    set t : ℝ := Int.fract (a / L)
    have hc' : c = lam ^ j * rposExp (t * L) := by
      refine rposLog_injective ?_
      rw [rposLog_mul, rposLog_zpow, rposLog_rposExp, ← add_mul, Int.floor_add_fract,
        div_mul_cancel₀ _ hL]
    refine ⟨f (t, y), ⟨(t, y), ⟨⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, hy⟩, rfl⟩, ?_⟩
    refine (Quotient.sound (MulAction.orbitRel_apply.2
      ⟨⟨divHom G₁ lam (γ⁻¹, Multiplicative.ofAdd j), _, rfl⟩, ?_⟩)).symm
    show divHom G₁ lam (γ⁻¹, Multiplicative.ofAdd j) • f (t, y) = x
    rw [divHom_smul]
    simp only [toAdd_ofAdd, f]
    rw [← hc, hc', posSMul_mul, autMap_smul_posSMul, autMap_smul_posSMul, InvMemClass.coe_inv]
  rw [huniv]
  exact hK₂.image continuous_quotient_mk'

/-- **`F(B)` is divisible when `B` is** (« On construira une variété localement affine compacte,
quotient de $F(B)$, en prenant le quotient de $F(B)$ par un groupe d'automorphismes, produit de
$F(G)$ par un sous-groupe cyclique infini du groupe $\R^+$ des homothéties »), for the group
`F(G₁) × λ^ℤ` of any ratio `λ ≠ 1` (`isDivisible_divHom`). -/
theorem isDivisible_divHom (G₁ : Subgroup (GXAut (GSR n) (S n) B))
    (h1 : ProperlyDiscontinuousSMul G₁ B) (h2 : IsCancelSMul G₁ B)
    (h3 : CompactSpace (MulAction.orbitRel.Quotient G₁ B)) {lam : RPos} (hlam : lam ≠ 1) :
    ProperlyDiscontinuousSMul (divHom G₁ lam).range (FCone n B) ∧
      IsCancelSMul (divHom G₁ lam).range (FCone n B) ∧
      CompactSpace (MulAction.orbitRel.Quotient (divHom G₁ lam).range (FCone n B)) :=
  ⟨properlyDiscontinuousSMul_divHom (hG := h1) G₁ hlam, isCancelSMul_divHom (hG := h2) G₁ hlam,
    compactSpace_quotient_divHom G₁ h3 hlam⟩

/-- **`F(B)` is divisible when `B` is.** -/
theorem isDivisible_of_isDivisible (h : IsDivisible (GSR n) (S n) B) :
    IsDivisible (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B) := by
  obtain ⟨G₁, h1, h2, h3⟩ := h
  exact ⟨_, isDivisible_divHom G₁ h1 h2 h3 rposExp_one_ne_one⟩

/-- **§ 3 Prop. 1** (`bzprop:c1s3p1_F_homogene`): « Si $B$ est une variété localement projective
homogène (resp. balayable, resp. divisible), $F(B)$ considérée comme variété localement affine est
homogène (resp. balayable, resp. divisible) ». -/
theorem prop1_F_homogene :
    (IsHomogeneous (GSR n) (S n) B → IsHomogeneous (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B)) ∧
    (IsBalayable (GSR n) (S n) B → IsBalayable (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B)) ∧
    (IsDivisible (GSR n) (S n) B → IsDivisible (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B)) :=
  ⟨isHomogeneous_of_isHomogeneous, isBalayable_of_isBalayable, isDivisible_of_isDivisible⟩

end FCone

/-! ### The circle coordinate `ℝ₊*/λ^ℤ ≃ S¹` -/

section CircleCoord

/-- **The angle of `c ∈ ℝ₊*` modulo `λ`**: `θ_λ(c) = exp(2iπ log c / log λ) ∈ S¹` (Mathlib's
`Circle`, the unit circle of `ℂ`). -/
def circleCoord (lam c : RPos) : Circle :=
  Circle.exp (2 * Real.pi * (rposLog c / rposLog lam))

variable {lam : RPos}

theorem circleCoord_eq_iff (hlam : lam ≠ 1) {c c' : RPos} :
    circleCoord lam c = circleCoord lam c' ↔ ∃ k : ℤ, c = lam ^ k * c' := by
  have hl := rposLog_ne_zero hlam
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  rw [circleCoord, circleCoord, Circle.exp_eq_exp]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, rposLog_injective ?_⟩
    rw [rposLog_mul, rposLog_zpow]
    have h2 : rposLog c / rposLog lam = rposLog c' / rposLog lam + k := by
      have h3 : 2 * Real.pi * (rposLog c / rposLog lam) =
          2 * Real.pi * (rposLog c' / rposLog lam + k) := by rw [hk]; ring
      exact mul_left_cancel₀ hpi h3
    rw [div_eq_iff hl, add_mul, div_mul_cancel₀ _ hl] at h2
    linarith
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    rw [rposLog_mul, rposLog_zpow]
    field_simp
    ring

theorem circleCoord_zpow_mul (lam c : RPos) (k : ℤ) :
    circleCoord lam (lam ^ k * c) = circleCoord lam c := by
  by_cases hlam : lam = 1
  · rw [hlam, one_zpow, one_mul]
  · exact (circleCoord_eq_iff hlam).2 ⟨k, rfl⟩

theorem isLocalHomeomorph_circleCoord (hlam : lam ≠ 1) : IsLocalHomeomorph (circleCoord lam) := by
  have hl := rposLog_ne_zero hlam
  have ha : 2 * Real.pi / rposLog lam ≠ 0 := div_ne_zero (by positivity) hl
  have : circleCoord lam = Circle.exp ∘ (rposLogHomeomorph.trans (Homeomorph.mulLeft₀ _ ha)) := by
    funext c
    simp only [circleCoord, Function.comp_apply, Homeomorph.trans_apply,
      Homeomorph.coe_mulLeft₀]
    congr 1
    rw [mul_div_assoc', div_mul_eq_mul_div]
    rfl
  rw [this]
  exact isLocalHomeomorph_circleExp.comp (Homeomorph.isLocalHomeomorph _)

theorem circleCoord_surjective (hlam : lam ≠ 1) : Surjective (circleCoord lam) := by
  have hl := rposLog_ne_zero hlam
  intro z
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  refine ⟨rposExp (t * rposLog lam / (2 * Real.pi)), ?_⟩
  rw [circleCoord, rposLog_rposExp]
  congr 1
  field_simp

end CircleCoord

/-- **A product of local homeomorphisms is a local homeomorphism.** -/
theorem isLocalHomeomorph_prodMap {X Y X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y'] {f : X → X'} {g : Y → Y'}
    (hf : IsLocalHomeomorph f) (hg : IsLocalHomeomorph g) : IsLocalHomeomorph (Prod.map f g) := by
  refine IsLocalHomeomorph.mk _ fun p => ?_
  obtain ⟨e, he, hfe⟩ := hf p.1
  obtain ⟨e', he', hge⟩ := hg p.2
  refine ⟨e.prod e', ⟨he, he'⟩, ?_⟩
  intro q _
  rw [OpenPartialHomeomorph.prod_apply, Prod.map_apply, hfe, hge]

/-! ### The corollary: `B × S¹` is locally affine -/

namespace FCone

variable {n : ℕ} {B : Type u} [TopologicalSpace B] [ChartedSpace (S n) B]
  [HasGroupoid B (projGroupoid n)] [T2Space B]

/-- **`F(B)/ℝ₊* ≃ₜ B`** by the source projection (`baseProj`, a bijective local isomorphism). -/
def baseProjHomeomorph : ConeBase n (FCone n B) ≃ₜ B :=
  (Equiv.ofBijective _ baseProj_bijective).toHomeomorphOfContinuousOpen continuous_baseProj
    isGXMorphism_baseProj.isLocalHomeomorph.isOpenMap

@[simp] theorem baseProjHomeomorph_apply (b : ConeBase n (FCone n B)) :
    baseProjHomeomorph b = baseProj b := rfl

/-- **The corollary in its full form** (the proof's last paragraph, « le quotient de $F(B)$ par un
sous-groupe infini discret du groupe $\R^+$ des homothéties est une variété localement affine
topologiquement isomorphe au produit de $B$ par le cercle $S_1$ »), for a paracompact `B` and any
ratio `λ ≠ 1`: there is a surjective local homeomorphism `Φ : F(B) → B × S¹` over `B` whose fibres
are exactly the orbits of `λ^ℤ`, and `B × S¹` carries a locally affine structure for which `Φ` is a
morphism — the quotient structure of `F(B)/λ^ℤ`, unique as such (maximal atlas). `Φ(x) = (π(x),
θ_λ(N(x)))` for a homogeneous norm `N` (the section of `Cone/Section`). -/
theorem exists_affine_prod_circle [ParacompactSpace B] {lam : RPos} (hlam : lam ≠ 1) :
    ∃ Φ : FCone n B → B × Circle, IsLocalHomeomorph Φ ∧ Surjective Φ ∧
      (∀ x, (Φ x).1 = proj x) ∧
      (∀ x x', Φ x = Φ x' ↔ ∃ k : ℤ, posSMul (n + 1) (lam ^ k) x = x') ∧
      ∃ cs : ChartedSpace (Fin (n + 1) → ℝ) (B × Circle),
        ∃ _ : @HasGroupoid _ _ (B × Circle) _ cs (affGroupoid (n + 1)),
        @IsGXMorphism (GAR (n + 1)) (Fin (n + 1) → ℝ) _ _ _ (FCone n B) _ (B × Circle) _ _ cs Φ ∧
        ∀ cs' : ChartedSpace (Fin (n + 1) → ℝ) (B × Circle),
          ∀ _ : @HasGroupoid _ _ (B × Circle) _ cs' (affGroupoid (n + 1)),
          @IsGXMorphism (GAR (n + 1)) (Fin (n + 1) → ℝ) _ _ _ (FCone n B) _ (B × Circle) _ _ cs'
            Φ →
          @StructureGroupoid.maximalAtlas _ (B × Circle) _ _ cs' (affGroupoid (n + 1)) =
            @StructureGroupoid.maximalAtlas _ (B × Circle) _ _ cs (affGroupoid (n + 1)) := by
  haveI := t2Space_coneBase (n := n) (B := B)
  haveI : ParacompactSpace (ConeBase n (FCone n B)) :=
    (baseProjHomeomorph.paracompactSpace_iff).2 inferInstance
  obtain ⟨T, hT1, hT2⟩ := ConeBase.exists_trivialization (n := n) (V := FCone n B)
  set Φ : FCone n B → B × Circle := fun x => (baseProj (T x).1, circleCoord lam (T x).2) with hΦ
  have hΦ1 : ∀ x, (Φ x).1 = proj x := fun x => by simp only [Φ, hT1, baseProj_mk]
  have hΦeq : ∀ x x', Φ x = Φ x' ↔ ∃ k : ℤ, posSMul (n + 1) (lam ^ k) x = x' := by
    intro x x'
    constructor
    · intro h
      have h1 : (T x).1 = (T x').1 := baseProj_injective (congrArg Prod.fst h)
      obtain ⟨k, hk⟩ := (circleCoord_eq_iff hlam).1 (congrArg Prod.snd h).symm
      refine ⟨k, T.injective ?_⟩
      rw [hT2, h1, ← hk]
    · rintro ⟨k, rfl⟩
      simp only [Φ, hT2, circleCoord_zpow_mul]
  have hloc : IsLocalHomeomorph Φ :=
    (isLocalHomeomorph_prodMap baseProjHomeomorph.isLocalHomeomorph
      (isLocalHomeomorph_circleCoord hlam)).comp T.isLocalHomeomorph
  have hsurj : Surjective Φ := by
    rintro ⟨b, z⟩
    obtain ⟨q, rfl⟩ := baseProj_surjective (n := n) b
    obtain ⟨c, rfl⟩ := circleCoord_surjective hlam z
    exact ⟨T.symm (q, c), by simp only [Φ, Homeomorph.apply_symm_apply]⟩
  have hdeck : IsGXDeck (GAR (n + 1)) (Fin (n + 1) → ℝ) Φ := by
    intro x x' h
    obtain ⟨k, rfl⟩ := (hΦeq x x').1 h
    obtain ⟨g, hg⟩ := (isGXMorphism_affine_smul (n := n + 1) (V := FCone n B) (lam ^ k)).exists_smul_eq x
    exact ⟨posSMul (n + 1) (lam ^ k),
      ((continuous_posSMul (n := n + 1)).comp (continuous_const.prodMk continuous_id)).continuousAt,
      rfl, Eventually.of_forall fun y => ((hΦeq y _).2 ⟨k, rfl⟩).symm, g, hg⟩
  obtain ⟨cs, hcs, hmor, huniq⟩ := existsUnique_pushforward hloc hsurj hdeck
  exact ⟨Φ, hloc, hsurj, hΦ1, hΦeq, cs, hcs, hmor, huniq⟩

/-! ### The quotient `F(B)/λ^ℤ`, literally -/

/-- `k ↦ λ^k` as a homomorphism `ℤ → Aut_aff(F(B))`. -/
def lamHom (lam : RPos) : Multiplicative ℤ →* GXAut (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B) :=
  homAutHom.comp (zpowersHom RPos lam)

theorem lamHom_smul (lam : RPos) (k : Multiplicative ℤ) (x : FCone n B) :
    lamHom (n := n) (B := B) lam k • x = posSMul (n + 1) (lam ^ (Multiplicative.toAdd k)) x := rfl

/-- **`λ^ℤ` acts properly discontinuously on `F(B)`** (« un sous-groupe infini discret du groupe
$\R^+$ des homothéties »; the action of `ℝ₊*` is proper, `FCone.properSMul`). -/
theorem properlyDiscontinuousSMul_lamHom {lam : RPos} (hlam : lam ≠ 1) :
    ProperlyDiscontinuousSMul (lamHom (n := n) (B := B) lam).range (FCone n B) := by
  refine ⟨fun {K L} hK hL => ?_⟩
  refine ((finite_setOf_zpow_inter_nonempty hlam hK hL).image fun k : ℤ =>
    (⟨lamHom lam (Multiplicative.ofAdd k), _, rfl⟩ : (lamHom (n := n) (B := B) lam).range)).subset ?_
  rintro ⟨γ, k, rfl⟩ hne
  exact ⟨Multiplicative.toAdd k, hne, rfl⟩

/-- **`λ^ℤ` acts freely on `F(B)`** for `λ ≠ 1`. -/
theorem isCancelSMul_lamHom {lam : RPos} (hlam : lam ≠ 1) :
    IsCancelSMul (lamHom (n := n) (B := B) lam).range (FCone n B) := by
  refine isCancelSMul_iff_eq_one_of_smul_eq.2 ?_
  rintro ⟨γ, k, rfl⟩ x hx
  have h2 := eq_one_of_posSMul_eq
    (show posSMul (n + 1) (lam ^ (Multiplicative.toAdd k)) x = x from hx)
  have h3 : Multiplicative.toAdd k = 0 := by
    have := congrArg rposLog h2
    rw [rposLog_zpow, rposLog_one, mul_eq_zero] at this
    exact_mod_cast this.resolve_right (rposLog_ne_zero hlam)
  have hk : k = 1 := h3
  exact Subtype.ext (show lamHom lam k = 1 by rw [hk, map_one])

/-- **`F(B)/λ^ℤ` is a locally affine manifold** (« le quotient de $F(B)$ par un sous-groupe infini
discret du groupe $\R^+$ des homothéties est une variété localement affine »), for Mathlib's
charted space on the quotient (p. 238, `hasGroupoid_quotient`). -/
theorem hasGroupoid_quotient_lamHom {lam : RPos} (hlam : lam ≠ 1) :
    haveI := properlyDiscontinuousSMul_lamHom (n := n) (B := B) hlam
    haveI := isCancelSMul_lamHom (n := n) (B := B) hlam
    haveI := locallyCompactSpace (n := n) (B := B)
    haveI := continuousConstSMul_of_isGXMorphism (G := GAR (n + 1)) (X := Fin (n + 1) → ℝ)
      fun γ : (lamHom (n := n) (B := B) lam).range =>
        (γ : GXAut (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B)).isGXMorphism
    HasGroupoid (MulAction.orbitRel.Quotient (lamHom (n := n) (B := B) lam).range (FCone n B))
      (affGroupoid (n + 1)) :=
  haveI := properlyDiscontinuousSMul_lamHom (n := n) (B := B) hlam
  haveI := isCancelSMul_lamHom (n := n) (B := B) hlam
  haveI := locallyCompactSpace (n := n) (B := B)
  hasGroupoid_quotient (Γ := (lamHom (n := n) (B := B) lam).range) fun γ => (γ : GXAut (GAR (n + 1)) (Fin (n + 1) → ℝ) (FCone n B)).isGXMorphism

/-- **`F(B)/λ^ℤ` is « topologiquement isomorphe au produit de $B$ par le cercle $S_1$ »**, for `B`
paracompact (no compactness needed), by a homeomorphism over `B`. -/
theorem exists_quotient_lamHom_homeomorph [ParacompactSpace B] {lam : RPos} (hlam : lam ≠ 1) :
    ∃ e : MulAction.orbitRel.Quotient (lamHom (n := n) (B := B) lam).range (FCone n B) ≃ₜ
      B × Circle, ∀ x : FCone n B, (e (Quotient.mk _ x)).1 = proj x := by
  obtain ⟨Φ, hloc, hsurj, hΦ1, hΦeq, -⟩ := exists_affine_prod_circle (n := n) (B := B) hlam
  let ΦC : C(FCone n B, B × Circle) := ⟨Φ, hloc.continuous⟩
  have hq : IsQuotientMap ΦC := hloc.isOpenMap.isQuotientMap hloc.continuous hsurj
  set Γ := (lamHom (n := n) (B := B) lam).range
  have hrel : ∀ x x' : FCone n B, MulAction.orbitRel Γ (FCone n B) x x' ↔ Φ x = Φ x' := by
    intro x x'
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨⟨γ, k, rfl⟩, hγ⟩
      exact ((hΦeq x' x).2 ⟨_, hγ⟩).symm
    · intro h
      obtain ⟨k, hk⟩ := (hΦeq x' x).1 h.symm
      exact ⟨⟨lamHom lam (Multiplicative.ofAdd k), _, rfl⟩, hk⟩
  let g : C(FCone n B, MulAction.orbitRel.Quotient Γ (FCone n B)) :=
    ⟨Quotient.mk _, continuous_quotient_mk'⟩
  have hg : FactorsThrough g ΦC := fun a b h => Quotient.sound ((hrel a b).2 h)
  let toF : MulAction.orbitRel.Quotient Γ (FCone n B) → B × Circle :=
    Quotient.lift Φ fun a b h => (hrel a b).1 h
  have hlift : ∀ x, hq.lift g hg (Φ x) = Quotient.mk _ x := fun x =>
    DFunLike.congr_fun (hq.lift_comp g hg) x
  refine ⟨⟨⟨toF, hq.lift g hg, fun q => ?_, fun p => ?_⟩, continuous_quot_lift _ hloc.continuous,
    (hq.lift g hg).continuous⟩, fun x => hΦ1 x⟩
  · obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
    exact hlift x
  · obtain ⟨x, rfl⟩ := hsurj p
    show toF (hq.lift g hg (Φ x)) = Φ x
    rw [hlift]
    rfl

end FCone

/-- **§ 3, corollary of Prop. 1** (`bzcor:c1s3p1c_produit_cercle`): « Si $B$ peut être muni d'une
structure localement projective, $B\times S_1$ peut être muni d'une structure localement affine »,
for `B` a « variété » (Hausdorff, paracompact; no compactness is printed and none is needed). -/
theorem produit_cercle {n : ℕ} (B : Type u) [TopologicalSpace B] [T2Space B] [ParacompactSpace B]
    (h : ∃ cs : ChartedSpace (S n) B, @HasGroupoid _ _ B _ cs (projGroupoid n)) :
    ∃ cs : ChartedSpace (Fin (n + 1) → ℝ) (B × Circle),
      @HasGroupoid _ _ (B × Circle) _ cs (affGroupoid (n + 1)) := by
  obtain ⟨cs, hcs⟩ := h
  obtain ⟨-, -, -, -, -, cs', hcs', -⟩ :=
    FCone.exists_affine_prod_circle (n := n) (B := B) rposExp_one_ne_one
  exact ⟨cs', hcs'⟩

end Benzecri
