import Benzecri.Structure.Quotient
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Algebra.ProperAction.Basic

/-!
# `BenzecriScaffold.Cone.Basic` — open cones, affine conical manifolds, positive homotheties (§ 2, Déf. 1–3, Prop. 1)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 2, journal pp. 239–240; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`, checked against the scan (PDF p. 12–13).
Package WP-45m (wave 3, layer L4; fix round after AUDIT-1 and DEC-122).

* **`bzdef:c1s2d1_cone_ouvert`** — `benzecri1960_ch1.tex:482` (Déf. 1, l.482–485, p. 239):
  `Benzecri.IsOpenCone` (open, `O ∉ C`, stable under `t > 0`); the printed form « réunion de
  demi-droites ouvertes issues de l'origine » is `isOpenCone_iff_iUnion_halfLine`; open cones are
  the `F(A)`, `A` open in `S(E)` (`isOpenCone_iff_exists_F`); in `ℝⁿ − {O}`: `IsConeSet`,
  `isConeSet_iff`.
* **`bzdef:c1s2d2_variete_conique_affine`** — `benzecri1960_ch1.tex:488` (Déf. 2, l.488–503,
  p. 240): the model `RnO n = ℝⁿ − {O}` (`Benzecri.Punctured`), the group `GU(n, ℝ)` (`GUR n`,
  acting analytically, `IsAnalyticAction`), `coneGroupoid n`; Déf. 2 as printed is
  `Benzecri.IsConeJetStructure` (an open set of jets of isomorphisms with 1°, 2°, 3°); in atlas
  form an affine conical manifold is `[ChartedSpace (RnO n) V] [HasGroupoid V (coneGroupoid n)]
  [HasConeCharts n V]`, and **the two are equivalent** (`def2_iff`). 3° prints « paragraphe 1,
  définition 2 »: read Déf. 13 (DEC-113, the transcription's `[sic]`).
* **`bzprop:c1s2p1_atlas_conique`** — `benzecri1960_ch1.tex:508` (Prop. 1, l.508–516, p. 240):
  `existsUnique_coneStructure_of_atlas` (transitions only locally in `GU(n)`, the strongest form)
  and `existsUnique_coneStructure_of_atlas_printed` (`{V_i}` read `{U_i}`, `f_i = g_ij ∘ f_i` read
  `f_i = g_ij ∘ f_j`, the transcription's `[sic]`).
* `bzdef:c1s2d3_homotheties_positives` — `benzecri1960_ch1.tex:526` (Déf. 3, l.526–538, p. 240),
  **not marked here** (marked in `Cone/Section`, closed in its corrected form, DEC-122): this file
  proves the action and its stated properties —
  `posSMul` (`λm = f⁻¹(λ f(m))`), **independence of the chart** (`IsConeChart.symm_smul_eq`,
  `posSMul_eq`, for `V` Hausdorff), the action law (`coneMulAction`, `posSMul_mul`), continuity
  (`continuous_posSMul`), freeness (`eq_one_of_posSMul_eq`), « groupe d'automorphismes de sa
  structure localement affine » (`isGXMorphism_affine_smul`) « mais non de sa structure conique
  affine » (`not_isGXMorphism_cone_smul`); the principal bundle is `Cone/Base`
  (`ConeBase.coneTrivialization`), the section and the triviality `Cone/Section`. **Finding
  (DEC-122)**: « cet espace fibré est topologiquement trivial » is false without a hypothesis the
  paper does not print — the counterexample of `Cone/Counterexample` (`n = 3`) is a Hausdorff,
  second countable affine conical manifold whose base is not Hausdorff, so that `V` is homeomorphic
  to `B × ℝ₊*` by no homeomorphism; the corrected form adds that the action of `ℝ₊*` is proper
  (equivalently `B` Hausdorff, `ConeBase.t2Space_iff_properSMul`), automatic for `n ≤ 2`
  (`Cone/LowDim`).
* Unlabelled prose (l.518–524, p. 240): **the canonical locally affine structure**
  (`affineChartedSpace`, `hasGroupoid_affineChartedSpace`, `jetVal_mem_jets_affine`) is « l'unique
  structure affine dont l'ensemble $J(V)$ des jets affins contienne $J_1(V)$ »
  (`maximalAtlas_affine_unique`); **the category** `ConeCat n` (objects `IsProperConeObject`:
  cone charts, Hausdorff, a proper `ℝ₊*`-action, DEC-122; morphisms the
  `(GU(n), ℝⁿ − {O})`-morphisms, which are the maps with `J₁(V₂) ∘ f ⊆ J₁(V₁)` by
  `isGXMorphism_iff_jets`); conical morphisms commute with the homotheties
  (`IsGXMorphism.map_posSMul`, for wave 4's `F⁻¹`).

> **Déf. 1.** On appelle cône ouvert de $\R^n$, une partie ouverte de $\R^n-\{O\}$, réunion de
> demi-droites ouvertes issues de l'origine.
>
> **Déf. 2.** Sur une variété $V$ de dimension $n$, une structure de variété conique affine de
> dimension $n$ est définie par la donnée d'un ensemble ouvert $J_1(V)$ de jets d'isomorphismes de
> $V$ dans $\R^n-\{O\}$ tel que
> 1° L'image de $J_1(V)$ par la projection source est $V$ tout entier;
> 2° $GU(n, \R)$ opère transitivement sur chaque fibre des jets de source donnée;
> 3° Comme dans le paragraphe 1, définition 2, appelons carte compatible, toute carte dont les jets
> appartiennent à $J_1$ : tout point de $V$ possède un voisinage dont il existe une carte compatible
> sur un cône ouvert de $\R^n$.
>
> **Prop. 1.** Soit $\{V_i\}$ un recouvrement d'une variété $V$ par un système d'ouverts; $f_i$ un
> système de cartes des $U_i$ sur des cônes ouverts de $\R^n$, tel que, si $U_i\cap U_j\neq\emptyset$,
> on ait, sur $U_i\cap U_j$, $f_i=g_{ij}\circ f_i$, avec $g_{ij}\in GU(n, \R)$. Alors il existe sur
> $V$ une structure conique affine, et une seule, avec laquelle les cartes $f_i$ soient compatibles.
>
> Sur une variété conique affine $V$, est canoniquement définie une structure de variété localement
> affine : c'est l'unique structure affine dont l'ensemble $J(V)$ des jets affins contienne
> $J_1(V)$. Les variétés coniques affines de dimension $n$ sont les objets d'une catégorie, dont les
> morphismes sont les applications $f$ de $V_1$ dans $V_2$ telles que $J_1(V_2)\circ f\subset
> J_1(V_1)$.
>
> **Déf. 3.** Le groupe $\R^+$ des réels positifs opère sur un cône affin $V$ de la façon suivante :
> soit $m\in V$; soit $U$ un voisinage de $m$ dont il existe une carte compatible $f$ sur un cône
> ouvert de $\R^n$; on pose $\lambda m=f^{-1}(\lambda f(m))$, où $\lambda\in\R^+$ opère sur $\R^n$
> comme une homothétie de centre $O$ et de rapport $\lambda$. Cette définition est indépendante de
> la carte $f$ choisie. $V$ est ainsi munie d'une structure d'espace fibré $\R^+$-principal : cet
> espace fibré est topologiquement trivial, puisque $\R^+$ est homéomorphe au segment ouvert, et
> nous en construirons plus loin une section. $\R^+$ opère sur $V$ comme un groupe d'automorphismes
> de sa structure localement affine (mais non de sa structure conique affine), que nous appellerons
> le groupe des homothéties positives de $V$.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `V` a « variété » of dimension `n` (plan F6: connected, Hausdorff, second countable) | Déf. 1, 2, Prop. 1, the affine structure, the category: none used. Déf. 3: **Hausdorff** (`[T2Space V]`) — reading of « variété », and necessary: without it « indépendante de la carte » fails (SCOPE) |
| « ensemble ouvert $J_1(V)$ de jets d'isomorphismes », 1°, 2° | ✓ carried: `IsJetStructure (GUR n)` (open in the étalé topology, `Structure/Jets`) |
| 3° « carte compatible » (« définition 2 », `[sic]`, read Déf. 13, DEC-113) | ✓ carried: all jets in `J₁`, equivalently in the maximal atlas |
| « cône ouvert de $\R^n$ » | ✓ carried: `IsOpenCone`, `IsConeSet` for subsets of `ℝⁿ − {O}` |
| Prop. 1: `f_i = g_ij ∘ f_j` on all of `U_i ∩ U_j` | generalised: near each point of `U_i ∩ U_j` suffices; the printed form is the corollary |
| `GU(n, ℝ)` commutes with the homotheties | ✓ proved (`SMulCommClass`), the reason Déf. 3 is well defined |
| `λ ∈ ℝ⁺` | `RPos = Units.posSubgroup ℝ`, as `glEquivProd` (`Projective/Groups`) |
| the affine structure: `GU(n) ⊆ GA(n)`, `ℝⁿ − {O} ⊆ ℝⁿ` | ✓ carried: `guToGA`, `Punctured.isOpenEmbedding_val`, `[NeZero n]` (the transport needs a nonempty model) |

## SCOPE (disclosed)

* **Hausdorffness is necessary for Déf. 3's « indépendante de la carte »** (a reading of « variété »,
  plan F6; question for the author, not a finding): on the half-line `]0, ∞[` with the point `1`
  doubled (`n = 1`, `GU(1) = {±1}`), the identity charts of the two copies are cone charts with
  identical transition, and `½ · 2` is `1` in one chart and `1'` in the other. This counterexample
  is described, not formalized.
* The action is a reducible `def` (`coneMulAction`), not an instance: the model `RnO n` cannot be
  inferred from `V`, so a `MulAction RPos V` instance has no synthesis order. Statements use
  `posSMul n c m`; `Cone/Base` uses `letI := coneMulAction n V` locally.
* **The objects of `ConeCat n` carry a proper `ℝ₊*`-action (DEC-122)**: `IsProperConeObject`
  (cone charts, Hausdorff, `ProperSMul` for Déf. 3's action), so that wave 4's base functor lands in
  Hausdorff locally projective manifolds (`ConeBase.existsUnique_baseStructure_of_properSMul`).
  `IsConeObject` (`HasConeCharts n V ∧ T2Space V`, Déf. 2 with « variété » Hausdorff) is kept and
  admits the non-Hausdorff bases of `Cone/Counterexample`; `IsProperConeObject.isConeObject`.
  Connectedness is not imposed (plan F6, carried where used).
* The canonical affine structure is stated for `[NeZero n]` (the strict library's transport assumes
  a nonempty model); for `n = 0`, `ℝ⁰ − {O}` is empty and so is every conical manifold.
* Instances added are on this file's own type `Punctured E` (actions of `E ≃ₗ[ℝ] E`, its subgroups
  and `RPos`, `IsAnalyticAction`, `Nonempty`); none on a Mathlib type. `connectedSpace_RPos` is a
  theorem, not an instance (`RPos` is a Mathlib type).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

universe u v

/-! ### `ℝⁿ − {O}` and the actions on it -/

section Punctured

variable (E : Type*) [AddCommGroup E]

/-- **`E − {O}`**, the model of the affine conical manifolds (`ℝⁿ − {O}`, Déf. 2). A type synonym
of `{v : E // v ≠ 0}` (the domain of `Sphere.s`), so that the actions below are not instances on a
Mathlib type. -/
def Punctured : Type _ := {v : E // v ≠ 0}

/-- `ℝⁿ − {O}`, `n = dim`. -/
abbrev RnO (n : ℕ) : Type := Punctured (Fin n → ℝ)

/-- The positive reals `ℝ₊*` (Benzécri's `ℝ⁺`), as the subgroup `Units.posSubgroup ℝ` of `ℝˣ`
(as in `Projective/Groups`, `glEquivProd`). -/
abbrev RPos : Type := Units.posSubgroup ℝ

namespace Punctured

variable {E}

/-- The underlying vector. -/
def val (v : Punctured E) : E := Subtype.val v

theorem val_ne_zero (v : Punctured E) : v.val ≠ 0 := Subtype.property v

/-- A nonzero vector as a point of `E − {O}`. -/
def mk (v : E) (hv : v ≠ 0) : Punctured E := ⟨v, hv⟩

@[simp] theorem val_mk (v : E) (hv : v ≠ 0) : (mk v hv).val = v := rfl

@[ext] theorem ext {v w : Punctured E} (h : v.val = w.val) : v = w := Subtype.ext h

theorem val_injective : Function.Injective (val : Punctured E → E) := fun _ _ h => ext h

/-- A point of `E − {O}` from the subtype `{v // v ≠ 0}` (the domain of `Sphere.s`). -/
def ofSubtype (v : {v : E // v ≠ 0}) : Punctured E := ⟨v.1, v.2⟩

/-- A point of `E − {O}` as an element of the subtype `{v // v ≠ 0}`. -/
def toSubtype (v : Punctured E) : {v : E // v ≠ 0} := ⟨v.val, v.val_ne_zero⟩

@[simp] theorem ofSubtype_toSubtype (v : Punctured E) : ofSubtype (toSubtype v) = v := rfl

@[simp] theorem toSubtype_ofSubtype (v : {v : E // v ≠ 0}) : toSubtype (ofSubtype v) = v := rfl

variable [Module ℝ E]

instance instNonempty [Nontrivial E] : Nonempty (Punctured E) :=
  let ⟨v, hv⟩ := exists_ne (0 : E); ⟨mk v hv⟩

/-- The linear automorphisms of `E` act on `E − {O}`. -/
instance instMulActionLin : MulAction (E ≃ₗ[ℝ] E) (Punctured E) where
  smul g v := ⟨g v.val, (LinearEquiv.map_ne_zero_iff g).2 v.val_ne_zero⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem val_smul_lin (g : E ≃ₗ[ℝ] E) (v : Punctured E) : (g • v).val = g v.val := rfl

@[simp] theorem val_smul_sub {H : Subgroup (E ≃ₗ[ℝ] E)} (g : H) (v : Punctured E) :
    (g • v).val = (g : E ≃ₗ[ℝ] E) v.val := rfl

/-- The positive reals act on `E − {O}` by the homotheties of centre `O`. -/
instance instMulActionPos : MulAction RPos (Punctured E) where
  smul c v := ⟨((c : ℝˣ) : ℝ) • v.val, smul_ne_zero (c : ℝˣ).ne_zero v.val_ne_zero⟩
  one_smul v := Subtype.ext (one_smul ℝ v.val)
  mul_smul a b v := Subtype.ext (mul_smul ((a : ℝˣ) : ℝ) ((b : ℝˣ) : ℝ) v.val)

@[simp] theorem val_smul_pos (c : RPos) (v : Punctured E) :
    (c • v).val = ((c : ℝˣ) : ℝ) • v.val := rfl

/-- **Linear automorphisms commute with the homotheties** (the reason Déf. 3 is well defined). -/
instance : SMulCommClass (E ≃ₗ[ℝ] E) RPos (Punctured E) :=
  ⟨fun g c v => ext (by simp)⟩

instance {H : Subgroup (E ≃ₗ[ℝ] E)} : SMulCommClass H RPos (Punctured E) :=
  ⟨fun g c v => ext (by simp)⟩

/-- The homothety of ratio `c` fixes a point only if `c = 1`: the action of `ℝ₊*` is free. -/
theorem eq_one_of_smul_pos_eq {c : RPos} {v : Punctured E} (h : c • v = v) : c = 1 := by
  have h1 : (((c : ℝˣ) : ℝ) - 1) • v.val = 0 := by
    rw [sub_smul, one_smul, sub_eq_zero]
    exact congrArg val h
  rcases smul_eq_zero.1 h1 with h2 | h2
  · exact Subtype.ext (Units.ext (by simpa [sub_eq_zero] using h2))
  · exact absurd h2 v.val_ne_zero

/-- The positive real `t` as an element of `ℝ₊*`. -/
def posUnit (t : ℝ) (ht : 0 < t) : RPos := ⟨Units.mk0 t ht.ne', ht⟩

@[simp] theorem coe_posUnit (t : ℝ) (ht : 0 < t) : (((posUnit t ht : RPos) : ℝˣ) : ℝ) = t := rfl

theorem pos (c : RPos) : (0 : ℝ) < ((c : ℝˣ) : ℝ) := c.2

section Topology

variable [TopologicalSpace E]

instance instTopologicalSpace : TopologicalSpace (Punctured E) := instTopologicalSpaceSubtype

omit [Module ℝ E] in
theorem continuous_val : Continuous (val : Punctured E → E) := continuous_subtype_val

omit [Module ℝ E] in
theorem isEmbedding_val : IsEmbedding (val : Punctured E → E) := IsEmbedding.subtypeVal

omit [Module ℝ E] in
theorem isOpenEmbedding_val [T1Space E] : IsOpenEmbedding (val : Punctured E → E) :=
  IsOpen.isOpenEmbedding_subtypeVal isOpen_ne

/-- `ℝ₊*` acts continuously on `E − {O}`. -/
instance [ContinuousSMul ℝ E] : ContinuousSMul RPos (Punctured E) := by
  refine ⟨?_⟩
  refine continuous_induced_rng.2 ?_
  exact ((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).smul
    (continuous_val.comp continuous_snd)

instance [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E] :
    ContinuousConstSMul (E ≃ₗ[ℝ] E) (Punctured E) :=
  ⟨fun g => continuous_induced_rng.2
    ((LinearMap.continuous_of_finiteDimensional (g : E →ₗ[ℝ] E)).comp continuous_val)⟩

instance [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]
    {H : Subgroup (E ≃ₗ[ℝ] E)} : ContinuousConstSMul H (Punctured E) :=
  ⟨fun g => continuous_const_smul (g : E ≃ₗ[ℝ] E)⟩

end Topology

end Punctured

/-- **`ℝ₊*` is connected** (it is homeomorphic to `]0, ∞[` by the coercion). -/
theorem isPreconnected_univ_RPos : IsPreconnected (univ : Set RPos) := by
  have hemb : IsInducing (fun c : RPos => ((c : ℝˣ) : ℝ)) :=
    (Units.isEmbedding_val₀.comp IsEmbedding.subtypeVal).isInducing
  rw [← hemb.isPreconnected_image, image_univ]
  have : range (fun c : RPos => ((c : ℝˣ) : ℝ)) = Ioi 0 := by
    ext t
    refine ⟨?_, fun ht => ⟨Punctured.posUnit t ht, rfl⟩⟩
    rintro ⟨c, rfl⟩
    exact Punctured.pos c
  rw [this]
  exact isPreconnected_Ioi

/-- `ℝ₊*` is a connected space (a theorem, not an instance: `RPos` is a Mathlib type). -/
theorem connectedSpace_RPos : ConnectedSpace RPos where
  toPreconnectedSpace := ⟨isPreconnected_univ_RPos⟩
  toNonempty := ⟨1⟩

end Punctured

/-! ### Déf. 1 — open cones -/

section Def1

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The open half-line issued from the origin through `v` (« demi-droite ouverte issue de
l'origine »). -/
def halfLine (v : E) : Set E := {w | ∃ t : ℝ, 0 < t ∧ w = t • v}

theorem mem_halfLine_self (v : E) : v ∈ halfLine v := ⟨1, one_pos, (one_smul ℝ v).symm⟩

variable [TopologicalSpace E]

/-- **Déf. 1** (`bzdef:c1s2d1_cone_ouvert`): an *open cone* of `E` — an open part of `E − {O}`
which is a union of open half-lines issued from the origin, i.e. stable under the positive
homotheties (`isOpenCone_iff_iUnion_halfLine` is the printed form). -/
def IsOpenCone (C : Set E) : Prop :=
  IsOpen C ∧ (0 : E) ∉ C ∧ ∀ v ∈ C, ∀ t : ℝ, 0 < t → t • v ∈ C

/-- **Déf. 1 as printed**: « une partie ouverte de $\R^n-\{O\}$, réunion de demi-droites ouvertes
issues de l'origine ». -/
theorem isOpenCone_iff_iUnion_halfLine {C : Set E} :
    IsOpenCone C ↔ IsOpen C ∧ C ⊆ {0}ᶜ ∧ ∃ D : Set E, C = ⋃ v ∈ D, halfLine v := by
  constructor
  · rintro ⟨hO, h0, hC⟩
    refine ⟨hO, fun v hv (h : v = 0) => h0 (h ▸ hv), C, ?_⟩
    ext w
    simp only [mem_iUnion, exists_prop]
    refine ⟨fun hw => ⟨w, hw, mem_halfLine_self w⟩, ?_⟩
    rintro ⟨v, hv, t, ht, rfl⟩
    exact hC v hv t ht
  · rintro ⟨hO, h0, D, rfl⟩
    refine ⟨hO, fun h => h0 h rfl, ?_⟩
    intro w hw t ht
    simp only [mem_iUnion, exists_prop] at hw ⊢
    obtain ⟨v, hv, s, hs, rfl⟩ := hw
    exact ⟨v, hv, t * s, mul_pos ht hs, by rw [smul_smul]⟩

/-- **Open cones are the `F(A)` of the open sets `A` of `S(E)`** (`Sphere.F`, Déf. 3 of § 1), the
bridge to the base `S(n−1)` of § 2. -/
theorem isOpenCone_iff_exists_F [T1Space E] {C : Set E} :
    IsOpenCone C ↔ ∃ A : Set (Sphere E), IsOpen A ∧ C = Sphere.F A := by
  constructor
  · rintro ⟨hO, h0, hC⟩
    have hC' : ∀ c : ℝ, 0 < c → ∀ v ∈ C, c • v ∈ C := fun c hc v hv => hC v hv c hc
    have hF : Sphere.F (Sphere.ofCone C) = C := by
      rw [Sphere.F_ofCone hC', sdiff_singleton_eq_self h0]
    refine ⟨Sphere.ofCone C, ?_, hF.symm⟩
    rw [Sphere.isOpen_iff_F, hF]
    exact hO
  · rintro ⟨A, hA, rfl⟩
    exact ⟨Sphere.isOpen_iff_F.1 hA, Sphere.zero_notMem_F A,
      fun v hv t ht => Sphere.smul_mem_F hv ht⟩

/-- An open cone, as a subset of `E − {O}`: open, and stable under `ℝ₊*`. -/
def IsConeSet (T : Set (Punctured E)) : Prop :=
  IsOpen T ∧ ∀ c : RPos, ∀ v ∈ T, c • v ∈ T

/-- A subset of `E − {O}` is a cone set iff its image in `E` is an open cone (Déf. 1). -/
theorem isConeSet_iff [T1Space E] {T : Set (Punctured E)} :
    IsConeSet T ↔ IsOpenCone (Punctured.val '' T) := by
  constructor
  · rintro ⟨hO, hT⟩
    refine ⟨Punctured.isOpenEmbedding_val.isOpenMap _ hO, fun ⟨v, _, hv⟩ => v.val_ne_zero hv, ?_⟩
    rintro _ ⟨v, hv, rfl⟩ t ht
    exact ⟨Punctured.posUnit t ht • v, hT _ v hv, rfl⟩
  · rintro ⟨hO, -, hT⟩
    refine ⟨?_, fun c v hv => ?_⟩
    · have : T = Punctured.val ⁻¹' (Punctured.val '' T) :=
        (Punctured.val_injective.preimage_image T).symm
      rw [this]
      exact hO.preimage Punctured.continuous_val
    · obtain ⟨w, hw, hwv⟩ := hT _ ⟨v, hv, rfl⟩ _ (Punctured.pos c)
      rwa [← Punctured.val_injective (hwv.trans (Punctured.val_smul_pos c v).symm)]

/-- The image of a cone set by a (continuous) linear automorphism is a cone set. -/
theorem IsConeSet.image_smul [ContinuousConstSMul (E ≃ₗ[ℝ] E) (Punctured E)] {T : Set (Punctured E)}
    (hT : IsConeSet T) (g : E ≃ₗ[ℝ] E) : IsConeSet ((g • ·) '' T) := by
  refine ⟨isOpenMap_smul g _ hT.1, ?_⟩
  rintro c _ ⟨v, hv, rfl⟩
  exact ⟨c • v, hT.2 c v hv, smul_comm g c v⟩

end Def1

/-! ### Rigidity of the linear action on `E − {O}` -/

section Rigidity

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E] [T1Space E]

/-- A linear map agreeing with `c • id` on a nonempty open set of `E − {O}` is `c • id`. -/
theorem eq_smul_of_eqOn_punctured (g : E →ₗ[ℝ] E) (c : ℝ) {U : Set (Punctured E)} (hU : IsOpen U)
    (hne : U.Nonempty) (h : ∀ v ∈ U, g v.val = c • v.val) : ∀ y, g y = c • y := by
  obtain ⟨x, hx⟩ := hne
  have hO : IsOpen (Punctured.val '' U) := Punctured.isOpenEmbedding_val.isOpenMap _ hU
  obtain ⟨c', hc', hall⟩ := exists_forall_eq_smul_of_isOpen g hO ⟨x, hx, rfl⟩ x.val_ne_zero
    (by rintro _ ⟨v, hv, rfl⟩; exact ⟨c, h v hv⟩)
  have : c' = c := by
    have h1 := (h x hx).symm.trans hc'
    have h2 : (c - c') • x.val = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · linarith [sub_eq_zero.1 h3]
    · exact absurd h3 x.val_ne_zero
  rw [← this]
  exact hall

/-- **The action of `GL(E)` on `E − {O}` is analytic** (faithful and rigid): two automorphisms
agreeing on a nonempty open set are equal. -/
instance : IsAnalyticAction (E ≃ₗ[ℝ] E) (Punctured E) where
  eq_of_smul_eq_smul {g h} hgh := by
    ext y
    by_cases hy : y = 0
    · simp [hy]
    · exact congrArg Punctured.val (hgh (Punctured.mk y hy))
  smul_eq_of_eqOn {g h U} hU hne heq p := by
    have key := eq_smul_of_eqOn_punctured ((g.trans h.symm : E ≃ₗ[ℝ] E) : E →ₗ[ℝ] E) 1 hU hne
      (fun v hv => by
        have := congrArg Punctured.val (heq hv)
        simp only [Punctured.val_smul_lin] at this
        simp [this])
    ext
    have := key p.val
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, one_smul] at this
    simp only [Punctured.val_smul_lin]
    rw [← h.apply_symm_apply (g p.val), this]

/-- The action of a subgroup of `GL(E)` on `E − {O}` is analytic (e.g. `GU(n)`). -/
instance {H : Subgroup (E ≃ₗ[ℝ] E)} : IsAnalyticAction H (Punctured E) where
  eq_of_smul_eq_smul h := Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (α := Punctured E) h)
  smul_eq_of_eqOn hU hne heq p := IsRigidAction.smul_eq_of_eqOn (G := E ≃ₗ[ℝ] E) hU hne heq p

end Rigidity

/-! ### The projection `ℝⁿ − {O} → S(n−1)` -/

section ToSphere

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace Punctured

/-- The canonical projection `s : E − {O} → S(E)` (§ 1, Déf. 3), on `Punctured E`. -/
def toSphere (v : Punctured E) : Sphere E := Sphere.mk v.val v.val_ne_zero

theorem toSphere_eq_s (v : Punctured E) : toSphere v = Sphere.s v := rfl

@[simp] theorem toSphere_smul_pos (c : RPos) (v : Punctured E) : toSphere (c • v) = toSphere v :=
  Sphere.mk_smul _ (pos c) _

theorem toSphere_smul_lin (g : E ≃ₗ[ℝ] E) (v : Punctured E) : toSphere (g • v) = g • toSphere v :=
  rfl

theorem toSphere_surjective : Function.Surjective (toSphere : Punctured E → Sphere E) :=
  Sphere.s_surjective

/-- `s(v) = s(w)` iff `w = λ v` for some `λ > 0`. -/
theorem toSphere_eq_toSphere_iff {v w : Punctured E} :
    toSphere v = toSphere w ↔ ∃ c : RPos, c • v = w := by
  constructor
  · intro h
    obtain ⟨r, hr, hrv⟩ := (Sphere.mk_eq_mk_iff_exists_pos v.val_ne_zero w.val_ne_zero).1 h
    exact ⟨posUnit r hr, ext (by simpa using hrv)⟩
  · rintro ⟨c, rfl⟩
    exact (toSphere_smul_pos c v).symm

variable [TopologicalSpace E]

theorem continuous_toSphere : Continuous (toSphere : Punctured E → Sphere E) :=
  Sphere.continuous_s

theorem isOpenQuotientMap_toSphere [ContinuousConstSMul ℝ E] :
    IsOpenQuotientMap (toSphere : Punctured E → Sphere E) :=
  ⟨toSphere_surjective, continuous_toSphere, Sphere.isOpenMap_s⟩

end Punctured

end ToSphere

/-! ### Déf. 2 — affine conical manifolds -/

variable (n : ℕ)

/-- **The groupoid of affine conical `n`-manifolds**: `gxGroupoid (GU(n, ℝ)) (ℝⁿ − {O})`. -/
abbrev coneGroupoid : StructureGroupoid (RnO n) := gxGroupoid (GUR n) (RnO n)

section Def2

variable {V : Type u} [TopologicalSpace V]

section Jets

/-- **Déf. 2 in the paper's form** (`bzdef:c1s2d2_variete_conique_affine`): `J₁` is a set of conical
affine jets — an open set of jets of isomorphisms of `V` into `ℝⁿ − {O}` with 1° (every point is a
source) and 2° (`GU(n, ℝ)` operates transitively on each fibre), which is `IsJetStructure`, and
3° every point has a neighbourhood with a compatible chart (all jets in `J₁`, « comme dans le
paragraphe 1, définition 2 » `[sic]`, read Déf. 13, DEC-113) onto an open cone. -/
structure IsConeJetStructure (J : Set (Jet V (RnO n))) : Prop extends IsJetStructure (GUR n) J where
  /-- 3° « tout point de $V$ possède un voisinage dont il existe une carte compatible sur un cône
  ouvert de $\R^n$ ». -/
  exists_cone : ∀ x : V, ∃ e : OpenPartialHomeomorph V (RnO n), x ∈ e.source ∧
    IsConeSet e.target ∧ ∀ y ∈ e.source, jet y e ∈ J

end Jets

variable [ChartedSpace (RnO n) V]

/-- A **cone chart**: a compatible chart (Déf. 13: in the maximal atlas) onto an open cone. -/
def IsConeChart (e : OpenPartialHomeomorph V (RnO n)) : Prop :=
  e ∈ (coneGroupoid n).maximalAtlas V ∧ IsConeSet e.target

variable (V) in
/-- **Déf. 2, 3°, in atlas form**: every point has a neighbourhood with a compatible chart onto an
open cone. An affine conical `n`-manifold is `[ChartedSpace (RnO n) V]
[HasGroupoid V (coneGroupoid n)] [HasConeCharts n V]` (`def2_iff` is the equivalence with
`IsConeJetStructure`). -/
class HasConeCharts : Prop where
  exists_isConeChart : ∀ x : V, ∃ e : OpenPartialHomeomorph V (RnO n), IsConeChart n e ∧ x ∈ e.source

end Def2

section Def2Iff

variable {V : Type u} [TopologicalSpace V]

/-- **Déf. 2 is equivalent to the atlas definition**: a set `J₁` of jets of `V` into `ℝⁿ − {O}` is the
set of jets of a `(GU(n), ℝⁿ − {O})`-structure with cone charts (`HasConeCharts`) iff it satisfies
Déf. 2 (open, 1°, 2°, 3°). -/
theorem def2_iff (J : Set (Jet V (RnO n))) :
    (∃ cs : ChartedSpace (RnO n) V, ∃ _ : @HasGroupoid _ _ V _ cs (coneGroupoid n),
      @HasConeCharts n V _ cs ∧ @jets (GUR n) (RnO n) V _ _ _ _ _ cs = J) ↔
      IsConeJetStructure n J := by
  constructor
  · rintro ⟨cs, hcs, hcc, rfl⟩
    refine ⟨(exists_hasGroupoid_jets_eq_iff (G := GUR n) _).1 ⟨cs, hcs, rfl⟩, fun x => ?_⟩
    obtain ⟨e, ⟨he, hT⟩, hx⟩ := hcc.exists_isConeChart x
    exact ⟨e, hx, hT, fun y hy => @jet_mem_jets V _ _ _ (GUR n) _ _ _ cs e he y hy⟩
  · intro hJ
    obtain ⟨cs, hcs, hJ'⟩ := (exists_hasGroupoid_jets_eq_iff (G := GUR n) J).2 hJ.toIsJetStructure
    refine ⟨cs, hcs, ⟨fun x => ?_⟩, hJ'⟩
    obtain ⟨e, hx, hT, he⟩ := hJ.exists_cone x
    refine ⟨e, ⟨?_, hT⟩, hx⟩
    rw [@mem_maximalAtlas_iff_jets V _ _ _ (GUR n) _ _ _ cs hcs, hJ']
    exact he

end Def2Iff

/-! ### Prop. 1 of § 2 — conical atlases -/

section Prop1

variable {V : Type u} [TopologicalSpace V]

/-- **Prop. 1 of § 2** (`bzprop:c1s2p1_atlas_conique`), strongest form: charts `f_i` of a cover of
`V` onto open cones, with transitions locally in `GU(n, ℝ)`, define an affine conical structure for
which every `f_i` is compatible, and it is the only one (indeed the only
`(GU(n), ℝⁿ − {O})`-structure for which every `f_i` is compatible). -/
theorem existsUnique_coneStructure_of_atlas {ι : Type*} (f : ι → OpenPartialHomeomorph V (RnO n))
    (hcov : ∀ x, ∃ i, x ∈ (f i).source) (hcone : ∀ i, IsConeSet (f i).target)
    (htrans : ∀ i j, ∀ x ∈ (f i).source ∩ (f j).source, ∃ g : GUR n,
      ∀ᶠ z in 𝓝 x, f i z = g • f j z) :
    ∃ cs : ChartedSpace (RnO n) V, ∃ _ : @HasGroupoid _ _ V _ cs (coneGroupoid n),
      @HasConeCharts n V _ cs ∧
      (∀ i, f i ∈ @StructureGroupoid.maximalAtlas _ V _ _ cs (coneGroupoid n)) ∧
      ∀ cs' : ChartedSpace (RnO n) V, @HasGroupoid _ _ V _ cs' (coneGroupoid n) →
        (∀ i, f i ∈ @StructureGroupoid.maximalAtlas _ V _ _ cs' (coneGroupoid n)) →
        @StructureGroupoid.maximalAtlas _ V _ _ cs' (coneGroupoid n) =
          @StructureGroupoid.maximalAtlas _ V _ _ cs (coneGroupoid n) := by
  obtain ⟨cs, hcs, hf, huniq⟩ := existsUnique_structure_of_atlas (G := GUR n) f hcov htrans
  refine ⟨cs, hcs, ⟨fun x => ?_⟩, hf, huniq⟩
  obtain ⟨i, hi⟩ := hcov x
  exact ⟨f i, ⟨hf i, hcone i⟩, hi⟩

/-- **Prop. 1 of § 2 as printed** (`{V_i}` read `{U_i}`, `f_i = g_ij ∘ f_i` read `f_i = g_ij ∘ f_j`,
the transcription's `[sic]`): if, whenever `U_i ∩ U_j ≠ ∅`, `f_i = g_ij ∘ f_j` on `U_i ∩ U_j` with
`g_ij ∈ GU(n, ℝ)`, there is a unique affine conical structure with which the `f_i` are compatible. -/
theorem existsUnique_coneStructure_of_atlas_printed {ι : Type*}
    (f : ι → OpenPartialHomeomorph V (RnO n)) (hcov : ∀ x, ∃ i, x ∈ (f i).source)
    (hcone : ∀ i, IsConeSet (f i).target)
    (htrans : ∀ i j, ((f i).source ∩ (f j).source).Nonempty →
      ∃ g : GUR n, ∀ x ∈ (f i).source ∩ (f j).source, f i x = g • f j x) :
    ∃ cs : ChartedSpace (RnO n) V, ∃ _ : @HasGroupoid _ _ V _ cs (coneGroupoid n),
      @HasConeCharts n V _ cs ∧
      (∀ i, @IsCompatibleChart V _ _ _ (GUR n) _ _ _ cs (f i)) ∧
      ∀ cs' : ChartedSpace (RnO n) V, @HasGroupoid _ _ V _ cs' (coneGroupoid n) →
        @HasConeCharts n V _ cs' →
        (∀ i, @IsCompatibleChart V _ _ _ (GUR n) _ _ _ cs' (f i)) →
        @StructureGroupoid.maximalAtlas _ V _ _ cs' (coneGroupoid n) =
          @StructureGroupoid.maximalAtlas _ V _ _ cs (coneGroupoid n) := by
  obtain ⟨cs, hcs, hf, huniq⟩ := existsUnique_structure_of_atlas_printed (G := GUR n) f hcov htrans
  refine ⟨cs, hcs, ⟨fun x => ?_⟩, hf, fun cs' hcs' _ hf' => huniq cs' hcs' hf'⟩
  obtain ⟨i, hi⟩ := hcov x
  exact ⟨f i, ⟨(@isCompatibleChart_iff V _ _ _ (GUR n) _ _ _ cs hcs _).1 (hf i), hcone i⟩, hi⟩

end Prop1

/-! ### Two structures sharing a covering family of charts are equal -/

section Cover

variable {M : Type u} [TopologicalSpace M] {X : Type v} [TopologicalSpace X] {G : Type*} [Group G]
  [MulAction G X] [ContinuousConstSMul G X]

/-- Two `(G,X)`-structures on `M` whose maximal atlases share a family of charts covering `M` have
the same maximal atlas (the uniqueness argument of Prop. 3, as a lemma). -/
theorem maximalAtlas_eq_of_common_cover (cs cs' : ChartedSpace X M)
    [h : @HasGroupoid X _ M _ cs (gxGroupoid G X)] [h' : @HasGroupoid X _ M _ cs' (gxGroupoid G X)]
    {ι : Type*} (f : ι → OpenPartialHomeomorph M X) (hcov : ∀ x, ∃ i, x ∈ (f i).source)
    (hf : ∀ i, f i ∈ @StructureGroupoid.maximalAtlas X M _ _ cs (gxGroupoid G X))
    (hf' : ∀ i, f i ∈ @StructureGroupoid.maximalAtlas X M _ _ cs' (gxGroupoid G X)) :
    @StructureGroupoid.maximalAtlas X M _ _ cs (gxGroupoid G X) =
      @StructureGroupoid.maximalAtlas X M _ _ cs' (gxGroupoid G X) := by
  ext e
  rw [@mem_maximalAtlas_iff_eventually_of_cover G X _ _ _ _ M _ cs h ι f hf hcov e,
    @mem_maximalAtlas_iff_eventually_of_cover G X _ _ _ _ M _ cs' h' ι f hf' hcov e]

end Cover

/-! ### The canonical locally affine structure of an affine conical manifold -/

section Affine

/-- `GU(n, ℝ) ⊆ GL(n, ℝ) ⊆ GA(n, ℝ)`: a unimodular automorphism as an affine automorphism. -/
def guToGA : GUR n →* GAR n where
  toFun g := (g : GLR n).toAffineEquiv
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[simp] theorem guToGA_apply (g : GUR n) (y : Fin n → ℝ) : guToGA n g y = (g : GLR n) y := rfl

/-- The inclusion `ℝⁿ − {O} ⊆ ℝⁿ` is equivariant through `GU(n) → GA(n)`. -/
theorem val_smul_guToGA (g : GUR n) (v : RnO n) :
    Punctured.val (g • v) = guToGA n g • Punctured.val v := rfl

variable [NeZero n] {V : Type u} [TopologicalSpace V] [ChartedSpace (RnO n) V]
  [HasGroupoid V (coneGroupoid n)]

variable (V) in
/-- **The canonical affine charted space** of an affine conical manifold: the charts are the
`ι ∘ e`, `ι : ℝⁿ − {O} → ℝⁿ` the inclusion (`transportChartedSpace`). -/
abbrev affineChartedSpace : ChartedSpace (Fin n → ℝ) V :=
  transportChartedSpace (Punctured.isOpenEmbedding_val (E := Fin n → ℝ)) V

/-- **« Sur une variété conique affine $V$, est canoniquement définie une structure de variété
localement affine »**: the charts `ι ∘ e` form a locally affine structure. -/
theorem hasGroupoid_affineChartedSpace :
    @HasGroupoid _ _ V _ (affineChartedSpace n V) (affGroupoid n) :=
  hasGroupoid_transport _ (guToGA n) (val_smul_guToGA n)

/-- Every compatible conical chart `e`, composed with `ι`, is a compatible affine chart: the
affine jets contain `ι ∘ J₁(V)`. -/
theorem trans_mem_maximalAtlas_affine {e : OpenPartialHomeomorph V (RnO n)}
    (he : e ∈ (coneGroupoid n).maximalAtlas V) :
    e.trans ((Punctured.isOpenEmbedding_val (E := Fin n → ℝ)).toOpenPartialHomeomorph _) ∈
      @StructureGroupoid.maximalAtlas _ V _ _ (affineChartedSpace n V) (affGroupoid n) :=
  trans_mem_maximalAtlas_transport _ (guToGA n) (val_smul_guToGA n) he

/-- The jet `ι ∘ j` of a jet `j` of `V` into `ℝⁿ − {O}`. -/
def jetVal (j : Jet V (RnO n)) : Jet V (Fin n → ℝ) := ⟨j.1, j.2.map Punctured.val⟩

/-- **The canonical affine structure contains `J₁(V)`**: `ι ∘ j ∈ J(V)` for every `j ∈ J₁(V)`. -/
theorem jetVal_mem_jets_affine {j : Jet V (RnO n)} (hj : j ∈ jets (GUR n) (RnO n) V) :
    jetVal n j ∈ @jets (GAR n) (Fin n → ℝ) V _ _ _ _ _ (affineChartedSpace n V) := by
  obtain ⟨x, γ⟩ := j
  obtain ⟨e, he, hx, hγ⟩ := hj
  simp only at hx hγ
  subst hγ
  refine ⟨_, trans_mem_maximalAtlas_affine n he, ?_, ?_⟩
  · simp only [jetVal, OpenPartialHomeomorph.trans_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
    exact hx
  · simp only [jetVal, Germ.map_coe]
    rfl

/-- **« c'est l'unique structure affine dont l'ensemble $J(V)$ des jets affins contienne
$J_1(V)$ »**: any locally affine structure on `V` whose jets contain `ι ∘ J₁(V)` has the maximal
atlas of the canonical one. -/
theorem maximalAtlas_affine_unique (cs : ChartedSpace (Fin n → ℝ) V)
    [hcs : @HasGroupoid _ _ V _ cs (affGroupoid n)]
    (h : ∀ j ∈ jets (GUR n) (RnO n) V, jetVal n j ∈ @jets (GAR n) (Fin n → ℝ) V _ _ _ _ _ cs) :
    @StructureGroupoid.maximalAtlas _ V _ _ cs (affGroupoid n) =
      @StructureGroupoid.maximalAtlas _ V _ _ (affineChartedSpace n V) (affGroupoid n) := by
  haveI := hasGroupoid_affineChartedSpace n (V := V)
  set ι := (Punctured.isOpenEmbedding_val (E := Fin n → ℝ)).toOpenPartialHomeomorph
    (Punctured.val : RnO n → Fin n → ℝ)
  let f : (coneGroupoid n).maximalAtlas V → OpenPartialHomeomorph V (Fin n → ℝ) :=
    fun e => (e : OpenPartialHomeomorph V (RnO n)).trans ι
  have hsrc : ∀ e : OpenPartialHomeomorph V (RnO n), (e.trans ι).source = e.source := by
    intro e
    rw [OpenPartialHomeomorph.trans_source]
    have : ι.source = univ := IsOpenEmbedding.toOpenPartialHomeomorph_source _ _
    rw [this, preimage_univ, inter_univ]
  refine maximalAtlas_eq_of_common_cover (G := GAR n) cs (affineChartedSpace n V) f
    (fun x => ⟨⟨chartAt _ x, (coneGroupoid n).chart_mem_maximalAtlas x⟩,
      by simp only [f, hsrc]; exact mem_chart_source _ x⟩) (fun e => ?_)
    (fun e => trans_mem_maximalAtlas_affine n e.2)
  rw [@mem_maximalAtlas_iff_jets V _ _ _ (GAR n) _ _ _ cs hcs]
  intro x hx
  have hx' : x ∈ (e : OpenPartialHomeomorph V (RnO n)).source := by
    simpa only [f, hsrc] using hx
  have := h _ (jet_mem_jets e.2 hx')
  simp only [jetVal, jet, Germ.map_coe] at this
  change jet x (Punctured.val ∘ (e : OpenPartialHomeomorph V (RnO n))) ∈ _
  exact this

end Affine

/-! ### A morphism criterion through arbitrary charts of the maximal atlases -/

section MorphismCriterion

variable {G : Type*} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]
  [ChartedSpace X M] [ChartedSpace X N] [HasGroupoid M (gxGroupoid G X)]
  [HasGroupoid N (gxGroupoid G X)]

/-- A continuous map which, near every point, reads as an element of `G` in SOME charts of the
maximal atlases, is a morphism (the converse of `IsGXMorphism.exists_smul_eq_of_mem_maximalAtlas`). -/
theorem isGXMorphism_of_mem_maximalAtlas {f : M → N} (hf : Continuous f)
    (h : ∀ x, ∃ e ∈ (gxGroupoid G X).maximalAtlas M, ∃ e' ∈ (gxGroupoid G X).maximalAtlas N,
      x ∈ e.source ∧ f x ∈ e'.source ∧ ∃ g : G, ∀ᶠ y in 𝓝 x, e' (f y) = g • e y) :
    IsGXMorphism G X f := by
  refine ⟨hf, fun x => ?_⟩
  obtain ⟨e, he, e', he', hx, hfx, g, hg⟩ := h x
  obtain ⟨a, ha⟩ := eventually_smul_eq_of_mem_maximalAtlas he'
    ((gxGroupoid G X).chart_mem_maximalAtlas (f x)) hfx (mem_chart_source X (f x))
  obtain ⟨b, hb⟩ := eventually_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid G X).chart_mem_maximalAtlas x) he (mem_chart_source X x) hx
  refine ⟨a * g * b, ?_⟩
  filter_upwards [hf.continuousAt.eventually ha, hg, hb] with y h1 h2 h3
  rw [h1, h2, h3, mul_smul, mul_smul]

end MorphismCriterion

/-! ### Déf. 3 — the positive homotheties of an affine conical manifold -/

section Def3

variable {n} {V : Type u} [TopologicalSpace V] [ChartedSpace (RnO n) V]

namespace IsConeChart

variable {e : OpenPartialHomeomorph V (RnO n)}

theorem smul_mem_target (he : IsConeChart n e) {v : RnO n} (hv : v ∈ e.target) (c : RPos) :
    c • v ∈ e.target :=
  he.2.2 c v hv

theorem symm_smul_mem_source (he : IsConeChart n e) {m : V} (hm : m ∈ e.source) (c : RPos) :
    e.symm (c • e m) ∈ e.source :=
  e.map_target (he.smul_mem_target (e.map_source hm) c)

theorem apply_symm_smul (he : IsConeChart n e) {m : V} (hm : m ∈ e.source) (c : RPos) :
    e (e.symm (c • e m)) = c • e m :=
  e.right_inv (he.smul_mem_target (e.map_source hm) c)

/-- Along a cone chart, `λ ↦ f⁻¹(λ f(m))` is continuous. -/
theorem continuous_symm_smul (he : IsConeChart n e) {m : V} (hm : m ∈ e.source) :
    Continuous fun c : RPos => e.symm (c • e m) :=
  e.continuousOn_symm.comp_continuous (continuous_id.smul continuous_const)
    fun c => he.smul_mem_target (e.map_source hm) c

/-- **« Cette définition est indépendante de la carte $f$ choisie »** (Déf. 3), for `V` Hausdorff:
two compatible charts `f, f'` of neighbourhoods of `m` onto open cones give the same
`f⁻¹(λ f(m)) = f'⁻¹(λ f'(m))`. The proof: the two curves `λ ↦ f⁻¹(λ f(m))`, `λ ↦ f'⁻¹(λ f'(m))`
agree at `λ = 1`, the set where they agree is closed (`V` Hausdorff) and open (near a common point,
`f' = g ∘ f` with `g ∈ GU(n)` linear, which commutes with the homotheties), and `ℝ₊*` is connected.
Hausdorffness is necessary (SCOPE). -/
theorem symm_smul_eq [T2Space V] {e' : OpenPartialHomeomorph V (RnO n)} (he : IsConeChart n e)
    (he' : IsConeChart n e') {m : V} (hm : m ∈ e.source) (hm' : m ∈ e'.source) (c : RPos) :
    e.symm (c • e m) = e'.symm (c • e' m) := by
  haveI := connectedSpace_RPos
  set γ : RPos → V := fun c => e.symm (c • e m) with hγdef
  set γ' : RPos → V := fun c => e'.symm (c • e' m) with hγ'def
  have hγ : Continuous γ := he.continuous_symm_smul hm
  have hγ' : Continuous γ' := he'.continuous_symm_smul hm'
  have hS : IsClopen {c | γ c = γ' c} := by
    refine ⟨isClosed_eq hγ hγ', isOpen_iff_mem_nhds.2 fun c₀ hc₀ => ?_⟩
    have hc₀ : γ c₀ = γ' c₀ := hc₀
    have hp : γ c₀ ∈ e.source := he.symm_smul_mem_source hm c₀
    have hp' : γ c₀ ∈ e'.source := by rw [hc₀]; exact he'.symm_smul_mem_source hm' c₀
    obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas he.1 he'.1 hp hp'
    have hge : g • e m = e' m := by
      have h1 : e' (γ c₀) = g • e (γ c₀) := hg.self_of_nhds
      have h2 : e' (γ c₀) = c₀ • e' m := by rw [hc₀]; exact he'.apply_symm_smul hm' c₀
      rw [show e (γ c₀) = c₀ • e m from he.apply_symm_smul hm c₀, h2, smul_comm] at h1
      exact (MulAction.injective c₀ h1).symm
    filter_upwards [(hγ.tendsto c₀).eventually (hg.and (e'.open_source.mem_nhds hp'))] with c hc
    show γ c = γ' c
    have h3 : e' (γ c) = c • e' m := by
      rw [hc.1, show e (γ c) = c • e m from he.apply_symm_smul hm c, smul_comm, hge]
    calc γ c = e'.symm (e' (γ c)) := (e'.left_inv hc.2).symm
      _ = γ' c := by rw [h3]
  have h1 : (1 : RPos) ∈ {c | γ c = γ' c} := by
    show e.symm ((1 : RPos) • e m) = e'.symm ((1 : RPos) • e' m)
    rw [one_smul, one_smul, e.left_inv hm, e'.left_inv hm']
  have := hS.eq_univ ⟨1, h1⟩
  have hc : c ∈ {c | γ c = γ' c} := by rw [this]; trivial
  exact hc

end IsConeChart

/-- A cone chart followed by an element of `GU(n)` is a cone chart. -/
theorem IsConeChart.transHomeomorph_smul [HasGroupoid V (coneGroupoid n)]
    {e : OpenPartialHomeomorph V (RnO n)} (he : IsConeChart n e) (g : GUR n) :
    IsConeChart n (e.transHomeomorph (Homeomorph.smul g)) := by
  refine ⟨transHomeomorph_smul_mem_maximalAtlas he.1 g, (e.transHomeomorph _).open_target,
    fun c v hv => ?_⟩
  simp only [OpenPartialHomeomorph.transHomeomorph_target, mem_preimage, Homeomorph.smul_symm_apply]
    at hv ⊢
  rw [smul_comm]
  exact he.2.2 c _ hv

/-- **Every jet of `J₁(V)` is the jet of a cone chart** (Déf. 2: 2° and 3°): `GU(n)` maps cone charts
to cone charts and acts transitively on the fibres. -/
theorem exists_isConeChart_jet_eq [HasGroupoid V (coneGroupoid n)] [HasConeCharts n V] {x : V}
    {γ : Germ (𝓝 x) (RnO n)} (hj : (⟨x, γ⟩ : Jet V (RnO n)) ∈ jets (GUR n) (RnO n) V) :
    ∃ e : OpenPartialHomeomorph V (RnO n), IsConeChart n e ∧ x ∈ e.source ∧
      γ = ((e : V → RnO n) : Germ (𝓝 x) (RnO n)) := by
  obtain ⟨e₀, he₀, hx⟩ := HasConeCharts.exists_isConeChart (n := n) x
  obtain ⟨g, hg⟩ := (isJetStructure_jets (G := GUR n) (X := RnO n) (M := V)).transitive x _ γ
    (jet_mem_jets he₀.1 hx) hj
  refine ⟨_, he₀.transHomeomorph_smul g, hx, ?_⟩
  rw [hg, Germ.map_coe]
  rfl

variable [HasConeCharts n V]

variable (n) in
/-- A cone chart at `x`, chosen (Déf. 2, 3°). -/
def coneChartAt (x : V) : OpenPartialHomeomorph V (RnO n) :=
  (HasConeCharts.exists_isConeChart (n := n) x).choose

theorem isConeChart_coneChartAt (x : V) : IsConeChart n (coneChartAt n x) :=
  (HasConeCharts.exists_isConeChart (n := n) x).choose_spec.1

theorem mem_coneChartAt_source (x : V) : x ∈ (coneChartAt n x).source :=
  (HasConeCharts.exists_isConeChart (n := n) x).choose_spec.2

variable (n) in
/-- **Déf. 3** (`bzdef:c1s2d3_homotheties_positives`): the action of `λ ∈ ℝ₊*` on `m ∈ V`,
`λm = f⁻¹(λ f(m))` for a compatible chart `f` of a neighbourhood of `m` onto an open cone (the
chosen one, `coneChartAt`; any other gives the same point, `posSMul_eq`, for `V` Hausdorff). -/
def posSMul (c : RPos) (m : V) : V := (coneChartAt n m).symm (c • coneChartAt n m m)

/-- **Déf. 3, independence of the chart**: for every cone chart `f` at `m`, `λm = f⁻¹(λ f(m))`. -/
theorem posSMul_eq [T2Space V] {e : OpenPartialHomeomorph V (RnO n)} (he : IsConeChart n e)
    {m : V} (hm : m ∈ e.source) (c : RPos) : posSMul n c m = e.symm (c • e m) :=
  (isConeChart_coneChartAt m).symm_smul_eq he (mem_coneChartAt_source m) hm c

variable (n V) in
/-- **Déf. 3: `ℝ₊*` operates on `V`** (« Le groupe $\R^+$ des réels positifs opère sur un cône affin
$V$ »), for `V` Hausdorff. A reducible `def`, not an instance (the model `RnO n` cannot be
inferred from `V`): use `letI := coneMulAction n V`, or `posSMul n` directly. -/
abbrev coneMulAction [T2Space V] : MulAction RPos V where
  smul := posSMul n
  one_smul m := by
    show (coneChartAt n m).symm ((1 : RPos) • coneChartAt n m m) = m
    rw [one_smul]
    exact (coneChartAt n m).left_inv (mem_coneChartAt_source m)
  mul_smul a b m := by
    show posSMul n (a * b) m = posSMul n a (posSMul n b m)
    have he := isConeChart_coneChartAt (n := n) m
    have hm := mem_coneChartAt_source (n := n) m
    have hbm : posSMul n b m ∈ (coneChartAt n m).source := he.symm_smul_mem_source hm b
    rw [posSMul_eq he hbm a]
    show (coneChartAt n m).symm ((a * b) • coneChartAt n m m) =
      (coneChartAt n m).symm (a • coneChartAt n m ((coneChartAt n m).symm
        (b • coneChartAt n m m)))
    rw [he.apply_symm_smul hm, mul_smul]

variable [T2Space V]

/-- The action law `λ(μm) = (λμ)m`. -/
theorem posSMul_mul (a b : RPos) (m : V) : posSMul n (a * b) m = posSMul n a (posSMul n b m) :=
  (coneMulAction n V).mul_smul a b m

@[simp] theorem posSMul_one (m : V) : posSMul n 1 m = m := (coneMulAction n V).one_smul m

@[simp] theorem posSMul_inv_posSMul (c : RPos) (m : V) : posSMul n c⁻¹ (posSMul n c m) = m := by
  rw [← posSMul_mul, inv_mul_cancel, posSMul_one]

namespace IsConeChart

variable {e : OpenPartialHomeomorph V (RnO n)}

/-- Déf. 3 in a cone chart: `λm = f⁻¹(λ f(m))`. -/
theorem smul_eq (he : IsConeChart n e) {m : V} (hm : m ∈ e.source) (c : RPos) :
    posSMul n c m = e.symm (c • e m) :=
  posSMul_eq he hm c

theorem smul_mem_source (he : IsConeChart n e) {m : V} (hm : m ∈ e.source) (c : RPos) :
    posSMul n c m ∈ e.source := by
  rw [he.smul_eq hm]
  exact he.symm_smul_mem_source hm c

/-- The source of a cone chart is `ℝ₊*`-invariant. -/
theorem smul_mem_source_iff (he : IsConeChart n e) {m : V} (c : RPos) :
    posSMul n c m ∈ e.source ↔ m ∈ e.source := by
  refine ⟨fun h => ?_, fun h => he.smul_mem_source h c⟩
  have := he.smul_mem_source h c⁻¹
  rwa [posSMul_inv_posSMul] at this

/-- **A cone chart is `ℝ₊*`-equivariant**: `f(λm) = λ f(m)`. -/
theorem map_smul (he : IsConeChart n e) {m : V} (hm : m ∈ e.source) (c : RPos) :
    e (posSMul n c m) = c • e m := by
  rw [he.smul_eq hm]
  exact he.apply_symm_smul hm c

theorem symm_smul (he : IsConeChart n e) {v : RnO n} (hv : v ∈ e.target) (c : RPos) :
    e.symm (c • v) = posSMul n c (e.symm v) := by
  rw [he.smul_eq (e.map_target hv), e.right_inv hv]

end IsConeChart

/-- **Déf. 3: the action is continuous** (jointly). -/
theorem continuous_posSMul : Continuous fun p : RPos × V => posSMul n p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun ⟨c₀, m₀⟩ => ?_
  set e := coneChartAt n m₀
  have he := isConeChart_coneChartAt (n := n) m₀
  have hm₀ := mem_coneChartAt_source (n := n) m₀
  have hev : (fun p : RPos × V => posSMul n p.1 p.2) =ᶠ[𝓝 (c₀, m₀)] fun p => e.symm (p.1 • e p.2) := by
    filter_upwards [(continuous_snd.tendsto (c₀, m₀)).eventually (e.open_source.mem_nhds hm₀)]
      with p hp
    exact he.smul_eq hp p.1
  refine ContinuousAt.congr ?_ hev.symm
  refine (e.continuousAt_symm ?_).comp ?_
  · exact he.smul_mem_target (e.map_source hm₀) c₀
  · exact continuousAt_fst.smul ((e.continuousAt hm₀).comp continuousAt_snd)

theorem continuousSMul_cone : @ContinuousSMul RPos V (coneMulAction n V).toSMul _ _ :=
  @ContinuousSMul.mk RPos V (coneMulAction n V).toSMul _ _ continuous_posSMul

/-- **The action of `ℝ₊*` is free** (« espace fibré $\R^+$-principal »). -/
theorem eq_one_of_posSMul_eq {c : RPos} {m : V} (h : posSMul n c m = m) : c = 1 := by
  have he := isConeChart_coneChartAt (n := n) m
  have hm := mem_coneChartAt_source (n := n) m
  refine Punctured.eq_one_of_smul_pos_eq (v := coneChartAt n m m) ?_
  rw [← he.map_smul hm, h]

variable [HasGroupoid V (coneGroupoid n)]

/-- **« $\R^+$ opère sur $V$ comme un groupe d'automorphismes de sa structure localement
affine »**: every homothety `m ↦ λm` is a morphism of the canonical locally affine structure
(`affineChartedSpace`); in the charts `ι ∘ f` it is the homothety of ratio `λ` of `ℝⁿ`, an element
of `GA(n, ℝ)`. -/
theorem isGXMorphism_affine_smul [NeZero n] (c : RPos) :
    @IsGXMorphism (GAR n) (Fin n → ℝ) _ _ _ V _ V _ (affineChartedSpace n V)
      (affineChartedSpace n V) (posSMul n c) := by
  letI := affineChartedSpace n V
  haveI := hasGroupoid_affineChartedSpace n (V := V)
  refine isGXMorphism_of_mem_maximalAtlas
    ((continuous_posSMul (n := n)).comp (continuous_const.prodMk continuous_id)) fun x => ?_
  have he := isConeChart_coneChartAt (n := n) x
  have hx := mem_coneChartAt_source (n := n) x
  have hsrc : ∀ e : OpenPartialHomeomorph V (RnO n), (e.trans
      ((Punctured.isOpenEmbedding_val (E := Fin n → ℝ)).toOpenPartialHomeomorph _)).source =
      e.source := by
    intro e
    simp only [OpenPartialHomeomorph.trans_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
  refine ⟨_, trans_mem_maximalAtlas_affine n he.1, _, trans_mem_maximalAtlas_affine n he.1,
    by rw [hsrc]; exact hx, by rw [hsrc]; exact he.smul_mem_source hx c,
    (homothety (Fin n → ℝ) (c : ℝˣ)).toAffineEquiv, ?_⟩
  filter_upwards [(coneChartAt n x).open_source.mem_nhds hx] with y hy
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply, affineEquiv_smul_def,
    LinearEquiv.coe_toAffineEquiv, homothety_apply]
  rw [he.map_smul hy c, Punctured.val_smul_pos]

/-- **« (mais non de sa structure conique affine) »**: for `λ ≠ 1`, the homothety `m ↦ λm` of a
nonempty affine conical manifold is not a morphism of its conical structure (in a cone chart it is
the homothety `λ`, which agrees with no element of `GU(n, ℝ)` on an open set, since `λⁿ ≠ ±1`). -/
theorem not_isGXMorphism_cone_smul [Nonempty V] {c : RPos} (hc : c ≠ 1) :
    ¬ IsGXMorphism (GUR n) (RnO n) (posSMul n c : V → V) := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty V›
  set e := coneChartAt n x with he_def
  have he := isConeChart_coneChartAt (n := n) x
  have hx := mem_coneChartAt_source (n := n) x
  obtain ⟨g, hg⟩ := h.exists_smul_eq_of_mem_maximalAtlas he.1 he.1 hx (he.smul_mem_source hx c)
  obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 (hg.and (e.open_source.mem_nhds hx))
  have hU : IsOpen (e '' t) := e.isOpen_image_of_subset_source hto fun z hz => (ht hz).2
  have key := eq_smul_of_eqOn_punctured ((g : GLR n) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    ((c : ℝˣ) : ℝ) hU ⟨e x, mem_image_of_mem e hxt⟩ (by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : e (posSMul n c y) = g • e y := (ht hy).1
      rw [he.map_smul (ht hy).2] at h1
      have := congrArg Punctured.val h1
      simp only [Punctured.val_smul_pos, Punctured.val_smul_sub] at this
      exact this.symm)
  have hn : n ≠ 0 := by
    rintro rfl
    exact (e x).val_ne_zero (Subsingleton.elim _ _)
  have hdet : |((LinearEquiv.det (g : GLR n) : ℝˣ) : ℝ)| = 1 := g.2
  have hg' : (g : GLR n) = homothety (Fin n → ℝ) (c : ℝˣ) := by
    ext y : 1
    simpa using key y
  rw [hg', det_homothety, Module.finrank_fin_fun, abs_of_pos (pow_pos (Punctured.pos c) n)]
    at hdet
  have hc1 : ((c : ℝˣ) : ℝ) = 1 := (pow_eq_one_iff_of_nonneg (Punctured.pos c).le hn).1 hdet
  exact hc (Subtype.ext (Units.ext hc1))

/-- **Conical morphisms commute with the positive homotheties** (for § 2's functor `F⁻¹`): a
`(GU(n), ℝⁿ − {O})`-morphism `φ : V → W` of Hausdorff affine conical manifolds satisfies
`φ(λm) = λφ(m)`. In cone charts `φ` is an element of `GU(n)`, linear, so the two curves
`λ ↦ φ(λm)` and `λ ↦ λφ(m)` agree near any common point; they agree at `λ = 1`, and `ℝ₊*` is
connected. -/
theorem IsGXMorphism.map_posSMul {W : Type*} [TopologicalSpace W]
    [ChartedSpace (RnO n) W] [HasGroupoid W (coneGroupoid n)] [HasConeCharts n W] [T2Space W]
    {φ : V → W} (hφ : IsGXMorphism (GUR n) (RnO n) φ) (c : RPos) (m : V) :
    φ (posSMul n c m) = posSMul n c (φ m) := by
  haveI := connectedSpace_RPos
  set e₁ := coneChartAt n m
  set e₂ := coneChartAt n (φ m)
  have he₁ : IsConeChart n e₁ := isConeChart_coneChartAt m
  have hm₁ : m ∈ e₁.source := mem_coneChartAt_source m
  have he₂ : IsConeChart n e₂ := isConeChart_coneChartAt (φ m)
  have hm₂ : φ m ∈ e₂.source := mem_coneChartAt_source (φ m)
  have hcont : Continuous fun c : RPos => posSMul n c m :=
    continuous_posSMul.comp (continuous_id.prodMk continuous_const)
  set γ₁ : RPos → W := fun c => φ (posSMul n c m) with hγ₁def
  set γ₂ : RPos → W := fun c => posSMul n c (φ m) with hγ₂def
  have hγ₁ : Continuous γ₁ := hφ.continuous.comp hcont
  have hγ₂ : Continuous γ₂ := continuous_posSMul.comp (continuous_id.prodMk continuous_const)
  have hS : IsClopen {c | γ₁ c = γ₂ c} := by
    refine ⟨isClosed_eq hγ₁ hγ₂, isOpen_iff_mem_nhds.2 fun c₀ hc₀ => ?_⟩
    have hc₀ : φ (posSMul n c₀ m) = posSMul n c₀ (φ m) := hc₀
    have hq : posSMul n c₀ m ∈ e₁.source := he₁.smul_mem_source hm₁ c₀
    have hp : φ (posSMul n c₀ m) ∈ e₂.source := by rw [hc₀]; exact he₂.smul_mem_source hm₂ c₀
    obtain ⟨g, hg⟩ := hφ.exists_smul_eq_of_mem_maximalAtlas he₁.1 he₂.1 hq hp
    have hge : g • e₁ m = e₂ (φ m) := by
      have h1 : e₂ (φ (posSMul n c₀ m)) = g • e₁ (posSMul n c₀ m) := hg.self_of_nhds
      rw [he₁.map_smul hm₁, hc₀, he₂.map_smul hm₂, smul_comm] at h1
      exact (MulAction.injective c₀ h1).symm
    filter_upwards [(hcont.tendsto c₀).eventually (Filter.Eventually.and hg
      (hφ.continuous.continuousAt.preimage_mem_nhds (e₂.open_source.mem_nhds hp)))] with c hc
    show φ (posSMul n c m) = posSMul n c (φ m)
    have h3 : e₂ (φ (posSMul n c m)) = c • e₂ (φ m) := by
      rw [hc.1, he₁.map_smul hm₁, smul_comm, hge]
    calc φ (posSMul n c m) = e₂.symm (e₂ (φ (posSMul n c m))) := (e₂.left_inv hc.2).symm
      _ = posSMul n c (φ m) := by rw [h3, he₂.smul_eq hm₂]
  have h1 : (1 : RPos) ∈ {c | γ₁ c = γ₂ c} := by
    show φ (posSMul n 1 m) = posSMul n 1 (φ m)
    rw [posSMul_one, posSMul_one]
  have := hS.eq_univ ⟨1, h1⟩
  have hc : c ∈ {c | γ₁ c = γ₂ c} := by rw [this]; trivial
  exact hc

end Def3

/-! ### The category of affine conical manifolds -/

section Category

/-- The affine conical `n`-manifolds of Déf. 2 among the `(GU(n), ℝⁿ − {O})`-manifolds: those with
cone charts (Déf. 2, 3°), Hausdorff (« variété »; needed by Déf. 3, see `IsConeChart.symm_smul_eq`).
This class admits non-Hausdorff bases (`Cone/Counterexample`); the objects of `ConeCat` are
`IsProperConeObject`. -/
def IsConeObject (V : GXCat (GUR n) (RnO n)) : Prop := HasConeCharts n V ∧ T2Space V

/-- **The objects of wave 4's category (DEC-122)**: affine conical `n`-manifolds (cone charts,
Hausdorff) on which the action of `ℝ₊*` of Déf. 3 is proper (Bourbaki), equivalently whose base
`V/ℝ⁺` is Hausdorff (`ConeBase.t2Space_iff_properSMul`). DEC-122: « wave 4's affine conical objects
(the § 2 equivalence, DEC-113) carry a proper ℝ₊* action ». -/
structure IsProperConeObject (V : GXCat (GUR n) (RnO n)) : Prop where
  /-- Déf. 2, 3°. -/
  hasConeCharts : HasConeCharts n V
  /-- « variété »: Hausdorff. -/
  t2Space : T2Space V
  /-- The positive homotheties act properly (DEC-122). -/
  properSMul : @ProperSMul RPos V _ _ _ (@coneMulAction n V _ _ hasConeCharts t2Space)

theorem IsProperConeObject.isConeObject {V : GXCat (GUR n) (RnO n)} (h : IsProperConeObject n V) :
    IsConeObject n V :=
  ⟨h.hasConeCharts, h.t2Space⟩

/-- **The category of affine conical `n`-manifolds** (« Les variétés coniques affines de dimension
$n$ sont les objets d'une catégorie, dont les morphismes sont les applications $f$ … telles que
$J_1(V_2)\circ f\subset J_1(V_1)$ »): the full subcategory of `GXCat (GUR n) (RnO n)` on
`IsProperConeObject` (DEC-122: a proper action of `ℝ₊*`, so that wave 4's base functor lands in
Hausdorff locally projective manifolds); its morphisms are the `(GU(n), ℝⁿ − {O})`-morphisms,
which are exactly the maps with `J₁(V₂) ∘ f ⊆ J₁(V₁)` (`isGXMorphism_iff_jets`), and they commute
with the homotheties (`IsGXMorphism.map_posSMul`). -/
abbrev ConeCat : Type 1 := CategoryTheory.ObjectProperty.FullSubcategory (IsProperConeObject n)

example : CategoryTheory.Category (ConeCat n) := inferInstance

end Category

end Benzecri
