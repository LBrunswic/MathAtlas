import BenzecriScaffold.Cone.Lift
import Benzecri.Cone.Counterexample
import Benzecri.Cone.LowDim

/-!
# `BenzecriScaffold.Cone.Functor` — the « isomorphisme fonctoriel » of § 2: affine conical manifolds ≌ locally projective manifolds

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 2, journal pp. 241–242; transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex`, checked against the scan (PDF pp. 14–15).
Package WP-45r (wave 4). Indexing: cones of dimension `n + 1` (`ConeCat (n + 1)`), bases of
dimension `n` (`ProjCat n`), i.e. Benzécri's `n` and `n − 1`.

* `bzthm:c1s2_isomorphisme_fonctoriel` — `benzecri1960_ch1.tex:554` (Énoncé, l.554–558, p. 241;
  proof l.560–649, pp. 241–242; « Dans ce qui suit, nous noterons $F^{-1}$ … » l.651–652).
  **Proved in full, with no `sorry`, in the corrected form DEC-122/DEC-124 rule** and under the
  reading DEC-113 rules (plan F5: an equivalence of categories, not an isomorphism); NOT MARKED,
  because the corrected form adds DEC-122's hypothesis (see the finding below), pending the author's
  ruling as for Prop. 2 (DEC-124). The formalization of record:
  - `Benzecri.coneEquivalence n : ConeCat (n + 1) ≌ ProjCat n`, whose functor is the base functor
    `baseFunctor n`, `V ↦ V/ℝ₊*` (`coneEquivalence_functor`), and whose inverse is Benzécri's
    `F = coneFunctor n`, `B ↦ FJ(B)/ℛ` (`coneEquivalence_inverse`); `Prop` form:
    `baseFunctor_isEquivalence`.
  - the natural isomorphisms: `counitIso n : F ⋙ F⁻¹ ≅ 𝟭`, canonically `F(B)/ℝ₊* ≅ B` through the
    source projection (« une variété conique affine $F(B)$ … dont la base soit $B$ »;
    `FCone.isGXMorphism_baseProj`, `FCone.baseProj_bijective`), and `unitIso n : 𝟭 ≅ F⁻¹ ⋙ F`,
    canonically `V ≅ F(V/ℝ₊*)`, `m ↦ [(p(jet_m f), f(m))]` for a cone chart `f` at `m` (« $FJ(B)$
    s'identifie donc avec l'espace des jets de cartes compatibles »; `ConeBase.unitMap`,
    independent of `f`: `unitMap_eq`; in charts the identity: `coneChart_unitMap`; natural:
    `unitMap_naturality`).
  - the objects (DEC-124): `ConeCat (n + 1)` = connected Hausdorff affine conical manifolds with a
    proper `ℝ₊*`-action (`Cone/Basic`); `ProjCat n` = connected Hausdorff locally projective
    manifolds (`IsProjObject`); the functors land in them (`Cone/Base`'s bridge lemmas;
    `Cone/Lift`'s `FCone.t2Space`, `connectedSpace`, `properSMul`).
  - **the finding** (DEC-122, propagated to the Énoncé): read over all Hausdorff connected affine
    conical manifolds, the Énoncé is FALSE in every Benzécri dimension `n + 1 ≥ 3`: the essential
    image of `F` is exactly the cones with a proper action (`exists_iso_coneObj_iff`,
    `properSMul_of_iso`), and `Cone/Counterexample`'s `ConeCex.VDim m` is isomorphic to no `F(B)`
    (`not_essSurjAsPrinted_dim`, against the `Prop` `EssSurjAsPrintedDim`); in dimension
    `n + 1 ≤ 2` the printed form holds (`essSurjAsPrinted_of_le_one`).

Also: a bijective morphism of `(G,X)`-manifolds is an isomorphism (`GXCat.isoOfBijective`, from
`IsGXMorphism.of_rightInverse`); the base of an injective conical morphism is injective
(`ConeBase.map_injective`).

> **Énoncé.** Nous nous proposons de montrer que la correspondance établie entre une variété conique
> affine et sa base, définit un isomorphisme fonctoriel entre la catégorie des variétés coniques
> affines de dimension $n$, et celle des variétés localement projectives de dimension $n-1$.
>
> *Démonstration* (extraits). Étant donnée une variété localement projective $B$ de dimension
> $(n-1)$, nous allons construire une variété conique affine $F(B)$ de dimension $n$ dont la base
> soit $B$. […] $FJ(B)$ s'identifie donc avec l'espace des jets de cartes compatibles de $F(B)$.
> […] Pour achever de construire l'isomorphisme fonctionnel $F$ entre la catégorie des variétés
> localement projectives de dimension $n-1$ et celles des variétés coniques affines de dimension
> $n$, il faut construire l'image $F(\varphi)$ d'un morphisme. […] $F(\varphi)$ est aussi un
> isomorphisme local de $F(B_1)$ dans $F(B_2)$, d'où l'on déduit facilement qu'il est un morphisme
> de la catégorie des variétés coniques affines.
>
> Dans ce qui suit, nous noterons $F^{-1}$ le foncteur inverse de $F$ qui à une variété conique
> affine associe la variété localement projective qui est sa base.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| « isomorphisme fonctoriel » | reading (DEC-113, plan F5): `CategoryTheory.Equivalence`, with canonical natural isomorphisms `F⁻¹ ∘ F ≅ 𝟭`, `𝟭 ≅ F ∘ F⁻¹`; on the nose `F⁻¹(F(B)) = B` is not expected (`F(B)/ℝ₊*` is another type) |
| « variétés coniques affines de dimension $n$ » (Déf. 2), « variété »: Hausdorff, connected | ✓ carried: `ConeCat (n + 1)` (cone charts, `T2Space`, `ConnectedSpace`) |
| (not printed) the `ℝ₊*`-action is proper | ✓ **carried (ruled, DEC-122/DEC-124)**: a field of `IsProperConeObject`; NECESSARY (`not_essSurjAsPrinted_dim`), and exactly the essential image of `F` (`exists_iso_coneObj_iff`) |
| « variétés localement projectives de dimension $n-1$ », « variété »: Hausdorff, connected | ✓ carried: `ProjCat n` (`IsProjObject`: `T2Space ∧ ConnectedSpace`) |
| « variété »: second countable (plan F6) | generalised: not needed on either side; both functors preserve it (`ConeBase.secondCountableTopology`, `FCone.secondCountableTopology`), so the equivalence restricts to second countable objects |
| the morphisms: `J_1(V_2)∘f ⊂ J_1(V_1)`, resp. `J(V_2)∘f ⊂ J(V_1)` (p. 238, p. 240) | ✓ carried: `IsGXMorphism` (`isGXMorphism_iff_jets`), full subcategories of `GXCat` |

## SCOPE (disclosed)

* The objects are bundled in universe `0` (`GXCat`, plan F5); `ConeCat` and `ProjCat` are full
  subcategories (`ObjectProperty.FullSubcategory`) of `GXCat (GUR (n + 1)) (RnO (n + 1))` and of
  `LocProj n = GXCat (GSR n) (S n)`.
* The equivalence is built with `CategoryTheory.Equivalence.mk`, which adjusts the unit to satisfy
  the triangle identities; its functor and inverse are `baseFunctor n` and `coneFunctor n` on the
  nose (`rfl`), its counit is `counitIso n`.
* The finding is stated against the weakest printed-form consequence (`EssSurjAsPrintedDim`:
  every Hausdorff connected cone is some `F(B)`), so it refutes every reading of the printed Énoncé
  over that larger category in which `F` is the inverse; that the base functor itself does not
  land in Hausdorff manifolds is Prop. 2's finding (`Cone/Base`, `Cone/Counterexample`).
* `t2Space_RnO` is a local instance; `gsOf`, `isoGUR_gsOf`, `toSphere_smul_GU`,
  `baseChart_eventually_eq` are small `ConeBase` helpers (REPORT `upstream_moves`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology CategoryTheory

namespace Benzecri

universe u v

/-! ### Isomorphisms of `(G,X)`-manifolds -/

section Iso

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type*} [TopologicalSpace M] {N : Type*} [TopologicalSpace N]
  [ChartedSpace X M] [ChartedSpace X N]

omit [ContinuousConstSMul G X] in
/-- **A continuous right inverse of a morphism is a morphism**: if `f ∘ g = id`, `g` continuous and
`f` a `(G,X)`-morphism, then `g` reads, near every point, as the inverse of the element of `G` by
which `f` reads. -/
theorem IsGXMorphism.of_rightInverse {f : M → N} {g : N → M} (hf : IsGXMorphism G X f)
    (hg : Continuous g) (hfg : ∀ y, f (g y) = y) : IsGXMorphism G X g := by
  refine ⟨hg, fun y => ?_⟩
  obtain ⟨a, ha⟩ := hf.exists_smul_eq (g y)
  rw [hfg y] at ha
  refine ⟨a⁻¹, ?_⟩
  filter_upwards [hg.continuousAt.eventually ha] with w hw
  rw [hfg w] at hw
  rw [hw, inv_smul_smul]

variable (G X) in
/-- **A bijective morphism of `(G,X)`-manifolds is an isomorphism** (a bijective local
homeomorphism is a homeomorphism, and its inverse reads in charts as the inverses of the elements
of `G` by which the morphism reads). -/
def GXCat.isoOfBijective {V W : GXCat G X} (f : V ⟶ W) (hf : Function.Bijective f.1) : V ≅ W :=
  let E := (Equiv.ofBijective f.1 hf).toHomeomorphOfContinuousOpen f.2.continuous
    f.2.isLocalHomeomorph.isOpenMap
  { hom := f
    inv := ⟨E.symm, f.2.of_rightInverse E.symm.continuous E.apply_symm_apply⟩
    hom_inv_id := GXCat.hom_ext (funext E.symm_apply_apply)
    inv_hom_id := GXCat.hom_ext (funext E.apply_symm_apply) }

@[simp] theorem GXCat.isoOfBijective_hom {V W : GXCat G X} (f : V ⟶ W)
    (hf : Function.Bijective f.1) : (GXCat.isoOfBijective G X f hf).hom = f := rfl

end Iso

/-! ### The base side: `F(B)/ℝ₊* ≅ B` -/

namespace FCone

attribute [local instance] t2Space_RnO

variable {n : ℕ} {B : Type u} [TopologicalSpace B] [ChartedSpace (S n) B]
  [HasGroupoid B (projGroupoid n)] [T2Space B]

/-- **The canonical map `F(B)/ℝ₊* → B` is a morphism of locally projective manifolds**: in the base
chart of the cone chart over `e`, it reads as the identity (`p(f_e)(p(x)) = s(f_e(x)) = e(π(x))`). -/
theorem isGXMorphism_baseProj :
    IsGXMorphism (GSR n) (S n) (baseProj : ConeBase n (FCone n B) → B) := by
  refine isGXMorphism_of_mem_maximalAtlas continuous_baseProj fun b => ?_
  obtain ⟨x, rfl⟩ := ConeBase.mk_surjective b
  have he := chartAt_mem x
  have hφ := isConeChart_coneChart he
  have hx : x ∈ (coneChart he).source := mem_chart_source (S n) (proj x)
  refine ⟨ConeBase.baseChart hφ, ConeBase.baseChart_mem_maximalAtlas hφ, _, he, ⟨x, hx, rfl⟩,
    mem_chart_source (S n) (proj x), 1, ?_⟩
  filter_upwards [ConeBase.mk_image_mem_nhds ((coneChart he).open_source.mem_nhds hx)] with b hb
  obtain ⟨x', hx', rfl⟩ := hb
  rw [one_smul, ConeBase.baseChart_mk hφ hx', baseProj_mk, coneChart_apply,
    toSphere_coneFun he hx']

theorem baseProj_bijective : Function.Bijective (baseProj : ConeBase n (FCone n B) → B) :=
  ⟨baseProj_injective, baseProj_surjective⟩

end FCone

/-! ### The cone side: `V ≅ F(V/ℝ₊*)` -/

namespace ConeBase

attribute [local instance] t2Space_RnO

variable {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (RnO (n + 1)) V]
  [HasConeCharts (n + 1) V] [T2Space V]

/-- The element of `GS(n, ℝ)` induced by an element of `GU(n+1, ℝ)`: its class in `GL/ℝ₊*`. -/
abbrev gsOf (g : GUR (n + 1)) : GSR n := QuotientGroup.mk (g : GLR (n + 1))

/-- `i(ḡ) = g` for `g ∈ GU(n+1, ℝ)`. -/
theorem isoGUR_gsOf (g : GUR (n + 1)) : isoGUR n (gsOf g) = g := by
  have h := isoGU_symm_apply (E := Fin (n + 1) → ℝ) g
  show isoGU _ (QuotientGroup.mk (g : GLR (n + 1))) = g
  rw [← h]
  exact MulEquiv.apply_symm_apply _ g

/-- `s(g v) = ḡ s(v)`. -/
theorem toSphere_smul_GU (g : GUR (n + 1)) (v : RnO (n + 1)) :
    Punctured.toSphere (g • v) = gsOf g • Punctured.toSphere v := by
  conv_lhs => rw [← isoGUR_gsOf g]
  rw [toSphere_isoGUR_smul]

/-- If two cone charts satisfy `e' = g • e` near `m`, their base charts satisfy `p(e') = ḡ • p(e)`
near `p(m)`. -/
theorem baseChart_eventually_eq {e e' : OpenPartialHomeomorph V (RnO (n + 1))}
    (he : IsConeChart (n + 1) e) (he' : IsConeChart (n + 1) e') {m : V} (hm : m ∈ e.source)
    (hm' : m ∈ e'.source) {g : GUR (n + 1)} (hg : ∀ᶠ y in 𝓝 m, e' y = g • e y) :
    ∀ᶠ b in 𝓝 (mk (n := n) m), baseChart he' b = gsOf g • baseChart he b := by
  have ht : {y | e' y = g • e y ∧ y ∈ e.source ∧ y ∈ e'.source} ∈ 𝓝 m :=
    Filter.Eventually.and hg (Filter.Eventually.and (e.open_source.mem_nhds hm)
      (e'.open_source.mem_nhds hm'))
  filter_upwards [mk_image_mem_nhds ht] with z hz
  obtain ⟨y, ⟨hy, hys, hys'⟩, rfl⟩ := hz
  rw [baseChart_mk he hys, baseChart_mk he' hys', hy, toSphere_smul_GU]

theorem jet_baseChart_mem {e : OpenPartialHomeomorph V (RnO (n + 1))} (he : IsConeChart (n + 1) e)
    {m : V} (hm : m ∈ e.source) :
    jet (mk (n := n) m) (baseChart he) ∈ jets (GSR n) (S n) (ConeBase n V) :=
  jet_mem_jets (baseChart_mem_maximalAtlas he) ⟨m, hm, rfl⟩

theorem toSphere_eq_value_baseChart {e : OpenPartialHomeomorph V (RnO (n + 1))}
    (he : IsConeChart (n + 1) e) {m : V} (hm : m ∈ e.source) :
    Punctured.toSphere (e m) = Jet.value (jet (mk (n := n) m) (baseChart he)) := by
  rw [Jet.value_jet, baseChart_mk he hm]

/-- **The canonical map `V → F(V/ℝ₊*)`** (« $FJ(B)$ s'identifie donc avec l'espace des jets de cartes
compatibles »): `m ↦ [(p(jet_m f), f(m))]`, `f` a cone chart at `m` (the chosen one; any other gives
the same point, `unitMap_eq`). -/
def unitMap (m : V) : FCone n (ConeBase n V) :=
  FCone.mk (jet (mk m) (baseChart (isConeChart_coneChartAt (n := n + 1) m)))
    (jet_baseChart_mem _ (mem_coneChartAt_source m)) (coneChartAt (n + 1) m m)
    (toSphere_eq_value_baseChart _ (mem_coneChartAt_source m))

/-- **`unitMap` does not depend on the cone chart**: for every cone chart `f` at `m`,
`unitMap m = [(p(jet_m f), f(m))]` (two cone charts differ near `m` by `g ∈ GU(n+1)`, and
`(ḡ ∘ j, i(ḡ) w) ~ (j, w)`). -/
theorem unitMap_eq {e : OpenPartialHomeomorph V (RnO (n + 1))} (he : IsConeChart (n + 1) e)
    {m : V} (hm : m ∈ e.source) :
    unitMap m = FCone.mk (jet (mk m) (baseChart he)) (jet_baseChart_mem he hm) (e m)
      (toSphere_eq_value_baseChart he hm) := by
  have he₀ := isConeChart_coneChartAt (n := n + 1) m
  have hm₀ := mem_coneChartAt_source (n := n + 1) m
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas he₀.1 he.1 hm₀ hm
  have h1 : jet (mk (n := n) m) (baseChart he) =
      jetSMul (gsOf g) (jet (mk m) (baseChart he₀)) := by
    rw [jetSMul_jet, jet_eq_jet_iff]
    exact baseChart_eventually_eq he₀ he hm₀ hm hg
  have h2 : e m = isoGUR n (gsOf g) • coneChartAt (n + 1) m m := by
    rw [isoGUR_gsOf]
    exact hg.self_of_nhds
  rw [FCone.mk_congr (hj' := h1 ▸ jet_baseChart_mem he hm)
    (hm' := h1 ▸ h2 ▸ toSphere_eq_value_baseChart he hm) h1 h2]
  exact (FCone.mk_smul _ _ _ _ _).symm

@[simp] theorem proj_unitMap (m : V) : FCone.proj (unitMap m) = mk (n := n) m := rfl

/-- **`unitMap` in charts is the identity**: in a cone chart `f` of `V` and the cone chart of
`F(V/ℝ₊*)` over the base chart `p(f)`, `unitMap` reads as `id`. -/
theorem coneChart_unitMap {e : OpenPartialHomeomorph V (RnO (n + 1))} (he : IsConeChart (n + 1) e)
    {m : V} (hm : m ∈ e.source) :
    FCone.coneChart (baseChart_mem_maximalAtlas he) (unitMap m) = e m := by
  rw [unitMap_eq he hm, FCone.coneChart_apply,
    FCone.coneFun_mk_jet _ (show mk m ∈ (baseChart he).source from ⟨m, hm, rfl⟩)]

theorem unitMap_mem_source {e : OpenPartialHomeomorph V (RnO (n + 1))} (he : IsConeChart (n + 1) e)
    {m : V} (hm : m ∈ e.source) :
    unitMap m ∈ (FCone.coneChart (baseChart_mem_maximalAtlas he)).source :=
  show mk m ∈ (baseChart he).source from ⟨m, hm, rfl⟩

theorem unitMap_eq_symm {e : OpenPartialHomeomorph V (RnO (n + 1))} (he : IsConeChart (n + 1) e)
    {m : V} (hm : m ∈ e.source) :
    unitMap m = (FCone.coneChart (baseChart_mem_maximalAtlas he)).symm (e m) := by
  rw [← coneChart_unitMap he hm, OpenPartialHomeomorph.left_inv _ (unitMap_mem_source he hm)]

theorem continuous_unitMap : Continuous (unitMap : V → FCone n (ConeBase n V)) := by
  refine continuous_iff_continuousAt.2 fun m => ?_
  have he := isConeChart_coneChartAt (n := n + 1) m
  have hm := mem_coneChartAt_source (n := n + 1) m
  set Φ := FCone.coneChart (baseChart_mem_maximalAtlas he)
  have ht : coneChartAt (n + 1) m m ∈ Φ.target := by
    rw [← coneChart_unitMap he hm]
    exact Φ.map_source (unitMap_mem_source he hm)
  refine ContinuousAt.congr (f := fun m' => Φ.symm (coneChartAt (n + 1) m m')) ?_ ?_
  · exact ContinuousAt.comp (f := coneChartAt (n + 1) m) (Φ.continuousAt_symm ht)
      ((coneChartAt (n + 1) m).continuousAt hm)
  · filter_upwards [(coneChartAt (n + 1) m).open_source.mem_nhds hm] with m' hm'
    exact (unitMap_eq_symm he hm').symm

theorem unitMap_injective : Function.Injective (unitMap : V → FCone n (ConeBase n V)) := by
  intro m m' h
  have he := isConeChart_coneChartAt (n := n + 1) m
  have hm := mem_coneChartAt_source (n := n + 1) m
  have hb : mk (n := n) m' = mk m := by
    rw [← proj_unitMap (n := n) m', ← h, proj_unitMap]
  have hm' : m' ∈ (coneChartAt (n + 1) m).source := by
    rw [← mk_mem_baseChart_source_iff he, hb]
    exact ⟨m, hm, rfl⟩
  refine (coneChartAt (n + 1) m).injOn hm hm' ?_
  rw [← coneChart_unitMap he hm, ← coneChart_unitMap he hm', h]

theorem unitMap_surjective : Function.Surjective (unitMap : V → FCone n (ConeBase n V)) := by
  intro x
  obtain ⟨m, hm0⟩ := mk_surjective (n := n) (FCone.proj x)
  have he := isConeChart_coneChartAt (n := n + 1) m
  have hm := mem_coneChartAt_source (n := n + 1) m
  set e := coneChartAt (n + 1) m
  set Φ := FCone.coneChart (baseChart_mem_maximalAtlas he)
  have hx : x ∈ Φ.source := show FCone.proj x ∈ (baseChart he).source by
    rw [← hm0]
    exact ⟨m, hm, rfl⟩
  have hw : Φ x ∈ e.target := by
    obtain ⟨v, hv, hvw⟩ := (show Punctured.toSphere (Φ x) ∈ (baseChart he).target from
      Φ.map_source hx)
    obtain ⟨c, hc⟩ := Punctured.toSphere_eq_toSphere_iff.1 hvw
    rw [← hc]
    exact he.smul_mem_target hv c
  refine ⟨e.symm (Φ x), ?_⟩
  rw [unitMap_eq_symm he (e.map_target hw), e.right_inv hw]
  exact Φ.left_inv hx

theorem unitMap_bijective : Function.Bijective (unitMap : V → FCone n (ConeBase n V)) :=
  ⟨unitMap_injective, unitMap_surjective⟩

variable [HasGroupoid V (coneGroupoid (n + 1))]

/-- **`V → F(V/ℝ₊*)` is a morphism of affine conical manifolds** (it reads as the identity in the
charts `f`, `f_{p(f)}`). -/
theorem isGXMorphism_unitMap :
    IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) (unitMap : V → FCone n (ConeBase n V)) := by
  refine isGXMorphism_of_mem_maximalAtlas continuous_unitMap fun m => ?_
  have he := isConeChart_coneChartAt (n := n + 1) m
  have hm := mem_coneChartAt_source (n := n + 1) m
  refine ⟨_, he.1, _, FCone.coneChart_mem_maximalAtlas (baseChart_mem_maximalAtlas he), hm,
    unitMap_mem_source he hm, 1, ?_⟩
  filter_upwards [(coneChartAt (n + 1) m).open_source.mem_nhds hm] with m' hm'
  rw [coneChart_unitMap he hm', one_smul]

/-- **Naturality of `unitMap`**: for a conical morphism `ψ : V → W`,
`F(ψ/ℝ₊*) ∘ unitMap = unitMap ∘ ψ`. -/
theorem unitMap_naturality {W : Type v} [TopologicalSpace W] [ChartedSpace (RnO (n + 1)) W]
    [HasGroupoid W (coneGroupoid (n + 1))] [HasConeCharts (n + 1) W] [T2Space W] {ψ : V → W}
    (hψ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) ψ) (m : V) :
    FCone.map (isGXMorphism_map hψ) (unitMap m) = unitMap (ψ m) := by
  have heV := isConeChart_coneChartAt (n := n + 1) m
  have hmV := mem_coneChartAt_source (n := n + 1) m
  have heW := isConeChart_coneChartAt (n := n + 1) (ψ m)
  have hmW := mem_coneChartAt_source (n := n + 1) (ψ m)
  obtain ⟨g, hg⟩ := hψ.exists_smul_eq_of_mem_maximalAtlas heV.1 heW.1 hmV hmW
  have hgW : ∀ᶠ y in 𝓝 m, (fun y => coneChartAt (n + 1) (ψ m) (ψ y)) y =
      g • coneChartAt (n + 1) m y := hg
  -- the base charts: `p(f_W) ∘ (ψ/ℝ₊*) = ḡ • p(f_V)` near `p(m)`
  have hbase : ∀ᶠ b in 𝓝 (mk (n := n) m), (baseChart heW ∘ map hψ) b = gsOf g • baseChart heV b := by
    have ht : {y | coneChartAt (n + 1) (ψ m) (ψ y) = g • coneChartAt (n + 1) m y ∧
        y ∈ (coneChartAt (n + 1) m).source ∧ ψ y ∈ (coneChartAt (n + 1) (ψ m)).source} ∈ 𝓝 m :=
      Filter.Eventually.and hg (Filter.Eventually.and
        ((coneChartAt (n + 1) m).open_source.mem_nhds hmV)
        (hψ.continuous.continuousAt.preimage_mem_nhds
          ((coneChartAt (n + 1) (ψ m)).open_source.mem_nhds hmW)))
    filter_upwards [mk_image_mem_nhds ht] with z hz
    obtain ⟨y, ⟨hy, hys, hys'⟩, rfl⟩ := hz
    rw [Function.comp_apply, map_mk, baseChart_mk heW hys', baseChart_mk heV hys, hy,
      toSphere_smul_GU]
  have hjf : jet (mk (n := n) m) (baseChart heV) =
      jetSMul (gsOf g)⁻¹ (jet (mk m) (baseChart heW ∘ map hψ)) := by
    rw [jetSMul_jet, jet_eq_jet_iff]
    filter_upwards [hbase] with b hb
    rw [hb, inv_smul_smul]
  have hf : jet (map hψ (mk (n := n) m)) (baseChart heW) ∈ jets (GSR n) (S n) (ConeBase n W) :=
    jet_baseChart_mem heW hmW
  rw [unitMap, FCone.map_mk_of_eq (isGXMorphism_map hψ) _ _ hf hjf]
  have h2 : coneChartAt (n + 1) (ψ m) (ψ m) =
      isoGUR n (gsOf g) • coneChartAt (n + 1) m m := by
    rw [isoGUR_gsOf]
    exact hg.self_of_nhds
  have hf' := jet_baseChart_mem (n := n) heW hmW
  have hm1 : Punctured.toSphere (isoGUR n (gsOf g) • coneChartAt (n + 1) m m) =
      Jet.value (jet (mk (n := n) (ψ m)) (baseChart heW)) := by
    rw [← h2]
    exact toSphere_eq_value_baseChart heW hmW
  refine (FCone.mk_congr (j' := jetSMul (gsOf g)⁻¹ (jet (mk (ψ m)) (baseChart heW)))
    (m' := isoGUR n (gsOf g)⁻¹ • (isoGUR n (gsOf g) • coneChartAt (n + 1) m m))
    (hj' := (isJetStructure_jets (G := GSR n) (X := S n) (M := ConeBase n W)).smul_mem _ _ hf')
    (hm' := by rw [toSphere_isoGUR_smul, hm1, value_jetSMul]) rfl
    (by rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul])).trans ?_
  exact (FCone.mk_smul (gsOf g)⁻¹ hf' _ hm1 _).trans (FCone.mk_congr rfl h2.symm)

end ConeBase

/-! ### The two categories and the two functors -/

variable (n : ℕ)

/-- **The projective objects of § 2's equivalence (DEC-124)**: the Hausdorff and connected locally
projective `n`-manifolds (« variété », plan F6; second countability is carried where used). -/
def IsProjObject (B : LocProj n) : Prop := T2Space B ∧ ConnectedSpace B

/-- **`ProjCat n`**: the full subcategory of `LocProj n` on Hausdorff connected objects. Its
morphisms are the `(GS(n), S(n))`-morphisms, i.e. the local isomorphisms (p. 238). -/
abbrev ProjCat : Type 1 := ObjectProperty.FullSubcategory (IsProjObject n)

example : Category (ProjCat n) := inferInstance

variable {n}

attribute [local instance] t2Space_RnO

/-- The base `V/ℝ₊*` of an object of `ConeCat (n+1)`, as an object of `ProjCat n`
(`ConeBase.chartedSpace`, `ConeBase.hasGroupoid`; Hausdorff and connected by
`IsProperConeObject.connectedSpace_and_t2Space_coneBase`). -/
def baseObj (V : ConeCat (n + 1)) : ProjCat n :=
  letI := V.property.hasConeCharts
  letI := V.property.t2Space
  ⟨{ carrier := ConeBase n V.obj }, V.property.t2Space_coneBase, V.property.connectedSpace_coneBase⟩

/-- The base of a morphism of `ConeCat (n+1)` (`ConeBase.map`). -/
def baseMap {V W : ConeCat (n + 1)} (f : V ⟶ W) : baseObj V ⟶ baseObj W :=
  letI := V.property.hasConeCharts
  letI := V.property.t2Space
  letI := W.property.hasConeCharts
  letI := W.property.t2Space
  ObjectProperty.homMk ⟨ConeBase.map f.hom.2, ConeBase.isGXMorphism_map f.hom.2⟩

variable (n) in
/-- **The base functor `F⁻¹ : ConeCat (n+1) ⥤ ProjCat n`**, `V ↦ V/ℝ₊*` (« nous noterons $F^{-1}$
le foncteur … qui à une variété conique affine associe la variété localement projective qui est sa
base »). -/
def baseFunctor : ConeCat (n + 1) ⥤ ProjCat n where
  obj := baseObj
  map := baseMap
  map_id V := by
    letI := V.property.hasConeCharts
    letI := V.property.t2Space
    refine ObjectProperty.hom_ext _ (GXCat.hom_ext ?_)
    funext b
    obtain ⟨m, rfl⟩ := ConeBase.mk_surjective (n := n) (V := V.obj) b
    rfl
  map_comp f g := by
    refine ObjectProperty.hom_ext _ (GXCat.hom_ext ?_)
    funext b
    letI := ‹ConeCat (n + 1)›
    obtain ⟨m, rfl⟩ := Quotient.mk_surjective b
    rfl

/-- `F(B)` for an object of `ProjCat n`, an object of `ConeCat (n+1)`: cone charts, Hausdorff, a
proper `ℝ₊*`-action and connected. -/
def coneObj (B : ProjCat n) : ConeCat (n + 1) :=
  letI := B.property.1
  letI := B.property.2
  ⟨{ carrier := FCone n B.obj },
    ⟨FCone.hasConeCharts, FCone.t2Space, FCone.properSMul, FCone.connectedSpace⟩⟩

/-- `F(φ)` for a morphism of `ProjCat n`. -/
def coneMap {B B' : ProjCat n} (f : B ⟶ B') : coneObj B ⟶ coneObj B' :=
  ObjectProperty.homMk ⟨FCone.map f.hom.2, FCone.isGXMorphism_map f.hom.2⟩

variable (n) in
/-- **The cone functor `F : ProjCat n ⥤ ConeCat (n+1)`** (§ 2, proof of the Énoncé, pp. 241–242):
`B ↦ F(B) = FJ(B)/ℛ`, `φ ↦ F(φ)`. -/
def coneFunctor : ProjCat n ⥤ ConeCat (n + 1) where
  obj := coneObj
  map := coneMap
  map_id _ := ObjectProperty.hom_ext _ (GXCat.hom_ext FCone.map_id)
  map_comp f g := ObjectProperty.hom_ext _ (GXCat.hom_ext (FCone.map_comp g.hom.2 f.hom.2))

/-! ### The two natural isomorphisms and the equivalence -/

/-- **`F(B)/ℝ₊* ≅ B`**, canonically (« une variété conique affine $F(B)$ … dont la base soit $B$ »). -/
def counitApp (B : ProjCat n) : baseObj (coneObj B) ≅ B :=
  letI := B.property.1
  ObjectProperty.isoMk _ (GXCat.isoOfBijective _ _
    ⟨FCone.baseProj, FCone.isGXMorphism_baseProj⟩ FCone.baseProj_bijective)

variable (n) in
/-- **The natural isomorphism `F⁻¹ ∘ F ≅ 𝟭`**. -/
def counitIso : coneFunctor n ⋙ baseFunctor n ≅ 𝟭 (ProjCat n) :=
  NatIso.ofComponents counitApp fun {_ _} f => by
    refine ObjectProperty.hom_ext _ (GXCat.hom_ext ?_)
    funext b
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective b
    exact FCone.proj_map f.hom.2 x

/-- **`V ≅ F(V/ℝ₊*)`**, canonically (through the cone charts and the jets). -/
def unitApp (V : ConeCat (n + 1)) : V ≅ coneObj (baseObj V) :=
  letI := V.property.hasConeCharts
  letI := V.property.t2Space
  ObjectProperty.isoMk _ (GXCat.isoOfBijective _ _
    ⟨ConeBase.unitMap, ConeBase.isGXMorphism_unitMap⟩ ConeBase.unitMap_bijective)

variable (n) in
/-- **The natural isomorphism `𝟭 ≅ F ∘ F⁻¹`**. -/
def unitIso : 𝟭 (ConeCat (n + 1)) ≅ baseFunctor n ⋙ coneFunctor n :=
  NatIso.ofComponents unitApp fun {V W} f => by
    letI := V.property.hasConeCharts
    letI := V.property.t2Space
    letI := W.property.hasConeCharts
    letI := W.property.t2Space
    refine ObjectProperty.hom_ext _ (GXCat.hom_ext ?_)
    funext m
    exact (ConeBase.unitMap_naturality f.hom.2 m).symm

variable (n) in
/-- **§ 2, the « isomorphisme fonctoriel »** (`bzthm:c1s2_isomorphisme_fonctoriel`): the base functor
`V ↦ V/ℝ₊*` is an equivalence between the category of (connected, Hausdorff, proper) affine conical
`(n+1)`-manifolds and that of (connected, Hausdorff) locally projective `n`-manifolds, with inverse
Benzécri's `F`. -/
def coneEquivalence : ConeCat (n + 1) ≌ ProjCat n :=
  CategoryTheory.Equivalence.mk (baseFunctor n) (coneFunctor n) (unitIso n) (counitIso n)

theorem coneEquivalence_functor : (coneEquivalence n).functor = baseFunctor n := rfl

theorem coneEquivalence_inverse : (coneEquivalence n).inverse = coneFunctor n := rfl

variable (n) in
/-- **The base functor is an equivalence of categories** (`bzthm:c1s2_isomorphisme_fonctoriel`, the
`Prop` form: « la correspondance établie entre une variété conique affine et sa base, définit un
isomorphisme fonctoriel », read as an equivalence, plan F5 / DEC-113). -/
theorem baseFunctor_isEquivalence : (baseFunctor n).IsEquivalence :=
  (coneEquivalence n).isEquivalence_functor

/-! ### The essential image of `F`: exactly the proper cones (DEC-122) -/

namespace ConeBase

variable {V : Type u} [TopologicalSpace V] [ChartedSpace (RnO (n + 1)) V]
  [HasGroupoid V (coneGroupoid (n + 1))] [HasConeCharts (n + 1) V] [T2Space V]
  {W : Type v} [TopologicalSpace W] [ChartedSpace (RnO (n + 1)) W]
  [HasGroupoid W (coneGroupoid (n + 1))] [HasConeCharts (n + 1) W] [T2Space W]

/-- The base of an injective conical morphism is injective (conical morphisms commute with the
homotheties, `IsGXMorphism.map_posSMul`). -/
theorem map_injective {ψ : V → W} (hψ : IsGXMorphism (GUR (n + 1)) (RnO (n + 1)) ψ)
    (hinj : Function.Injective ψ) : Function.Injective (map hψ) := by
  intro b b' h
  obtain ⟨a, rfl⟩ := mk_surjective (n := n) b
  obtain ⟨a', rfl⟩ := mk_surjective (n := n) b'
  rw [map_mk, map_mk] at h
  obtain ⟨c, hc⟩ := mk_eq_mk_iff.1 h
  rw [← hψ.map_posSMul] at hc
  exact mk_eq_mk_iff.2 ⟨c, hinj hc⟩

end ConeBase

/-- **Only proper cones are of the form `F(B)`**: an affine conical manifold isomorphic to `F(B)`
(`B` Hausdorff) has a proper `ℝ₊*`-action — its base injects continuously into the Hausdorff base
of `F(B)`. -/
theorem properSMul_of_iso {V : GXCat (GUR (n + 1)) (RnO (n + 1))} [HasConeCharts (n + 1) V]
    [T2Space V] (B : ProjCat n) (ψ : V ≅ (coneObj B).obj) :
    @ProperSMul RPos V _ _ _ (coneMulAction (n + 1) V) := by
  letI := (coneObj B).property.hasConeCharts
  letI := (coneObj B).property.t2Space
  haveI : T2Space (ConeBase n (coneObj B).obj) := (coneObj B).property.t2Space_coneBase
  have hinj : Function.Injective ψ.hom.1 := by
    refine Function.LeftInverse.injective (g := ψ.inv.1) fun m => ?_
    exact congrFun (congrArg Subtype.val ψ.hom_inv_id) m
  haveI : T2Space (ConeBase n V) := T2Space.of_injective_continuous
    (ConeBase.map_injective ψ.hom.2 hinj) (ConeBase.continuous_map ψ.hom.2)
  exact ConeBase.properSMul_of_t2Space

/-- **The essential image of `F`** among the Hausdorff connected affine conical `(n+1)`-manifolds:
`V ≅ F(B)` for some Hausdorff connected locally projective `B` iff the action of `ℝ₊*` on `V` is
proper (DEC-122's hypothesis is exactly the essential image). -/
theorem exists_iso_coneObj_iff {V : GXCat (GUR (n + 1)) (RnO (n + 1))} [HasConeCharts (n + 1) V]
    [T2Space V] [ConnectedSpace V] :
    (∃ B : ProjCat n, Nonempty (V ≅ (coneObj B).obj)) ↔
      @ProperSMul RPos V _ _ _ (coneMulAction (n + 1) V) := by
  refine ⟨fun ⟨B, ⟨ψ⟩⟩ => properSMul_of_iso B ψ, fun h => ?_⟩
  let V' : ConeCat (n + 1) := ⟨V, ⟨inferInstance, inferInstance, h, inferInstance⟩⟩
  exact ⟨baseObj V', ⟨(ObjectProperty.ι _).mapIso (unitApp V')⟩⟩

/-- **The Énoncé read over all Hausdorff connected affine conical manifolds** (« variété », plan F6,
without DEC-122's properness), in its weakest form, as a `Prop` (kb/0022): every Hausdorff,
connected affine conical `(n+1)`-manifold is isomorphic to `F(B)` for a Hausdorff connected
locally projective `B` (i.e. `F` is essentially surjective onto that category). FALSE for every
`n ≥ 2` (Benzécri's dimension `n + 1 ≥ 3`): `not_essSurjAsPrinted_dim`. -/
def EssSurjAsPrintedDim (n : ℕ) : Prop :=
  ∀ (V : GXCat (GUR (n + 1)) (RnO (n + 1))) [HasConeCharts (n + 1) V] [T2Space V]
    [ConnectedSpace V], ∃ B : ProjCat n, Nonempty (V ≅ (coneObj B).obj)

/-- **FINDING (DEC-122, propagated to the Énoncé)**: in every Benzécri dimension `n + 1 ≥ 3`, the
Hausdorff, second countable, connected affine conical manifold `ConeCex.VDim` of
`Cone/Counterexample` is isomorphic to no `F(B)`: without the properness of the `ℝ₊*`-action the
« isomorphisme fonctoriel » fails, whatever the functor in the other direction. -/
theorem not_essSurjAsPrinted_dim {n : ℕ} (hn : 2 ≤ n) : ¬ EssSurjAsPrintedDim n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  intro h
  obtain ⟨B, ⟨ψ⟩⟩ := h ⟨ConeCex.VDim m⟩
  exact ConeCex.not_properSMul_dim m (properSMul_of_iso B ψ)

/-- **In Benzécri's dimension `n + 1 ≤ 2` the Énoncé holds as printed**: every Hausdorff connected
affine conical `(n+1)`-manifold is some `F(B)` (the action is automatically proper, `Cone/LowDim`). -/
theorem essSurjAsPrinted_of_le_one {n : ℕ} (hn : n ≤ 1) : EssSurjAsPrintedDim n := by
  intro V _ _ _
  exact exists_iso_coneObj_iff.2 (LowDim.properSMul_of_le_one hn)

end Benzecri
