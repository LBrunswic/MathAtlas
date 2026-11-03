import BenzecriScaffold.Structure.Basic
import Mathlib.Topology.Covering.Quotient
import Mathlib.Geometry.Manifold.Instances.Quotient
import Mathlib.CategoryTheory.Category.Basic

/-!
# `BenzecriScaffold.Structure.Quotient` — morphisms, the category, quotients `V/G`, étalé pull-backs (p. 238)

J.-P. Benzécri, *Sur les variétés localement affines et localement projectives*, Bull. SMF 88
(1960) 229–332, Chapter 1 § 1, journal p. 238 (unlabelled prose); transcription
`papers/benzecri/legacy/labeled/benzecri1960_ch1.tex:390–408`. Package WP-45i (wave 2, layer L3).
No ledger label: the prose of p. 238 carries none, so nothing is marked; it is groundwork for the
« isomorphisme fonctoriel » of § 2 (`benzecri1960_ch1.tex:551`, not certified here; DEC-113: a
`CategoryTheory.Equivalence`).

What is proved, for an arbitrary `(G, X)` (the paper's two cases are `(GSR n, S n)` and
`(GAR n, Fin n → ℝ)`):
* **Morphisms** (`benzecri1960_ch1.tex:390–396`): `Benzecri.IsGXMorphism` (continuous, and in charts
  locally an element of `G`; ported from `lean-gx/GX/Structure/Basic.lean:512–660` at lean-gx
  `4a577c5`), identity, composition, chart independence, and a morphism is a local homeomorphism
  (`IsGXMorphism.isLocalHomeomorph`, the paper's « isomorphisme local »). **The paper's definition
  by jets, « $J(V_2)\circ f\subset J(V_1)$ », is equivalent** for continuous `f`
  (`isGXMorphism_iff_jets`).
* **The category** (`:390`): bundled objects `Benzecri.GXCat G X` (`carrier : Type`, with its
  topology, charted space and groupoid as instance fields; plan F5), the instance
  `GXCat.category` (morphisms the `IsGXMorphism` maps), `LocProj n`, `LocAff n`.
* **The quotient `V/G`** (`:398–401`): for a group `Γ` of automorphisms (each `γ • ·` a morphism),
  properly discontinuous (`ProperlyDiscontinuousSMul`) and free (`IsCancelSMul`, « sans point
  fixe »), `V` Hausdorff and locally compact, Mathlib's charted space on
  `MulAction.orbitRel.Quotient Γ V` is a `(G,X)`-structure (`hasGroupoid_quotient`), the projection
  is a morphism (`isGXMorphism_quotientMk`), and it is the only such structure
  (`maximalAtlas_quotient_unique`). In general: the push-forward along a surjective local
  homeomorphism whose deck transformations are `(G,X)`-maps (`IsGXDeck`,
  `existsUnique_pushforward`).
* **The étalé pull-back** (`:401–405`): along a local homeomorphism `p : E → V` (an « ouvert étalé »)
  there is a unique structure making `p` a morphism (`existsUnique_pullback`, ported from
  `lean-gx/GX/Structure/Basic.lean:761–880`); in particular on every covering
  (`existsUnique_pullback_of_isCoveringMap`).

> Les variétés localement projectives sont les objets d'une catégorie, où l'on définit ainsi les
> morphismes : soient $V_1$, $V_2$ localement projectives; $J(V_2)$, $J(V_2)$ les ensembles
> correspondants de jets projectifs; $f$ une application de $V_1$ dans $V_2$. Notons
> $J(V_2)\circ f$, l'ensemble des jets de $V_1$ dans $S(n)$ obtenus en composant un jet de $f$ et un
> jet de $J(V_2)$ : $f$ est un morphisme de la structure lacalement projective, si et seulement si
> $J(V_2)\circ f\subset J(V_1)$.
>
> En particulier, on définit les automorphismes d'une variété localement projective. Soit $G$ un
> groupe proprement discontinu sans point fixe, d'automorphismes de la structure localement
> projective de $V$ : l'espace quotient $V/G$ est muni canoniquement d'une structure localement
> projective : c'est l'unique structure pour laquelle la projection de $V$ sur $V/G$ soit un
> morphisme. Tout ouvert étalé $E$ au-dessus d'une variété localement projective $V$ est muni
> canoniquement d'une structure localement projective : l'unique structure telle que la projection
> soit un morphisme. En particulier, tout revêtement $R$ de $V$ est une variété localement
> projective, et si $R$ est galoisien, $V$ est le quotient de $R$ par un groupe d'automorphismes de
> sa structure projective. Au revêtement universel de $V$, s'applique la proposition 2 : il peut être
> muni d'une projection sur $S(n)$ qui est isomorphisme local des structures projectives.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `f : V₁ → V₂` « une application » | ⚠ reading: continuous (the composite of a jet of `f` with a jet of `J(V₂)` is a germ only if `f` maps a neighbourhood into the chart's domain); `isGXMorphism_iff_jets` takes `Continuous f` |
| `V₁`, `V₂` of the same dimension | ✓ carried: one model `X` for both |
| `G` « proprement discontinu » | ✓ carried as Mathlib's `ProperlyDiscontinuousSMul` (compact sets meet finitely many translates) |
| « sans point fixe » | ✓ carried as `IsCancelSMul Γ V` (free action) |
| « d'automorphismes de la structure » | ✓ carried: every `γ • ·` is a morphism (its inverse `γ⁻¹ • ·` is one too) |
| `V` a variété (Hausdorff; plan F6) | ✓ carried where used: `[T2Space V] [LocallyCompactSpace V]` for the quotient only (Mathlib's covering lemma); locally compact holds for every `V` charted on `S(n)` or `ℝⁿ` (`ChartedSpace.locallyCompactSpace`) |
| « ouvert étalé » = local homeomorphism (`kb/0001`) | ✓ carried: `IsLocalHomeomorph p` |

## SCOPE (disclosed)

* No label, so nothing is marked; the category is groundwork for § 2's functor (DEC-113).
* The objects `GXCat G X` carry no connectedness, Hausdorffness or countability (plan F6: carried
  where used); `carrier : Type` (universe 0, plan F5).
* Not formalized: « si $R$ est galoisien, $V$ est le quotient de $R$ par un groupe d'automorphismes »,
  and the universal covering's developing map (Prop. 2, wave 3). Automorphisms are not given a name
  (`CategoryTheory.Aut` applies to `GXCat`).
* `[sic]`, not findings: « $J(V_2)$, $J(V_2)$ » is read « $J(V_1)$, $J(V_2)$ », « lacalement »
  « localement ».

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology

namespace Benzecri

universe u v w y

/-! ### Morphisms: local `(G,X)`-isomorphisms (port of `lean-gx/GX/Structure/Basic.lean:512–660`) -/

section Morphism

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M] {N : Type y} [TopologicalSpace N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace X M] [ChartedSpace X N] [ChartedSpace X P]

variable (G X) in
/-- **A morphism of `(G,X)`-manifolds** (p. 238): a continuous map which, read in the preferred
charts near every point, is the restriction of an element of `G`. Port of `GX.IsGXMorphism`
(`lean-gx/GX/Structure/Basic.lean:524`). The paper's definition by jets is
`isGXMorphism_iff_jets`. -/
structure IsGXMorphism (f : M → N) : Prop where
  continuous : Continuous f
  exists_smul_eq : ∀ x : M, ∃ g : G, ∀ᶠ y in 𝓝 x, chartAt X (f x) (f y) = g • chartAt X x y

/-- **Chart independence**: a morphism read in any charts of the maximal atlases is, near every
point, the restriction of an element of `G`. Port of
`GX.IsGXMorphism.exists_smul_eq_of_mem_maximalAtlas` (`lean-gx/GX/Structure/Basic.lean:536`). -/
theorem IsGXMorphism.exists_smul_eq_of_mem_maximalAtlas [HasGroupoid M (gxGroupoid G X)]
    [HasGroupoid N (gxGroupoid G X)] {f : M → N} (hf : IsGXMorphism G X f)
    {e : OpenPartialHomeomorph M X} {e' : OpenPartialHomeomorph N X}
    (he : e ∈ (gxGroupoid G X).maximalAtlas M) (he' : e' ∈ (gxGroupoid G X).maximalAtlas N)
    {x : M} (hx : x ∈ e.source) (hfx : f x ∈ e'.source) :
    ∃ g : G, ∀ᶠ y in 𝓝 x, e' (f y) = g • e y := by
  obtain ⟨g, hg⟩ := hf.exists_smul_eq x
  obtain ⟨a, ha⟩ := eventually_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid G X).chart_mem_maximalAtlas x) he (mem_chart_source X x) hx
  obtain ⟨b, hb⟩ := eventually_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid G X).chart_mem_maximalAtlas (f x)) he' (mem_chart_source X (f x)) hfx
  refine ⟨b * g * a⁻¹, ?_⟩
  filter_upwards [hf.continuous.continuousAt.eventually hb, hg, ha] with y h1 h2 h3
  rw [h1, h2, h3]
  simp only [mul_smul, inv_smul_smul]

omit [ContinuousConstSMul G X] in
/-- The identity is a morphism. -/
theorem isGXMorphism_id : IsGXMorphism G X (id : M → M) :=
  ⟨continuous_id, fun _ => ⟨1, Eventually.of_forall fun _ => (one_smul G _).symm⟩⟩

omit [ContinuousConstSMul G X] in
/-- **Composition** of morphisms. -/
theorem IsGXMorphism.comp {f : M → N} {f' : N → P} (hf' : IsGXMorphism G X f')
    (hf : IsGXMorphism G X f) : IsGXMorphism G X (f' ∘ f) := by
  refine ⟨hf'.continuous.comp hf.continuous, fun x => ?_⟩
  obtain ⟨g, hg⟩ := hf.exists_smul_eq x
  obtain ⟨g', hg'⟩ := hf'.exists_smul_eq (f x)
  refine ⟨g' * g, ?_⟩
  filter_upwards [hf.continuous.continuousAt.eventually hg', hg] with y h1 h2
  simp only [Function.comp_apply]
  rw [h1, h2, mul_smul]

/-- **A morphism is a local homeomorphism** (« isomorphisme local »). Port of
`GX.IsGXMorphism.isLocalHomeomorph` (`lean-gx/GX/Structure/Basic.lean:582`). -/
theorem IsGXMorphism.isLocalHomeomorph {f : M → N} (hf : IsGXMorphism G X f) :
    IsLocalHomeomorph f := by
  refine IsLocalHomeomorph.mk _ fun x => ?_
  obtain ⟨g, hg⟩ := hf.exists_smul_eq x
  have hev : ∀ᶠ y in 𝓝 x, f y ∈ (chartAt X (f x)).source ∧
      chartAt X (f x) (f y) = g • chartAt X x y :=
    (hf.continuous.continuousAt.eventually
      ((chartAt X (f x)).open_source.mem_nhds (mem_chart_source X (f x)))).and hg
  obtain ⟨O, hO, hOo, hxO⟩ := mem_nhds_iff.1 hev
  refine ⟨(((chartAt X x).transHomeomorph (Homeomorph.smul g)).trans
    (chartAt X (f x)).symm).restrOpen O hOo, ?_, fun y hy => ?_⟩
  · show (x ∈ (chartAt X x).source ∧ g • chartAt X x x ∈ (chartAt X (f x)).target) ∧ x ∈ O
    refine ⟨⟨mem_chart_source X x, ?_⟩, hxO⟩
    rw [← (hO hxO).2]
    exact (chartAt X (f x)).map_source (hO hxO).1
  · have hyO : y ∈ O := hy.2
    show f y = (chartAt X (f x)).symm (g • chartAt X x y)
    rw [← (hO hyO).2, (chartAt X (f x)).left_inv (hO hyO).1]

omit [ContinuousConstSMul G X] in
/-- A morphism into the model space: near every point a translate of the preferred chart. -/
theorem isGXMorphism_iff_model {D : M → X} :
    IsGXMorphism G X D ↔ Continuous D ∧
      ∀ x : M, ∃ g : G, ∀ᶠ y in 𝓝 x, D y = g • chartAt X x y := by
  constructor
  · intro h
    refine ⟨h.1, fun x => ?_⟩
    obtain ⟨g, hg⟩ := h.2 x
    exact ⟨g, by simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq] using hg⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x => ?_⟩
    obtain ⟨g, hg⟩ := h2 x
    exact ⟨g, by simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq] using hg⟩

/-- **The paper's definition of the morphisms** (p. 238, « $f$ est un morphisme … si et seulement
si $J(V_2)\circ f\subset J(V_1)$ »): for a continuous `f`, `f` is a morphism iff composing a jet of
`f` with a jet of `J(V₂)` always gives a jet of `J(V₁)`. -/
theorem isGXMorphism_iff_jets [HasGroupoid M (gxGroupoid G X)] [HasGroupoid N (gxGroupoid G X)]
    {f : M → N} (hf : Continuous f) :
    IsGXMorphism G X f ↔ ∀ (x : M) (γ : Germ (𝓝 (f x)) X), (⟨f x, γ⟩ : Jet N X) ∈ jets G X N →
      (⟨x, γ.compTendsto f (hf.tendsto x)⟩ : Jet M X) ∈ jets G X M := by
  constructor
  · rintro hm x γ ⟨e', he', hx', hγ⟩
    simp only at hx' hγ
    subst hγ
    obtain ⟨g, hg⟩ := hm.exists_smul_eq_of_mem_maximalAtlas
      ((gxGroupoid G X).chart_mem_maximalAtlas x) he' (mem_chart_source X x) hx'
    have hmem := (isJetStructure_jets (G := G) (X := X) (M := M)).smul_mem g _
      (jet_mem_jets ((gxGroupoid G X).chart_mem_maximalAtlas x) (mem_chart_source X x))
    rw [jetSMul_jet] at hmem
    rw [Germ.coe_compTendsto]
    convert hmem using 1
    exact (jet_eq_jet_iff.2 hg)
  · intro h
    refine ⟨hf, fun x => ?_⟩
    have hj := h x _ (jet_mem_jets ((gxGroupoid G X).chart_mem_maximalAtlas (f x))
      (mem_chart_source X (f x)))
    rw [Germ.coe_compTendsto] at hj
    obtain ⟨e, he, hx, hγ⟩ := hj
    simp only at hx hγ
    obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas
      ((gxGroupoid G X).chart_mem_maximalAtlas x) he (mem_chart_source X x) hx
    refine ⟨g, ?_⟩
    filter_upwards [Germ.coe_eq.1 hγ, hg] with y h1 h2
    rw [← h2]
    exact h1

end Morphism

/-! ### The category of locally projective (resp. affine) manifolds -/

section Category

variable (G : Type w) (X : Type v) [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X]

/-- **A `(G,X)`-manifold, bundled** (the objects of the category of p. 238, plan F5): a type with a
topology, a charted space structure over `X` and transitions in `gxGroupoid G X`. -/
structure GXCat where
  /-- The underlying space. -/
  carrier : Type
  [str : TopologicalSpace carrier]
  [charted : ChartedSpace X carrier]
  [groupoid : HasGroupoid carrier (gxGroupoid G X)]

attribute [instance] GXCat.str GXCat.charted GXCat.groupoid

instance : CoeSort (GXCat G X) Type := ⟨GXCat.carrier⟩

/-- **The category of `(G,X)`-manifolds** (p. 238, « Les variétés localement projectives sont les
objets d'une catégorie »): morphisms are the `(G,X)`-morphisms, i.e. the local isomorphisms. -/
instance GXCat.category : CategoryTheory.Category (GXCat G X) where
  Hom V W := {f : V → W // IsGXMorphism G X f}
  id _ := ⟨id, isGXMorphism_id⟩
  comp f g := ⟨g.1 ∘ f.1, g.2.comp f.2⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- **`LocProj n`**: the category of locally projective `n`-manifolds. -/
abbrev LocProj (n : ℕ) : Type 1 := GXCat (GSR n) (S n)

/-- **`LocAff n`**: the category of locally affine `n`-manifolds. -/
abbrev LocAff (n : ℕ) : Type 1 := GXCat (GAR n) (Fin n → ℝ)

example (n : ℕ) : CategoryTheory.Category (LocProj n) := inferInstance
example (n : ℕ) : CategoryTheory.Category (LocAff n) := inferInstance

variable {G X}

/-- Every morphism of the category is a local homeomorphism. -/
theorem GXCat.isLocalHomeomorph_hom {V W : GXCat G X} (f : V ⟶ W) : IsLocalHomeomorph f.1 :=
  f.2.isLocalHomeomorph

end Category

/-! ### Pull-back along a local homeomorphism: « ouvert étalé », coverings (port of
`lean-gx/GX/Structure/Basic.lean:761–880`) -/

section Pullback

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M] {N : Type y} [TopologicalSpace N]
  [ChartedSpace X N]

variable (G X) in
/-- The charts of `M` in which `p : M → N` is, near every point, the restriction of an element
of `G`. Port of `GX.gxPullbackAtlas` (`lean-gx/GX/Structure/Basic.lean:772`). -/
def gxPullbackAtlas (p : M → N) : Set (OpenPartialHomeomorph M X) :=
  {e | ∀ x ∈ e.source, ∃ g : G, ∀ᶠ y in 𝓝 x, chartAt X (p x) (p y) = g • e y}

/-- **The pull-back of a charted space along a local homeomorphism** `p : M → N`: the chart at `x`
is the chart of `N` at `p x` composed with the local inverse of `p` through `x` (Mathlib's
`IsLocalHomeomorph.localInverseAt`). Port of `GX.pullbackChartedSpace`
(`lean-gx/GX/Structure/Basic.lean:790`). -/
@[reducible] def pullbackChartedSpace {p : M → N} (hp : IsLocalHomeomorph p) :
    ChartedSpace X M where
  atlas := range fun x => (hp.localInverseAt x).symm.trans (chartAt X (p x))
  chartAt x := (hp.localInverseAt x).symm.trans (chartAt X (p x))
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
      OpenPartialHomeomorph.symm_source, hp.localInverseAt_symm]
    exact ⟨hp.self_mem_localInverseAt_target (x := x), mem_chart_source X (p x)⟩
  chart_mem_atlas x := ⟨x, rfl⟩

/-- The pulled-back structure is a `(G,X)`-structure. Port of `GX.hasGroupoid_pullback`
(`lean-gx/GX/Structure/Basic.lean:800`). -/
theorem hasGroupoid_pullback [HasGroupoid N (gxGroupoid G X)] {p : M → N}
    (hp : IsLocalHomeomorph p) :
    @HasGroupoid X _ M _ (pullbackChartedSpace hp) (gxGroupoid G X) := by
  refine @HasGroupoid.mk X _ M _ (pullbackChartedSpace hp) (gxGroupoid G X) ?_
  rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
  refine symm_trans_mem_gxGroupoid fun z hz => ?_
  simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.symm_source, hp.localInverseAt_symm] at hz
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid G X).chart_mem_maximalAtlas (p x))
    ((gxGroupoid G X).chart_mem_maximalAtlas (p x')) hz.1.2 hz.2.2
  refine ⟨g, ?_⟩
  filter_upwards [hp.continuous.continuousAt.eventually hg] with y hy
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hp.localInverseAt_symm]
  exact hy

omit [ContinuousConstSMul G X] in
/-- For the pulled-back structure, `p` is a morphism. Port of `GX.isGXMorphism_pullback`
(`lean-gx/GX/Structure/Basic.lean:818`). -/
theorem isGXMorphism_pullback {p : M → N} (hp : IsLocalHomeomorph p) :
    @IsGXMorphism G X _ _ _ M _ N _ (pullbackChartedSpace hp) _ p := by
  refine @IsGXMorphism.mk G X _ _ _ M _ N _ (pullbackChartedSpace hp) _ p hp.continuous
    fun x => ⟨1, Eventually.of_forall fun y => ?_⟩
  show chartAt X (p x) (p y) = (1 : G) • ((hp.localInverseAt x).symm.trans (chartAt X (p x))) y
  rw [one_smul, OpenPartialHomeomorph.coe_trans, Function.comp_apply, hp.localInverseAt_symm]

/-- **Uniqueness of the pull-back**: for any `(G,X)`-structure on `M` making `p` a morphism, the
maximal atlas is `gxPullbackAtlas G X p`. Port of `GX.IsGXMorphism.maximalAtlas_eq`
(`lean-gx/GX/Structure/Basic.lean:827`). -/
theorem IsGXMorphism.maximalAtlas_eq [ChartedSpace X M] [HasGroupoid M (gxGroupoid G X)]
    [HasGroupoid N (gxGroupoid G X)] {p : M → N} (hp : IsGXMorphism G X p) :
    (gxGroupoid G X).maximalAtlas M = gxPullbackAtlas G X p := by
  ext e
  constructor
  · intro he x hx
    exact hp.exists_smul_eq_of_mem_maximalAtlas he
      ((gxGroupoid G X).chart_mem_maximalAtlas (p x)) hx (mem_chart_source X (p x))
  · intro he
    rw [mem_maximalAtlas_iff_eventually]
    intro x hx
    obtain ⟨a, ha⟩ := he x hx
    obtain ⟨b, hb⟩ := hp.exists_smul_eq x
    refine ⟨a⁻¹ * b, ?_⟩
    filter_upwards [ha, hb] with y h1 h2
    rw [mul_smul, ← h2, h1, inv_smul_smul]

/-- **The étalé pull-back** (p. 238, « Tout ouvert étalé $E$ au-dessus d'une variété localement
projective $V$ est muni canoniquement d'une structure localement projective : l'unique structure
telle que la projection soit un morphisme »): along a local homeomorphism `p : M → N` there is a
`(G,X)`-structure on `M` making `p` a morphism, and any two such have the same maximal atlas. Port
of `GX.existsUnique_pullback` (`lean-gx/GX/Structure/Basic.lean:856`). -/
theorem existsUnique_pullback [HasGroupoid N (gxGroupoid G X)] {p : M → N}
    (hp : IsLocalHomeomorph p) :
    ∃ cs : ChartedSpace X M, @HasGroupoid X _ M _ cs (gxGroupoid G X) ∧
      @IsGXMorphism G X _ _ _ M _ N _ cs _ p ∧
      ∀ cs' : ChartedSpace X M, @HasGroupoid X _ M _ cs' (gxGroupoid G X) →
        @IsGXMorphism G X _ _ _ M _ N _ cs' _ p →
        @StructureGroupoid.maximalAtlas X M _ _ cs' (gxGroupoid G X) =
          @StructureGroupoid.maximalAtlas X M _ _ cs (gxGroupoid G X) := by
  refine ⟨pullbackChartedSpace hp, hasGroupoid_pullback hp, isGXMorphism_pullback hp,
    fun cs' hcs' hp' => ?_⟩
  have h1 := @IsGXMorphism.maximalAtlas_eq G X _ _ _ _ M _ N _ _ cs' hcs' _ p hp'
  have h2 := @IsGXMorphism.maximalAtlas_eq G X _ _ _ _ M _ N _ _ (pullbackChartedSpace hp)
    (hasGroupoid_pullback hp) _ p (isGXMorphism_pullback hp)
  rw [h1, h2]

/-- **Coverings** (p. 238, « En particulier, tout revêtement $R$ de $V$ est une variété localement
projective »): the case of a covering map. Port of `GX.existsUnique_pullback_of_isCoveringMap`
(`lean-gx/GX/Structure/Basic.lean:871`). -/
theorem existsUnique_pullback_of_isCoveringMap [HasGroupoid N (gxGroupoid G X)] {p : M → N}
    (hp : IsCoveringMap p) :
    ∃ cs : ChartedSpace X M, @HasGroupoid X _ M _ cs (gxGroupoid G X) ∧
      @IsGXMorphism G X _ _ _ M _ N _ cs _ p ∧
      ∀ cs' : ChartedSpace X M, @HasGroupoid X _ M _ cs' (gxGroupoid G X) →
        @IsGXMorphism G X _ _ _ M _ N _ cs' _ p →
        @StructureGroupoid.maximalAtlas X M _ _ cs' (gxGroupoid G X) =
          @StructureGroupoid.maximalAtlas X M _ _ cs (gxGroupoid G X) :=
  existsUnique_pullback hp.isLocalHomeomorph

end Pullback

/-! ### Push-forward along a surjective local homeomorphism; the quotient `V/G` -/

section Pushforward

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M] {N : Type y} [TopologicalSpace N]

/-- Two maps into `M` which agree at `z` and become equal near `z` after a local homeomorphism
`p : M → N` agree near `z` (local injectivity of `p`). -/
theorem eventually_eq_of_comp_eventually_eq {Z : Type*} [TopologicalSpace Z] {p : M → N}
    (hp : IsLocalHomeomorph p) {u v : Z → M} {z : Z} (hu : ContinuousAt u z) (hv : ContinuousAt v z)
    (huv : u z = v z) (h : ∀ᶠ w in 𝓝 z, p (u w) = p (v w)) : ∀ᶠ w in 𝓝 z, u w = v w := by
  obtain ⟨e, hxe, hpe⟩ := hp (u z)
  have h1 := hu.eventually (e.open_source.mem_nhds hxe)
  have h2 := hv.eventually (e.open_source.mem_nhds (huv ▸ hxe))
  filter_upwards [h1, h2, h] with w hw1 hw2 hw3
  exact e.injOn hw1 hw2 (by rw [← hpe]; exact hw3)

variable [ChartedSpace X M]

variable (G X) in
/-- **The local deck transformations of `p` are `(G,X)`-maps**: for `p x = p x'` there is a map
`τ`, continuous at `x`, with `τ x = x'` and `p ∘ τ = p` near `x`, which near `x` is an element of
`G` in the charts at `x` and `x'`. This is what makes the push-forward along `p` a structure (for
`V → V/G`, `τ` is an element of the group). -/
def IsGXDeck (p : M → N) : Prop :=
  ∀ x x' : M, p x = p x' → ∃ τ : M → M, ContinuousAt τ x ∧ τ x = x' ∧
    (∀ᶠ y in 𝓝 x, p (τ y) = p y) ∧ ∃ g : G, ∀ᶠ y in 𝓝 x, chartAt X x' (τ y) = g • chartAt X x y

variable [HasGroupoid M (gxGroupoid G X)]

/-- **The push-forward of a `(G,X)`-structure** along a surjective local homeomorphism `p` whose
local deck transformations are `(G,X)`-maps (`IsGXDeck`), for Mathlib's charted space
`IsLocalHomeomorph.chartedSpaceOfRightInverse` (the charts of `M` through local sections of `p`). -/
theorem hasGroupoid_chartedSpaceOfRightInverse {p : M → N} (hp : IsLocalHomeomorph p)
    {s : N → M} (hs : Function.RightInverse s p) (hdeck : IsGXDeck G X p) :
    @HasGroupoid X _ N _ (hp.chartedSpaceOfRightInverse hs) (gxGroupoid G X) := by
  refine @HasGroupoid.mk X _ N _ (hp.chartedSpaceOfRightInverse hs) (gxGroupoid G X) ?_
  rintro e e' ⟨q, rfl⟩ ⟨q', rfl⟩
  refine symm_trans_mem_gxGroupoid fun z hz => ?_
  set L := hp.localInverseAt (s q) with hL
  set L' := hp.localInverseAt (s q') with hL'
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source] at hz
  obtain ⟨⟨hzL, hzc⟩, ⟨hzL', hzc'⟩⟩ := hz
  have hpx : p (L z) = z := hp.apply_localInverseAt_of_mem hzL
  have hpx' : p (L' z) = z := hp.apply_localInverseAt_of_mem hzL'
  obtain ⟨τ, hτc, hτx, hτp, g, hg⟩ := hdeck (L z) (L' z) (hpx.trans hpx'.symm)
  have hLc : ContinuousAt L z := L.continuousAt hzL
  have hL'c : ContinuousAt L' z := L'.continuousAt hzL'
  have hτLc : ContinuousAt (τ ∘ L) z := hτc.comp hLc
  -- `L'` and `τ ∘ L` are two local sections through `L' z`
  have hsec : ∀ᶠ w in 𝓝 z, L' w = τ (L w) := by
    refine eventually_eq_of_comp_eventually_eq hp hL'c hτLc hτx.symm ?_
    filter_upwards [L'.open_source.mem_nhds hzL', L.open_source.mem_nhds hzL,
      hLc.eventually hτp] with w h1 h2 h3
    rw [hp.apply_localInverseAt_of_mem h1, h3, hp.apply_localInverseAt_of_mem h2]
  obtain ⟨a, ha⟩ := eventually_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid G X).chart_mem_maximalAtlas (L' z))
    ((gxGroupoid G X).chart_mem_maximalAtlas (s q')) (mem_chart_source X _) hzc'
  obtain ⟨b, hb⟩ := eventually_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid G X).chart_mem_maximalAtlas (L z))
    ((gxGroupoid G X).chart_mem_maximalAtlas (s q)) (mem_chart_source X _) hzc
  refine ⟨a * g * b⁻¹, ?_⟩
  have ha' : ∀ᶠ w in 𝓝 z, chartAt X (s q') (τ (L w)) = a • chartAt X (L' z) (τ (L w)) := by
    have : Tendsto (τ ∘ L) (𝓝 z) (𝓝 (L' z)) := by
      have := hτLc.tendsto; rwa [Function.comp_apply, hτx] at this
    exact this.eventually ha
  filter_upwards [hsec, ha', hLc.eventually hg, hLc.eventually hb] with w h1 h2 h3 h4
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  rw [h1, h2, h3, h4, mul_smul, mul_smul, inv_smul_smul]

omit [ContinuousConstSMul G X] [HasGroupoid M (gxGroupoid G X)] in
/-- For the push-forward structure, `p` is a morphism. -/
theorem isGXMorphism_chartedSpaceOfRightInverse {p : M → N} (hp : IsLocalHomeomorph p)
    {s : N → M} (hs : Function.RightInverse s p) (hdeck : IsGXDeck G X p) :
    @IsGXMorphism G X _ _ _ M _ N _ _ (hp.chartedSpaceOfRightInverse hs) p := by
  refine @IsGXMorphism.mk G X _ _ _ M _ N _ _ (hp.chartedSpaceOfRightInverse hs) p hp.continuous
    fun x => ?_
  set x' := s (p x) with hx'
  set L := hp.localInverseAt x' with hL
  have hpx : p x = p x' := (hs (p x)).symm
  obtain ⟨τ, hτc, hτx, hτp, g, hg⟩ := hdeck x x' hpx
  have hsrc : p x ∈ L.source := by rw [hpx]; exact hp.apply_self_mem_localInverseAt_source
  have hLp : ContinuousAt (L ∘ p) x := (L.continuousAt hsrc).comp hp.continuous.continuousAt
  have hLx : L (p x) = x' := by rw [hpx]; exact hp.localInverseAt_apply_self
  have hsec : ∀ᶠ y in 𝓝 x, L (p y) = τ y := by
    refine eventually_eq_of_comp_eventually_eq hp hLp hτc (hLx.trans hτx.symm) ?_
    filter_upwards [hp.continuous.continuousAt.eventually (L.open_source.mem_nhds hsrc), hτp]
      with y h1 h2
    show p (L (p y)) = p (τ y)
    rw [hp.apply_localInverseAt_of_mem h1, h2]
  refine ⟨g, ?_⟩
  filter_upwards [hsec, hg] with y h1 h2
  show chartAt X x' (L (p y)) = g • chartAt X x y
  rw [h1, h2]

/-- **Uniqueness of the push-forward**: along a surjective local homeomorphism `p`, a
`(G,X)`-structure on `N` for which `p` is a morphism has maximal atlas
`{e | ∀ x, p x ∈ e.source → e ∘ p is near x an element of G in the chart at x}`; it depends on `p`
and the structure of `M` alone. -/
theorem IsGXMorphism.maximalAtlas_eq_of_surjective [ChartedSpace X N]
    [HasGroupoid N (gxGroupoid G X)] {p : M → N} (hpm : IsGXMorphism G X p)
    (hsurj : Function.Surjective p) :
    (gxGroupoid G X).maximalAtlas N =
      {e | ∀ x : M, p x ∈ e.source → ∃ g : G, ∀ᶠ y in 𝓝 x, e (p y) = g • chartAt X x y} := by
  ext e
  constructor
  · intro he x hx
    exact hpm.exists_smul_eq_of_mem_maximalAtlas ((gxGroupoid G X).chart_mem_maximalAtlas x) he
      (mem_chart_source X x) hx
  · intro he
    rw [mem_maximalAtlas_iff_eventually]
    intro z hz
    obtain ⟨x, rfl⟩ := hsurj z
    obtain ⟨a, ha⟩ := he x hz
    obtain ⟨b, hb⟩ := hpm.exists_smul_eq x
    refine ⟨a * b⁻¹, ?_⟩
    rw [← hpm.isLocalHomeomorph.map_nhds_eq x, Filter.eventually_map]
    filter_upwards [ha, hb] with y h1 h2
    rw [h1, mul_smul, h2, inv_smul_smul]

/-- **The push-forward exists and is unique** (the structure of `V/G`, p. 238, in general): along a
surjective local homeomorphism whose deck transformations are `(G,X)`-maps, there is a unique
`(G,X)`-structure on `N` (up to its maximal atlas) for which `p` is a morphism. -/
theorem existsUnique_pushforward {p : M → N} (hp : IsLocalHomeomorph p)
    (hsurj : Function.Surjective p) (hdeck : IsGXDeck G X p) :
    ∃ cs : ChartedSpace X N, ∃ _ : @HasGroupoid X _ N _ cs (gxGroupoid G X),
      @IsGXMorphism G X _ _ _ M _ N _ _ cs p ∧
      ∀ cs' : ChartedSpace X N, ∀ _ : @HasGroupoid X _ N _ cs' (gxGroupoid G X),
        @IsGXMorphism G X _ _ _ M _ N _ _ cs' p →
        @StructureGroupoid.maximalAtlas X N _ _ cs' (gxGroupoid G X) =
          @StructureGroupoid.maximalAtlas X N _ _ cs (gxGroupoid G X) := by
  have hs := hsurj.hasRightInverse.choose_spec
  refine ⟨hp.chartedSpaceOfRightInverse hs, hasGroupoid_chartedSpaceOfRightInverse hp hs hdeck,
    isGXMorphism_chartedSpaceOfRightInverse hp hs hdeck, fun cs' hcs' hp' => ?_⟩
  have h1 := @IsGXMorphism.maximalAtlas_eq_of_surjective G X _ _ _ _ M _ N _ _ _ cs' hcs' p hp' hsurj
  have h2 := @IsGXMorphism.maximalAtlas_eq_of_surjective G X _ _ _ _ M _ N _ _ _
    (hp.chartedSpaceOfRightInverse hs) (hasGroupoid_chartedSpaceOfRightInverse hp hs hdeck) p
    (isGXMorphism_chartedSpaceOfRightInverse hp hs hdeck) hsurj
  rw [h1, h2]

end Pushforward

section Quotient

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {V : Type u} [TopologicalSpace V] [ChartedSpace X V]
  [HasGroupoid V (gxGroupoid G X)] {Γ : Type*} [Group Γ] [MulAction Γ V]

omit [ContinuousConstSMul G X] [HasGroupoid V (gxGroupoid G X)] in
/-- For a group `Γ` of automorphisms of `V`, the deck transformations of `V → V/Γ` are the
elements of `Γ`, hence `(G,X)`-maps. -/
theorem isGXDeck_quotientMk (hΓ : ∀ γ : Γ, IsGXMorphism G X fun v : V => γ • v) :
    IsGXDeck G X (Quotient.mk (MulAction.orbitRel Γ V)) := by
  intro x x' hxx'
  obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.1 (Quotient.exact hxx')
  replace hγ : γ • x' = x := hγ
  refine ⟨fun v => γ⁻¹ • v, (hΓ γ⁻¹).continuous.continuousAt, ?_, Eventually.of_forall fun y => ?_,
    ?_⟩
  · rw [← hγ]; exact inv_smul_smul γ x'
  · exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨γ⁻¹, rfl⟩)
  · obtain ⟨g, hg⟩ := (hΓ γ⁻¹).exists_smul_eq x
    have hx : γ⁻¹ • x = x' := by rw [← hγ, inv_smul_smul]
    exact ⟨g, by rw [← hx]; exact hg⟩

variable [ProperlyDiscontinuousSMul Γ V] [ContinuousConstSMul Γ V] [IsCancelSMul Γ V]
  [T2Space V] [LocallyCompactSpace V]

/-- **The quotient `V/Γ` is a `(G,X)`-manifold** (p. 238, « Soit $G$ un groupe proprement
discontinu sans point fixe, d'automorphismes de la structure localement projective de $V$ :
l'espace quotient $V/G$ est muni canoniquement d'une structure localement projective »), for
Mathlib's charted space on the quotient (`MulAction.instChartedSpaceQuotient`). The paper's group is
`Γ` here; « sans point fixe » is `IsCancelSMul`, « proprement discontinu »
`ProperlyDiscontinuousSMul`; `V` Hausdorff and locally compact (implicit in « variété »). -/
theorem hasGroupoid_quotient (hΓ : ∀ γ : Γ, IsGXMorphism G X fun v : V => γ • v) :
    HasGroupoid (MulAction.orbitRel.Quotient Γ V) (gxGroupoid G X) :=
  hasGroupoid_chartedSpaceOfRightInverse
    ((isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := Γ)
      (E := V)).isCoveringMap.isLocalHomeomorph)
    (Quotient.mk_surjective (s := MulAction.orbitRel Γ V)).hasRightInverse.choose_spec
    (isGXDeck_quotientMk hΓ)

omit [ContinuousConstSMul G X] [HasGroupoid V (gxGroupoid G X)] in
/-- The projection `V → V/Γ` is a morphism. -/
theorem isGXMorphism_quotientMk (hΓ : ∀ γ : Γ, IsGXMorphism G X fun v : V => γ • v) :
    IsGXMorphism G X (Quotient.mk (MulAction.orbitRel Γ V)) :=
  isGXMorphism_chartedSpaceOfRightInverse
    ((isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := Γ)
      (E := V)).isCoveringMap.isLocalHomeomorph)
    (Quotient.mk_surjective (s := MulAction.orbitRel Γ V)).hasRightInverse.choose_spec
    (isGXDeck_quotientMk hΓ)

/-- **« c'est l'unique structure pour laquelle la projection de $V$ sur $V/G$ soit un morphisme »**:
any `(G,X)`-structure on `V/Γ` making the projection a morphism has the maximal atlas of Mathlib's
charted space on the quotient (`hasGroupoid_quotient`). -/
theorem maximalAtlas_quotient_unique (hΓ : ∀ γ : Γ, IsGXMorphism G X fun v : V => γ • v) :
    ∀ (cs' : ChartedSpace X (MulAction.orbitRel.Quotient Γ V)),
      @HasGroupoid X _ _ _ cs' (gxGroupoid G X) →
      @IsGXMorphism G X _ _ _ V _ _ _ _ cs' (Quotient.mk (MulAction.orbitRel Γ V)) →
      @StructureGroupoid.maximalAtlas X _ _ _ cs' (gxGroupoid G X) =
        @StructureGroupoid.maximalAtlas X _ _ _
          (MulAction.instChartedSpaceQuotient (G := Γ) (M := V) (H := X)) (gxGroupoid G X) := by
  intro cs' hcs' hp'
  have h1 := @IsGXMorphism.maximalAtlas_eq_of_surjective G X _ _ _ _ V _ _ _ _ _ cs' hcs' _ hp'
    Quotient.mk_surjective
  have h2 := @IsGXMorphism.maximalAtlas_eq_of_surjective G X _ _ _ _ V _ _ _ _ _
    (MulAction.instChartedSpaceQuotient (G := Γ) (M := V) (H := X)) (hasGroupoid_quotient hΓ) _
    (isGXMorphism_quotientMk hΓ) Quotient.mk_surjective
  exact h1.trans h2.symm

end Quotient

end Benzecri
