import GX.BTZ.AbsMax

/-!
# btz § 5: BTZ-embeddings, BTZ-extensions, common sub- and over-BTZ-extensions, for `𝔼₀`-manifolds

Target `T-btz-embeddings` (`roadmap/roadmap.toml`, DEC-208). `papers/btz/legacy/labeled/BTZ_1.tex`.
None of the six rows is marked: every definition is stated for `𝔼₀`-manifolds only (DEC-116 (b),
DEC-125 (a)(e)), where the paper says `𝔼_{≥0}`; the rows stay partial until T-btz-scope rules.

* `btzdef:btz_extension_btz_embedding` — `BTZ_1.tex:323` — `GX.IsBTZEmbedding`,
  `GX.BTZExtension` (partial: `𝔼₀` only; « a.e. `𝔼`-morphism » read as `E0Spear.IsE0Mor`).
* `btzdef:common_sub_btz_extension` — `BTZ_1.tex:1302` — `GX.CommonSubBTZ` (partial: `𝔼₀`).
* `btzdef:morphism_common_sub_extension` — `BTZ_1.tex:1317` — `GX.CommonSubBTZ.IsMorphism`,
  `GX.CommonSubBTZ.Equivalent` (partial: `𝔼₀`).
* `btzdef:maximal_common_sub_btz_extension` — `BTZ_1.tex:1332` — `GX.CommonSubBTZ.IsMaximal`
  (partial: `𝔼₀`).
* `btzdef:common_over_btz_extension` — `BTZ_1.tex:1381` — `GX.CommonOverBTZ` (partial: `𝔼₀`).
* `btzdef:morphism_common_over_btz_extension` — `BTZ_1.tex:1397` —
  `GX.CommonOverBTZ.IsMorphism`, `GX.CommonOverBTZ.Equivalent` (partial: `𝔼₀`).

> Let $M$ be a $\mass{\geq 0}$-manifold. A BTZ-extension of $M$ is an embedding of
> $M\xrightarrow{\iota} N$ where $N$ is a $\mass{\geq 0}$-manifold and $\iota$ an a.e
> $\mass{}$-morphism and such that the complement of the image of $\iota$ only contains singular
> points of type $\mass{0}$. Such a map $\iota$ is called a BTZ-embedding. (l.325–327)
>
> since any $\mass{\geq0}$-manifold is a 3-manifold, an a.e $\mass{}$-morphism is an embedding if
> and only if it is injective (l.1264)
>
> A common sub-BTZ-extension to $M_1$ and $M_2$ is BTZ-extension $M_0\rightarrow M$ together with
> two BTZ-embeddings $M\xrightarrow{a} M_1$, $M \rightarrow M_2$ such that the following diagram
> commutes (l.1309)
>
> A morphism of sub-BTZ-extension is a $\mass{\geq0}$-morphism $M\xrightarrow{~~\phi~~} M'$ such
> that the following diagram commutes […] If $\phi$ is bijective, then $M$ and $M'$ are equivalent.
> (l.1320, 1330)
>
> $M$ is maximal if for all common sub-BTZ-extension $M'$ to $M_1$ and $M_2$, there exists an
> injective morphism of common sub-BTZ-extension from $M'$ to $M$. (l.1336)
>
> A common over-BTZ-extension BTZ to $M_1$ and $M_2$ is a $\mass{\geq0}$-manifold $M$ together
> with BTZ-embeddings $M_1\xrightarrow{a} M$; $M_2 \xrightarrow{b} M$ such that the following
> diagram commutes (l.1384)
>
> A morphism of over-BTZ-extensions from $M$ to $M'$ is a $\mass{\geq0}$-morphism
> $M\xrightarrow{~~\phi~~} M'$ such that the following diagram commutes […] If $\phi$ is bijective
> then $M$ and $M'$ are equivalent. (l.1401, 1411)

## Hypothesis checklist

| paper | here |
|---|---|
| `𝔼_{≥0}`-manifolds | ⚠ `𝔼₀` only (DEC-116 (b), DEC-125 (a)(e); T-btz-scope): `ChartedSpace E0Y`, `HasGroupoid e0Groupoid` |
| a singular manifold is second countable Hausdorff (l.261) | ✓ carried by `GX.E0Mfd` (the carriers); not required connected (l.261 does not; DEC-66 adds it for Prop 2.16–2.17 only) |
| « embedding » (l.325) | ✓ carried literally (`IsEmbedding`); equivalent to injectivity (`GX.isBTZEmbedding_iff_injective`, l.1264) and to an open embedding (`IsBTZEmbedding.isOpenEmbedding`), with no invariance of domain: an `IsE0Mor` is a local homeomorphism by definition |
| « a.e. `𝔼`-morphism » (l.325; defined l.263, l.359) | ⚠ read: `E0Spear.IsE0Mor ι univ` (DEC-62's local form, `LiftPropOn` of `e0Groupoid`, the a.e.-isomorphisms of `Y`): a local homeomorphism preserving the type of points. The paper's l.263 form (continuous, a `(G,X)`-morphism on dense locally connected opens of the regular parts) agrees with it on embeddings only through the invariance of the type of a point (a BTZ point is not sent to a regular one), not formalized here |
| « complement of the image only contains singular points of type `𝔼₀` » | ✓ `(range ι)ᶜ ⊆ S0 N` |
| the source and targets of `i`, `j` are BTZ-extensions | ⚠ weakened: `i`, `j` arbitrary maps (BTZ-ness of `i` follows from `b ∘ a = i`) |

## SCOPE (disclosed)

The six definitions and their API: identity and composition (`isBTZEmbedding_id`,
`IsBTZEmbedding.comp`, the AbstractDev shape `GX.btzMor` on the bundled `GX.E0Mfd`), types of
points preserved (`GX.mem_S0_iff_of_isE0Mor`), density of the image (`IsBTZEmbedding.dense_range`),
the bridge to `GX.BTZ.AbsMax`'s open-set form (`GX.isBTZEmbedding_subtypeVal_iff`,
`IsBTZEmbedding.rangeOpens`, the inverse onto the image `IsBTZEmbedding.isE0Mor_invFunOn`),
uniqueness of maps fixed on the image (`IsBTZEmbedding.ext`, l.1352) and Liouville for
`𝔼₀`-morphisms (`GX.eq_of_isE0Mor_of_eqOn`, l.361, from `GX.e0_rigid`). Morphisms of common
sub-extensions are unique, injective, BTZ-embeddings, and commute with `a`; two maximal common
sub-extensions are equivalent; equivalence is an equivalence relation on both sides.
`Reg N ↪ N` is a BTZ-embedding (`GX.isBTZEmbedding_regM`, the extension of btzcor:common_reg);
`E0Y` is an `E0Mfd` (`GX.E0Mfd.model`) and `CommonSubBTZ.base` a common sub-extension, so the
predicates are inhabited. Nothing of btzprop:pgcd / btzprop:ppcm (existence) is claimed.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; lean-causal as pinned
in `lake-manifest.json`.
-/

namespace GX

open Set Filter Topology Function TopologicalSpace
open E0CBG E0Spear

/-! ### §1 BTZ-embeddings -/

section Embedding

variable {M N P : Type} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [ChartedSpace E0Y M] [ChartedSpace E0Y N] [ChartedSpace E0Y P]

/-- **`btzdef:btz_extension_btz_embedding`, the BTZ-embedding** (`BTZ_1.tex:325–327`): a
topological embedding `ι : M → N` which is an (a.e.) `𝔼₀`-morphism and whose image misses only
BTZ points of `N`. -/
def IsBTZEmbedding (ι : M → N) : Prop :=
  IsEmbedding ι ∧ IsE0Mor ι univ ∧ (range ι)ᶜ ⊆ S0 N

/-- An `𝔼₀`-morphism on `univ` is an open map (it is a local homeomorphism by definition). -/
theorem isOpenMap_of_isE0Mor {f : M → N} (hf : IsE0Mor f univ) : IsOpenMap f := by
  intro V hV
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hxV, rfl⟩
  obtain ⟨O, hxO, -, hO⟩ := (Causal.CBG.liftPropOn_iff_repOn isOpen_univ).1 hf x (mem_univ x)
  have hO' := hO.mono (hO.1.inter hV) inter_subset_left
  exact mem_of_superset (hO'.isOpen_image.mem_nhds (mem_image_of_mem f ⟨hxO, hxV⟩))
    (image_mono inter_subset_right)

/-- **An `𝔼₀`-morphism preserves and reflects the BTZ points** (`cor:model_corresponding`). -/
theorem mem_S0_iff_of_isE0Mor {f : M → N} (hf : IsE0Mor f univ) (x : M) :
    f x ∈ S0 N ↔ x ∈ S0 M := by
  exact (Causal.CBG.mem_chartedSing_iff_of_liftPropOn e0_sing_mem isOpen_univ hf (mem_univ x)
    le_rfl).symm

/-- **l.1264**: an `𝔼₀`-morphism is an embedding iff it is injective. -/
theorem isBTZEmbedding_iff_injective {ι : M → N} :
    IsBTZEmbedding ι ↔ Injective ι ∧ IsE0Mor ι univ ∧ (range ι)ᶜ ⊆ S0 N := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1.injective, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(IsOpenEmbedding.of_continuous_injective_isOpenMap
      (E0AbsMax.continuous_of_isE0Mor h2) h1 (isOpenMap_of_isE0Mor h2)).isEmbedding, h2, h3⟩

namespace IsBTZEmbedding

variable {ι : M → N}

theorem isEmbedding (h : IsBTZEmbedding ι) : IsEmbedding ι := h.1

theorem isE0Mor (h : IsBTZEmbedding ι) : IsE0Mor ι univ := h.2.1

theorem compl_range_subset (h : IsBTZEmbedding ι) : (range ι)ᶜ ⊆ S0 N := h.2.2

theorem injective (h : IsBTZEmbedding ι) : Injective ι := h.1.injective

theorem continuous (h : IsBTZEmbedding ι) : Continuous ι := h.1.continuous

/-- A BTZ-embedding is an open embedding. -/
theorem isOpenEmbedding (h : IsBTZEmbedding ι) : IsOpenEmbedding ι := by
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap h.continuous h.injective
    (isOpenMap_of_isE0Mor h.isE0Mor)

theorem isOpen_range (h : IsBTZEmbedding ι) : IsOpen (range ι) := h.isOpenEmbedding.isOpen_range

/-- **The image of a BTZ-embedding is dense** (`BTZ_1.tex:1356`): its complement is BTZ, and the
BTZ locus has empty interior. -/
theorem dense_range [HasGroupoid N e0Groupoid] (h : IsBTZEmbedding ι) : Dense (range ι) := by
  refine (E0LM.dense_e0RegM (M := N)).mono fun y hy => ?_
  by_contra hn
  exact hy (h.compl_range_subset hn)

/-- A BTZ-embedding preserves and reflects the BTZ points. -/
theorem mem_S0_iff (h : IsBTZEmbedding ι) (x : M) : ι x ∈ S0 N ↔ x ∈ S0 M :=
  mem_S0_iff_of_isE0Mor h.isE0Mor x

omit [ChartedSpace E0Y P] in
/-- **Uniqueness of a map fixed on the image** (`BTZ_1.tex:1354`, « unique since it continuous and
equal to `j ∘ i⁻¹` on `reg(M)` which is dense »): two continuous maps into a Hausdorff space which
agree after a BTZ-embedding are equal. -/
theorem ext [HasGroupoid N e0Groupoid] [T2Space P] (h : IsBTZEmbedding ι) {f g : N → P}
    (hf : Continuous f) (hg : Continuous g) (hfg : f ∘ ι = g ∘ ι) : f = g := by
  refine Continuous.ext_on h.dense_range hf hg ?_
  rintro _ ⟨x, rfl⟩
  exact congrFun hfg x

/-- **The open-set form of `GX.BTZ.AbsMax`**: the image of a BTZ-embedding, an open set with BTZ
complement. -/
def rangeOpens (h : IsBTZEmbedding ι) : Opens N := ⟨range ι, h.isOpen_range⟩

theorem coe_rangeOpens (h : IsBTZEmbedding ι) : (h.rangeOpens : Set N) = range ι := rfl

theorem compl_rangeOpens_subset (h : IsBTZEmbedding ι) : (h.rangeOpens : Set N)ᶜ ⊆ S0 N :=
  h.compl_range_subset

/-- **The inverse onto the image is an `𝔼₀`-morphism**: a BTZ-embedding is an `𝔼₀`-isomorphism
of `M` onto the open `ι(M)`. -/
theorem isE0Mor_invFunOn [Nonempty M] (h : IsBTZEmbedding ι) :
    IsE0Mor (invFunOn ι univ) (range ι) := by
  have := Causal.CBG.liftPropOn_invFunOn isOpen_univ h.isE0Mor h.injective.injOn
  rwa [image_univ] at this

/-- **Composition of BTZ-embeddings.** -/
theorem comp {κ : N → P} (hκ : IsBTZEmbedding κ) (hι : IsBTZEmbedding ι) :
    IsBTZEmbedding (κ ∘ ι) := by
  refine ⟨hκ.isEmbedding.comp hι.isEmbedding,
    Causal.CBG.liftPropOn_comp isOpen_univ isOpen_univ hκ.isE0Mor hι.isE0Mor (mapsTo_univ _ _),
    fun y hy => ?_⟩
  by_cases hyκ : y ∈ range κ
  · obtain ⟨x, rfl⟩ := hyκ
    have hx : x ∉ range ι := fun ⟨w, hw⟩ => hy ⟨w, by simp [hw]⟩
    exact (hκ.mem_S0_iff x).2 (hι.compl_range_subset hx)
  · exact hκ.compl_range_subset hyκ

end IsBTZEmbedding

/-- **The identity is a BTZ-embedding.** -/
theorem isBTZEmbedding_id : IsBTZEmbedding (id : M → M) := by
  refine isBTZEmbedding_iff_injective.2 ⟨injective_id, Causal.CBG.liftPropOn_id isOpen_univ, ?_⟩
  rw [range_id, compl_univ]
  exact empty_subset _

/-- A bijective `𝔼₀`-morphism is a BTZ-embedding. -/
theorem isBTZEmbedding_of_bijective {f : M → N} (hf : IsE0Mor f univ) (hb : Bijective f) :
    IsBTZEmbedding f := by
  refine isBTZEmbedding_iff_injective.2 ⟨hb.1, hf, ?_⟩
  rw [hb.2.range_eq, compl_univ]
  exact empty_subset _

/-- **The bridge to the open-set form** (`GX.BTZ.AbsMax`, kb/0001 of lean-causal): the inclusion
of an open `A ⊆ N` is a BTZ-embedding iff `Aᶜ ⊆ sing₀(N)`. -/
theorem isBTZEmbedding_subtypeVal_iff [HasGroupoid N e0Groupoid] (A : Opens N) :
    IsBTZEmbedding (Subtype.val : A → N) ↔ (A : Set N)ᶜ ⊆ S0 N := by
  have hQ : ∀ y : E0Y, e0Groupoid.IsLocalStructomorphWithinAt id univ y := fun y _ =>
    ⟨OpenPartialHomeomorph.refl E0Y, e0Groupoid.id_mem, fun _ _ => rfl, mem_univ y⟩
  have hmor : IsE0Mor (Subtype.val : A → N) univ := by
    show ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt (Subtype.val : A → N) univ
    rw [StructureGroupoid.liftPropOn_univ]
    exact (StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp
      e0Groupoid).liftProp_subtype_val hQ A
  rw [IsBTZEmbedding, Subtype.range_coe]
  exact ⟨fun h => h.2.2, fun h => ⟨IsEmbedding.subtypeVal, hmor, h⟩⟩

/-- **`Reg N ↪ N` is a BTZ-embedding**: an `𝔼₀`-manifold is a BTZ-extension of its regular
part (the inclusion behind btzcor:common_reg, `M ≃ Ext_BTZ(Reg M)`). -/
theorem isBTZEmbedding_regM [HasGroupoid N e0Groupoid] :
    IsBTZEmbedding (Subtype.val : E0LM.e0RegM N → N) :=
  (isBTZEmbedding_subtypeVal_iff _).2 fun _ hy => by_contra fun hn => hy hn

/-- **Liouville for `𝔼₀`-morphisms** (`btzlem:liouville`, `BTZ_1.tex:361`, at `𝔼₀`): two
`𝔼₀`-morphisms of a connected `M` into a Hausdorff `N` which agree on a non-empty open set are
equal (`GX.e0_rigid`, `Causal.CBG.eqOn_of_liftPropOn`). -/
theorem eq_of_isE0Mor_of_eqOn [PreconnectedSpace M] [T2Space N] {f g : M → N}
    (hf : IsE0Mor f univ) (hg : IsE0Mor g univ) {O : Set M} (hO : IsOpen O) (hne : O.Nonempty)
    (hfg : EqOn f g O) : f = g := by
  have h := Causal.CBG.eqOn_of_liftPropOn e0_rigid isOpen_univ isPreconnected_univ hf hg hO
    (subset_univ O) hne hfg
  exact funext fun x => h (mem_univ x)

/-- **The inverse of a bijective `𝔼₀`-morphism is an `𝔼₀`-morphism.** -/
theorem isE0Mor_inv_of_bijective {f : M → N} (hf : IsE0Mor f univ) (hb : Bijective f) :
    ∃ g : N → M, IsE0Mor g univ ∧ g ∘ f = id ∧ f ∘ g = id := by
  refine ⟨surjInv hb.2, ?_, funext (leftInverse_surjInv hb), funext (rightInverse_surjInv hb.2)⟩
  rcases isEmpty_or_nonempty M with hM | hM
  · intro y
    obtain ⟨x, -⟩ := hb.2 y
    exact isEmptyElim x
  · have h := Causal.CBG.liftPropOn_invFunOn isOpen_univ hf hb.1.injOn
    rw [image_univ, hb.2.range_eq] at h
    refine Causal.CBG.liftPropOn_congr_of_eqOn isOpen_univ h fun y _ => ?_
    apply hb.1
    rw [rightInverse_surjInv hb.2 y]
    exact invFunOn_eq (f := f) (s := univ) (by obtain ⟨x, hx⟩ := hb.2 y; exact ⟨x, mem_univ x, hx⟩)

end Embedding

/-! ### §2 Bundled `𝔼₀`-manifolds, BTZ-extensions, and the AbstractDev shape -/

/-- **An `𝔼₀`-manifold** (`BTZ_1.tex:261`: « a second countable Hausdorff topological space `M`
endowed with an almost everywhere `(Isom₀(𝔼), 𝔼)`-structure », at `A = {0}`): a carrier with an
`E0Y`-atlas in `e0Groupoid`, Hausdorff and second countable. Not required connected. -/
structure E0Mfd where
  /-- The carrier. -/
  carrier : Type
  [top : TopologicalSpace carrier]
  [t2 : T2Space carrier]
  [sc : SecondCountableTopology carrier]
  [cs : ChartedSpace E0Y carrier]
  [hg : HasGroupoid carrier e0Groupoid]

attribute [instance] E0Mfd.top E0Mfd.t2 E0Mfd.sc E0Mfd.cs E0Mfd.hg

instance : CoeSort E0Mfd Type := ⟨E0Mfd.carrier⟩

/-- The model space `Y = 𝕄 ⊕ 𝔼₀` as an `𝔼₀`-manifold (sanity: `E0Mfd` is inhabited). -/
noncomputable def E0Mfd.model : E0Mfd := ⟨E0Y⟩

/-- The bundled `𝔼₀`-manifold of a type. -/
def E0Mfd.of (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace E0Y M] [HasGroupoid M e0Groupoid] : E0Mfd := ⟨M⟩

/-- **The morphism class of the BTZ-extension problem** (the shape of `Causal.AbstractDev`: a type
of developments `E0Mfd`, carriers `E0Mfd.carrier`, a morphism predicate). -/
def btzMor (X Y : E0Mfd) (f : X → Y) : Prop := IsBTZEmbedding f

theorem btzMor_id (X : E0Mfd) : btzMor X X id := isBTZEmbedding_id

theorem btzMor_comp {X Y Z : E0Mfd} {f : X → Y} {g : Y → Z} (hf : btzMor X Y f)
    (hg : btzMor Y Z g) : btzMor X Z (g ∘ f) := IsBTZEmbedding.comp hg hf

section Extension

variable (M : Type) [TopologicalSpace M] [ChartedSpace E0Y M]

/-- **`btzdef:btz_extension_btz_embedding`, the BTZ-extension** (`BTZ_1.tex:325`): an
`𝔼₀`-manifold `N` with a BTZ-embedding `M → N`. -/
structure BTZExtension where
  /-- The extension. -/
  N : E0Mfd
  /-- The BTZ-embedding. -/
  ι : M → N
  isBTZ : IsBTZEmbedding ι

/-- The trivial BTZ-extension. -/
def BTZExtension.refl (M : E0Mfd) : BTZExtension M := ⟨M, id, isBTZEmbedding_id⟩

end Extension

/-! ### §3 Common sub-BTZ-extensions (`BTZ_1.tex:1302–1337`) -/

section Sub

variable {M₀ M₁ M₂ : Type} [TopologicalSpace M₀] [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace E0Y M₀] [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂]

variable (i : M₀ → M₁) (j : M₀ → M₂) in
/-- `btzdef:common_sub_btz_extension` (unmarked) (`BTZ_1.tex:1306`): a BTZ-extension `a : M₀ → X`
with two BTZ-embeddings `b : X → M₁`, `c : X → M₂` such that `b ∘ a = i` and `c ∘ a = j`. -/
structure CommonSubBTZ where
  /-- The common sub-extension. -/
  X : E0Mfd
  a : M₀ → X
  b : X → M₁
  c : X → M₂
  ha : IsBTZEmbedding a
  hb : IsBTZEmbedding b
  hc : IsBTZEmbedding c
  comm₁ : b ∘ a = i
  comm₂ : c ∘ a = j

namespace CommonSubBTZ

variable {i : M₀ → M₁} {j : M₀ → M₂}

/-- `btzdef:morphism_common_sub_extension` (unmarked) (`BTZ_1.tex:1322`): an `𝔼₀`-morphism commuting
with the embeddings into `M₁` and `M₂`. -/
def IsMorphism (X Y : CommonSubBTZ i j) (φ : X.X → Y.X) : Prop :=
  IsE0Mor φ univ ∧ Y.b ∘ φ = X.b ∧ Y.c ∘ φ = X.c

/-- **`btzdef:morphism_common_sub_extension`, equivalence** (`BTZ_1.tex:1330`): a bijective
morphism. -/
def Equivalent (X Y : CommonSubBTZ i j) : Prop :=
  ∃ φ : X.X → Y.X, X.IsMorphism Y φ ∧ Bijective φ

/-- `btzdef:maximal_common_sub_btz_extension` (unmarked) (`BTZ_1.tex:1336`): every common
sub-BTZ-extension has an injective morphism into `X`. -/
def IsMaximal (X : CommonSubBTZ i j) : Prop :=
  ∀ Y : CommonSubBTZ i j, ∃ φ : Y.X → X.X, Y.IsMorphism X φ ∧ Injective φ

/-- The trivial common sub-extension `M₀` itself. -/
def base [T2Space M₀] [SecondCountableTopology M₀] [HasGroupoid M₀ e0Groupoid]
    (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j) : CommonSubBTZ i j where
  X := E0Mfd.of M₀
  a := id
  b := i
  c := j
  ha := isBTZEmbedding_id
  hb := hi
  hc := hj
  comm₁ := rfl
  comm₂ := rfl

theorem isMorphism_id (X : CommonSubBTZ i j) : X.IsMorphism X id := by
  exact ⟨Causal.CBG.liftPropOn_id isOpen_univ, rfl, rfl⟩

theorem IsMorphism.comp {X Y Z : CommonSubBTZ i j} {φ : X.X → Y.X} {ψ : Y.X → Z.X}
    (hψ : Y.IsMorphism Z ψ) (hφ : X.IsMorphism Y φ) : X.IsMorphism Z (ψ ∘ φ) := by
  refine ⟨Causal.CBG.liftPropOn_comp isOpen_univ isOpen_univ hψ.1 hφ.1 (mapsTo_univ _ _), ?_, ?_⟩
  · rw [← comp_assoc, hψ.2.1, hφ.2.1]
  · rw [← comp_assoc, hψ.2.2, hφ.2.2]

/-- A morphism of common sub-extensions is injective. -/
theorem IsMorphism.injective {X Y : CommonSubBTZ i j} {φ : X.X → Y.X} (h : X.IsMorphism Y φ) :
    Injective φ := by
  intro x y hxy
  apply X.hb.injective
  have hx := congrFun h.2.1 x
  have hy := congrFun h.2.1 y
  simp only [comp_apply] at hx hy
  rw [← hx, ← hy, hxy]

/-- A morphism of common sub-extensions commutes with the extensions of `M₀`. -/
theorem IsMorphism.comp_a {X Y : CommonSubBTZ i j} {φ : X.X → Y.X} (h : X.IsMorphism Y φ) :
    φ ∘ X.a = Y.a := by
  funext x
  apply Y.hb.injective
  have h0 := congrFun h.2.1 (X.a x)
  have h1 := congrFun X.comm₁ x
  have h2 := congrFun Y.comm₁ x
  simp only [comp_apply] at h0 h1 h2 ⊢
  rw [h0, h1, h2]

/-- A morphism of common sub-extensions is a BTZ-embedding. -/
theorem IsMorphism.isBTZEmbedding {X Y : CommonSubBTZ i j} {φ : X.X → Y.X}
    (h : X.IsMorphism Y φ) : IsBTZEmbedding φ := by
  refine isBTZEmbedding_iff_injective.2 ⟨h.injective, h.1, fun y hy => ?_⟩
  have hb : Y.b y ∉ range X.b := by
    rintro ⟨x, hx⟩
    apply hy
    refine ⟨x, Y.hb.injective ?_⟩
    rw [← hx, ← congrFun h.2.1 x, comp_apply]
  exact (Y.hb.mem_S0_iff y).1 (X.hb.compl_range_subset hb)

/-- **Morphisms of common sub-extensions are unique.** -/
theorem IsMorphism.unique {X Y : CommonSubBTZ i j} {φ ψ : X.X → Y.X} (hφ : X.IsMorphism Y φ)
    (hψ : X.IsMorphism Y ψ) : φ = ψ := by
  funext x
  apply Y.hb.injective
  have h1 := congrFun hφ.2.1 x
  have h2 := congrFun hψ.2.1 x
  simp only [comp_apply] at h1 h2
  rw [h1, h2]

/-- The inverse of a bijective morphism is a morphism. -/
theorem IsMorphism.inv {X Y : CommonSubBTZ i j} {φ : X.X → Y.X} (h : X.IsMorphism Y φ)
    (hb : Bijective φ) : ∃ ψ : Y.X → X.X, Y.IsMorphism X ψ ∧ Bijective ψ ∧ ψ ∘ φ = id ∧
      φ ∘ ψ = id := by
  obtain ⟨g, hg, hgf, hfg⟩ := isE0Mor_inv_of_bijective h.1 hb
  have hfg' : ∀ y, φ (g y) = y := fun y => congrFun hfg y
  have hgf' : ∀ x, g (φ x) = x := fun x => congrFun hgf x
  refine ⟨g, ⟨hg, ?_, ?_⟩, ⟨fun a b hab => by rw [← hfg' a, ← hfg' b, hab],
    fun x => ⟨φ x, hgf' x⟩⟩, hgf, hfg⟩
  · funext y
    show X.b (g y) = Y.b y
    rw [← congrFun h.2.1 (g y), comp_apply, hfg' y]
  · funext y
    show X.c (g y) = Y.c y
    rw [← congrFun h.2.2 (g y), comp_apply, hfg' y]

theorem Equivalent.refl (X : CommonSubBTZ i j) : X.Equivalent X :=
  ⟨id, X.isMorphism_id, bijective_id⟩

theorem Equivalent.symm {X Y : CommonSubBTZ i j} (h : X.Equivalent Y) : Y.Equivalent X := by
  obtain ⟨φ, hφ, hb⟩ := h
  obtain ⟨ψ, hψ, hψb, -⟩ := hφ.inv hb
  exact ⟨ψ, hψ, hψb⟩

theorem Equivalent.trans {X Y Z : CommonSubBTZ i j} (h : X.Equivalent Y) (h' : Y.Equivalent Z) :
    X.Equivalent Z := by
  obtain ⟨φ, hφ, hb⟩ := h
  obtain ⟨ψ, hψ, hb'⟩ := h'
  exact ⟨ψ ∘ φ, hψ.comp hφ, hb'.comp hb⟩

/-- The injectivity in `IsMaximal` is automatic. -/
theorem isMaximal_iff (X : CommonSubBTZ i j) :
    X.IsMaximal ↔ ∀ Y : CommonSubBTZ i j, ∃ φ : Y.X → X.X, Y.IsMorphism X φ := by
  exact ⟨fun h Y => (h Y).imp fun _ hφ => hφ.1, fun h Y => (h Y).imp fun _ hφ => ⟨hφ, hφ.injective⟩⟩

/-- **Two maximal common sub-BTZ-extensions are equivalent.** -/
theorem IsMaximal.equivalent {X Y : CommonSubBTZ i j} (hX : X.IsMaximal) (hY : Y.IsMaximal) :
    X.Equivalent Y := by
  obtain ⟨ψ, hψ, -⟩ := hY X
  obtain ⟨φ, hφ, -⟩ := hX Y
  have h1 : φ ∘ ψ = id := (hφ.comp hψ).unique X.isMorphism_id
  have h2 : ψ ∘ φ = id := (hψ.comp hφ).unique Y.isMorphism_id
  refine ⟨ψ, hψ, fun a b hab => ?_, fun y => ⟨φ y, congrFun h2 y⟩⟩
  have ha : φ (ψ a) = a := congrFun h1 a
  have hb : φ (ψ b) = b := congrFun h1 b
  rw [← ha, ← hb, hab]

/-- When `i` is bijective, the trivial common sub-extension is maximal (sanity of `IsMaximal`). -/
theorem base_isMaximal [T2Space M₀] [SecondCountableTopology M₀] [HasGroupoid M₀ e0Groupoid]
    (hi : IsBTZEmbedding i) (hj : IsBTZEmbedding j) (hbij : Bijective i) :
    (base hi hj).IsMaximal := by
  obtain ⟨g, hg, hgi, hig⟩ := isE0Mor_inv_of_bijective hi.isE0Mor hbij
  intro Y
  -- every point of `Y` is in the image of `Y.a`
  have hYa : ∀ y, Y.a (g (Y.b y)) = y := fun y => by
    apply Y.hb.injective
    rw [← comp_apply (f := Y.b), Y.comm₁]
    exact congrFun hig (Y.b y)
  refine ⟨g ∘ Y.b, ⟨Causal.CBG.liftPropOn_comp isOpen_univ isOpen_univ hg Y.hb.isE0Mor
    (mapsTo_univ _ _), ?_, ?_⟩, ?_⟩
  · funext y
    show i (g (Y.b y)) = Y.b y
    exact congrFun hig (Y.b y)
  · funext y
    show j (g (Y.b y)) = Y.c y
    conv_rhs => rw [← hYa y]
    rw [← comp_apply (f := Y.c), Y.comm₂]
  · intro a b hab
    rw [← hYa a, ← hYa b]
    simp only [comp_apply] at hab
    rw [hab]

end CommonSubBTZ

end Sub

/-! ### §4 Common over-BTZ-extensions (`BTZ_1.tex:1381–1412`) -/

section Over

variable {M₀ M₁ M₂ : Type} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [ChartedSpace E0Y M₁] [ChartedSpace E0Y M₂]

variable (i : M₀ → M₁) (j : M₀ → M₂) in
/-- `btzdef:common_over_btz_extension` (unmarked) (`BTZ_1.tex:1385`): an `𝔼₀`-manifold `X` with
BTZ-embeddings `a : M₁ → X`, `b : M₂ → X` such that `a ∘ i = b ∘ j`. -/
structure CommonOverBTZ where
  /-- The common over-extension. -/
  X : E0Mfd
  a : M₁ → X
  b : M₂ → X
  ha : IsBTZEmbedding a
  hb : IsBTZEmbedding b
  comm : a ∘ i = b ∘ j

namespace CommonOverBTZ

variable {i : M₀ → M₁} {j : M₀ → M₂}

/-- `btzdef:morphism_common_over_btz_extension` (unmarked) (`BTZ_1.tex:1401`): an `𝔼₀`-morphism
commuting with the embeddings of `M₁` and `M₂`. -/
def IsMorphism (X Y : CommonOverBTZ i j) (φ : X.X → Y.X) : Prop :=
  IsE0Mor φ univ ∧ φ ∘ X.a = Y.a ∧ φ ∘ X.b = Y.b

/-- **`btzdef:morphism_common_over_btz_extension`, equivalence** (`BTZ_1.tex:1411`): a bijective
morphism. -/
def Equivalent (X Y : CommonOverBTZ i j) : Prop :=
  ∃ φ : X.X → Y.X, X.IsMorphism Y φ ∧ Bijective φ

theorem isMorphism_id (X : CommonOverBTZ i j) : X.IsMorphism X id := by
  exact ⟨Causal.CBG.liftPropOn_id isOpen_univ, rfl, rfl⟩

theorem IsMorphism.comp {X Y Z : CommonOverBTZ i j} {φ : X.X → Y.X} {ψ : Y.X → Z.X}
    (hψ : Y.IsMorphism Z ψ) (hφ : X.IsMorphism Y φ) : X.IsMorphism Z (ψ ∘ φ) := by
  refine ⟨Causal.CBG.liftPropOn_comp isOpen_univ isOpen_univ hψ.1 hφ.1 (mapsTo_univ _ _), ?_, ?_⟩
  · rw [comp_assoc, hφ.2.1, hψ.2.1]
  · rw [comp_assoc, hφ.2.2, hψ.2.2]

/-- **Morphisms of common over-extensions are unique**: they are fixed on the dense image of
`M₁`. -/
theorem IsMorphism.unique {X Y : CommonOverBTZ i j} {φ ψ : X.X → Y.X} (hφ : X.IsMorphism Y φ)
    (hψ : X.IsMorphism Y ψ) : φ = ψ := by
  refine X.ha.ext (E0AbsMax.continuous_of_isE0Mor hφ.1)
    (E0AbsMax.continuous_of_isE0Mor hψ.1) ?_
  rw [hφ.2.1, hψ.2.1]

theorem Equivalent.refl (X : CommonOverBTZ i j) : X.Equivalent X :=
  ⟨id, X.isMorphism_id, bijective_id⟩

theorem Equivalent.symm {X Y : CommonOverBTZ i j} (h : X.Equivalent Y) : Y.Equivalent X := by
  obtain ⟨φ, hφ, hb⟩ := h
  obtain ⟨g, hg, hgf, hfg⟩ := isE0Mor_inv_of_bijective hφ.1 hb
  have hfg' : ∀ y, φ (g y) = y := fun y => congrFun hfg y
  have hgf' : ∀ x, g (φ x) = x := fun x => congrFun hgf x
  refine ⟨g, ⟨hg, ?_, ?_⟩, fun a b hab => by rw [← hfg' a, ← hfg' b, hab],
    fun x => ⟨φ x, hgf' x⟩⟩
  · rw [← hφ.2.1, ← comp_assoc, hgf, id_comp]
  · rw [← hφ.2.2, ← comp_assoc, hgf, id_comp]

theorem Equivalent.trans {X Y Z : CommonOverBTZ i j} (h : X.Equivalent Y)
    (h' : Y.Equivalent Z) : X.Equivalent Z := by
  obtain ⟨φ, hφ, hb⟩ := h
  obtain ⟨ψ, hψ, hb'⟩ := h'
  exact ⟨ψ ∘ φ, hψ.comp hφ, hb'.comp hb⟩

end CommonOverBTZ

end Over

end GX
