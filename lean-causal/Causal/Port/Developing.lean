import Causal.Port.GXBasic
import Causal.Port.UniversalCover
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# The classical developing theorem for `(G,X)`-manifolds

**Ported from `lean-gx/GX/Structure/Developing.lean` at commit `e5a1d46` (gx wave 1, WP-24),
mechanically: namespace `GX` → `Causal`; `gxGroupoid` deduplicated against
`Causal.GXStructure`** (through `Causal.Port.GXBasic`, which uses the strict library's
`Causal.gxGroupoid`). Package WP-32a. `lean-causal` never imports `lean-gx` (gx imports
`Causal`, DEC-33; `docs/BARBOT.md`, "The contract with gx"), so the module is copied for
Barbot's wave 3 (WP-32). Every change that is not the rename `GX.x` → `Causal.x`
(`_root_.GX.x` → `_root_.Causal.x`): the imports `GX.Structure.Basic` /
`GX.Topology.UniversalCover` became `Causal.Port.GXBasic` /
`Causal.Port.UniversalCover`; in this docstring, this paragraph and the provenance line.
No proof and no statement changed. The `RamcovGX.tex` line numbers below are those of the gx
paper (`papers/gx/`); "WP-24b" is gx's universal-cover package, here
`Causal.Port.UniversalCover`.

Package WP-24f (DEC-23: a cited result, built). **No ledger label**, so no label is marked: the
statement is the introduction's `RamcovGX.tex:293` and the commented line `RamcovGX.tex:344`,
cited there to Ehresmann (`MR794193_loc_hom`), Kuiper (`MR0031310`), Epstein (`MR755162`) and the
author's thesis. Built in full, with no `sorry`.

> The existence of a developing map from the universal covering of such a manifold $M$ to the
> model space $X$ and of an holonomy from its fundamental group to the model group $G$ is a
> general property as long as the universal covering exists. (`RamcovGX.tex:293`)

> %The fundamental theorem of such manifolds, coming from the analyticity of the action of $G$,
> is that the exists a map $\D : \widetilde M \rightarrow X$ which is $\rho$-equivariant for some
> representation $\rho:\pi_1(M)\rightarrow G$ of the fundamental group of $M$ into $G$.
> Furthermore, such couples $(\d,\rho)$ only differ by conjugation by some element of  $G$.
> (`RamcovGX.tex:344`, commented out in the source)

## Main declarations

* `Causal.DevSpace G X N`, the **developing space** of a `(G,X)`-manifold `N`: pairs `⟨x, g⟩`
  standing for the germ at `x` of `g • chartAt X x`, topologised by the basic sets
  `DevSpace.basic` (`DevSpace.isTopologicalBasis`). `DevSpace.isCoveringMap_pt`: the base-point
  map is a covering, trivial over each chart domain with sheets indexed by `G` (analyticity).
* `DevSpace.isGXMorphism_of_section`, `DevSpace.sectionOf`, `DevSpace.continuous_sectionOf`:
  continuous sections of the developing space are exactly developing maps.
* `Causal.IsGXMorphism.eq_of_eventuallyEq` — analyticity of developing maps **without** any
  separation hypothesis; `Causal.developing_unique_of_preconnected` — two developing maps of a
  connected manifold differ by a unique `g ∈ G`; `Causal.exists_developingMap`,
  `Causal.developing_theorem_of_simplyConnected` — **(4)**: a simply connected, locally
  path-connected `(G,X)`-manifold has a developing map `N → X`, unique up to a unique `g`.
* `Causal.coverChartedSpace` — the pulled-back structure on `UniversalCover M x₀`
  (`Causal.hasGroupoid_cover`, `Causal.isGXMorphism_cover_proj`); `Causal.isGXMorphism_of_comp_eq_pullback`
  — deck transformations are `(G,X)`-automorphisms.
* `Causal.developing_theorem` — **(1)**: `dev : M̃ → X` a `(G,X)`-morphism (so a local
  homeomorphism) and `hol : Deck (proj M x₀) →* G` with `dev ∘ γ = hol γ • dev`;
  `Causal.developing_theorem_fundamentalGroup` — the same with `ρ : π₁(M, x₀) →* G` through
  `UniversalCover.deckHom`.
* `Causal.developing_unique` — **(2)**: another pair is `(g • dev, g hol g⁻¹)` for a unique `g`.
* `Causal.developing_descends` — **(3)**: trivial holonomy, then `dev = D ∘ proj` with `D : M → X` a
  `(G,X)`-morphism (`M` connected).
* `Causal.exists_developingMap_translation` (inhabitant: the line, translations);
  `Causal.developing_unique_fails_for_bare_maps` (the literal reading of `:344` is false).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| action faithful and rigid ("analytical") | ✓ carried: `IsAnalyticAction G X` (faithfulness: the sheets of the developing covering are disjoint, and `hol` is well defined) |
| action by homeomorphisms | ✓ carried: `ContinuousConstSMul G X` |
| `X` Hausdorff (`:293`, `:341`) | ⚠ weakened: never used — uniqueness goes through the covering, not through closedness of `{D = D'}` |
| `X` connected, locally (path-)connected | ⚠ weakened: never used |
| `M` second countable, Hausdorff | ⚠ weakened: never used |
| `M` connected | ⚠ weakened: not used in (1), (2) (`M̃ = UniversalCover M x₀` is path-connected for every `M`); ✓ carried in (3) (`ConnectedSpace M`, for the surjectivity of `proj`) |
| "as long as the universal covering exists" | ✓ carried as `LocPathConnectedSpace M` and `SemilocallySimplyConnected M`, which give the universal cover (`UniversalCover.isCoveringMap_proj`) and are equivalent to its existence for connected, locally path-connected `M` (`semilocallySimplyConnected_iff_exists_simplyConnected_cover`); `LocPathConnectedSpace M` follows from `X` locally path-connected (`:293`, `ChartedSpace.locPathConnectedSpace`) |
| (4) `N` simply connected | ✓ carried, with `LocPathConnectedSpace N` (lifting criterion) |

## SCOPE (disclosed)

* **(a)** "Developing map" is read as a `(G,X)`-morphism `M̃ → X` for the pulled-back structure
  (`isGXMorphism_iff_model`: near every point a translate of the chart). `:344` literally asks
  only for "a map … $\rho$-equivariant"; under that reading the uniqueness assertion is false
  (`developing_unique_fails_for_bare_maps`) and the existence is trivial (a constant map, `ρ = 1`).
* **(b)** The holonomy is a homomorphism on the deck group `Deck (proj M x₀)`; the paper's
  `π₁(M)` version is `developing_theorem_fundamentalGroup`, through the isomorphism
  `UniversalCover.deckEquiv` of WP-24b. The sign convention of `deckHom` (`a ↦` left
  multiplication by `a⁻¹`) is WP-24b's.
* **(c)** The universal cover is `UniversalCover M x₀` of WP-24b with the structure pulled back
  along `proj` (`coverChartedSpace`, unique by `existsUnique_pullback_of_isCoveringMap`). Any other
  simply connected cover is homeomorphic to it over `M`
  (`UniversalCover.exists_homeomorph_of_simplyConnected`); the transport is not restated here.
* **(d)** Route: the étale space of germs of local developing maps (`DevSpace`) is a covering,
  and a developing map is a section of it (`IsCoveringMap.existsUnique_continuousMap_lifts` on a
  simply connected base). Mathlib's `TopCat.Presheaf` étale space was not used.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Ported from
`lean-gx/GX/Structure/Developing.lean` at `e5a1d46` (WP-24) by WP-32a.
-/

namespace Causal

open Set Filter Topology

universe u v w

/-! ### Rigidity, read in a chart -/

section Rigidity

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  {M : Type u} [TopologicalSpace M]

/-- Two translates of one chart which agree near a point of its source are translates by the
same element (analyticity of the action). -/
theorem eq_of_eventuallyEq_smul [IsAnalyticAction G X] {e : OpenPartialHomeomorph M X} {y : M}
    (hy : y ∈ e.source) {g h : G}
    (heq : (fun z => g • e z) =ᶠ[𝓝 y] fun z => h • e z) : g = h := by
  obtain ⟨W, hW, hWo, hyW⟩ := _root_.mem_nhds_iff.1 heq
  refine eq_of_eqOn (e.isOpen_image_of_subset_source (hWo.inter e.open_source)
    inter_subset_right) ⟨e y, y, ⟨hyW, hy⟩, rfl⟩ ?_
  rintro _ ⟨z, ⟨hzW, -⟩, rfl⟩
  exact hW hzW

end Rigidity

/-! ### The developing space of germs of local developing maps -/

section Germs

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  {N : Type u} [TopologicalSpace N] [ChartedSpace X N]

/-- The **developing space** of a `(G,X)`-manifold `N`: a point `⟨x, g⟩` stands for the germ at
`x` of the local developing map `g • chartAt X x`. The model `X` is a parameter of the type only:
it fixes which charts the points refer to. -/
@[ext, nolint unusedArguments]
structure DevSpace (G : Type w) (X : Type v) (N : Type u) : Type (max u w) where
  /-- The base point. -/
  pt : N
  /-- The element of `G` translating the preferred chart at `pt`. -/
  g : G

namespace DevSpace

/-- The local developing map a point of the developing space stands for. -/
def germ (c : DevSpace G X N) : N → X := fun z => c.g • chartAt X c.pt z

theorem germ_apply (c : DevSpace G X N) (z : N) : c.germ z = c.g • chartAt X c.pt z := rfl

/-- The basic set `B(c, U)`: the points over `U ∩ (chartAt X c.pt).source` whose germ is that
of `c`. -/
def basic (c : DevSpace G X N) (U : Set N) : Set (DevSpace G X N) :=
  {c' | c'.pt ∈ U ∩ (chartAt X c.pt).source ∧ c'.germ =ᶠ[𝓝 c'.pt] c.germ}

/-- The topology of the developing space: generated by the basic sets over open sets. -/
instance : TopologicalSpace (DevSpace G X N) :=
  TopologicalSpace.generateFrom {S | ∃ c U, IsOpen U ∧ S = basic c U}

theorem mem_basic_self {c : DevSpace G X N} {U : Set N} (h : c.pt ∈ U) : c ∈ basic c U :=
  ⟨⟨h, mem_chart_source X c.pt⟩, EventuallyEq.rfl⟩

theorem basic_mono {c : DevSpace G X N} {U V : Set N} (h : U ⊆ V) : basic c U ⊆ basic c V :=
  fun _ hc' => ⟨⟨h hc'.1.1, hc'.1.2⟩, hc'.2⟩

/-- Every point of a basic set has a basic neighbourhood inside it. -/
theorem exists_basic_subset {c c' : DevSpace G X N} {U : Set N} (hU : IsOpen U)
    (h : c' ∈ basic c U) : ∃ V, IsOpen V ∧ c'.pt ∈ V ∧ basic c' V ⊆ basic c U := by
  obtain ⟨W, hW, hWo, hxW⟩ := _root_.mem_nhds_iff.1 h.2
  refine ⟨W ∩ (U ∩ (chartAt X c.pt).source),
    hWo.inter (hU.inter (chartAt X c.pt).open_source), ⟨hxW, h.1⟩, ?_⟩
  rintro d ⟨⟨hdV, -⟩, hd⟩
  refine ⟨hdV.2, hd.trans ?_⟩
  filter_upwards [hWo.mem_nhds hdV.1] with z hz using hW hz

theorem isOpen_basic (c : DevSpace G X N) {U : Set N} (hU : IsOpen U) : IsOpen (basic c U) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨c, U, hU, rfl⟩

theorem basic_mem_nhds {c : DevSpace G X N} {U : Set N} (hU : IsOpen U) (hc : c.pt ∈ U) :
    basic c U ∈ 𝓝 c :=
  (isOpen_basic c hU).mem_nhds (mem_basic_self hc)

/-- The basic sets form a basis of the topology. -/
theorem isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis
      {S : Set (DevSpace G X N) | ∃ c U, IsOpen U ∧ S = basic c U} where
  exists_subset_inter := by
    rintro _ ⟨c, U, hU, rfl⟩ _ ⟨c', U', hU', rfl⟩ d ⟨h1, h2⟩
    obtain ⟨V, hV, hdV, hV1⟩ := exists_basic_subset hU h1
    obtain ⟨V', hV', hdV', hV2⟩ := exists_basic_subset hU' h2
    exact ⟨basic d (V ∩ V'), ⟨d, V ∩ V', hV.inter hV', rfl⟩, mem_basic_self ⟨hdV, hdV'⟩,
      subset_inter ((basic_mono inter_subset_left).trans hV1)
        ((basic_mono inter_subset_right).trans hV2)⟩
  sUnion_eq := eq_univ_of_forall fun c =>
    ⟨basic c univ, ⟨c, univ, isOpen_univ, rfl⟩, mem_basic_self (mem_univ _)⟩
  eq_generateFrom := rfl

theorem mem_nhds_iff {c : DevSpace G X N} {s : Set (DevSpace G X N)} :
    s ∈ 𝓝 c ↔ ∃ U, IsOpen U ∧ c.pt ∈ U ∧ basic c U ⊆ s := by
  rw [isTopologicalBasis.mem_nhds_iff]
  constructor
  · rintro ⟨_, ⟨c', U, hU, rfl⟩, hc, hs⟩
    obtain ⟨V, hV, hcV, hV'⟩ := exists_basic_subset hU hc
    exact ⟨V, hV, hcV, hV'.trans hs⟩
  · rintro ⟨U, hU, hc, hs⟩
    exact ⟨_, ⟨c, U, hU, rfl⟩, mem_basic_self hc, hs⟩

theorem continuous_pt : Continuous (DevSpace.pt : DevSpace G X N → N) := by
  rw [continuous_def]
  intro s hs
  rw [isOpen_iff_mem_nhds]
  intro c hc
  exact mem_of_superset (basic_mem_nhds hs hc) fun _ h => h.1.1

/-- `pt` is injective on every basic set (analyticity). -/
theorem injOn_pt_basic [IsAnalyticAction G X] (c : DevSpace G X N) (U : Set N) :
    InjOn DevSpace.pt (basic c U) := by
  rintro ⟨y, h⟩ ⟨-, h1⟩ ⟨y', h'⟩ ⟨-, h2⟩ hyy
  change y = y' at hyy
  subst hyy
  have : h = h' := eq_of_eventuallyEq_smul (mem_chart_source X y) (h1.trans h2.symm)
  rw [this]

variable [ContinuousConstSMul G X] [HasGroupoid N (gxGroupoid G X)]

/-- Over every point of the chart domain of `c` lies a germ equal to that of `c`. -/
theorem exists_germ_eq (c : DevSpace G X N) {y : N} (hy : y ∈ (chartAt X c.pt).source) :
    ∃ h : G, (⟨y, h⟩ : DevSpace G X N).germ =ᶠ[𝓝 y] c.germ := by
  obtain ⟨a, ha⟩ := eventually_smul_eq_of_mem_maximalAtlas (G := G)
    ((gxGroupoid G X).chart_mem_maximalAtlas y) ((gxGroupoid G X).chart_mem_maximalAtlas c.pt)
    (mem_chart_source X y) hy
  refine ⟨c.g * a, ?_⟩
  filter_upwards [ha] with z hz
  simp only [germ_apply, hz, mul_smul]

theorem pt_image_basic (c : DevSpace G X N) (U : Set N) :
    DevSpace.pt '' basic c U = U ∩ (chartAt X c.pt).source := by
  ext y
  constructor
  · rintro ⟨c', hc', rfl⟩
    exact hc'.1
  · intro hy
    obtain ⟨h, hh⟩ := exists_germ_eq c hy.2
    exact ⟨⟨y, h⟩, ⟨hy, hh⟩, rfl⟩

theorem isOpenMap_pt : IsOpenMap (DevSpace.pt : DevSpace G X N → N) := by
  rw [isTopologicalBasis.isOpenMap_iff]
  rintro _ ⟨c, U, hU, rfl⟩
  rw [pt_image_basic]
  exact hU.inter (chartAt X c.pt).open_source

/-- **The developing space is a covering of `N`**, trivial over every chart domain: the sheets
over `(chartAt X x).source` are indexed by `G`. -/
theorem isCoveringMap_pt [IsAnalyticAction G X] :
    IsCoveringMap (DevSpace.pt : DevSpace G X N → N) := by
  intro x
  refine isEvenlyCovered_of_sheets continuous_pt isOpenMap_pt (chartAt X x).open_source
    (mem_chart_source X x) (ι := G) (fun g => basic ⟨x, g⟩ (chartAt X x).source)
    (fun g => isOpen_basic _ (chartAt X x).open_source) (fun g => injOn_pt_basic _ _)
    (fun g w hw => ?_) (fun g g' hgg' => ?_) (fun c hc => ?_)
  · obtain ⟨h, hh⟩ := exists_germ_eq (⟨x, g⟩ : DevSpace G X N) hw
    exact ⟨⟨w, h⟩, ⟨⟨hw, hw⟩, hh⟩, rfl⟩
  · rw [Function.onFun, disjoint_left]
    rintro c ⟨⟨-, hc⟩, h1⟩ ⟨-, h2⟩
    exact hgg' (eq_of_eventuallyEq_smul hc (h1.symm.trans h2))
  · obtain ⟨a, ha⟩ := eventually_smul_eq_of_mem_maximalAtlas (G := G)
      ((gxGroupoid G X).chart_mem_maximalAtlas x) ((gxGroupoid G X).chart_mem_maximalAtlas c.pt)
      hc (mem_chart_source X c.pt)
    refine mem_iUnion.2 ⟨c.g * a, ⟨hc, hc⟩, ?_⟩
    filter_upwards [ha] with z hz
    simp only [germ_apply, hz, mul_smul]

/-! ### Sections of the developing space and developing maps -/

omit [ContinuousConstSMul G X] [HasGroupoid N (gxGroupoid G X)] in
/-- Near `x`, the germs of a continuous section agree with the germ at `x`. -/
theorem eventually_germ_eq {s : N → DevSpace G X N} (hs : Continuous s)
    (hps : ∀ x, (s x).pt = x) (x : N) :
    ∀ᶠ y in 𝓝 x, (s y).germ =ᶠ[𝓝 y] (s x).germ := by
  have : s ⁻¹' basic (s x) univ ∈ 𝓝 x :=
    hs.continuousAt.preimage_mem_nhds (basic_mem_nhds isOpen_univ (mem_univ _))
  filter_upwards [this] with y hy
  have h := hy.2
  rwa [hps y] at h

omit [HasGroupoid N (gxGroupoid G X)] in
/-- A map which is, near every point, a translate of the chart there, is a `(G,X)`-morphism
(continuity comes for free). -/
theorem _root_.Causal.isGXMorphism_of_eventually {D : N → X}
    (h : ∀ x : N, ∃ g : G, D =ᶠ[𝓝 x] fun y => g • chartAt X x y) : IsGXMorphism G X D := by
  rw [isGXMorphism_iff_model]
  refine ⟨continuous_iff_continuousAt.2 fun x => ?_, h⟩
  obtain ⟨g, hg⟩ := h x
  exact (((continuous_const_smul g).continuousAt).comp
    ((chartAt X x).continuousAt (mem_chart_source X x))).congr hg.symm

omit [HasGroupoid N (gxGroupoid G X)] in
/-- **A continuous section of the developing space is a developing map**: reading each germ at
its own base point gives a `(G,X)`-morphism `N → X`. -/
theorem isGXMorphism_of_section {s : N → DevSpace G X N} (hs : Continuous s)
    (hps : ∀ x, (s x).pt = x) : IsGXMorphism G X fun y => (s y).germ y := by
  refine isGXMorphism_of_eventually fun x => ⟨(s x).g, ?_⟩
  filter_upwards [eventually_germ_eq hs hps x] with y hy
  rw [hy.self_of_nhds, germ_apply, hps x]

/-- The section of the developing space defined by a developing map `D`: at `x`, the element of
`G` with `D = g • chartAt X x` near `x`. -/
noncomputable def sectionOf {D : N → X} (hD : IsGXMorphism G X D) (x : N) : DevSpace G X N :=
  ⟨x, ((isGXMorphism_iff_model.1 hD).2 x).choose⟩

omit [ContinuousConstSMul G X] [HasGroupoid N (gxGroupoid G X)] in
theorem sectionOf_pt {D : N → X} (hD : IsGXMorphism G X D) (x : N) : (sectionOf hD x).pt = x :=
  rfl

omit [ContinuousConstSMul G X] [HasGroupoid N (gxGroupoid G X)] in
theorem germ_sectionOf {D : N → X} (hD : IsGXMorphism G X D) (x : N) :
    (sectionOf hD x).germ =ᶠ[𝓝 x] D :=
  Filter.EventuallyEq.symm ((isGXMorphism_iff_model.1 hD).2 x).choose_spec

omit [ContinuousConstSMul G X] [HasGroupoid N (gxGroupoid G X)] in
theorem germ_sectionOf_self {D : N → X} (hD : IsGXMorphism G X D) (x : N) :
    (sectionOf hD x).germ x = D x :=
  (germ_sectionOf hD x).self_of_nhds

omit [ContinuousConstSMul G X] [HasGroupoid N (gxGroupoid G X)] in
theorem continuous_sectionOf {D : N → X} (hD : IsGXMorphism G X D) :
    Continuous (sectionOf hD) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_def]
  intro s hs
  obtain ⟨U, hU, hxU, hsub⟩ := mem_nhds_iff.1 hs
  obtain ⟨W, hW, hWo, hxW⟩ := _root_.mem_nhds_iff.1 (germ_sectionOf hD x)
  filter_upwards [hU.mem_nhds hxU, (chartAt X x).open_source.mem_nhds (mem_chart_source X x),
    hWo.mem_nhds hxW] with y hyU hys hyW
  refine hsub ⟨⟨hyU, hys⟩, (germ_sectionOf hD y).trans ?_⟩
  filter_upwards [hWo.mem_nhds hyW] with z hz using (hW hz).symm

end DevSpace

end Germs

/-! ### Analyticity and uniqueness of developing maps -/

section Unique

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {N : Type u} [TopologicalSpace N] [ChartedSpace X N]
  [HasGroupoid N (gxGroupoid G X)]

open DevSpace

/-- **Analyticity of developing maps**, with no separation hypothesis: two developing maps of a
connected `(G,X)`-manifold which agree near one point agree everywhere. The proof compares the
two sections of the developing covering. -/
theorem IsGXMorphism.eq_of_eventuallyEq [IsAnalyticAction G X] [PreconnectedSpace N]
    {D D' : N → X} (hD : IsGXMorphism G X D) (hD' : IsGXMorphism G X D') {x₀ : N}
    (h : D =ᶠ[𝓝 x₀] D') : D = D' := by
  have hs : sectionOf hD = sectionOf hD' := by
    refine (isCoveringMap_pt (G := G) (X := X) (N := N)).eq_of_comp_eq (continuous_sectionOf hD)
      (continuous_sectionOf hD') rfl x₀ ?_
    refine DevSpace.ext rfl (eq_of_eventuallyEq_smul (mem_chart_source X x₀) ?_)
    exact (germ_sectionOf hD x₀).trans (h.trans (germ_sectionOf hD' x₀).symm)
  funext x
  rw [← germ_sectionOf_self hD x, ← germ_sectionOf_self hD' x, hs]

omit [HasGroupoid N (gxGroupoid G X)] in
/-- A developing map determines the translating element: `g • D = h • D` forces `g = h`. -/
theorem IsGXMorphism.smul_injective [IsAnalyticAction G X] [Nonempty N] {D : N → X}
    (hD : IsGXMorphism G X D) {g h : G} (heq : ∀ z, g • D z = h • D z) : g = h :=
  Causal.eq_of_eqOn (hD.isOpenMap _ isOpen_univ) (univ_nonempty.image D)
    (by rintro _ ⟨z, -, rfl⟩; exact heq z)

/-- **Uniqueness of developing maps**: on a connected `(G,X)`-manifold, two developing maps
differ by a unique element of `G`. -/
theorem developing_unique_of_preconnected [IsAnalyticAction G X] [PreconnectedSpace N]
    [Nonempty N] {D D' : N → X} (hD : IsGXMorphism G X D) (hD' : IsGXMorphism G X D') :
    ∃! g : G, ∀ z, D' z = g • D z := by
  obtain ⟨x₀⟩ := ‹Nonempty N›
  obtain ⟨a, ha⟩ := (isGXMorphism_iff_model.1 hD).2 x₀
  obtain ⟨b, hb⟩ := (isGXMorphism_iff_model.1 hD').2 x₀
  have hgD : IsGXMorphism G X fun z => (b * a⁻¹) • D z := (isGXMorphism_smul (b * a⁻¹)).comp hD
  have hev : D' =ᶠ[𝓝 x₀] fun z => (b * a⁻¹) • D z := by
    filter_upwards [ha, hb] with z hza hzb
    rw [hzb, hza, mul_smul, inv_smul_smul]
  have heq := hD'.eq_of_eventuallyEq hgD hev
  refine ⟨b * a⁻¹, fun z => congrFun heq z, fun g hg => ?_⟩
  exact hD.smul_injective fun z => by rw [← hg z, ← congrFun heq z]

/-- **Existence of a developing map** on a simply connected, locally path-connected
`(G,X)`-manifold: a global section of the developing covering, through the lifting criterion. -/
theorem exists_developingMap [IsAnalyticAction G X] [SimplyConnectedSpace N]
    [LocPathConnectedSpace N] : ∃ D : N → X, IsGXMorphism G X D := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty N)
  obtain ⟨s, ⟨-, hs⟩, -⟩ := (isCoveringMap_pt (G := G) (X := X) (N := N)).existsUnique_continuousMap_lifts
    (ContinuousMap.id N) x₀ ⟨x₀, 1⟩ rfl
  exact ⟨_, isGXMorphism_of_section s.continuous fun x => congrFun hs x⟩

/-- **The developing theorem, simply connected case** (DEC-23, item (4) of the dispatch): a
simply connected, locally path-connected `(G,X)`-manifold has a developing map `N → X`, unique up
to a unique element of `G`. -/
theorem developing_theorem_of_simplyConnected [IsAnalyticAction G X] [SimplyConnectedSpace N]
    [LocPathConnectedSpace N] :
    ∃ D : N → X, IsGXMorphism G X D ∧
      ∀ D' : N → X, IsGXMorphism G X D' → ∃! g : G, ∀ z, D' z = g • D z := by
  obtain ⟨D, hD⟩ := exists_developingMap (G := G) (X := X) (N := N)
  exact ⟨D, hD, fun D' hD' => developing_unique_of_preconnected hD hD'⟩

end Unique

/-! ### Pulled-back structures: charts and maps over the base -/

section Pullback

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  {E : Type*} [TopologicalSpace E] {M : Type u} [TopologicalSpace M] [ChartedSpace X M]

/-- The preferred charts of the pulled-back structure, read through `p`. -/
theorem pullback_chartAt_apply {p : E → M} (hp : IsLocalHomeomorph p) (x y : E) :
    @chartAt X _ E _ (pullbackChartedSpace hp) x y = chartAt X (p x) (p y) := by
  show ((localHomeomorphAt hp x).trans (chartAt X (p x))) y = _
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, coe_localHomeomorphAt]

/-- For a pulled-back structure, every continuous map over the base is a `(G,X)`-morphism; in
particular every deck transformation of a covering is one. -/
theorem isGXMorphism_of_comp_eq_pullback {p : E → M} (hp : IsLocalHomeomorph p) {φ : E → E}
    (hφ : Continuous φ) (h : p ∘ φ = p) :
    letI := pullbackChartedSpace (X := X) hp
    IsGXMorphism G X φ := by
  letI := pullbackChartedSpace (X := X) hp
  refine ⟨hφ, fun x => ⟨1, Eventually.of_forall fun y => ?_⟩⟩
  rw [pullback_chartAt_apply hp, pullback_chartAt_apply hp, one_smul]
  have h' := congrFun h
  simp only [Function.comp_apply] at h'
  rw [h', h']

end Pullback

/-! ### The developing theorem on the universal cover -/

section Universal

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M] [ChartedSpace X M]
  [HasGroupoid M (gxGroupoid G X)] [LocPathConnectedSpace M]

variable (X) in
/-- The `(G,X)`-structure of the universal cover `M̃ = UniversalCover M x₀`, pulled back along
the covering map `proj` (`existsUnique_pullback_of_isCoveringMap`: the unique one making `proj`
a `(G,X)`-morphism). -/
@[reducible] noncomputable def coverChartedSpace (hM : SemilocallySimplyConnected M) (x₀ : M) :
    ChartedSpace X (UniversalCover M x₀) :=
  pullbackChartedSpace (UniversalCover.isCoveringMap_proj (y₀ := x₀) hM).isLocalHomeomorph

/-- The pulled-back structure on the universal cover is a `(G,X)`-structure. -/
theorem hasGroupoid_cover (hM : SemilocallySimplyConnected M) (x₀ : M) :
    @HasGroupoid X _ _ _ (coverChartedSpace X hM x₀) (gxGroupoid G X) :=
  hasGroupoid_pullback _

omit [ContinuousConstSMul G X] [HasGroupoid M (gxGroupoid G X)] in
/-- For it, the covering map `proj : M̃ → M` is a `(G,X)`-morphism. -/
theorem isGXMorphism_cover_proj (hM : SemilocallySimplyConnected M) (x₀ : M) :
    letI := coverChartedSpace X hM x₀
    IsGXMorphism G X (UniversalCover.proj M x₀) :=
  isGXMorphism_pullback _

/-- **The classical developing theorem** (`RamcovGX.tex:344`, `:293`; DEC-23), existence: the
universal cover `M̃` of a locally path-connected, semilocally simply connected `(G,X)`-manifold
`M`, with its pulled-back structure, has a developing map `dev : M̃ → X` (a `(G,X)`-morphism,
hence a local homeomorphism) and a holonomy homomorphism `hol : Deck(M̃ → M) →* G` such that
`dev ∘ γ = hol γ • dev` for every deck transformation `γ`. -/
theorem developing_theorem [IsAnalyticAction G X] (hM : SemilocallySimplyConnected M) (x₀ : M) :
    letI := coverChartedSpace X hM x₀
    ∃ (dev : UniversalCover M x₀ → X) (hol : Deck (UniversalCover.proj M x₀) →* G),
      IsGXMorphism G X dev ∧ IsLocalHomeomorph dev ∧
        ∀ (γ : Deck (UniversalCover.proj M x₀)) (z : UniversalCover M x₀),
          dev (γ.1 z) = hol γ • dev z := by
  letI := coverChartedSpace X hM x₀
  haveI : HasGroupoid (UniversalCover M x₀) (gxGroupoid G X) := hasGroupoid_cover hM x₀
  haveI := UniversalCover.simplyConnectedSpace (y₀ := x₀) hM
  obtain ⟨dev, hdev⟩ := exists_developingMap (G := G) (X := X) (N := UniversalCover M x₀)
  have hdeck : ∀ γ : Deck (UniversalCover.proj M x₀),
      IsGXMorphism G X (γ.1 : UniversalCover M x₀ → UniversalCover M x₀) :=
    fun γ => isGXMorphism_of_comp_eq_pullback _ γ.1.continuous γ.2
  have hex : ∀ γ : Deck (UniversalCover.proj M x₀), ∃ g : G, ∀ z, dev (γ.1 z) = g • dev z :=
    fun γ => (developing_unique_of_preconnected hdev (hdev.comp (hdeck γ))).exists
  choose hol hhol using hex
  refine ⟨dev, { toFun := hol, map_one' := ?_, map_mul' := ?_ }, hdev, hdev.isLocalHomeomorph, hhol⟩
  · exact hdev.smul_injective fun z => by rw [← hhol 1 z, one_smul]; rfl
  · intro γ δ
    exact hdev.smul_injective fun z => by
      rw [← hhol (γ * δ) z, mul_smul, ← hhol δ z, ← hhol γ (δ.1 z)]; rfl

/-- The developing theorem with the holonomy on the fundamental group `π₁(M, x₀)`, through its
action `UniversalCover.deckHom` by deck transformations. -/
theorem developing_theorem_fundamentalGroup [IsAnalyticAction G X]
    (hM : SemilocallySimplyConnected M) (x₀ : M) :
    letI := coverChartedSpace X hM x₀
    ∃ (dev : UniversalCover M x₀ → X) (ρ : FundamentalGroup M x₀ →* G),
      IsGXMorphism G X dev ∧
        ∀ (a : FundamentalGroup M x₀) (z : UniversalCover M x₀),
          dev ((UniversalCover.deckHom a).1 z) = ρ a • dev z := by
  letI := coverChartedSpace X hM x₀
  obtain ⟨dev, hol, hdev, -, hhol⟩ := developing_theorem (G := G) (X := X) hM x₀
  exact ⟨dev, hol.comp UniversalCover.deckHom, hdev, fun a z => hhol _ z⟩

/-- **The developing theorem, uniqueness** (`RamcovGX.tex:344`: "such couples only differ by
conjugation by some element of `G`"): two developing pairs `(dev, hol)`, `(dev', hol')` of `M̃`
are related by a unique `g ∈ G`: `dev' = g • dev` and `hol' = g hol g⁻¹`. -/
theorem developing_unique [IsAnalyticAction G X] (hM : SemilocallySimplyConnected M) (x₀ : M) :
    letI := coverChartedSpace X hM x₀
    ∀ {dev dev' : UniversalCover M x₀ → X} {hol hol' : Deck (UniversalCover.proj M x₀) →* G},
      IsGXMorphism G X dev → (∀ γ z, dev (γ.1 z) = hol γ • dev z) →
      IsGXMorphism G X dev' → (∀ γ z, dev' (γ.1 z) = hol' γ • dev' z) →
      ∃! g : G, (∀ z, dev' z = g • dev z) ∧ ∀ γ, hol' γ = g * hol γ * g⁻¹ := by
  letI := coverChartedSpace X hM x₀
  intro dev dev' hol hol' hdev hhol hdev' hhol'
  haveI : HasGroupoid (UniversalCover M x₀) (gxGroupoid G X) := hasGroupoid_cover hM x₀
  obtain ⟨g, hg, huniq⟩ := developing_unique_of_preconnected hdev hdev'
  refine ⟨g, ⟨hg, fun γ => hdev'.smul_injective fun z => ?_⟩, fun g' hg' => huniq g' hg'.1⟩
  rw [← hhol' γ z, hg (γ.1 z), hhol γ z, hg z]
  simp only [mul_smul, inv_smul_smul]

omit [HasGroupoid M (gxGroupoid G X)] in
/-- **The developing theorem, descent**: if the holonomy is trivial, the developing map factors
through `proj` as a `(G,X)`-morphism `M → X` (`M` connected). -/
theorem developing_descends [ConnectedSpace M] (hM : SemilocallySimplyConnected M) (x₀ : M) :
    letI := coverChartedSpace X hM x₀
    ∀ {dev : UniversalCover M x₀ → X} {hol : Deck (UniversalCover.proj M x₀) →* G},
      IsGXMorphism G X dev → (∀ γ z, dev (γ.1 z) = hol γ • dev z) → (∀ γ, hol γ = 1) →
      ∃ D : M → X, IsGXMorphism G X D ∧ dev = D ∘ UniversalCover.proj M x₀ := by
  letI := coverChartedSpace X hM x₀
  intro dev hol hdev hhol htriv
  haveI : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.2 ‹_›
  have hinv : ∀ (γ : Deck (UniversalCover.proj M x₀)) z, dev (γ.1 z) = dev z := fun γ z => by
    rw [hhol, htriv, one_smul]
  have htrans : ∀ c c' : UniversalCover M x₀, c.pt = c'.pt →
      ∃ γ : Deck (UniversalCover.proj M x₀), γ.1 c = c' := by
    rintro ⟨y, a⟩ ⟨y', b⟩ h
    change y = y' at h
    subst h
    refine ⟨⟨UniversalCover.leftMulHomeomorph (b.trans a.symm), rfl⟩, ?_⟩
    show (⟨y, (b.trans a.symm).trans a⟩ : UniversalCover M x₀) = ⟨y, b⟩
    rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.trans_refl]
  have hsurj := UniversalCover.proj_surjective (Y := M) (y₀ := x₀)
  let lift : M → UniversalCover M x₀ := fun y => (hsurj y).choose
  have hlift : ∀ y, (lift y).pt = y := fun y => (hsurj y).choose_spec
  let D : M → X := fun y => dev (lift y)
  have hD : ∀ c : UniversalCover M x₀, D c.pt = dev c := by
    intro c
    obtain ⟨γ, hγ⟩ := htrans (lift c.pt) c (hlift c.pt)
    show dev (lift c.pt) = dev c
    rw [← hinv γ (lift c.pt), hγ]
  refine ⟨D, isGXMorphism_of_eventually fun y => ?_, funext fun c => (hD c).symm⟩
  obtain ⟨g, hg⟩ := (isGXMorphism_iff_model.1 hdev).2 (lift y)
  refine ⟨g, ?_⟩
  have hopen : IsOpenMap (UniversalCover.proj M x₀) :=
    (UniversalCover.isCoveringMap_proj (y₀ := x₀) hM).isOpenMap
  have hmem := hopen.image_mem_nhds hg
  have hl : UniversalCover.proj M x₀ (lift y) = y := hlift y
  rw [hl] at hmem
  filter_upwards [hmem] with y' ⟨z, hz, hzy⟩
  have hz' : dev z = g • chartAt X y z.pt := by
    rw [hz, pullback_chartAt_apply, hl]
  rw [← hzy]
  change D z.pt = g • chartAt X y z.pt
  rw [hD, hz']

end Universal

/-! ### An inhabitant -/

/-- The hypotheses are inhabited: the line with its translation structure, simply connected and
locally path-connected, has a developing map. -/
theorem exists_developingMap_translation :
    ∃ D : ℝ → ℝ, IsGXMorphism (Multiplicative ℝ) ℝ D :=
  exists_developingMap

/-- **The commented statement `RamcovGX.tex:344`, read literally, is false in its uniqueness
half** (DEC-27): it asks only for "a map `D` which is `ρ`-equivariant", and on the simply
connected line (deck group trivial, so every map is equivariant for the trivial `ρ`) the
developing map `id` and the constant map `0` are two such couples not related by any element of
`G`. The constant map is not a `(G,X)`-morphism; `developing_unique` holds for developing maps,
which is the reading taken. -/
theorem developing_unique_fails_for_bare_maps :
    ∃ D D' : ℝ → ℝ, IsGXMorphism (Multiplicative ℝ) ℝ D ∧
      ¬ IsGXMorphism (Multiplicative ℝ) ℝ D' ∧
      ¬ ∃ g : Multiplicative ℝ, ∀ z, D' z = g • D z := by
  refine ⟨id, fun _ => 0, isGXMorphism_id, fun h => ?_, ?_⟩
  · have := h.isOpenMap _ isOpen_univ
    rw [image_univ, range_const] at this
    exact not_isOpen_singleton (0 : ℝ) this
  · rintro ⟨g, hg⟩
    have h0 : (0 : ℝ) = g • (0 : ℝ) := hg 0
    have h1 : (0 : ℝ) = g • (1 : ℝ) := hg 1
    exact zero_ne_one ((smul_left_cancel_iff g).1 (h0.symm.trans h1))

end Causal
