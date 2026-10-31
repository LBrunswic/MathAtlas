import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# `(G,X)`-structures: analytic actions, `(G,X)`-atlases, morphisms and pullbacks

No ledger label: the definitions certified here are the paper's unlabelled ones, of the
introduction (`RamcovGX.tex:293`) and of the first paragraph of §2 (`RamcovGX.tex:341`–`343`),
together with the "usual results" the proof of `lem:aepullback` invokes (`RamcovGX.tex:549`: the
pullback of a `(G,X)`-structure along a local homeomorphism, unique).

> […] a couple $(G,X)$ where $X$ is a locally path-connected Hausdorff topological space and $G$ a
> group acting analytically on $X$ by homeomorphisms. Here ``analytically'' means that for all
> $g,h\in G$, if the restrictions to any non trivial open subset $\U$ of $g$ and $h$ agree then
> $g=h$. A $(G,X)$-manifold is then a second countable Hausdorff topological space $M$ endowed
> with an atlas whose change of charts lies in $G$. (`RamcovGX.tex:293`)

> We give ourselves some analytical structure $(G,X)$, ie a connected, locally connected,
> Hausdorff topological space $X$ together with a faithful action of a group $G$ by
> homeomorphisms such that for all $\phi_1,\phi_2\in G$ and all non trivial open subset
> $\U\subset X$, if the action of $\phi_1$ and $\phi_1$ agree on $\U$ they agree on $X$.
> A $(G,X)$-atlas on a topological space $M$ is a family $(\U_i,\V_i,\varphi_i)_{i\in I}$ where
> for all $i\in I$, $\U_i$ is an open subset of $M$, $\V_i$ is an open subset of $X$ and
> $\varphi_i:\U_i\rightarrow \V_i$ an homeomorphism, with the property that for all $i,j\in I$
> such that $\U_i\cap \U_j\neq \emptyset$ and for all connected component $\W$ of
> $\U_i\cap \U_j$, there exists a $\phi \in G$ such that
> $\phi\circ \varphi_{i|\W} = \varphi_{j|\W}$. By analyticity of $(G,X)$, such a $\phi$ is
> unique. The support $\supp(\A)$ of such an atlas $\A$ is defined as the union of the $\U_i$.
> A $(G,X)$-manifold is a second countable Hausdorff topological space $M$ endowed with an
> $(G,X)$-atlas whose support is $M$. (`RamcovGX.tex:341`–`343`)

## Contents

* `GX.IsRigidAction`, `GX.IsAnalyticAction` (faithful + rigid), `GX.AnalyticStructure`;
  `GX.IsAnalyticAction.of_eq_of_eqOn` — the introduction's formulation implies §2's.
* `GX.gxPregroupoid`, `GX.gxGroupoid` (ported from `lean-causal/Causal/GXStructure.lean`,
  section `GX`), `GX.exists_smul_eq_of_mem_gxGroupoid` (ported),
  `GX.symm_trans_mem_gxGroupoid_iff` (membership is "locally a translation, near every point").
* `GX.IsGXAtlas` — the paper's `(G,X)`-atlas, per connected component of the overlaps;
  `GX.IsGXAtlas.unique` (the `φ` is unique); `GX.hasGroupoid_iff_isGXAtlas` — equivalence with
  the DEC-16 convention `[ChartedSpace X M] [HasGroupoid M (gxGroupoid G X)]`;
  `GX.exists_isGXAtlas_iff_exists_hasGroupoid` — the paper's `(G,X)`-manifolds are exactly the
  DEC-16 ones.
* `GX.eventually_smul_eq_of_mem_maximalAtlas`, `GX.mem_maximalAtlas_iff_eventually` — the
  maximal atlas, pointwise.
* `GX.IsGXMorphism` — continuous, and in charts locally the restriction of an element of `G`;
  `GX.IsGXMorphism.exists_smul_eq_of_mem_maximalAtlas` (chart independence),
  `GX.isGXMorphism_id`, `GX.IsGXMorphism.comp`, `GX.IsGXMorphism.isLocalHomeomorph`,
  `GX.IsGXMorphism.isOpenMap`, `GX.IsGXMorphism.eq_of_eqOn` (analyticity of morphisms),
  `GX.isGXMorphism_iff_model` (morphisms into `X`: the shape of a developing map),
  `GX.isGXMorphism_smul`.
* `GX.pullbackChartedSpace` — the pullback along a local homeomorphism;
  `GX.hasGroupoid_pullback`, `GX.isGXMorphism_pullback`,
  `GX.IsGXMorphism.maximalAtlas_eq` (uniqueness), `GX.existsUnique_pullback`, and the covering-map
  case `GX.existsUnique_pullback_of_isCoveringMap`.
* An inhabitant: the translations of `ℝ`, `GX.analyticStructure_translation`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `X` connected, locally connected, Hausdorff | ⚠ weakened: each result asks only what it uses (`LocallyConnectedSpace X` for the atlas equivalence and the uniqueness of `φ`) |
| `X` locally path-connected (introduction, l.293) | ⚠ weakened: local connectedness (§2, l.341) is what is used |
| action faithful + rigid ("analytical") | ⚠ weakened: rigidity alone (`IsRigidAction`) suffices everywhere except the uniqueness of `φ` |
| action by homeomorphisms | ✓ carried: `ContinuousConstSMul G X` |
| `M` second countable Hausdorff | ⚠ weakened: not used; `T2Space N` is used by the analyticity of morphisms |
| `M` connected (analyticity of morphisms) | ✓ carried: `PreconnectedSpace M` |

## SCOPE (disclosed)

* **(a)** DEC-16: a `(G,X)`-manifold is `[ChartedSpace X M] [HasGroupoid M (gxGroupoid G X)]`,
  the structure being the maximal atlas `(gxGroupoid G X).maximalAtlas M`. The paper's
  per-component atlas is `IsGXAtlas`, and `hasGroupoid_iff_isGXAtlas` shows the two agree when
  `X` is locally connected and the action rigid.
* **(b)** The paper does not define a `(G,X)`-morphism between regular manifolds; the reading
  taken (dispatch WP-24c) is: continuous, and in charts near every point the restriction of an
  element of `G`. It is chart independent over the maximal atlases.
* **(c)** The paper's "family $(\U_i,\V_i,\varphi_i)_{i\in I}$" is a set of open partial
  homeomorphisms `M → X`; repetitions in a family change nothing.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. The groupoid is
ported from `lean-causal/Causal/GXStructure.lean` (section `GX`), not imported.
-/

namespace GX

open Set Filter Topology

universe u v w y

/-! ### Analytic actions -/

section Analytic

variable (G : Type w) (X : Type v) [TopologicalSpace X] [Group G] [MulAction G X]

/-- **Rigidity** of an action: two elements whose actions agree on a nonempty open set agree
everywhere. This is the half of "analytical" (`RamcovGX.tex:341`) that every result of the
library uses. -/
class IsRigidAction : Prop where
  smul_eq_of_eqOn : ∀ {g h : G} {U : Set X}, IsOpen U → U.Nonempty →
    EqOn (fun p : X => g • p) (fun p => h • p) U → ∀ p : X, g • p = h • p

/-- **An analytical action** (`RamcovGX.tex:341`): faithful, and rigid. -/
class IsAnalyticAction : Prop extends FaithfulSMul G X, IsRigidAction G X

/-- **An analytical structure** `(G,X)` (`RamcovGX.tex:341`): `X` connected, locally connected,
Hausdorff, with a faithful rigid action of `G` by homeomorphisms. -/
structure AnalyticStructure : Prop where
  connectedSpace : ConnectedSpace X
  locallyConnectedSpace : LocallyConnectedSpace X
  t2Space : T2Space X
  continuousConstSMul : ContinuousConstSMul G X
  isAnalyticAction : IsAnalyticAction G X

variable {G X}

/-- Under an analytical action, two elements agreeing on a nonempty open set are equal. -/
theorem eq_of_eqOn [IsAnalyticAction G X] {g h : G} {U : Set X} (hU : IsOpen U)
    (hne : U.Nonempty) (heq : EqOn (fun p : X => g • p) (fun p => h • p) U) : g = h :=
  FaithfulSMul.eq_of_smul_eq_smul (IsRigidAction.smul_eq_of_eqOn hU hne heq)

/-- The introduction's formulation (`RamcovGX.tex:293`) — two elements agreeing on a nonempty
open set are equal — gives an analytical action in the sense of §2, as soon as `X` is nonempty. -/
theorem IsAnalyticAction.of_eq_of_eqOn [Nonempty X]
    (h : ∀ {g h : G} {U : Set X}, IsOpen U → U.Nonempty →
      EqOn (fun p : X => g • p) (fun p => h • p) U → g = h) : IsAnalyticAction G X where
  eq_of_smul_eq_smul hgh := h isOpen_univ univ_nonempty fun p _ => hgh p
  smul_eq_of_eqOn hU hne heq := by rw [h hU hne heq]; exact fun _ => rfl

/-- Conversely, an analytical action satisfies the introduction's formulation. -/
theorem isAnalyticAction_iff [Nonempty X] : IsAnalyticAction G X ↔
    ∀ {g h : G} {U : Set X}, IsOpen U → U.Nonempty →
      EqOn (fun p : X => g • p) (fun p => h • p) U → g = h :=
  ⟨fun _ _ _ _ hU hne heq => eq_of_eqOn hU hne heq, IsAnalyticAction.of_eq_of_eqOn⟩

end Analytic

/-! ### The groupoid of a `(G,X)`-structure (ported from `lean-causal`) -/

section Groupoid

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M]

variable (G X) in
/-- The pregroupoid of the maps which are, near every point of the set, the action of an element
of `G`. Ported from `lean-causal/Causal/GXStructure.lean`. -/
def gxPregroupoid : Pregroupoid X where
  property f s := ∀ x ∈ s, ∃ g : G, f =ᶠ[𝓝 x] fun y => g • y
  comp {f f' u v} hf hf' _ _ _ := by
    rintro x ⟨hxu, hxv⟩
    obtain ⟨a, ha⟩ := hf x hxu
    obtain ⟨b, hb⟩ := hf' (f x) hxv
    have hcont : ContinuousAt f x :=
      (continuous_const_smul a).continuousAt.congr ha.symm
    refine ⟨b * a, ?_⟩
    filter_upwards [hcont.eventually hb, ha] with y hy hy'
    show f' (f y) = (b * a) • y
    rw [hy, hy', mul_smul]
  id_mem x _ := ⟨1, Eventually.of_forall fun y => (one_smul G y).symm⟩
  locality {f u} _ h x hx := by
    obtain ⟨v, -, hxv, hp⟩ := h x hx
    exact hp x ⟨hx, hxv⟩
  congr {f f' u} hu heq hf x hx := by
    obtain ⟨g, hg⟩ := hf x hx
    refine ⟨g, ?_⟩
    filter_upwards [hu.mem_nhds hx, hg] with y hy hy'
    rw [heq y hy, hy']

variable (G X) in
/-- **The groupoid of a `(G,X)`-structure**: the open partial homeomorphisms of `X` which, near
every point of their source, are the restriction of an element of `G`. A `(G,X)`-manifold is a
charted space `ChartedSpace X M` with `HasGroupoid M (gxGroupoid G X)` (DEC-16). Ported from
`lean-causal/Causal/GXStructure.lean`. -/
def gxGroupoid : StructureGroupoid X := (gxPregroupoid G X).groupoid

theorem mem_gxGroupoid_iff {f : OpenPartialHomeomorph X X} :
    f ∈ gxGroupoid G X ↔ (∀ x ∈ f.source, ∃ g : G, f =ᶠ[𝓝 x] fun y => g • y) ∧
      ∀ x ∈ f.target, ∃ g : G, f.symm =ᶠ[𝓝 x] fun y => g • y :=
  Iff.rfl

/-- The transition between two charts of a `(G,X)`-manifold is, near every point of the overlap,
the action of an element of `G`. Ported from `lean-causal/Causal/GXStructure.lean`, with
`O : Opens M` bounded by `e.source ∩ e'.source`. -/
theorem exists_smul_eq_of_mem_gxGroupoid {e e' : OpenPartialHomeomorph M X}
    (h : e.symm.trans e' ∈ gxGroupoid G X) {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ∃ g : G, ∃ O : TopologicalSpace.Opens M, x ∈ O ∧ (O : Set M) ⊆ e.source ∩ e'.source ∧
      ∀ z ∈ O, e' z = g • e z := by
  have hmem : e x ∈ (e.symm.trans e').source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    exact ⟨e.map_source hx, by simpa [e.left_inv hx] using hx'⟩
  obtain ⟨g, hg⟩ := (mem_groupoid_of_pregroupoid.1 h).1 (e x) hmem
  rw [OpenPartialHomeomorph.coe_trans] at hg
  let O : TopologicalSpace.Opens M :=
    ⟨(e.source ∩ e'.source) ∩ e ⁻¹' interior {y | e' (e.symm y) = g • y}, by
      have := e.isOpen_inter_preimage (isOpen_interior (s := {y | e' (e.symm y) = g • y}))
      convert this.inter e'.open_source using 1
      ext z; simp only [mem_inter_iff, mem_preimage]; tauto⟩
  refine ⟨g, O, ⟨⟨hx, hx'⟩, ?_⟩, fun z hz => ⟨hz.1.1, hz.1.2⟩, fun z hz => ?_⟩
  · exact mem_interior_iff_mem_nhds.2 hg
  · have := interior_subset hz.2
    simp only [mem_setOf_eq, e.left_inv hz.1.1] at this
    exact this

/-- The eventual form: near every point of the overlap, `e' = g • e`. -/
theorem eventually_smul_eq_of_mem_gxGroupoid {e e' : OpenPartialHomeomorph M X}
    (h : e.symm.trans e' ∈ gxGroupoid G X) {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ∃ g : G, ∀ᶠ z in 𝓝 x, e' z = g • e z := by
  obtain ⟨g, O, hxO, -, hO⟩ := exists_smul_eq_of_mem_gxGroupoid h hx hx'
  exact ⟨g, Filter.mem_of_superset (O.isOpen.mem_nhds hxO) hO⟩

/-- Conversely, if near every point of the overlap `e' = g • e` for some `g`, the transition
`e.symm ≫ e'` lies in the groupoid. -/
theorem symm_trans_mem_gxGroupoid {e e' : OpenPartialHomeomorph M X}
    (h : ∀ x ∈ e.source ∩ e'.source, ∃ g : G, ∀ᶠ z in 𝓝 x, e' z = g • e z) :
    e.symm.trans e' ∈ gxGroupoid G X := by
  -- one direction, used twice
  have key : ∀ {e e' : OpenPartialHomeomorph M X},
      (∀ x ∈ e.source ∩ e'.source, ∃ g : G, ∀ᶠ z in 𝓝 x, e' z = g • e z) →
      (gxPregroupoid G X).property (e.symm.trans e') (e.symm.trans e').source := by
    intro e e' h q hq
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hq
    obtain ⟨g, hg⟩ := h (e.symm q) ⟨e.map_target hq.1, hq.2⟩
    refine ⟨g, ?_⟩
    filter_upwards [(e.continuousAt_symm hq.1).eventually hg,
      e.eventually_right_inverse hq.1] with w hw hw'
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hw, hw']
  refine mem_groupoid_of_pregroupoid.2 ⟨key h, ?_⟩
  have h' : ∀ x ∈ e'.source ∩ e.source, ∃ g : G, ∀ᶠ z in 𝓝 x, e z = g • e' z := by
    intro x hx
    obtain ⟨g, hg⟩ := h x ⟨hx.2, hx.1⟩
    refine ⟨g⁻¹, ?_⟩
    filter_upwards [hg] with z hz
    rw [hz, inv_smul_smul]
  have := key h'
  rwa [← OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]

/-- Membership of a transition in the `(G,X)`-groupoid, pointwise on the overlap. -/
theorem symm_trans_mem_gxGroupoid_iff {e e' : OpenPartialHomeomorph M X} :
    e.symm.trans e' ∈ gxGroupoid G X ↔
      ∀ x ∈ e.source ∩ e'.source, ∃ g : G, ∀ᶠ z in 𝓝 x, e' z = g • e z :=
  ⟨fun h _ hx => eventually_smul_eq_of_mem_gxGroupoid h hx.1 hx.2, symm_trans_mem_gxGroupoid⟩

end Groupoid

/-! ### Charts of the maximal atlas -/

section MaximalAtlas

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M]

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
/-- Two eventual translations of a common chart give an eventual translation between them. -/
theorem eventually_smul_eq_of_eventually_smul_eq {e₀ e₁ e₂ : M → X} {x : M} {g h : G}
    (h₁ : ∀ᶠ z in 𝓝 x, e₁ z = g • e₀ z) (h₂ : ∀ᶠ z in 𝓝 x, e₂ z = h • e₀ z) :
    ∀ᶠ z in 𝓝 x, e₂ z = (h * g⁻¹) • e₁ z := by
  filter_upwards [h₁, h₂] with z hz₁ hz₂
  rw [hz₁, hz₂, mul_smul, inv_smul_smul]

variable [ChartedSpace X M]

/-- Two charts of the maximal atlas differ, near every point of their overlap, by an element of
`G`. -/
theorem eventually_smul_eq_of_mem_maximalAtlas {e e' : OpenPartialHomeomorph M X}
    (he : e ∈ (gxGroupoid G X).maximalAtlas M) (he' : e' ∈ (gxGroupoid G X).maximalAtlas M)
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ∃ g : G, ∀ᶠ z in 𝓝 x, e' z = g • e z :=
  eventually_smul_eq_of_mem_gxGroupoid
    ((gxGroupoid G X).compatible_of_mem_maximalAtlas he he') hx hx'

variable [HasGroupoid M (gxGroupoid G X)]

/-- **The maximal atlas, pointwise**: an open partial homeomorphism belongs to the maximal atlas
iff near every point of its source it is a translate of the preferred chart there. -/
theorem mem_maximalAtlas_iff_eventually {e : OpenPartialHomeomorph M X} :
    e ∈ (gxGroupoid G X).maximalAtlas M ↔
      ∀ x ∈ e.source, ∃ g : G, ∀ᶠ z in 𝓝 x, e z = g • chartAt X x z := by
  refine ⟨fun he x hx => eventually_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid G X).chart_mem_maximalAtlas x) he (mem_chart_source X x) hx, fun h => ?_⟩
  intro c hc
  have hcm := (gxGroupoid G X).subset_maximalAtlas hc
  refine ⟨symm_trans_mem_gxGroupoid fun x hx => ?_, symm_trans_mem_gxGroupoid fun x hx => ?_⟩
  · obtain ⟨g, hg⟩ := h x hx.1
    obtain ⟨k, hk⟩ := eventually_smul_eq_of_mem_maximalAtlas
      ((gxGroupoid G X).chart_mem_maximalAtlas x) hcm (mem_chart_source X x) hx.2
    exact ⟨_, eventually_smul_eq_of_eventually_smul_eq hg hk⟩
  · obtain ⟨g, hg⟩ := h x hx.2
    obtain ⟨k, hk⟩ := eventually_smul_eq_of_mem_maximalAtlas
      ((gxGroupoid G X).chart_mem_maximalAtlas x) hcm (mem_chart_source X x) hx.1
    exact ⟨_, eventually_smul_eq_of_eventually_smul_eq hk hg⟩

end MaximalAtlas

/-! ### The paper's `(G,X)`-atlases, per connected component of the overlaps -/

section Atlas

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M]

variable (G) in
/-- **A `(G,X)`-atlas** in the paper's sense (`RamcovGX.tex:342`): on every connected component
`W` of every overlap `e.source ∩ e'.source`, one element `g` of `G` with `e' = g • e` on `W`.
The component is that of a point `x` of the overlap, `connectedComponentIn`. -/
def IsGXAtlas (A : Set (OpenPartialHomeomorph M X)) : Prop :=
  ∀ e ∈ A, ∀ e' ∈ A, ∀ x ∈ e.source ∩ e'.source, ∃ g : G,
    ∀ y ∈ connectedComponentIn (e.source ∩ e'.source) x, e' y = g • e y

/-- The support of an atlas (`RamcovGX.tex:342`): the union of the sources of its charts. -/
def support (A : Set (OpenPartialHomeomorph M X)) : Set M := ⋃ e ∈ A, e.source

theorem mem_support {A : Set (OpenPartialHomeomorph M X)} {x : M} :
    x ∈ support A ↔ ∃ e ∈ A, x ∈ e.source := by
  simp [support]

theorem support_eq_univ_iff {A : Set (OpenPartialHomeomorph M X)} :
    support A = univ ↔ ∀ x : M, ∃ e ∈ A, x ∈ e.source := by
  simp [eq_univ_iff_forall, mem_support]

/-- When `X` is locally connected, the connected components of an open subset of a chart's
source are open: the source is locally homeomorphic to `X`. -/
theorem isOpen_connectedComponentIn_of_subset_source [LocallyConnectedSpace X]
    (e : OpenPartialHomeomorph M X) {s : Set M} (hs : IsOpen s) (hse : s ⊆ e.source) (x : M) :
    IsOpen (connectedComponentIn s x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [connectedComponentIn_eq hy]
  have hys : y ∈ s := connectedComponentIn_subset s x hy
  have hes : IsOpen (e '' s) := e.isOpen_image_of_subset_source hs hse
  have hVo : IsOpen (connectedComponentIn (e '' s) (e y)) := hes.connectedComponentIn
  have hVs : connectedComponentIn (e '' s) (e y) ⊆ e '' s := connectedComponentIn_subset _ _
  have hVt : connectedComponentIn (e '' s) (e y) ⊆ e.target :=
    hVs.trans (by rintro _ ⟨z, hz, rfl⟩; exact e.map_source (hse hz))
  have hyV : e y ∈ connectedComponentIn (e '' s) (e y) :=
    mem_connectedComponentIn (mem_image_of_mem e hys)
  have hyV' : y ∈ e.symm '' connectedComponentIn (e '' s) (e y) :=
    ⟨e y, hyV, e.left_inv (hse hys)⟩
  have hW : e.symm '' connectedComponentIn (e '' s) (e y) ⊆ connectedComponentIn s y := by
    refine (isPreconnected_connectedComponentIn.image _
      (e.continuousOn_symm.mono hVt)).subset_connectedComponentIn hyV' ?_
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hVs hq
    rw [e.left_inv (hse hz)]
    exact hz
  exact Filter.mem_of_superset ((e.isOpen_image_symm_of_subset_target hVo hVt).mem_nhds hyV') hW

omit [ContinuousConstSMul G X] in
/-- **The `φ` of a `(G,X)`-atlas is unique** (`RamcovGX.tex:342`: "By analyticity of $(G,X)$,
such a $\phi$ is unique"): two elements realising the transition on a component agree. -/
theorem eq_of_forall_mem_connectedComponentIn [LocallyConnectedSpace X] [IsAnalyticAction G X]
    {e e' : OpenPartialHomeomorph M X} {x : M} (hx : x ∈ e.source ∩ e'.source) {g h : G}
    (hg : ∀ y ∈ connectedComponentIn (e.source ∩ e'.source) x, e' y = g • e y)
    (hh : ∀ y ∈ connectedComponentIn (e.source ∩ e'.source) x, e' y = h • e y) : g = h := by
  have hWo := isOpen_connectedComponentIn_of_subset_source e
    (e.open_source.inter e'.open_source) inter_subset_left x
  have hWs : connectedComponentIn (e.source ∩ e'.source) x ⊆ e.source :=
    (connectedComponentIn_subset _ _).trans inter_subset_left
  refine eq_of_eqOn (e.isOpen_image_of_subset_source hWo hWs)
    ⟨e x, mem_image_of_mem e (mem_connectedComponentIn hx)⟩ ?_
  rintro _ ⟨y, hy, rfl⟩
  exact (hg y hy).symm.trans (hh y hy)

omit [ContinuousConstSMul G X] in
/-- The `φ` of a `(G,X)`-atlas, unique: `IsGXAtlas` with `∃!`. -/
theorem IsGXAtlas.existsUnique [LocallyConnectedSpace X] [IsAnalyticAction G X]
    {A : Set (OpenPartialHomeomorph M X)} (hA : IsGXAtlas G A) {e e' : OpenPartialHomeomorph M X}
    (he : e ∈ A) (he' : e' ∈ A) {x : M} (hx : x ∈ e.source ∩ e'.source) :
    ∃! g : G, ∀ y ∈ connectedComponentIn (e.source ∩ e'.source) x, e' y = g • e y := by
  obtain ⟨g, hg⟩ := hA e he e' he' x hx
  exact ⟨g, hg, fun h hh => eq_of_forall_mem_connectedComponentIn hx hh hg⟩

/-- **The transition of a `gxGroupoid` pair is one element of `G` on each connected component of
the overlap** — the rigidity of the action propagates the local translation along the
component. -/
theorem exists_smul_eq_on_connectedComponentIn [IsRigidAction G X]
    {e e' : OpenPartialHomeomorph M X} (h : e.symm.trans e' ∈ gxGroupoid G X) {x : M}
    (hx : x ∈ e.source ∩ e'.source) :
    ∃ g : G, ∀ y ∈ connectedComponentIn (e.source ∩ e'.source) x, e' y = g • e y := by
  obtain ⟨g₀, hg₀⟩ := eventually_smul_eq_of_mem_gxGroupoid h hx.1 hx.2
  let u : Set M := {y | ∀ᶠ z in 𝓝 y, e' z = g₀ • e z}
  let v : Set M := {y | ∃ g : G, (∀ᶠ z in 𝓝 y, e' z = g • e z) ∧ ∃ p : X, g • p ≠ g₀ • p}
  have hu : IsOpen u := isOpen_setOf_eventually_nhds
  have hv : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨g, hg, hne⟩
    filter_upwards [hg.eventually_nhds] with y' hy' using ⟨g, hy', hne⟩
  have hcover : e.source ∩ e'.source ⊆ u ∪ v := by
    intro y hy
    obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_gxGroupoid h hy.1 hy.2
    by_cases hgg : ∀ p : X, g • p = g₀ • p
    · left
      filter_upwards [hg] with z hz
      rw [hz, hgg]
    · right
      obtain ⟨p, hp⟩ := not_forall.1 hgg
      exact ⟨g, hg, p, hp⟩
  have hdisj : (e.source ∩ e'.source) ∩ (u ∩ v) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y ⟨hys, hyu, g, hg, p, hp⟩ => hp ?_
    have hev : ∀ᶠ z in 𝓝 y, g • e z = g₀ • e z ∧ z ∈ e.source := by
      filter_upwards [hyu, hg, e.open_source.mem_nhds hys.1] with z h1 h2 h3
      exact ⟨by rw [← h2]; exact h1, h3⟩
    obtain ⟨t, ht, hto, hyt⟩ := mem_nhds_iff.1 hev
    exact IsRigidAction.smul_eq_of_eqOn
      (e.isOpen_image_of_subset_source hto fun z hz => (ht hz).2) ⟨e y, mem_image_of_mem e hyt⟩
      (by rintro _ ⟨z, hz, rfl⟩; exact (ht hz).1) p
  have hxW : x ∈ connectedComponentIn (e.source ∩ e'.source) x := mem_connectedComponentIn hx
  rcases isPreconnected_iff_subset_of_disjoint.1
    (isPreconnected_connectedComponentIn (x := x) (F := e.source ∩ e'.source)) u v hu hv
    ((connectedComponentIn_subset _ _).trans hcover)
    (by rw [← subset_empty_iff, ← hdisj]
        exact inter_subset_inter_left _ (connectedComponentIn_subset _ _)) with hWu | hWv
  · exact ⟨g₀, fun y hy => (hWu hy).self_of_nhds⟩
  · have : x ∈ (e.source ∩ e'.source) ∩ (u ∩ v) := ⟨hx, hg₀, hWv hxW⟩
    rw [hdisj] at this
    exact this.elim

/-- A `(G,X)`-atlas has its transitions in the `(G,X)`-groupoid, when `X` is locally connected. -/
theorem IsGXAtlas.symm_trans_mem [LocallyConnectedSpace X] {A : Set (OpenPartialHomeomorph M X)}
    (hA : IsGXAtlas G A) {e e' : OpenPartialHomeomorph M X} (he : e ∈ A) (he' : e' ∈ A) :
    e.symm.trans e' ∈ gxGroupoid G X := by
  refine symm_trans_mem_gxGroupoid fun x hx => ?_
  obtain ⟨g, hg⟩ := hA e he e' he' x hx
  exact ⟨g, Filter.mem_of_superset ((isOpen_connectedComponentIn_of_subset_source e
    (e.open_source.inter e'.open_source) inter_subset_left x).mem_nhds
      (mem_connectedComponentIn hx)) hg⟩

/-- A set of charts with pairwise transitions in the groupoid is a `(G,X)`-atlas, when the
action is rigid. -/
theorem isGXAtlas_of_symm_trans_mem [IsRigidAction G X] {A : Set (OpenPartialHomeomorph M X)}
    (h : ∀ e ∈ A, ∀ e' ∈ A, e.symm.trans e' ∈ gxGroupoid G X) : IsGXAtlas G A :=
  fun e he e' he' _ hx => exists_smul_eq_on_connectedComponentIn (h e he e' he') hx

/-- **The two conventions agree** (DEC-16 against `RamcovGX.tex:342`): for a charted space over
a locally connected `X` with a rigid action, `HasGroupoid M (gxGroupoid G X)` iff its atlas is a
`(G,X)`-atlas in the paper's sense. -/
theorem hasGroupoid_iff_isGXAtlas [LocallyConnectedSpace X] [IsRigidAction G X]
    [ChartedSpace X M] : HasGroupoid M (gxGroupoid G X) ↔ IsGXAtlas G (atlas X M) :=
  ⟨fun _ => isGXAtlas_of_symm_trans_mem fun _ he _ he' => HasGroupoid.compatible he he',
    fun hA => ⟨fun he he' => hA.symm_trans_mem he he'⟩⟩

/-- The maximal atlas of a `(G,X)`-manifold is a `(G,X)`-atlas in the paper's sense. -/
theorem isGXAtlas_maximalAtlas [IsRigidAction G X] [ChartedSpace X M]
    [HasGroupoid M (gxGroupoid G X)] : IsGXAtlas G ((gxGroupoid G X).maximalAtlas M) :=
  isGXAtlas_of_symm_trans_mem fun _ he _ he' =>
    (gxGroupoid G X).compatible_of_mem_maximalAtlas he he'

/-- The charted space of an atlas covering `M`, the preferred chart at `x` chosen among those
whose source contains `x`. -/
@[reducible] noncomputable def chartedSpaceOfAtlas (A : Set (OpenPartialHomeomorph M X))
    (hA : ∀ x : M, ∃ e ∈ A, x ∈ e.source) : ChartedSpace X M where
  atlas := A
  chartAt x := (hA x).choose
  mem_chart_source x := (hA x).choose_spec.2
  chart_mem_atlas x := (hA x).choose_spec.1

/-- A `(G,X)`-atlas of support `M` (`RamcovGX.tex:343`) makes `M` a `(G,X)`-manifold in the
DEC-16 convention, the atlas being exactly the given one. -/
theorem hasGroupoid_chartedSpaceOfAtlas [LocallyConnectedSpace X]
    {A : Set (OpenPartialHomeomorph M X)} (hGX : IsGXAtlas G A)
    (hA : ∀ x : M, ∃ e ∈ A, x ∈ e.source) :
    @HasGroupoid X _ M _ (chartedSpaceOfAtlas A hA) (gxGroupoid G X) :=
  @HasGroupoid.mk X _ M _ (chartedSpaceOfAtlas A hA) (gxGroupoid G X)
    fun he he' => hGX.symm_trans_mem he he'

/-- **The paper's `(G,X)`-manifolds are exactly the DEC-16 ones** (`RamcovGX.tex:343`): `M`
carries a `(G,X)`-atlas of support `M` iff it carries a charted space structure over `X` with
transitions in `gxGroupoid G X`. -/
theorem exists_isGXAtlas_iff_exists_hasGroupoid [LocallyConnectedSpace X] [IsRigidAction G X] :
    (∃ A : Set (OpenPartialHomeomorph M X), IsGXAtlas G A ∧ support A = univ) ↔
      ∃ cs : ChartedSpace X M, @HasGroupoid X _ M _ cs (gxGroupoid G X) := by
  constructor
  · rintro ⟨A, hGX, hA⟩
    rw [support_eq_univ_iff] at hA
    exact ⟨chartedSpaceOfAtlas A hA, hasGroupoid_chartedSpaceOfAtlas hGX hA⟩
  · rintro ⟨cs, hcs⟩
    letI := cs
    exact ⟨atlas X M, hasGroupoid_iff_isGXAtlas.1 hcs, support_eq_univ_iff.2 fun x =>
      ⟨chartAt X x, chart_mem_atlas X x, mem_chart_source X x⟩⟩

end Atlas

/-! ### `(G,X)`-morphisms -/

section Morphism

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M] {N : Type y} [TopologicalSpace N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace X M] [ChartedSpace X N] [ChartedSpace X P]

variable (G X) in
/-- **A `(G,X)`-morphism** (SCOPE (b)): a continuous map which, read in the preferred charts
near every point, is the restriction of an element of `G`. Chart independence over the maximal
atlases is `IsGXMorphism.exists_smul_eq_of_mem_maximalAtlas`. -/
structure IsGXMorphism (f : M → N) : Prop where
  continuous : Continuous f
  exists_smul_eq : ∀ x : M, ∃ g : G, ∀ᶠ y in 𝓝 x, chartAt X (f x) (f y) = g • chartAt X x y

omit [ContinuousConstSMul G X] in
/-- The definition, unfolded. -/
theorem isGXMorphism_iff' {f : M → N} : IsGXMorphism G X f ↔ Continuous f ∧
    ∀ x : M, ∃ g : G, ∀ᶠ y in 𝓝 x, chartAt X (f x) (f y) = g • chartAt X x y :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Chart independence**: a `(G,X)`-morphism read in any charts of the maximal atlases is,
near every point, the restriction of an element of `G`. -/
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

/-- A `(G,X)`-morphism, characterised over the maximal atlases. -/
theorem isGXMorphism_iff_maximalAtlas [HasGroupoid M (gxGroupoid G X)]
    [HasGroupoid N (gxGroupoid G X)] {f : M → N} :
    IsGXMorphism G X f ↔ Continuous f ∧
      ∀ e ∈ (gxGroupoid G X).maximalAtlas M, ∀ e' ∈ (gxGroupoid G X).maximalAtlas N,
        ∀ x ∈ e.source, f x ∈ e'.source → ∃ g : G, ∀ᶠ y in 𝓝 x, e' (f y) = g • e y := by
  refine ⟨fun hf => ⟨hf.continuous, fun e he e' he' x hx hfx =>
    hf.exists_smul_eq_of_mem_maximalAtlas he he' hx hfx⟩, fun h => ⟨h.1, fun x => ?_⟩⟩
  exact h.2 _ ((gxGroupoid G X).chart_mem_maximalAtlas x) _
    ((gxGroupoid G X).chart_mem_maximalAtlas (f x)) x (mem_chart_source X x)
    (mem_chart_source X (f x))

omit [ContinuousConstSMul G X] in
/-- The identity is a `(G,X)`-morphism. -/
theorem isGXMorphism_id : IsGXMorphism G X (id : M → M) :=
  ⟨continuous_id, fun _ => ⟨1, Eventually.of_forall fun _ => (one_smul G _).symm⟩⟩

omit [ContinuousConstSMul G X] in
/-- **Composition** of `(G,X)`-morphisms. -/
theorem IsGXMorphism.comp {f : M → N} {f' : N → P} (hf' : IsGXMorphism G X f')
    (hf : IsGXMorphism G X f) : IsGXMorphism G X (f' ∘ f) := by
  refine ⟨hf'.continuous.comp hf.continuous, fun x => ?_⟩
  obtain ⟨g, hg⟩ := hf.exists_smul_eq x
  obtain ⟨g', hg'⟩ := hf'.exists_smul_eq (f x)
  refine ⟨g' * g, ?_⟩
  filter_upwards [hf.continuous.continuousAt.eventually hg', hg] with y h1 h2
  simp only [Function.comp_apply]
  rw [h1, h2, mul_smul]

/-- **A `(G,X)`-morphism is a local homeomorphism.** -/
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

/-- A `(G,X)`-morphism is an open map. -/
theorem IsGXMorphism.isOpenMap {f : M → N} (hf : IsGXMorphism G X f) : IsOpenMap f :=
  hf.isLocalHomeomorph.isOpenMap

omit [ContinuousConstSMul G X] in
/-- A `(G,X)`-morphism into the model space (its charted space over itself): near every point,
the map is a translate of the preferred chart. This is the shape of a developing map. -/
theorem isGXMorphism_iff_model {D : M → X} :
    IsGXMorphism G X D ↔ Continuous D ∧
      ∀ x : M, ∃ g : G, ∀ᶠ y in 𝓝 x, D y = g • chartAt X x y := by
  simp only [isGXMorphism_iff', chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq]

/-- The action of an element of `G` is a `(G,X)`-morphism of the model space. -/
theorem isGXMorphism_smul (g : G) : IsGXMorphism G X fun p : X => g • p :=
  ⟨continuous_const_smul g, fun _ => ⟨g, Eventually.of_forall fun _ => by simp⟩⟩

omit [ContinuousConstSMul G X] in
/-- **Analyticity of `(G,X)`-morphisms**: two `(G,X)`-morphisms from a connected `M` into a
Hausdorff `N` which agree on a nonempty open set agree everywhere. -/
theorem IsGXMorphism.eq_of_eqOn [IsRigidAction G X] [PreconnectedSpace M] [T2Space N]
    {f₁ f₂ : M → N} (hf₁ : IsGXMorphism G X f₁) (hf₂ : IsGXMorphism G X f₂) {U : Set M}
    (hU : IsOpen U) (hne : U.Nonempty) (heq : EqOn f₁ f₂ U) : f₁ = f₂ := by
  have hSo : IsOpen (interior {x | f₁ x = f₂ x}) := isOpen_interior
  have hUS : U ⊆ interior {x | f₁ x = f₂ x} := interior_maximal (fun x hx => heq hx) hU
  have hSc : IsClosed (interior {x | f₁ x = f₂ x}) := by
    refine isClosed_of_closure_subset fun x hx => ?_
    have hfx : f₁ x = f₂ x := (isClosed_eq hf₁.continuous hf₂.continuous).closure_subset
      (closure_mono interior_subset hx)
    obtain ⟨g₁, hg₁⟩ := hf₁.exists_smul_eq x
    obtain ⟨g₂, hg₂⟩ := hf₂.exists_smul_eq x
    rw [← hfx] at hg₂
    have hx₂ : f₂ x ∈ (chartAt X (f₁ x)).source := by
      rw [← hfx]; exact mem_chart_source X (f₁ x)
    have hev : ∀ᶠ y in 𝓝 x, (chartAt X (f₁ x) (f₁ y) = g₁ • chartAt X x y ∧
        chartAt X (f₁ x) (f₂ y) = g₂ • chartAt X x y) ∧ y ∈ (chartAt X x).source ∧
        f₁ y ∈ (chartAt X (f₁ x)).source ∧ f₂ y ∈ (chartAt X (f₁ x)).source := by
      filter_upwards [hg₁, hg₂, (chartAt X x).open_source.mem_nhds (mem_chart_source X x),
        hf₁.continuous.continuousAt.eventually
          ((chartAt X (f₁ x)).open_source.mem_nhds (mem_chart_source X (f₁ x))),
        hf₂.continuous.continuousAt.eventually
          ((chartAt X (f₁ x)).open_source.mem_nhds hx₂)] with y a b c d e
      exact ⟨⟨a, b⟩, c, d, e⟩
    obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 hev
    obtain ⟨z, hzt, hzS⟩ := mem_closure_iff.1 hx t hto hxt
    have hsmul : ∀ q : X, g₁ • q = g₂ • q := by
      refine IsRigidAction.smul_eq_of_eqOn ((chartAt X x).isOpen_image_of_subset_source
        (hto.inter hSo) fun y hy => (ht hy.1).2.1)
        ⟨chartAt X x z, mem_image_of_mem _ ⟨hzt, hzS⟩⟩ ?_
      rintro _ ⟨y, ⟨hyt, hyS⟩, rfl⟩
      have hy : f₁ y = f₂ y := interior_subset (s := {x | f₁ x = f₂ x}) hyS
      show g₁ • chartAt X x y = g₂ • chartAt X x y
      rw [← (ht hyt).1.1, ← (ht hyt).1.2, hy]
    have hts : t ⊆ {x | f₁ x = f₂ x} := fun y hy => by
      obtain ⟨⟨h1, h2⟩, -, h3, h4⟩ := ht hy
      exact (chartAt X (f₁ x)).injOn h3 h4 (by rw [h1, h2, hsmul])
    exact mem_interior.2 ⟨t, hts, hto, hxt⟩
  have hSu : interior {x | f₁ x = f₂ x} = univ :=
    IsClopen.eq_univ ⟨hSc, hSo⟩ ⟨_, hUS hne.some_mem⟩
  funext x
  have : x ∈ interior {x | f₁ x = f₂ x} := by rw [hSu]; exact mem_univ x
  exact interior_subset (s := {x | f₁ x = f₂ x}) this

end Morphism

/-! ### Pullback of a `(G,X)`-structure along a local homeomorphism -/

section Pullback

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M] {N : Type y} [TopologicalSpace N]
  [ChartedSpace X N]

variable (G X) in
/-- The charts of `M` in which `p : M → N` is, near every point, the restriction of an element
of `G`: the maximal atlas of the pullback structure (`maximalAtlas_pullback`). -/
def gxPullbackAtlas (p : M → N) : Set (OpenPartialHomeomorph M X) :=
  {e | ∀ x ∈ e.source, ∃ g : G, ∀ᶠ y in 𝓝 x, chartAt X (p x) (p y) = g • e y}

/-- A local homeomorphism `M → N` at `x`, chosen. -/
noncomputable def localHomeomorphAt {p : M → N} (hp : IsLocalHomeomorph p) (x : M) :
    OpenPartialHomeomorph M N :=
  (hp x).choose

theorem mem_localHomeomorphAt_source {p : M → N} (hp : IsLocalHomeomorph p) (x : M) :
    x ∈ (localHomeomorphAt hp x).source :=
  (hp x).choose_spec.1

theorem coe_localHomeomorphAt {p : M → N} (hp : IsLocalHomeomorph p) (x : M) :
    ⇑(localHomeomorphAt hp x) = p :=
  (hp x).choose_spec.2.symm

/-- **The pullback of a charted space along a local homeomorphism**: the chart at `x` is the
chart of `N` at `p x` composed with a local inverse branch of `p` at `x`. -/
@[reducible] noncomputable def pullbackChartedSpace {p : M → N} (hp : IsLocalHomeomorph p) :
    ChartedSpace X M where
  atlas := range fun x => (localHomeomorphAt hp x).trans (chartAt X (p x))
  chartAt x := (localHomeomorphAt hp x).trans (chartAt X (p x))
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage, coe_localHomeomorphAt]
    exact ⟨mem_localHomeomorphAt_source hp x, mem_chart_source X (p x)⟩
  chart_mem_atlas x := ⟨x, rfl⟩

/-- The pulled-back structure is a `(G,X)`-structure. -/
theorem hasGroupoid_pullback [HasGroupoid N (gxGroupoid G X)] {p : M → N}
    (hp : IsLocalHomeomorph p) :
    @HasGroupoid X _ M _ (pullbackChartedSpace hp) (gxGroupoid G X) := by
  refine @HasGroupoid.mk X _ M _ (pullbackChartedSpace hp) (gxGroupoid G X) ?_
  rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
  refine symm_trans_mem_gxGroupoid fun z hz => ?_
  simp only [OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    coe_localHomeomorphAt] at hz
  obtain ⟨g, hg⟩ := eventually_smul_eq_of_mem_maximalAtlas
    ((gxGroupoid G X).chart_mem_maximalAtlas (p x))
    ((gxGroupoid G X).chart_mem_maximalAtlas (p x')) hz.1.2 hz.2.2
  refine ⟨g, ?_⟩
  filter_upwards [hp.continuous.continuousAt.eventually hg] with y hy
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, coe_localHomeomorphAt]
  exact hy

omit [ContinuousConstSMul G X] in
/-- For the pulled-back structure, `p` is a `(G,X)`-morphism. -/
theorem isGXMorphism_pullback {p : M → N} (hp : IsLocalHomeomorph p) :
    @IsGXMorphism G X _ _ _ M _ N _ (pullbackChartedSpace hp) _ p := by
  refine @IsGXMorphism.mk G X _ _ _ M _ N _ (pullbackChartedSpace hp) _ p hp.continuous
    fun x => ⟨1, Eventually.of_forall fun y => ?_⟩
  show chartAt X (p x) (p y) = (1 : G) • ((localHomeomorphAt hp x).trans (chartAt X (p x))) y
  rw [one_smul, OpenPartialHomeomorph.coe_trans, Function.comp_apply, coe_localHomeomorphAt]

/-- **Uniqueness of the pullback**: for any `(G,X)`-structure on `M` making `p` a
`(G,X)`-morphism, the maximal atlas is `gxPullbackAtlas G X p` — it depends on `p` alone. -/
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

/-- The maximal atlas of the pulled-back structure. -/
theorem maximalAtlas_pullback [HasGroupoid N (gxGroupoid G X)] {p : M → N}
    (hp : IsLocalHomeomorph p) :
    @StructureGroupoid.maximalAtlas X M _ _ (pullbackChartedSpace hp) (gxGroupoid G X) =
      gxPullbackAtlas G X p := by
  letI := pullbackChartedSpace (X := X) hp
  haveI := hasGroupoid_pullback (G := G) (X := X) hp
  exact (isGXMorphism_pullback (G := G) (X := X) hp).maximalAtlas_eq

/-- **The pullback of a `(G,X)`-structure along a local homeomorphism** (`RamcovGX.tex:549`,
"by usual results"): there is a `(G,X)`-structure on `M` making `p` a `(G,X)`-morphism, and it is
unique — any two such have the same maximal atlas. -/
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
  rw [maximalAtlas_pullback hp]
  letI := cs'
  exact hp'.maximalAtlas_eq

/-- The case of a covering map (`IsCoveringMap.isLocalHomeomorph`). -/
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

/-! ### An instance: the translations of the line -/

section Example

/-- The translations of `ℝ` act analytically: a translation is determined by one point. -/
instance isAnalyticAction_translation : IsAnalyticAction (Multiplicative ℝ) ℝ :=
  IsAnalyticAction.of_eq_of_eqOn fun {g h} _ _ hne heq => by
    obtain ⟨p, hp⟩ := hne
    have : Multiplicative.toAdd g + p = Multiplicative.toAdd h + p := heq hp
    exact Multiplicative.toAdd.injective (add_right_cancel this)

/-- The translations of `ℝ` act by homeomorphisms. -/
instance continuousConstSMul_translation : ContinuousConstSMul (Multiplicative ℝ) ℝ :=
  ⟨fun _ => continuous_const.add continuous_id⟩

/-- `(translations, ℝ)` is an analytical structure in the paper's sense. -/
theorem analyticStructure_translation : AnalyticStructure (Multiplicative ℝ) ℝ where
  connectedSpace := inferInstance
  locallyConnectedSpace := locallyConnectedSpace_iff_connected_subsets.2 fun x U hU => by
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
    exact ⟨Metric.ball x ε, Metric.ball_mem_nhds x hε,
      by rw [Real.ball_eq_Ioo]; exact isPreconnected_Ioo, hεU⟩
  t2Space := inferInstance
  continuousConstSMul := inferInstance
  isAnalyticAction := inferInstance

end Example

end GX
