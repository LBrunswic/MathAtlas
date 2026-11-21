import Causal.Port.SingularAtlas
import Causal.GXSingular

/-!
# The causality of a singular `(G,X)`-manifold, on gx's almost-everywhere atlases (DEC-25)

`prop:GX_sing_espace_temps_topo` — `ETT.tex:616` (proof `ETT.tex:626`).
`rem:hypotheses_proposition_prop_gx` — `ETT.tex:635`.
**Neither is marked.** The proposition is proved under one hypothesis the paper does not state,
(b′) below, which is shown to be exactly what its conclusion needs; its uniqueness is among
absolutely minimal causalities (OQ-18, open). The remark is proved for every a.e. morphism which
is a local homeomorphism, singular points included; at branch points it is open.

Target `T-ett-gxsingular-dec25`: the reconciliation of `Causal.GXSingular` (abstracted atlas)
with DEC-25, which rules OQ-19 by gx's definitions: "a singular (G,X)-manifold carries a maximal
almost-everywhere (G,X)-atlas, i.e. a (G,X)-atlas on a portly subset; a morphism is an
almost-everywhere morphism; an X_A-manifold is read from model spaces as in gx". The vocabulary is
the verbatim port of gx's a.e. atlases, `Causal.Port.SingularAtlas` (on
`Causal.Port.Portly` and the strict `Causal.Port.GXBasic`): `SingularGXStructure`,
`aeAtlas`, `Reg`, `Sing`, `IsRegularOn`, `IsAEMorphism`, `regLocus`.

> Let $(G,X,X_A)$ be an analytic singular structure and let $(M,\A)$ be a $(G,X,X_A)$-manifold.
> Assume moreover that (a) $X$ is a causally arc-connected Baire topological spacetime on which
> $G$ acts by morphisms of topological spacetimes; (b) for every $\alpha \in A$, the model space
> $X_\alpha$ is a causally arc-connected topological spacetime whose causality extends the
> natural causality of $\reg(X_\alpha)$ given by its $(G,X)$-manifold structure. Then $M$ admits
> a unique topological spacetime structure such that for every chart $(\U,Y,\V,\phi)$ of $\A$
> the homeomorphism $\phi:\U\rightarrow \V$ is an isomorphism of topological spacetimes.

> […] hypothesis $(B)$ from the fact that transition maps are restrictions of elements of $G$ and
> of isomorphisms of the model spaces […] (`ETT.tex:631–632`)

> Under the hypotheses of Proposition \ref{prop:GX_sing_espace_temps_topo}, every branched
> $(G,X)$-morphism is a morphism of topological spacetimes.

## What is proved (no `sorry` in this file)

* `IsAEChart G X e`: an open partial homeomorphism `e : M ⇀ N` of singular `(G,X)`-manifolds
  which, with its inverse, induces `(G,X)`-morphisms on the regular parts (gx's `IsRegularOn`):
  an a.e. isomorphism of open subsets, subtype-free (kb/0001). **It is gx's notion**:
  `isAEChart_iff_isAEMorphism` — for `e` realising `φ : U ≃ₜ V`, `e` is an `IsAEChart` iff `φ`
  is an a.e. `(G,X)`-isomorphism of the open subsets with their induced structures (gx's reading
  of "isomorphism" in `def:atlas`, `RamcovGX.tex:1905`); every such `φ` with `U ≠ ∅` is realised
  (`exists_openPartialHomeomorph_of_homeomorph`).
* **`existsUnique_causality_singularGX_dec25`** (`prop:GX_sing_espace_temps_topo`): under (a), (b)
  and (b′), if the singular points of `M` lie in `X_A`-charts, `M` carries an absolutely minimal
  causality for which every chart of its maximal a.e. atlas and every `X_A`-chart (every
  `IsAEChart` into a model) is an isomorphism, and any absolutely minimal causality for which
  some such chart at each point is an isomorphism is that one. gx-style form:
  `existsUnique_causality_singularGX_dec25_of_isAEMorphism`.
* **(b′) is exactly what is missing** (for this file's class of manifolds and reading of the
  charts, SCOPE): `forall_exists_causality_singularGX_iff` — under (a), (b),
  the existence half holds for every such `M` iff every a.e. isomorphism between open subsets of
  the model spaces is an isomorphism of topological spacetimes; at regular sources (b′) holds
  anyway (`chartIso_model_of_subset_reg`, `chartIso_of_isAEChart_of_subset_reg`).
* `rem:hypotheses_proposition_prop_gx`: **`strongMorphism_of_isAEMorphism_of_isLocalHomeomorph`**
  — for the causalities of the proposition, every a.e. `(G,X)`-morphism which is a local
  homeomorphism is a strong morphism (near a singular point, `f` followed by an `X_A`-chart of `N`
  is an `X_A`-chart of `M`); `strongMorphism_of_isRegularOn_univ`, `strongMorphism_of_isAEMorphism`
  (the case without singular points, `(a)` alone); `weakMorphism_local_of_isRegularOn` (on its
  regular locus an a.e. morphism is a local isomorphism); `weakMorphism_iff_of_isAEMorphism` (an
  a.e. morphism is a weak morphism iff the weak-morphism condition holds at the points outside
  `Reg(f) = Reg(M) ∩ f⁻¹(Reg(N))`).
* Non-vacuity: `singularGX_dec25_line` (`ℝ`, one model; the singular locus is empty).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(G,X,X_A)` an analytic singular structure | ⚠ weakened: `LocallyConnectedSpace X` (plus `T2Space X`, `IsRigidAction G X` for the gx bridge); analyticity of the family of models not used |
| `(M,𝒜)` a `(G,X,X_A)`-manifold | ✓ carried (DEC-25): `SingularGXStructure G X M` (maximal a.e. atlas); ⚠ weakened: only the singular points need an `X_A`-chart (gx's `X_A`-atlas covers `M`, with charts of connected image centred in `S_α`; here `IsAEChart` asks neither) |
| the charts of `𝒜` | ⚠ reading: every chart of the maximal a.e. atlas (into `X`) and every `IsAEChart` into a model (SCOPE) |
| (a) `X` causally arc-connected, `G` acts by morphisms | ✓ carried (strong morphisms, DEC-12) |
| (a) `X` Baire | **⚠ weakened: not used** (OQ-10) |
| (b) `X_α` causally arc-connected | ✓ carried |
| (b) extends the natural causality of `reg(X_α)` | ✓ carried as `hreg`: every chart of the maximal a.e. atlas of `X_α` is an isomorphism onto `X` — implied by (b) (the natural causality makes every chart of `reg(X_α)` an isomorphism, and these are the charts of the maximal a.e. atlas), equivalent to it under OQ-18's uniqueness |
| (none) | **⚠ strengthened (b′)**: every a.e. isomorphism between open subsets of the model spaces is an isomorphism of topological spacetimes (`hiso`, local form as DEC-62); necessary (`forall_exists_causality_singularGX_iff`) |
| uniqueness, as written | ⚠ strengthened: among absolutely minimal causalities (OQ-18) |
| topological spacetimes second countable, Hausdorff | ⚠ weakened: not used |
| remark: "branched `(G,X)`-morphism" | ✓ read (DEC-25): an a.e. `(G,X)`-morphism (`IsAEMorphism`) |
| remark: every branched morphism | ⚠ strengthened: `f` a local homeomorphism (unbranched; singular points allowed); branch points open |
| remark: "morphism of topological spacetimes" | ⚠ reading: strong (DEC-10/12) where proved, weak in the reduction |

## SCOPE (disclosed)

* **(b′)** is the paper's "isomorphisms of the model spaces", read in DEC-62's local form. (a) and
  (b) are not known to give it: (b) fixes the causality of `X_α` on its regular part only, and an a.e.
  isomorphism of model spaces is a `(G,X)`-map there only. The transition between two
  `X_A`-charts at a singular point is such an isomorphism (`IsAEChart.trans`, `IsAEChart.symm`),
  and the causalities they transport agree near it when it is causal
  (`ChartIso.agreeOn_of_isAEChart_of_isAEChart`); `forall_exists_causality_singularGX_iff` shows
  no weaker condition on the models suffices — for this file's class of manifolds and its
  maximal-atlas reading of the charts (under gx's definition of an `X_A`-manifold, `X_α` itself may
  not qualify). The proof of the proposition was supplied editorially (`ETT.tex:625`).
* **The atlas.** "Every chart `(U,Y,V,φ)` of `𝒜`" is read over the maximal atlas, as DEC-16 for
  `(G,X)`-manifolds: all charts of the maximal a.e. atlas and all a.e. isomorphisms of open
  subsets of `M` onto open subsets of models. gx's `X_A`-charts (connected image, centred at a
  point sent into `S_α`) are among them (`isAEChart_iff_isAEMorphism`), so the conclusion covers
  them; over fewer charts the conclusion is weaker.
* **Uniqueness** is false in the library's gluing-free reading of `defi:causalite` already for
  `(G,X)`-manifolds (`GX_maximal_not_unique`, `Causal.GXStructure`); proved among absolutely
  minimal causalities, for which one isomorphic chart at each point suffices.
* **The remark.** Where `f` is a local homeomorphism it reads in `X_A`-charts as an `X_A`-chart,
  so the proposition's causalities make it a local isomorphism. At a branch point it is not, and
  nothing in (a), (b), (b′) constrains it there: (b′) is about isomorphisms. The printed remark
  (every a.e. morphism, branch points included) is neither proved nor refuted;
  `weakMorphism_iff_of_isAEMorphism` is the exact reduction to the points outside `Reg(f)`.
* **Witness.** lean-causal has no singular `(G,X)`-structure with a singular point (gx's on its
  BTZ models are not ported), so `singularGX_dec25_line` has `Sing = ∅`: it exercises the
  hypotheses and the uniqueness, not (b′) at a singular point.
* **Restated verbatim from gx** (hub commit `a6be352`): `IsPortly.preimage_val_of_isOpen`
  (`lean-gx/GX/Branched/Basic.lean` l.728–739) and gx's section `Opens` of
  `lean-gx/GX/SingularII/Tame.lean` l.145–182 (`isAELocalHomeomorph_opensSingular_val` …
  `sing_opensSingular`, the instance `opensSingularGXStructure`), `GX.x` as `Causal.x`; the only
  change is `set_option linter.unusedSectionVars false in` before the first theorem (gx sets it
  for the whole file). Their elaborated types and values equal gx's after the rename.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology TopologicalSpace

universe u v w y z u'

/-- An eventual property near a point of an open set holds on an open neighbourhood of the point
inside the set. -/
theorem exists_opens_of_eventually {M : Type u} [TopologicalSpace M] {p : M → Prop} {x : M}
    {W : Set M} (hW : IsOpen W) (hxW : x ∈ W) (h : ∀ᶠ y in 𝓝 x, p y) :
    ∃ O : Opens M, x ∈ O ∧ (O : Set M) ⊆ W ∧ ∀ z ∈ O, p z := by
  obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 h
  exact ⟨⟨t ∩ W, hto.inter hW⟩, ⟨hxt, hxW⟩, inter_subset_right, fun z hz => ht hz.1⟩

/-! ### Charts which are almost-everywhere isomorphisms -/

section AEChart

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  {M : Type u} [TopologicalSpace M] [SingularGXStructure G X M]
  {N : Type y} [TopologicalSpace N] [SingularGXStructure G X N]
  {P : Type z} [TopologicalSpace P] [SingularGXStructure G X P]

variable (G X) in
/-- An **a.e. `(G,X)`-isomorphism chart** `e : M ⇀ N` between singular `(G,X)`-manifolds
(DEC-25): `e` and its inverse both induce `(G,X)`-morphisms (gx's `IsRegularOn`, `def:morphism`)
on the regular parts of their sources. -/
structure IsAEChart (e : OpenPartialHomeomorph M N) : Prop where
  regularOn : IsRegularOn G (aeAtlas G X M) (aeAtlas G X N) e (e.source ∩ Reg G X M)
  regularOn_symm : IsRegularOn G (aeAtlas G X N) (aeAtlas G X M) e.symm (e.target ∩ Reg G X N)

theorem IsAEChart.symm {e : OpenPartialHomeomorph M N} (h : IsAEChart G X e) :
    IsAEChart G X e.symm :=
  ⟨h.regularOn_symm, by simpa only [OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.symm_target] using h.regularOn⟩

theorem IsAEChart.mem_reg_iff {e : OpenPartialHomeomorph M N} (h : IsAEChart G X e) {x : M}
    (hx : x ∈ e.source) : x ∈ Reg G X M ↔ e x ∈ Reg G X N := by
  refine ⟨fun hr => h.regularOn.mapsTo ⟨hx, hr⟩, fun hr => ?_⟩
  have := h.regularOn_symm.mapsTo ⟨e.map_source hx, hr⟩
  rwa [e.left_inv hx] at this

/-- The composite of two maps inducing `(G,X)`-morphisms on the regular parts of their sources
induces one on the regular part of its source. -/
theorem isRegularOn_trans {e₁ : OpenPartialHomeomorph M N} {e₂ : OpenPartialHomeomorph N P}
    (h₁ : IsRegularOn G (aeAtlas G X M) (aeAtlas G X N) e₁ (e₁.source ∩ Reg G X M))
    (h₂ : IsRegularOn G (aeAtlas G X N) (aeAtlas G X P) e₂ (e₂.source ∩ Reg G X N)) :
    IsRegularOn G (aeAtlas G X M) (aeAtlas G X P) (e₁.trans e₂)
      ((e₁.trans e₂).source ∩ Reg G X M) := by
  have hsrc : ∀ {x}, x ∈ (e₁.trans e₂).source → x ∈ e₁.source ∧ e₁ x ∈ e₂.source := fun hx => by
    rw [OpenPartialHomeomorph.trans_source] at hx
    exact hx
  refine ⟨(e₁.trans e₂).open_source.inter (isOpen_reg G X M), fun x hx => hx.2,
    fun x hx => ?_, (e₁.trans e₂).continuousOn.mono inter_subset_left, ?_⟩
  · obtain ⟨hx₁, hx₂⟩ := hsrc hx.1
    exact h₂.mapsTo ⟨hx₂, h₁.mapsTo ⟨hx₁, hx.2⟩⟩
  · intro x hx c hc r hr hxc hxr
    obtain ⟨hx₁, hx₂⟩ := hsrc hx.1
    have hN : e₁ x ∈ Reg G X N := h₁.mapsTo ⟨hx₁, hx.2⟩
    obtain ⟨d, hd, hxd⟩ := mem_support.1 hN
    obtain ⟨g₁, hg₁⟩ := h₁.exists_smul_eq x ⟨hx₁, hx.2⟩ c hc d hd hxc hxd
    obtain ⟨g₂, hg₂⟩ := h₂.exists_smul_eq (e₁ x) ⟨hx₂, hN⟩ d hd r hr hxd hxr
    refine ⟨g₂ * g₁, ?_⟩
    filter_upwards [(e₁.continuousAt hx₁).eventually hg₂, hg₁] with y h1 h2
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, h1, h2, mul_smul]

theorem IsAEChart.trans {e₁ : OpenPartialHomeomorph M N} {e₂ : OpenPartialHomeomorph N P}
    (h₁ : IsAEChart G X e₁) (h₂ : IsAEChart G X e₂) : IsAEChart G X (e₁.trans e₂) := by
  refine ⟨isRegularOn_trans h₁.regularOn h₂.regularOn, ?_⟩
  have key := isRegularOn_trans h₂.regularOn_symm h₁.regularOn_symm
  have hT : (e₁.trans e₂).target = (e₂.symm.trans e₁.symm).source := by
    rw [← OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]; rfl
  rw [hT, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  exact key

theorem isAEChart_refl [ContinuousConstSMul G X] [LocallyConnectedSpace X] :
    IsAEChart G X (OpenPartialHomeomorph.refl M) := by
  have hA := (isMaximalAEAtlas_aeAtlas G X M).1.1
  have key : IsRegularOn G (aeAtlas G X M) (aeAtlas G X M) (OpenPartialHomeomorph.refl M)
      ((OpenPartialHomeomorph.refl M).source ∩ Reg G X M) :=
    IsRegularOn.of_exists hA hA ((OpenPartialHomeomorph.refl M).open_source.inter
      (isOpen_reg G X M)) (fun x hx => hx.2) (fun x hx => hx.2)
      ((OpenPartialHomeomorph.refl M).continuousOn.mono inter_subset_left) fun x hx => by
        obtain ⟨e, he, hxe⟩ := mem_support.1 hx.2
        exact ⟨e, he, e, he, hxe, hxe, 1, Eventually.of_forall fun _ => by simp⟩
  exact ⟨key, by simpa using key⟩

end AEChart

/-! ### Open subsets of a singular `(G,X)`-manifold, and gx's isomorphisms of open subsets

Restated verbatim from gx (hub commit `a6be352`): `IsPortly.preimage_val_of_isOpen` from
`lean-gx/GX/Branched/Basic.lean` l.728–739, and the section `Opens` of
`lean-gx/GX/SingularII/Tame.lean` l.145–182 (`isAELocalHomeomorph_opensSingular_val` …
`sing_opensSingular`), each `GX.x` as `Causal.x`. They make an open subset `U` of a singular
`(G,X)`-manifold one, by the pullback along the inclusion (`lem:aepullback`), which is how gx reads
"`φ : U → V` an isomorphism of singular `(G,X)`-manifolds" in `def:atlas` (`RamcovGX.tex:1905`,
gx's `XAChart`). The bridge `isAEChart_of_isAEMorphism` shows that such an isomorphism, realised
by an open partial homeomorphism, is an `IsAEChart`. -/

section Opens

variable {X : Type*} [TopologicalSpace X]

/-- A portly set meets an open set in a set portly in it. -/
theorem IsPortly.preimage_val_of_isOpen {P O : Set X} (hP : IsPortly P) (hO : IsOpen O) :
    IsPortly (((↑) : O → X) ⁻¹' P) := by
  have h : ((↑) : O → X) ⁻¹' P = (↑) ⁻¹' (P ∩ O) := by
    ext z; exact ⟨fun hz => ⟨hz, z.2⟩, fun hz => hz.1⟩
  rw [h, isPortly_subtype_iff hO inter_subset_right]
  refine ⟨hP.isOpen.inter hO, ?_, fun W hW hWO hWc => ?_⟩
  · rw [inter_comm]; exact hP.dense.open_subset_closure_inter hO
  · have : W ∩ (P ∩ O) = W ∩ P := by
      ext y; exact ⟨fun hy => ⟨hy.1, hy.2.1⟩, fun hy => ⟨hy.1, hy.2, hWO hy.1⟩⟩
    rw [this]
    exact hP.locallyConnectedIn W hW hWc

end Opens

section Opens

variable {G : Type*} {X : Type*} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  {M : Type*} [TopologicalSpace M] [SingularGXStructure G X M]

set_option linter.unusedSectionVars false in
/-- The inclusion of an open subset is almost everywhere a local homeomorphism into the regular
locus. -/
theorem isAELocalHomeomorph_opensSingular_val (U : Opens M) :
    IsAELocalHomeomorph (aeAtlas G X M) (Subtype.val : U → M) :=
  ⟨Subtype.val ⁻¹' Reg G X M, Reg G X M, (isPortly_reg G X M).preimage_val_of_isOpen U.isOpen,
    isPortly_reg G X M, subset_rfl, fun _ h => h,
    U.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn⟩

theorem aePullback_opensSingular_val_spec (U : Opens M) :
    IsMaximalAEAtlas G (aePullback G (aeAtlas G X M) (Subtype.val : U → M)) ∧
      IsAEMorphismOf G (aePullback G (aeAtlas G X M) (Subtype.val : U → M)) (aeAtlas G X M)
        Subtype.val :=
  aePullback_spec_of_isAELocalHomeomorph (isMaximalAEAtlas_aeAtlas G X M).1
    continuous_subtype_val (isAELocalHomeomorph_opensSingular_val U)

/-- An open subset `U` of a singular `(G,X)`-manifold is a singular `(G,X)`-manifold: its
structure is the pullback `ι^* B` along the inclusion (`lem:aepullback`), the unique maximal one
making the inclusion an a.e. morphism. -/
instance opensSingularGXStructure (U : Opens M) : SingularGXStructure G X U :=
  ⟨_, (aePullback_opensSingular_val_spec U).1⟩

theorem aeAtlas_opensSingular (U : Opens M) :
    aeAtlas G X U = aePullback G (aeAtlas G X M) (Subtype.val : U → M) := rfl

/-- The inclusion of an open subset is an a.e. `(G,X)`-morphism. -/
theorem isAEMorphism_opensSingular_val (U : Opens M) : IsAEMorphism G X (Subtype.val : U → M) :=
  (aePullback_opensSingular_val_spec U).2

theorem reg_opensSingular (U : Opens M) : Reg G X U = Subtype.val ⁻¹' Reg G X M :=
  ((isAEMorphism_opensSingular_val U).preimage_support_eq (isMaximalAEAtlas_aeAtlas G X U)
    (isMaximalAEAtlas_aeAtlas G X M) U.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph).1.symm

theorem sing_opensSingular (U : Opens M) : Sing G X U = Subtype.val ⁻¹' Sing G X M := by
  rw [Sing, Sing, reg_opensSingular, preimage_compl]

variable {N : Type*} [TopologicalSpace N] [SingularGXStructure G X N]

/-- An a.e. `(G,X)`-isomorphism `φ : U ≃ₜ V` of open subsets, for their induced structures (gx's
reading of an isomorphism of singular `(G,X)`-manifolds), read on `M` and `N`: any `f` which is
`φ` on `U` induces a `(G,X)`-morphism on `U ∩ Reg M` for the maximal atlases of `M` and `N`. -/
theorem isRegularOn_of_isAEMorphism {U : Opens M} {V : Opens N} (φ : U ≃ₜ V)
    (hφ : IsAEMorphism G X (φ : U → V)) {f : M → N} (hf : ContinuousOn f U)
    (heq : ∀ x : U, f x = φ x) :
    IsRegularOn G (aeAtlas G X M) (aeAtlas G X N) f (U ∩ Reg G X M) := by
  have hRφ := (hφ.preimage_reg_sing φ.isLocalHomeomorph).1
  have hregV : ∀ x : U, x ∈ Reg G X U → φ x ∈ Reg G X V := fun x hx => by
    rw [← hRφ] at hx; exact hx
  refine ⟨U.isOpen.inter (isOpen_reg G X M), fun x hx => hx.2, fun x hx => ?_,
    hf.mono inter_subset_left, ?_⟩
  · have hx' : (⟨x, hx.1⟩ : U) ∈ Reg G X U := by rw [reg_opensSingular]; exact hx.2
    have := hregV _ hx'
    rw [reg_opensSingular] at this
    rw [heq ⟨x, hx.1⟩]; exact this
  · intro x hx c hc r hr hxc hxr
    set x' : U := ⟨x, hx.1⟩
    have hx'U : x' ∈ Reg G X U := by rw [reg_opensSingular]; exact hx.2
    have hx'V : φ x' ∈ Reg G X V := hregV x' hx'U
    have hfx : ((φ x' : V) : N) ∈ Reg G X N := by
      have := hx'V; rw [reg_opensSingular] at this; exact this
    obtain ⟨cU, hcU, hx'cU⟩ := mem_support.1 hx'U
    obtain ⟨cV, hcV, hx'cV⟩ := mem_support.1 hx'V
    have h1 : x' ∈ regLocus G X (φ : U → V) := by rw [hφ.regLocus_eq]; exact ⟨hx'U, hx'V⟩
    obtain ⟨g₁, hg₁⟩ := (isRegularOn_regLocusOf _ _ _).exists_smul_eq x' h1 cU hcU cV hcV hx'cU
      hx'cV
    have hvU := isAEMorphism_opensSingular_val (G := G) (X := X) U
    have h2 : x' ∈ regLocus G X (Subtype.val : U → M) := by
      rw [hvU.regLocus_eq]; exact ⟨hx'U, hx.2⟩
    obtain ⟨g₂, hg₂⟩ := (isRegularOn_regLocusOf _ _ _).exists_smul_eq x' h2 cU hcU c hc hx'cU hxc
    have hvV := isAEMorphism_opensSingular_val (G := G) (X := X) V
    have h3 : φ x' ∈ regLocus G X (Subtype.val : V → N) := by
      rw [hvV.regLocus_eq]; exact ⟨hx'V, hfx⟩
    have hxr' : ((φ x' : V) : N) ∈ r.source := by rw [← heq x']; exact hxr
    obtain ⟨g₃, hg₃⟩ := (isRegularOn_regLocusOf _ _ _).exists_smul_eq (φ x') h3 cV hcV r hr
      hx'cV hxr'
    refine ⟨g₃ * g₁ * g₂⁻¹, ?_⟩
    have hsub : ∀ᶠ y' : U in 𝓝 x', r (f (y' : M)) = (g₃ * g₁ * g₂⁻¹) • c (y' : M) := by
      filter_upwards [φ.continuous.continuousAt.eventually hg₃, hg₁, hg₂] with y' e3 e1 e2
      rw [heq y', e3, e1, e2]
      simp only [mul_smul, inv_smul_smul]
    rw [← U.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x']
    exact eventually_map.2 hsub

omit [ContinuousConstSMul G X] [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
  [SingularGXStructure G X M] [SingularGXStructure G X N] in
/-- A homeomorphism `φ : U ≃ₜ V` of nonempty open subsets is realised by an open partial
homeomorphism `M ⇀ N` with source `U`. -/
theorem exists_openPartialHomeomorph_of_homeomorph {U : Opens M} {V : Opens N} (φ : U ≃ₜ V)
    (x₀ : U) : ∃ e : OpenPartialHomeomorph M N, e.source = U ∧ ∀ x : U, e x = φ x := by
  let ιU := U.openPartialHomeomorphSubtypeCoe ⟨x₀⟩
  let ιV := V.openPartialHomeomorphSubtypeCoe ⟨φ x₀⟩
  refine ⟨ιU.symm.trans (φ.toOpenPartialHomeomorph.trans ιV), ?_, fun x => ?_⟩
  · rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source]
    simp [ιU, ιV]
  · haveI : Nonempty U := ⟨x₀⟩
    have hx : ιU.symm (x : M) = x :=
      (U.isOpen.isOpenEmbedding_subtypeVal).toOpenPartialHomeomorph_left_inv _
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hx]
    rfl

/-- **The bridge to gx's isomorphisms of open subsets** (`def:atlas`, `RamcovGX.tex:1905`): an open
partial homeomorphism `e : M ⇀ N` which, on its source `U`, is an a.e. `(G,X)`-isomorphism
`φ : U ≃ₜ V` of the open subsets with their induced structures (gx's `IsAEMorphism`), is an
`IsAEChart`. In particular every gx `X_α`-chart, realised as an open partial homeomorphism, is
one. -/
theorem isAEChart_of_isAEMorphism {U : Opens M} {V : Opens N} (φ : U ≃ₜ V)
    (hφ : IsAEMorphism G X (φ : U → V)) {e : OpenPartialHomeomorph M N}
    (hsrc : e.source = U) (heq : ∀ x : U, e x = φ x) : IsAEChart G X e := by
  have htgt : e.target = V := by
    ext y
    constructor
    · intro hy
      rw [← e.image_source_eq_target] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hsrc] at hx
      rw [heq ⟨x, hx⟩]; exact (φ ⟨x, hx⟩).2
    · intro hy
      have hw := (φ.symm ⟨y, hy⟩).2
      have : e (φ.symm ⟨y, hy⟩) = y := by rw [heq, Homeomorph.apply_symm_apply]
      rw [← this]
      exact e.map_source (by rw [hsrc]; exact hw)
  have heq' : ∀ y : V, e.symm y = φ.symm y := fun y => by
    have hw : ((φ.symm y : U) : M) ∈ e.source := by rw [hsrc]; exact (φ.symm y).2
    have : e (φ.symm y) = y := by rw [heq, Homeomorph.apply_symm_apply]
    rw [← this, e.left_inv hw]
  refine ⟨?_, ?_⟩
  · have := isRegularOn_of_isAEMorphism φ hφ (f := e) (by rw [← hsrc]; exact e.continuousOn) heq
    rwa [hsrc]
  · have := isRegularOn_of_isAEMorphism φ.symm (IsAEMorphism.symm_of_homeomorph hφ) (f := e.symm)
      (by rw [← htgt]; exact e.continuousOn_symm) heq'
    rwa [htgt]

/-- **The converse bridge**: an `IsAEChart` `e`, restricted to a homeomorphism `φ : U ≃ₜ V` of its
source onto an open `V`, is an a.e. `(G,X)`-isomorphism of the open subsets with their induced
structures in gx's sense (`IsAEMorphism`, on the portly `Reg U`). -/
theorem isAEMorphism_of_isAEChart {e : OpenPartialHomeomorph M N} (he : IsAEChart G X e)
    {U : Opens M} {V : Opens N} (φ : U ≃ₜ V) (hsrc : e.source = U)
    (heq : ∀ x : U, e x = φ x) : IsAEMorphism G X (φ : U → V) := by
  refine (isAEMorphismOf_iff (isMaximalAEAtlas_aeAtlas G X V).1).2
    ⟨φ.continuous, Reg G X U, isPortly_reg G X U, isOpen_reg G X U, fun x hx => hx,
      fun x hx => ?_, φ.continuous.continuousOn, ?_⟩
  · have hxM : (x : M) ∈ Reg G X M := by rw [reg_opensSingular] at hx; exact hx
    have hxs : (x : M) ∈ e.source := by rw [hsrc]; exact x.2
    have := (he.mem_reg_iff hxs).1 hxM
    rw [heq x] at this
    show φ x ∈ Reg G X V
    rw [reg_opensSingular]; exact this
  · intro x' hx' cU hcU cV hcV hx'cU hx'cV
    have hxM : (x' : M) ∈ Reg G X M := by rw [reg_opensSingular] at hx'; exact hx'
    have hxs : (x' : M) ∈ e.source := by rw [hsrc]; exact x'.2
    have heM : e x' ∈ Reg G X N := (he.mem_reg_iff hxs).1 hxM
    have hx'V : φ x' ∈ Reg G X V := by
      rw [reg_opensSingular]; show ((φ x' : V) : N) ∈ Reg G X N; rw [← heq x']; exact heM
    obtain ⟨c, hc, hxc⟩ := mem_support.1 hxM
    obtain ⟨r, hr, hxr⟩ := mem_support.1 heM
    obtain ⟨g₁, hg₁⟩ := he.regularOn.exists_smul_eq x' ⟨hxs, hxM⟩ c hc r hr hxc hxr
    have hvU := isAEMorphism_opensSingular_val (G := G) (X := X) U
    have h2 : x' ∈ regLocus G X (Subtype.val : U → M) := by
      rw [hvU.regLocus_eq]; exact ⟨hx', hxM⟩
    obtain ⟨g₂, hg₂⟩ := (isRegularOn_regLocusOf _ _ _).exists_smul_eq x' h2 cU hcU c hc hx'cU hxc
    have hvV := isAEMorphism_opensSingular_val (G := G) (X := X) V
    have hfx : ((φ x' : V) : N) ∈ Reg G X N := by rw [← heq x']; exact heM
    have h3 : φ x' ∈ regLocus G X (Subtype.val : V → N) := by
      rw [hvV.regLocus_eq]; exact ⟨hx'V, hfx⟩
    have hxr' : ((φ x' : V) : N) ∈ r.source := by rw [← heq x']; exact hxr
    obtain ⟨g₃, hg₃⟩ := (isRegularOn_regLocusOf _ _ _).exists_smul_eq (φ x') h3 cV hcV r hr
      hx'cV hxr'
    refine ⟨g₃⁻¹ * g₁ * g₂, ?_⟩
    filter_upwards [φ.continuous.continuousAt.eventually hg₃,
      continuous_subtype_val.continuousAt.eventually hg₁, hg₂] with y' e3 e1 e2
    rw [← heq y'] at e3
    rw [e1, e2] at e3
    rw [mul_smul, mul_smul, e3, inv_smul_smul]

/-- `IsAEChart` is gx's notion: for an open partial homeomorphism `e` realising a homeomorphism
`φ : U ≃ₜ V` of open subsets, `e` is an `IsAEChart` iff `φ` is an a.e. `(G,X)`-isomorphism of the
open subsets with their induced structures (`def:atlas`, `RamcovGX.tex:1905`). -/
theorem isAEChart_iff_isAEMorphism {e : OpenPartialHomeomorph M N} {U : Opens M} {V : Opens N}
    (φ : U ≃ₜ V) (hsrc : e.source = U) (heq : ∀ x : U, e x = φ x) :
    IsAEChart G X e ↔ IsAEMorphism G X (φ : U → V) :=
  ⟨fun he => isAEMorphism_of_isAEChart he φ hsrc heq,
    fun hφ => isAEChart_of_isAEMorphism φ hφ hsrc heq⟩

end Opens

/-! ### `prop:GX_sing_espace_temps_topo` under DEC-25 -/

section GXSing

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X]
  {M : Type u} [TopologicalSpace M] [SingularGXStructure G X M]

/-- Two absolutely minimal causalities which agree near every point are equal. -/
theorem eq_of_agreeOn_locally {C₁ C₂ : Causality M} (h₁ : C₁.AbsolutelyMinimal)
    (h₂ : C₂.AbsolutelyMinimal) (h : ∀ x : M, ∃ O : Opens M, x ∈ O ∧ AgreeOn C₁ C₂ O) :
    C₁ = C₂ := by
  have hA₁ := Precausality.absolutelyMinimal_iff.1 h₁
  have hA₂ := Precausality.absolutelyMinimal_iff.1 h₂
  have h' : ∀ x : M, x ∈ (⊤ : Opens M) → ∃ O : Opens M, x ∈ O ∧ AgreeOn C₂ C₁ O := fun x _ => by
    obtain ⟨O, hxO, hO⟩ := h x
    exact ⟨O, hxO, hO.symm⟩
  apply Causality.ext_toPrecausality
  ext V x y
  · exact ⟨fun hxy => (imp_of_agree_locally hA₁ (fun x _ => h x) le_top).1 hxy,
      fun hxy => (imp_of_agree_locally hA₂ h' le_top).1 hxy⟩
  · exact ⟨fun hxy => (imp_of_agree_locally hA₁ (fun x _ => h x) le_top).2 hxy,
      fun hxy => (imp_of_agree_locally hA₂ h' le_top).2 hxy⟩

/-- (B) across two charts of the maximal a.e. atlas: their transition is, near every point, an
element of `G`. -/
theorem ChartIso.agreeOn_of_mem_aeAtlas [LocallyConnectedSpace X] {DX : Causality X}
    (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p) {C₁ C₂ : Causality M}
    {e e' : OpenPartialHomeomorph M X} (he : e ∈ aeAtlas G X M) (he' : e' ∈ aeAtlas G X M)
    (h₁ : ChartIso C₁ DX e) (h₂ : ChartIso C₂ DX e') {x : M} (hx : x ∈ e.source)
    (hx' : x ∈ e'.source) : ∃ O : Opens M, x ∈ O ∧ AgreeOn C₁ C₂ O := by
  obtain ⟨g, O, hxO, hO, heq⟩ := exists_smul_eq_of_mem_gxGroupoid
    ((isMaximalAEAtlas_aeAtlas G X M).1.1.symm_trans_mem he he') hx hx'
  exact ⟨O, hxO, h₁.agreeOn_of_smul hG h₂ hO heq⟩

/-- (B) across a chart `e` of the maximal a.e. atlas of `M` and an a.e. isomorphism chart `f` of
`M` into a singular `(G,X)`-manifold `Y` whose regular charts are isomorphisms (`hreg`, the second
half of (b)): near every point of the overlap, `f` reads in charts as an element of `G`. -/
theorem ChartIso.agreeOn_of_isAEChart {Y : Type y} [TopologicalSpace Y]
    [SingularGXStructure G X Y] {DX : Causality X} {DY : Causality Y}
    (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p)
    (hreg : ∀ r ∈ aeAtlas G X Y, ChartIso DY DX r) {C₁ C₂ : Causality M}
    {e : OpenPartialHomeomorph M X} {f : OpenPartialHomeomorph M Y} (he : e ∈ aeAtlas G X M)
    (hf : IsAEChart G X f) (h₁ : ChartIso C₁ DX e) (h₂ : ChartIso C₂ DY f) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ f.source) : ∃ O : Opens M, x ∈ O ∧ AgreeOn C₁ C₂ O := by
  have hxr : x ∈ Reg G X M := mem_support.2 ⟨e, he, hx⟩
  have hfx : f x ∈ Reg G X Y := (hf.mem_reg_iff hx').1 hxr
  obtain ⟨r, hr, hfxr⟩ := mem_support.1 hfx
  obtain ⟨g, hg⟩ := hf.regularOn.exists_smul_eq x ⟨hx', hxr⟩ e he r hr hx hfxr
  have hev : ∀ᶠ z in 𝓝 x, f z ∈ r.source ∧ r (f z) = g • e z :=
    ((f.continuousAt hx').eventually (r.open_source.mem_nhds hfxr)).and hg
  obtain ⟨O, hxO, hOW, hO⟩ := exists_opens_of_eventually (e.open_source.inter f.open_source)
    ⟨hx, hx'⟩ hev
  exact ⟨O, hxO, h₁.agreeOn_of_regular hG h₂ (hreg r hr) (fun z hz => hOW hz) hO⟩

omit [ContinuousConstSMul G X] in
/-- (B) across two a.e. isomorphism charts `f₁ : M ⇀ Y₁`, `f₂ : M ⇀ Y₂` into model spaces whose
a.e. isomorphisms are isomorphisms of topological spacetimes (`hiso`, (b′)): the transition
`f₁⁻¹ ≫ f₂` is one, so the two transported causalities agree on the whole overlap. -/
theorem ChartIso.agreeOn_of_isAEChart_of_isAEChart {Y₁ : Type y} {Y₂ : Type z}
    [TopologicalSpace Y₁] [TopologicalSpace Y₂] [SingularGXStructure G X Y₁]
    [SingularGXStructure G X Y₂] {D₁ : Causality Y₁} {D₂ : Causality Y₂}
    {f₁ : OpenPartialHomeomorph M Y₁} {f₂ : OpenPartialHomeomorph M Y₂}
    (hf₁ : IsAEChart G X f₁) (hf₂ : IsAEChart G X f₂)
    (hiso : ∀ ψ : OpenPartialHomeomorph Y₁ Y₂, IsAEChart G X ψ → ChartIso D₁ D₂ ψ)
    {C₁ C₂ : Causality M} (h₁ : ChartIso C₁ D₁ f₁) (h₂ : ChartIso C₂ D₂ f₂) :
    AgreeOn C₁ C₂ (chartSource f₁ ⊓ chartSource f₂) := by
  have hψ := hiso _ (hf₁.symm.trans hf₂)
  refine h₁.agreeOn_of_localIso h₂ hψ le_rfl fun z hz => ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    refine ⟨f₁.map_source hz.1, ?_⟩
    show f₁.symm (f₁ z) ∈ f₂.source
    rw [f₁.left_inv hz.1]; exact hz.2
  · rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, f₁.left_inv hz.1]

/-- **At regular points the isomorphisms are automatic.** Let `Y` be a singular `(G,X)`-manifold
with a causally arc-connected causality `DY` whose regular charts are isomorphisms (`hreg`), and
`C` a causality on `M` for which every chart of the maximal a.e. atlas is an isomorphism, absolutely
minimal on the source of an a.e. isomorphism chart `f : M ⇀ Y`. If the source of `f` is regular,
`f` is an isomorphism of topological spacetimes. So (b′) of
`existsUnique_causality_singularGX_dec25` is a condition at singular points only. -/
theorem chartIso_of_isAEChart_of_subset_reg {Y : Type y} [TopologicalSpace Y]
    [SingularGXStructure G X Y] {DX : Causality X} {DY : Causality Y}
    (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p) (hb : DY.CausallyArcConnected)
    (hreg : ∀ r ∈ aeAtlas G X Y, ChartIso DY DX r) {C : Causality M}
    (hC : ∀ e ∈ aeAtlas G X M, ChartIso C DX e) {f : OpenPartialHomeomorph M Y}
    (hf : IsAEChart G X f) (hmin : C.AbsolutelyMinimalOn (chartSource f))
    (hsub : f.source ⊆ Reg G X M) : ChartIso C DY f := by
  have hT := DY.chartTransport_chartIso f
  have hTmin : (DY.chartTransport f).AbsolutelyMinimalOn (chartSource f) :=
    hT.absolutelyMinimalOn le_rfl (hb.absolutelyMinimalOn_all _)
  have hloc : ∀ x ∈ chartSource f, ∃ O : Opens M, x ∈ O ∧ AgreeOn C (DY.chartTransport f) O := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := mem_support.1 (hsub hx)
    exact (hC e he).agreeOn_of_isAEChart hG hreg he hf hT hxe hx
  have hloc' : ∀ x ∈ chartSource f, ∃ O : Opens M, x ∈ O ∧ AgreeOn (DY.chartTransport f) C O :=
    fun x hx => by
      obtain ⟨O, hxO, hO⟩ := hloc x hx
      exact ⟨O, hxO, hO.symm⟩
  refine hT.congr fun V hV x y => ?_
  have h1 := imp_of_agree_locally hmin hloc hV (x := x) (y := y)
  have h2 := imp_of_agree_locally hTmin hloc' hV (x := x) (y := y)
  exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2, h2.2⟩⟩

variable [LocallyConnectedSpace X] {A : Type z} {Xα : A → Type y} [∀ a, TopologicalSpace (Xα a)]
  [∀ a, SingularGXStructure G X (Xα a)]

/-- **`prop:GX_sing_espace_temps_topo` under DEC-25.** Let `(G,X)` act on a locally connected `X`,
`(X_α)` be singular `(G,X)`-manifolds (the model spaces) and `M` a singular `(G,X)`-manifold (a
maximal a.e. `(G,X)`-atlas) whose singular points lie in `X_A`-charts (`IsAEChart`s into the
models). Assume (a), (b) (its second half read as `hreg`) and (b′), `hiso`: every a.e.
isomorphism between open subsets of the model spaces is an isomorphism of topological spacetimes.
Then `M` carries an absolutely minimal causality for which every chart of its maximal a.e. atlas
and every `X_A`-chart is an isomorphism of topological spacetimes; and an absolutely minimal
causality for which, at every point, some such chart is an isomorphism, is that one. -/
theorem existsUnique_causality_singularGX_dec25 (DX : Causality X) (DY : ∀ a, Causality (Xα a))
    -- (a)
    (ha : DX.CausallyArcConnected) (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p)
    -- (b)
    (hb : ∀ a, (DY a).CausallyArcConnected)
    (hreg : ∀ a, ∀ r ∈ aeAtlas G X (Xα a), ChartIso (DY a) DX r)
    -- (b′), the isomorphisms of the model spaces
    (hiso : ∀ a b (ψ : OpenPartialHomeomorph (Xα a) (Xα b)), IsAEChart G X ψ →
      ChartIso (DY a) (DY b) ψ)
    -- the `X_A`-charts cover the singular locus
    (hcov : ∀ x ∈ Sing G X M, ∃ a, ∃ e : OpenPartialHomeomorph M (Xα a), IsAEChart G X e ∧
      x ∈ e.source) :
    ∃ C : Causality M, (∀ e ∈ aeAtlas G X M, ChartIso C DX e) ∧
      (∀ a (e : OpenPartialHomeomorph M (Xα a)), IsAEChart G X e → ChartIso C (DY a) e) ∧
      C.AbsolutelyMinimal ∧
      ∀ C' : Causality M, C'.AbsolutelyMinimal →
        (∀ x : M, (∃ e ∈ aeAtlas G X M, x ∈ e.source ∧ ChartIso C' DX e) ∨
          ∃ a, ∃ e : OpenPartialHomeomorph M (Xα a), IsAEChart G X e ∧ x ∈ e.source ∧
            ChartIso C' (DY a) e) →
        C' = C := by
  let I := {e : OpenPartialHomeomorph M X // e ∈ aeAtlas G X M}
  let J := Σ a, {e : OpenPartialHomeomorph M (Xα a) // IsAEChart G X e}
  let U : I ⊕ J → Opens M := Sum.elim (fun i => chartSource i.1) fun j => chartSource j.2.1
  let Cl : I ⊕ J → Causality M :=
    Sum.elim (fun i => DX.chartTransport i.1) fun j => (DY j.1).chartTransport j.2.1
  have hX : ∀ i : I, ChartIso (Cl (Sum.inl i)) DX i.1 := fun i => DX.chartTransport_chartIso _
  have hY : ∀ j : J, ChartIso (Cl (Sum.inr j)) (DY j.1) j.2.1 := fun j =>
    (DY j.1).chartTransport_chartIso _
  have hU : ∀ x : M, ∃ s, x ∈ U s := by
    intro x
    by_cases hx : x ∈ Reg G X M
    · obtain ⟨e, he, hxe⟩ := mem_support.1 hx
      exact ⟨Sum.inl ⟨e, he⟩, hxe⟩
    · obtain ⟨a, e, he, hxe⟩ := hcov x hx
      exact ⟨Sum.inr ⟨a, e, he⟩, hxe⟩
  have hA : ∀ s, ∀ W : Opens M, W ≤ U s → (Cl s).AbsolutelyMinimalOn W := by
    rintro (i | j) W hW
    · exact (hX i).absolutelyMinimalOn hW (ha.absolutelyMinimalOn_all _)
    · exact (hY j).absolutelyMinimalOn hW ((hb _).absolutelyMinimalOn_all _)
  have hB : ∀ s t, ∀ x ∈ U s ⊓ U t, ∃ O : Opens M, x ∈ O ∧ AgreeOn (Cl s) (Cl t) O := by
    rintro (i | j) (i' | j') x hx
    · exact (hX i).agreeOn_of_mem_aeAtlas hG i.2 i'.2 (hX i') hx.1 hx.2
    · exact (hX i).agreeOn_of_isAEChart hG (hreg j'.1) i.2 j'.2.2 (hY j') hx.1 hx.2
    · obtain ⟨O, hxO, hO⟩ :=
        (hX i').agreeOn_of_isAEChart hG (hreg j.1) i'.2 j.2.2 (hY j) hx.2 hx.1
      exact ⟨O, hxO, hO.symm⟩
    · exact ⟨_, hx, (hY j).agreeOn_of_isAEChart_of_isAEChart j.2.2 j'.2.2 (hiso j.1 j'.1)
        (hY j')⟩
  obtain ⟨C, hC, hmin, -⟩ := existsUnique_absolutelyMinimal_of_agree_locally hU hA hB
  have hCX : ∀ e ∈ aeAtlas G X M, ChartIso C DX e := fun e he =>
    (hX ⟨e, he⟩).congr (hC (Sum.inl ⟨e, he⟩))
  have hCY : ∀ a (e : OpenPartialHomeomorph M (Xα a)), IsAEChart G X e → ChartIso C (DY a) e :=
    fun a e he => (hY ⟨a, e, he⟩).congr (hC (Sum.inr ⟨a, e, he⟩))
  refine ⟨C, hCX, hCY, hmin, fun C' hmin' hloc => eq_of_agreeOn_locally hmin' hmin fun x => ?_⟩
  rcases hloc x with ⟨e, he, hxe, h'⟩ | ⟨a, e, he, hxe, h'⟩
  · exact ⟨chartSource e, hxe, fun V hV y z => h'.agree (hCX e he) hV y z⟩
  · exact ⟨chartSource e, hxe, fun V hV y z => h'.agree (hCY a e he) hV y z⟩


/-- `existsUnique_causality_singularGX_dec25` with the `X_A`-charts given as in gx's `def:atlas`
(`RamcovGX.tex:1905`, gx's `XAChart`): every singular point `x` lies in an open `U` with an a.e.
`(G,X)`-isomorphism `φ : U ≃ₜ V` onto an open subset `V` of a model, for the induced structures
(gx asks moreover `V` connected and `φ(x) ∈ S_α`, not needed here). Such a `φ` is an `IsAEChart`
once realised (`exists_openPartialHomeomorph_of_homeomorph`, `isAEChart_of_isAEMorphism`). -/
theorem existsUnique_causality_singularGX_dec25_of_isAEMorphism [T2Space X] [IsRigidAction G X]
    (DX : Causality X) (DY : ∀ a, Causality (Xα a))
    (ha : DX.CausallyArcConnected) (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p)
    (hb : ∀ a, (DY a).CausallyArcConnected)
    (hreg : ∀ a, ∀ r ∈ aeAtlas G X (Xα a), ChartIso (DY a) DX r)
    (hiso : ∀ a b (ψ : OpenPartialHomeomorph (Xα a) (Xα b)), IsAEChart G X ψ →
      ChartIso (DY a) (DY b) ψ)
    (hcov : ∀ x ∈ Sing G X M, ∃ a, ∃ U : Opens M, ∃ V : Opens (Xα a), ∃ φ : U ≃ₜ V, x ∈ U ∧
      IsAEMorphism G X (φ : U → V)) :
    ∃ C : Causality M, (∀ e ∈ aeAtlas G X M, ChartIso C DX e) ∧
      (∀ a (e : OpenPartialHomeomorph M (Xα a)), IsAEChart G X e → ChartIso C (DY a) e) ∧
      C.AbsolutelyMinimal ∧
      ∀ C' : Causality M, C'.AbsolutelyMinimal →
        (∀ x : M, (∃ e ∈ aeAtlas G X M, x ∈ e.source ∧ ChartIso C' DX e) ∨
          ∃ a, ∃ e : OpenPartialHomeomorph M (Xα a), IsAEChart G X e ∧ x ∈ e.source ∧
            ChartIso C' (DY a) e) →
        C' = C := by
  refine existsUnique_causality_singularGX_dec25 DX DY ha hG hb hreg hiso fun x hx => ?_
  obtain ⟨a, U, V, φ, hxU, hφ⟩ := hcov x hx
  obtain ⟨e, hsrc, heq⟩ := exists_openPartialHomeomorph_of_homeomorph φ ⟨x, hxU⟩
  exact ⟨a, e, isAEChart_of_isAEMorphism φ hφ hsrc heq, by rw [hsrc]; exact hxU⟩

omit [LocallyConnectedSpace X] in
/-- (b′) **restricted to regular sources holds**: an a.e. isomorphism of model spaces whose source
is regular is an isomorphism of topological spacetimes, under (a) and (b) alone. -/
theorem chartIso_model_of_subset_reg (DX : Causality X) (DY : ∀ a, Causality (Xα a))
    (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p) (hb : ∀ a, (DY a).CausallyArcConnected)
    (hreg : ∀ a, ∀ r ∈ aeAtlas G X (Xα a), ChartIso (DY a) DX r) {a b : A}
    {ψ : OpenPartialHomeomorph (Xα a) (Xα b)} (hψ : IsAEChart G X ψ)
    (hsub : ψ.source ⊆ Reg G X (Xα a)) : ChartIso (DY a) (DY b) ψ :=
  chartIso_of_isAEChart_of_subset_reg hG (hb b) (hreg b) (hreg a) hψ
    ((hb a).absolutelyMinimalOn_all _) hsub

/-- **(b′) is exactly what `prop:GX_sing_espace_temps_topo` needs.** Under (a) and (b), the
existence half of the proposition holds for every singular `(G,X)`-manifold `M` (in the universe
of the models) whose singular points lie in `X_A`-charts, if and only if every a.e. isomorphism
between open subsets of the model spaces is an isomorphism of topological spacetimes (b′). The
"if" is `existsUnique_causality_singularGX_dec25`; for "only if", take `M = X_α`, whose identity is
an `X_A`-chart: the causality it produces is `DY α` (`eq_of_chartIso_refl`). -/
theorem forall_exists_causality_singularGX_iff (DX : Causality X) (DY : ∀ a, Causality (Xα a))
    (ha : DX.CausallyArcConnected) (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p)
    (hb : ∀ a, (DY a).CausallyArcConnected)
    (hreg : ∀ a, ∀ r ∈ aeAtlas G X (Xα a), ChartIso (DY a) DX r) :
    (∀ (N : Type y) [TopologicalSpace N] [SingularGXStructure G X N],
      (∀ x ∈ Sing G X N, ∃ a, ∃ e : OpenPartialHomeomorph N (Xα a), IsAEChart G X e ∧
        x ∈ e.source) →
      ∃ C : Causality N, (∀ e ∈ aeAtlas G X N, ChartIso C DX e) ∧
        ∀ a (e : OpenPartialHomeomorph N (Xα a)), IsAEChart G X e → ChartIso C (DY a) e) ↔
      ∀ a b (ψ : OpenPartialHomeomorph (Xα a) (Xα b)), IsAEChart G X ψ →
        ChartIso (DY a) (DY b) ψ := by
  constructor
  · intro h a b ψ hψ
    obtain ⟨C, -, hCY⟩ := h (Xα a) fun x _ =>
      ⟨a, OpenPartialHomeomorph.refl _, isAEChart_refl, trivial⟩
    have hC : C = DY a := eq_of_chartIso_refl (hCY a _ isAEChart_refl)
    subst hC
    exact hCY b ψ hψ
  · intro hiso N _ _ hcov
    obtain ⟨C, hCX, hCY, -⟩ :=
      existsUnique_causality_singularGX_dec25 (M := N) DX DY ha hG hb hreg hiso hcov
    exact ⟨C, hCX, hCY⟩

end GXSing


/-! ### `rem:hypotheses_proposition_prop_gx` under DEC-25 -/

section Remark

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X]
  {M : Type u} [TopologicalSpace M] [SingularGXStructure G X M]
  {N : Type u'} [TopologicalSpace N] [SingularGXStructure G X N]

/-- **On the regular locus, a map inducing a `(G,X)`-morphism is a local isomorphism**: at every
point `x` of an open set `W` on which `f` induces a `(G,X)`-morphism (gx's `IsRegularOn`), `f`
satisfies the local condition of a weak morphism (`def:category_topological_spacetimes`, DEC-12),
for causalities making the charts of the maximal a.e. atlases isomorphisms. -/
theorem weakMorphism_local_of_isRegularOn {DX : Causality X}
    (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p) {C : Causality M} {C' : Causality N}
    (hC : ∀ e ∈ aeAtlas G X M, ChartIso C DX e) (hC' : ∀ e ∈ aeAtlas G X N, ChartIso C' DX e)
    {f : M → N} {W : Set M} (hf : IsRegularOn G (aeAtlas G X M) (aeAtlas G X N) f W) {x : M}
    (hx : x ∈ W) (U : Opens N) (hfx : f x ∈ U) :
    ∃ V : Opens M, x ∈ V ∧ MapsTo f V U ∧ (∀ ⦃y z : M⦄, C.le V y z → C'.le U (f y) (f z)) ∧
      (∀ ⦃y z : M⦄, C.lt V y z → C'.lt U (f y) (f z)) := by
  obtain ⟨e, he, hxe⟩ := mem_support.1 (hf.subset_support hx)
  obtain ⟨e', he', hfxe'⟩ := mem_support.1 (hf.mapsTo hx)
  obtain ⟨g, hg⟩ := hf.exists_smul_eq x hx e he e' he' hxe hfxe'
  have hcont : ContinuousAt f x := hf.continuousOn.continuousAt (hf.isOpen.mem_nhds hx)
  have hev : ∀ᶠ z in 𝓝 x, (f z ∈ e'.source ∧ f z ∈ U) ∧ e' (f z) = g • e z :=
    (hcont.eventually ((e'.open_source.inter U.isOpen).mem_nhds ⟨hfxe', hfx⟩)).and hg
  obtain ⟨V, hxV, hVW, hV⟩ := exists_opens_of_eventually e.open_source hxe hev
  have hVe : V ≤ chartSource e := hVW
  have himg : f '' V = e'.symm '' ((fun p => g • p) '' (e '' V)) := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨g • e z, ⟨e z, ⟨z, hz, rfl⟩, rfl⟩, by rw [← (hV z hz).2, e'.left_inv (hV z hz).1.1]⟩
    · rintro ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      exact ⟨z, hz, by dsimp only; rw [← (hV z hz).2, e'.left_inv (hV z hz).1.1]⟩
  have hsub : (fun p => g • p) '' (e '' V) ⊆ e'.target := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    dsimp only
    rw [← (hV z hz).2]
    exact e'.map_source (hV z hz).1.1
  have hopen : IsOpen (f '' V) := by
    rw [himg]
    exact e'.symm.isOpen_image_of_subset_source
      (isOpenMap_smul g _ (e.isOpen_image_of_subset_source V.isOpen hVW)) hsub
  let W' : Opens N := ⟨f '' V, hopen⟩
  have hW'e' : W' ≤ chartSource e' := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hV z hz).1.1
  have hW'U : W' ≤ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hV z hz).1.2
  have himg' : chartImage e' W' = smulOpens g (chartImage e V) := by
    apply SetLike.coe_injective
    change (chartImage e' W' : Set X) = (fun p => g • p) '' (chartImage e V : Set X)
    rw [coe_chartImage_of_le hW'e', coe_chartImage_of_le hVe]
    change e' '' (f '' V) = _
    rw [image_image, image_image]
    exact image_congr fun z hz => (hV z hz).2
  have key : ∀ {a b : M}, a ∈ V → b ∈ V →
      (C.le V a b → C'.le W' (f a) (f b)) ∧ (C.lt V a b → C'.lt W' (f a) (f b)) := by
    intro a b ha hb
    have hfa : f a ∈ W' := mem_image_of_mem f ha
    have hfb : f b ∈ W' := mem_image_of_mem f hb
    rw [(hC e he V hVe a ha b hb).1, (hC e he V hVe a ha b hb).2,
      (hC' e' he' W' hW'e' _ hfa _ hfb).1, (hC' e' he' W' hW'e' _ hfa _ hfb).2,
      himg', (hV a ha).2, (hV b hb).2]
    exact ⟨(smul_rel_iff hG g _ _ _).1.2, (smul_rel_iff hG g _ _ _).2.2⟩
  refine ⟨V, hxV, fun z hz => (hV z hz).1.2, fun y z h => ?_, fun y z h => ?_⟩
  · exact C'.le_mono hW'U ((key (C.le_mem_left h) (C.le_mem_right h)).1 h)
  · exact C'.lt_mono hW'U ((key (C.lt_mem_left h) (C.lt_mem_right h)).2 h)

/-- **`rem:hypotheses_proposition_prop_gx`, unbranched**: a map inducing a `(G,X)`-morphism on all
of `M` (its regular locus is `M`: `Sing M = ∅` and `f(M) ⊆ Reg N`) is a strong morphism, for
causalities making the charts of the maximal a.e. atlases isomorphisms, the source one being
absolutely minimal. It is open (a local homeomorphism, `IsRegularOn.isLocalHomeomorphOn`). -/
theorem strongMorphism_of_isRegularOn_univ {DX : Causality X}
    (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p) {C : Causality M} {C' : Causality N}
    (hC : ∀ e ∈ aeAtlas G X M, ChartIso C DX e) (hC' : ∀ e ∈ aeAtlas G X N, ChartIso C' DX e)
    (hmin : C.AbsolutelyMinimal) {f : M → N}
    (hf : IsRegularOn G (aeAtlas G X M) (aeAtlas G X N) f univ) : StrongMorphism C C' f := by
  have hc : Continuous f := continuousOn_univ.1 hf.continuousOn
  have ho : IsOpenMap f :=
    (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.2 hf.isLocalHomeomorphOn).isOpenMap
  refine strongMorphism_of_gxMorphism hG hc ho hmin fun x => ?_
  obtain ⟨e, he, hxe⟩ := mem_support.1 (hf.subset_support (mem_univ x))
  obtain ⟨e', he', hfxe'⟩ := mem_support.1 (hf.mapsTo (mem_univ x))
  obtain ⟨g, hg⟩ := hf.exists_smul_eq x (mem_univ x) e he e' he' hxe hfxe'
  have hev : ∀ᶠ z in 𝓝 x, f z ∈ e'.source ∧ e' (f z) = g • e z :=
    (hc.continuousAt.eventually (e'.open_source.mem_nhds hfxe')).and hg
  obtain ⟨O, hxO, hOe, hO⟩ := exists_opens_of_eventually e.open_source hxe hev
  exact ⟨e, e', hC e he, hC' e' he', g, O, hxO, hOe, fun z hz => (hO z hz).1,
    fun z hz => (hO z hz).2⟩

/-- The same for an a.e. `(G,X)`-morphism (DEC-25) of a singular `(G,X)`-manifold without singular
point into the regular locus of `N`: by `lem:regf1` (`IsAEMorphism.regLocus_eq`) its regular
locus is `M`. -/
theorem strongMorphism_of_isAEMorphism [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {DX : Causality X} (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p) {C : Causality M}
    {C' : Causality N} (hC : ∀ e ∈ aeAtlas G X M, ChartIso C DX e)
    (hC' : ∀ e ∈ aeAtlas G X N, ChartIso C' DX e) (hmin : C.AbsolutelyMinimal) {f : M → N}
    (hf : IsAEMorphism G X f) (hM : Sing G X M = ∅) (hN : ∀ x, f x ∈ Reg G X N) :
    StrongMorphism C C' f := by
  have hR : regLocus G X f = univ := by
    rw [hf.regLocus_eq, eq_univ_iff_forall]
    intro x
    refine ⟨?_, hN x⟩
    by_contra hx
    have : x ∈ Sing G X M := hx
    rw [hM] at this
    exact this
  have := isRegularOn_regLocusOf (G := G) (aeAtlas G X M) (aeAtlas G X N) f
  refine strongMorphism_of_isRegularOn_univ hG hC hC' hmin ?_
  have h' : regLocusOf G (aeAtlas G X M) (aeAtlas G X N) f = univ := hR
  rwa [h'] at this

/-- **`rem:hypotheses_proposition_prop_gx` reduced to the points outside the regular locus**: an
a.e. `(G,X)`-morphism `f : M → N` (DEC-25), for causalities making the charts of the maximal a.e.
atlases isomorphisms, is a weak morphism of topological spacetimes if and only if it satisfies
the local condition of a weak morphism at the points of `M` outside its regular locus
`Reg(f) = Reg(M) ∩ f⁻¹(Reg(N))` (`lem:regf1`): the singular points of `M` and the regular points
mapped to singular points of `N`. On `Reg(f)` the condition holds
(`weakMorphism_local_of_isRegularOn`); outside it nothing in (a), (b), (b′) constrains `f`
(SCOPE). -/
theorem weakMorphism_iff_of_isAEMorphism {DX : Causality X}
    (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p) {C : Causality M} {C' : Causality N}
    (hC : ∀ e ∈ aeAtlas G X M, ChartIso C DX e) (hC' : ∀ e ∈ aeAtlas G X N, ChartIso C' DX e)
    {f : M → N} (hf : IsAEMorphism G X f) :
    WeakMorphism C C' f ↔ ∀ x ∉ regLocus G X f, ∀ U : Opens N, f x ∈ U →
      ∃ V : Opens M, x ∈ V ∧ MapsTo f V U ∧ (∀ ⦃y z : M⦄, C.le V y z → C'.le U (f y) (f z)) ∧
        (∀ ⦃y z : M⦄, C.lt V y z → C'.lt U (f y) (f z)) := by
  refine ⟨fun h x _ U hfx => h.local_mono x U hfx, fun h => ⟨IsAEMorphismOf.continuous hf,
    fun x U hfx => ?_⟩⟩
  by_cases hx : x ∈ regLocus G X f
  · exact weakMorphism_local_of_isRegularOn hG hC hC' (isRegularOn_regLocusOf _ _ _) hx U hfx
  · exact h x hx U hfx

/-- An a.e. `(G,X)`-morphism which is a local homeomorphism is, on the source of each of its local
inverses' charts, an `IsAEChart`: `f = e` with `e` an open partial homeomorphism. -/
theorem isAEChart_of_isAEMorphism_of_isLocalHomeomorph [LocallyConnectedSpace X] [T2Space X]
    [IsRigidAction G X] {f : M → N} (hf : IsAEMorphism G X f) (hlh : IsLocalHomeomorph f)
    {e : OpenPartialHomeomorph M N} (hfe : f = e) : IsAEChart G X e := by
  have hpre : f ⁻¹' Reg G X N = Reg G X M := (hf.preimage_reg_sing hlh).1
  have hR : regLocus G X f = Reg G X M := by rw [hf.regLocus_eq, hpre, inter_self]
  have hreg : IsRegularOn G (aeAtlas G X M) (aeAtlas G X N) f (Reg G X M) := by
    have := isRegularOn_regLocusOf (G := G) (aeAtlas G X M) (aeAtlas G X N) f
    have h' : regLocusOf G (aeAtlas G X M) (aeAtlas G X N) f = Reg G X M := hR
    rwa [h'] at this
  have hsymm : ∀ y ∈ e.target, y ∈ Reg G X N → e.symm y ∈ Reg G X M := fun y hy hyR => by
    have hfy : f (e.symm y) = y := by rw [hfe]; exact e.right_inv hy
    have h : e.symm y ∈ f ⁻¹' Reg G X N := by rw [mem_preimage, hfy]; exact hyR
    rwa [hpre] at h
  refine ⟨?_, ⟨e.open_target.inter (isOpen_reg G X N), fun y hy => hy.2,
    fun y hy => hsymm y hy.1 hy.2, e.continuousOn_symm.mono inter_subset_left, ?_⟩⟩
  · rw [← hfe]
    exact hreg.mono inter_subset_right (e.open_source.inter (isOpen_reg G X M))
  · intro y hy c' hc' c hc hyc' hyc
    have hfx : f (e.symm y) = y := by rw [hfe]; exact e.right_inv hy.1
    obtain ⟨g, hg⟩ := hreg.exists_smul_eq (e.symm y) (hsymm y hy.1 hy.2) c hc c' hc' hyc
      (by rw [hfx]; exact hyc')
    refine ⟨g⁻¹, ?_⟩
    filter_upwards [(e.continuousAt_symm hy.1).eventually hg, e.open_target.mem_nhds hy.1]
      with w hw hwt
    rw [hfe, e.right_inv hwt] at hw
    rw [hw, inv_smul_smul]

omit [ContinuousConstSMul G X] in
/-- Relations through a composite chart: if `e ≫ φ` is an isomorphism for `C` and `φ` one for `C'`
(onto the same model), `e` matches the relations of the small open sets of `M` with those of
their images. -/
theorem ChartIso.rel_iff_of_trans {Z : Type*} [TopologicalSpace Z] {C : Causality M}
    {C' : Causality N} {D : Causality Z} {e : OpenPartialHomeomorph M N}
    {φ : OpenPartialHomeomorph N Z} (h : ChartIso C D (e.trans φ)) (h' : ChartIso C' D φ)
    {V : Opens M} (hV : V ≤ chartSource (e.trans φ)) {a b : M} (ha : a ∈ V) (hb : b ∈ V) :
    (C.le V a b ↔ C'.le (chartImage e V) (e a) (e b)) ∧
      (C.lt V a b ↔ C'.lt (chartImage e V) (e a) (e b)) := by
  have hsrc : ∀ {z}, z ∈ V → z ∈ e.source ∧ e z ∈ φ.source := fun hz => by
    have := hV hz
    rw [mem_chartSource, OpenPartialHomeomorph.trans_source] at this
    exact this
  have hVe : V ≤ chartSource e := fun z hz => (hsrc hz).1
  have hW : chartImage e V ≤ chartSource φ := by
    intro q hq
    obtain ⟨z, -, hzV, rfl, -⟩ := exists_of_mem_chartImage hq
    exact (hsrc hzV).2
  have himg : chartImage (e.trans φ) V = chartImage φ (chartImage e V) := by
    apply SetLike.coe_injective
    rw [coe_chartImage_of_le hV, coe_chartImage_of_le hW, coe_chartImage_of_le hVe,
      OpenPartialHomeomorph.coe_trans, image_comp]
  have h1 := h V hV a ha b hb
  have h2 := h' (chartImage e V) hW (e a) (mem_chartImage_of_mem (hVe ha) ha) (e b)
    (mem_chartImage_of_mem (hVe hb) hb)
  rw [himg, OpenPartialHomeomorph.coe_trans, Function.comp_apply, Function.comp_apply] at h1
  exact ⟨h1.1.trans h2.1.symm, h1.2.trans h2.2.symm⟩

omit [ContinuousConstSMul G X] in
/-- The local step of a strong morphism through a composite chart. -/
theorem ChartIso.local_rel_of_trans {Z : Type*} [TopologicalSpace Z] {C : Causality M}
    {C' : Causality N} {D : Causality Z} {f : M → N} (ho : IsOpenMap f)
    {e : OpenPartialHomeomorph M N} (hfe : f = e) {φ : OpenPartialHomeomorph N Z}
    (h : ChartIso C D (e.trans φ)) (h' : ChartIso C' D φ) {x : M}
    (hx : x ∈ (e.trans φ).source) :
    ∃ O : Opens M, x ∈ O ∧ ∀ V : Opens M, V ≤ O → ∀ a b,
      (C.le V a b → C'.le (imageOpensOf ho V) (f a) (f b)) ∧
        (C.lt V a b → C'.lt (imageOpensOf ho V) (f a) (f b)) := by
  refine ⟨chartSource (e.trans φ), hx, fun V hV a b => ?_⟩
  have hVe : V ≤ chartSource e := fun z hz => by
    have := hV hz
    rw [mem_chartSource, OpenPartialHomeomorph.trans_source] at this
    exact this.1
  have himg : imageOpensOf ho V = chartImage e V := by
    apply SetLike.coe_injective
    rw [coe_chartImage_of_le hVe]
    show f '' V = e '' V
    rw [hfe]
  rw [himg, hfe]
  exact ⟨fun hab => (h.rel_iff_of_trans h' hV (C.le_mem_left hab) (C.le_mem_right hab)).1.1 hab,
    fun hab => (h.rel_iff_of_trans h' hV (C.lt_mem_left hab) (C.lt_mem_right hab)).2.1 hab⟩

/-- **`rem:hypotheses_proposition_prop_gx` for unbranched maps, singular points included**: for
the causalities of `prop:GX_sing_espace_temps_topo` (every chart of the maximal a.e. atlases and
every `X_A`-chart an isomorphism, as `existsUnique_causality_singularGX_dec25` produces, the source
one absolutely minimal), every a.e. `(G,X)`-morphism `f : M → N` which is a local homeomorphism is
a strong morphism of topological spacetimes. Near a point `x`, `f` is an `IsAEChart` `e`, and `e`
followed by a chart `φ` of `N` at `f x` (of the maximal atlas if `f x` is regular, an
`X_A`-chart if not) is a chart of `M` at `x`: of its maximal atlas, or an `X_A`-chart. Only the
branch points (where `f` is not a local homeomorphism) are left (SCOPE). -/
theorem strongMorphism_of_isAEMorphism_of_isLocalHomeomorph [LocallyConnectedSpace X]
    [T2Space X] [IsRigidAction G X] {A : Type z} {Xα : A → Type y}
    [∀ a, TopologicalSpace (Xα a)] [∀ a, SingularGXStructure G X (Xα a)] {DX : Causality X}
    {DY : ∀ a, Causality (Xα a)} {C : Causality M} {C' : Causality N}
    (hCX : ∀ e ∈ aeAtlas G X M, ChartIso C DX e)
    (hCY : ∀ a (e : OpenPartialHomeomorph M (Xα a)), IsAEChart G X e → ChartIso C (DY a) e)
    (hmin : C.AbsolutelyMinimal) (hC'X : ∀ e ∈ aeAtlas G X N, ChartIso C' DX e)
    (hC'Y : ∀ a (e : OpenPartialHomeomorph N (Xα a)), IsAEChart G X e → ChartIso C' (DY a) e)
    (hcovN : ∀ y ∈ Sing G X N, ∃ a, ∃ e : OpenPartialHomeomorph N (Xα a), IsAEChart G X e ∧
      y ∈ e.source)
    {f : M → N} (hf : IsAEMorphism G X f) (hlh : IsLocalHomeomorph f) : StrongMorphism C C' f := by
  refine strongMorphism_of_locally hlh.continuous hlh.isOpenMap hmin fun x => ?_
  obtain ⟨e, hxe, hfe⟩ := hlh x
  have heA : IsAEChart G X e := isAEChart_of_isAEMorphism_of_isLocalHomeomorph hf hlh hfe
  by_cases hfx : f x ∈ Reg G X N
  · obtain ⟨φ, hφ, hfxφ⟩ := mem_support.1 hfx
    have hχ : e.trans φ ∈ aeAtlas G X M := by
      apply (isMaximalAEAtlas_aeAtlas G X M).mem_of_compatible
      intro c hc y hy
      have hyR : y ∈ Reg G X M := mem_support.2 ⟨c, hc, hy.2⟩
      have hys : y ∈ e.source ∧ e y ∈ φ.source := by
        have := hy.1
        rw [OpenPartialHomeomorph.trans_source] at this
        exact this
      obtain ⟨g, hg⟩ := heA.regularOn.exists_smul_eq y ⟨hys.1, hyR⟩ c hc φ hφ hy.2 hys.2
      exact ⟨g⁻¹, hg.mono fun z hz => by
        rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hz, inv_smul_smul]⟩
    exact (hCX _ hχ).local_rel_of_trans hlh.isOpenMap hfe (hC'X φ hφ)
      (by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨hxe, by rw [mem_preimage, ← hfe]; exact hfxφ⟩)
  · obtain ⟨a, φ, hφ, hfxφ⟩ := hcovN (f x) hfx
    exact (hCY a _ (heA.trans hφ)).local_rel_of_trans hlh.isOpenMap hfe (hC'Y a φ hφ)
      (by
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨hxe, by rw [mem_preimage, ← hfe]; exact hfxφ⟩)

end Remark

/-! ### The hypotheses are satisfiable -/

section Line

/-- `ℝ` with the translations, as a singular `(G,X)`-manifold: the maximal atlas of its regular
structure, which is a maximal a.e. atlas (`isMaximalAEAtlas_maximalAtlas`); no singular point. -/
noncomputable abbrev lineSingularGX : SingularGXStructure (Multiplicative ℝ) ℝ ℝ :=
  SingularGXStructure.ofHasGroupoid (Multiplicative ℝ) ℝ ℝ

attribute [local instance] lineSingularGX

theorem aeAtlas_line :
    aeAtlas (Multiplicative ℝ) ℝ ℝ = (gxGroupoid (Multiplicative ℝ) ℝ).maximalAtlas ℝ := rfl

theorem reg_line : Reg (Multiplicative ℝ) ℝ ℝ = univ := by
  rw [Reg, aeAtlas_line, support_maximalAtlas]

theorem sing_line : Sing (Multiplicative ℝ) ℝ ℝ = ∅ := by
  rw [Sing, reg_line, compl_univ]

/-- **The hypotheses of `existsUnique_causality_singularGX_dec25` are satisfiable**, and the
causality produced is then the timelike line. Data: `X = ℝ` with the timelike line and the
translations; one model space, `ℝ` with the same structure and causality; `M = ℝ`. Each conjunct
is one hypothesis, in the theorem's order, instantiated: (a), (b) (both halves), (b′), and the
covering of the singular locus, which is empty (`sing_line`). The last conjunct is the conclusion.
The singular locus is empty: the library has no singular `(G,X)`-structure with a singular point
(SCOPE). -/
theorem singularGX_dec25_line :
    -- (a)
    timelikeLine.CausallyArcConnected ∧
    (∀ g : Multiplicative ℝ, StrongMorphism timelikeLine timelikeLine fun p : ℝ => g • p) ∧
    -- (b)
    (∀ _ : Unit, timelikeLine.CausallyArcConnected) ∧
    (∀ _ : Unit, ∀ r ∈ aeAtlas (Multiplicative ℝ) ℝ ℝ, ChartIso timelikeLine timelikeLine r) ∧
    -- (b′)
    (∀ _ _ : Unit, ∀ ψ : OpenPartialHomeomorph ℝ ℝ, IsAEChart (Multiplicative ℝ) ℝ ψ →
      ChartIso timelikeLine timelikeLine ψ) ∧
    -- the singular locus, covered vacuously
    Sing (Multiplicative ℝ) ℝ ℝ = ∅ ∧
    -- the conclusion
    ∀ C : Causality ℝ, C.AbsolutelyMinimal →
      (∀ e ∈ aeAtlas (Multiplicative ℝ) ℝ ℝ, ChartIso C timelikeLine e) → C = timelikeLine := by
  have hreg : ∀ r ∈ aeAtlas (Multiplicative ℝ) ℝ ℝ, ChartIso timelikeLine timelikeLine r :=
    fun r hr => chartIso_of_mem_maximalAtlas timelikeLine_causallyArcConnected
      timelikeLine_strongMorphism_translation
      (fun e he => by rw [chartedSpaceSelf_atlas.1 he]; exact chartIso_refl _)
      timelikeLine_causallyArcConnected.absolutelyMinimal hr
  have hiso : ∀ _ _ : Unit, ∀ ψ : OpenPartialHomeomorph ℝ ℝ, IsAEChart (Multiplicative ℝ) ℝ ψ →
      ChartIso timelikeLine timelikeLine ψ := fun _ _ ψ hψ =>
    chartIso_model_of_subset_reg (Xα := fun _ : Unit => ℝ) (a := ()) (b := ()) timelikeLine
      (fun _ => timelikeLine) timelikeLine_strongMorphism_translation
      (fun _ => timelikeLine_causallyArcConnected) (fun _ => hreg) hψ
      (by rw [reg_line]; exact subset_univ _)
  refine ⟨timelikeLine_causallyArcConnected, timelikeLine_strongMorphism_translation,
    fun _ => timelikeLine_causallyArcConnected, fun _ => hreg, hiso, sing_line, ?_⟩
  intro C hmin hC
  obtain ⟨C₀, -, -, -, huniq⟩ := existsUnique_causality_singularGX_dec25 (M := ℝ)
    (Xα := fun _ : Unit => ℝ) timelikeLine (fun _ => timelikeLine)
    timelikeLine_causallyArcConnected timelikeLine_strongMorphism_translation
    (fun _ => timelikeLine_causallyArcConnected) (fun _ => hreg) hiso
    (fun x hx => by rw [sing_line] at hx; exact absurd hx (notMem_empty x))
  have hloc : ∀ C' : Causality ℝ,
      (∀ e ∈ aeAtlas (Multiplicative ℝ) ℝ ℝ, ChartIso C' timelikeLine e) →
      ∀ x : ℝ, (∃ e ∈ aeAtlas (Multiplicative ℝ) ℝ ℝ, x ∈ e.source ∧ ChartIso C' timelikeLine e) ∨
        ∃ _ : Unit, ∃ e : OpenPartialHomeomorph ℝ ℝ, IsAEChart (Multiplicative ℝ) ℝ e ∧
          x ∈ e.source ∧ ChartIso C' timelikeLine e := fun C' hC' x => by
    have hx : x ∈ Reg (Multiplicative ℝ) ℝ ℝ := by rw [reg_line]; exact mem_univ x
    obtain ⟨e, he, hxe⟩ := mem_support.1 hx
    exact Or.inl ⟨e, he, hxe, hC' e he⟩
  rw [huniq C hmin (hloc C hC),
    huniq timelikeLine timelikeLine_causallyArcConnected.absolutelyMinimal (hloc _ hreg)]

end Line

end Causal
