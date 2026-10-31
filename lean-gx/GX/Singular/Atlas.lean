import GX.Topology.Portly
import GX.Structure.Basic

/-!
# Almost everywhere `(G,X)`-atlases and the category of singular `(G,X)`-manifolds

Almost everywhere `(G,X)`-atlases, singular `(G,X)`-manifolds, their regular and singular loci,
a.e. `(G,X)`-morphisms, their regular loci, and the pullback (`RamcovGX.tex:397`–`611`).

* **`def:almost_everywhere_atlas_topological`** — `RamcovGX.tex:402`: `GX.IsAEAtlas`,
  `GX.isAEAtlas_iff_exists_isPortly`; completion, thinness, `GX.AELe` (l.406).
* `lem:GX_atlas_union` — `RamcovGX.tex:412` — partial: `GX.isAEAtlas_iUnion` needs the family
  nonempty (`GX.not_isAEAtlas_iUnion_empty`).
* **`cor:maximal_atlas`** — `RamcovGX.tex:458`: `GX.maximal_atlas`, `GX.maximalAEAtlas`.
* **`def:structure_topological_space_atlas`** — `RamcovGX.tex:471`: `GX.IsAEStructure`.
* **`def:singular_manifold_locally_connected`** — `RamcovGX.tex:474`: `GX.SingularGXStructure`,
  `GX.Reg`, `GX.Sing`, `GX.SingGXCat`; `GX.isPortly_reg`, `GX.isSkeletal_sing`.
* **`def:morphism`** — `RamcovGX.tex:480`: `GX.IsAEMorphismOf`, `GX.IsAEMorphism`.
* **`rem:composition_morphisms_morphisms_category`** — `RamcovGX.tex:487`:
  `GX.IsAEMorphismOf.comp`, the category `SingGXCat`, `GX.SingGXCat.isoOfHomeomorph`,
  `GX.SingGXCat.homeomorphOfIso`, `GX.IsAEMorphism.symm_of_homeomorph`.
* `rem:morphisms_analytical_two_equal` — `RamcovGX.tex:491` — partial: `GX.IsAEMorphismOf.eq_of_eqOn`
  needs `M` connected and the open set nonempty (`GX.analytic_counterexample_disconnected`,
  `GX.analytic_counterexample_empty`).
* `prop:GX_sing_morph_local` — `RamcovGX.tex:497` — partial (a reading of "locally" and of
  restriction): `GX.isAEMorphismOf_tfae`.
* **`lem:singular_manifolds_morphism_set`** — `RamcovGX.tex:507`: `GX.isGreatest_regLocusOf`.
* **`def:singular_manifolds_morphism_maximal`** — `RamcovGX.tex:518`: `GX.regLocusOf`,
  `GX.regLocus`.
* **`lem:regf1`** — `RamcovGX.tex:523`: `GX.IsAEMorphismOf.regLocusOf_eq`.
* `rem:though_may_tempted_include` — `RamcovGX.tex:538` — partial (an informal remark, read):
  `GX.zero_notMem_regLocusOf_pow`, `GX.not_isAEMorphismOf_pow`.
* `lem:aepullback` — `RamcovGX.tex:541` — partial: `GX.existsUnique_aePullback`, uniqueness among
  MAXIMAL a.e. structures only (`GX.aePullback_counterexample_nonmaximal`).
* **`def:notations_lemma_lem_aepullback`** — `RamcovGX.tex:554`: `GX.aePullback`.
* `cor:locally_connected_hausdorff_topological` — `RamcovGX.tex:558` — partial (the implicit
  hypotheses under which the pullbacks exist, added): `GX.aePullback_comp`.
* **`lem:GX_sing_homeo_reg`** — `RamcovGX.tex:592`:
  `GX.IsAEMorphismOf.regLocusOf_eq_inter_isLocalHomeomorphOn`.
* **`cor:morphisms_also_local_homemorphism`** — `RamcovGX.tex:603`:
  `GX.IsAEMorphismOf.preimage_support_eq`, `GX.IsAEMorphism.preimage_reg_sing`.
* **`rem:consequence_isomorphism_singular_manifolds`** — `RamcovGX.tex:606`:
  `GX.IsAEMorphismOf.mem_iff_of_homeomorph`, `GX.IsAEMorphism.aeAtlas_eq_of_homeomorph`.
* Bridges: `GX.isMaximalAEAtlas_maximalAtlas` (a `(G,X)`-manifold is singular with empty singular
  locus), `GX.isAEMorphismOf_maximalAtlas_iff` (there a.e. morphisms are `(G,X)`-morphisms);
  the key lemma `GX.IsMaximalAEAtlas.mem_of_compatible` (the maximal atlas absorbs compatible
  charts).

> An almost everywhere $(G,X)$-atlas on a topological space $M$ is a $(G,X)$-atlas supported by
> some portly subset of $M$. (l.402)
>
> Let $N$ be a locally connected topological space. Let $(\B_k)_{k\in K}$ be a family of
> a.e.$(G,X)$-atlases on $N$. Assume for all $(k,k')\in K^2$, there exists an a.e $(G,X)$-atlas
> $\mathcal A$ such that $\A$ is thinner than both $\B_{k}$ and $\B_{k'}$. Then the union
> $\bigcup_{k\in K} \B_k$ is an a.e.$(G,X)$-atlas. (l.412)
>
> A.e. $(G,X)$-morphisms are analytical: if two are equal on an open set, they are equal
> everywhere. (l.491)
>
> If $f$ is a.e. a local homeomorphism there exists a unique a.e. $(G,X)$-structure on $M$ such
> that $f$ is an a.e. $(G,X)$-morphism. (l.545)
>
> Let $M$ and $N$ be singular $(G,X)$-manifolds and let $f:M\rightarrow N$ an a.e
> $(G,X)$-morphism. Then, $\reg(f)=\reg(M)\cap f^{-1}(\reg(N)).$ (l.523)

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(G,X)` analytical: `X` connected, locally connected, Hausdorff; action faithful, rigid, by homeomorphisms | ⚠ weakened: `LocallyConnectedSpace X`, `T2Space X`, `IsRigidAction`, `ContinuousConstSMul` where used; connectedness of `X` and faithfulness never used |
| `lem:GX_atlas_union`: `N` locally connected | ⚠ weakened: not used |
| `lem:GX_atlas_union`: the family (implicitly) nonempty | ⚠ strengthened: `[Nonempty K]`, a finding |
| `cor:maximal_atlas`, `lem:aepullback`: `M` locally connected Hausdorff | ⚠ weakened: not used |
| singular manifolds locally connected | ✓ carried where used (composition, `prop:GX_sing_morph_local`, `SingGXCat`) |
| singular manifolds Hausdorff, second countable | ⚠ weakened: not used (bundled in `SingGXCat`); `N` Hausdorff carried for analyticity |
| `rem:morphisms_analytical_two_equal`: `M` connected, open set nonempty | ⚠ strengthened: both added, a finding |
| `lem:aepullback`: `N` a singular manifold (maximal `B`) | ⚠ weakened: `B` an a.e. atlas suffices |
| `cor:locally_connected_hausdorff_topological`: `f`, `g` a.e. local homeomorphisms | ⚠ strengthened: implicit in the paper (the pullbacks must exist), added |
| `lem:singular_manifolds_morphism_set`: `f` an a.e. morphism | ⚠ weakened: any map |

## SCOPE (disclosed)

* **(a)** An atlas is a `Set (OpenPartialHomeomorph M X)` (`Structure/Basic.lean` SCOPE (c)); a
  `(G,X)`-atlas is `IsGXAtlas`, per connected component of the overlaps. "Supported by some
  portly subset" is read as "the support is portly"; the two agree since supports are open.
* **(b)** "`f` induces a `(G,X)`-morphism `U → V`" (`def:morphism`, `lem:singular_manifolds_morphism_set`)
  is `IsRegularOn`: `f` continuous on the open `U ⊆ supp A`, `f(U) ⊆ supp B`, and in charts of `A`
  at `x` and of `B` at `f x`, near `x`, the restriction of an element of `G` — the reading of a
  `(G,X)`-morphism of `Structure/Basic.lean` SCOPE (b), stated without subtypes; one pair of
  charts per point suffices (`IsRegularOn.of_exists`).
* **(c)** A singular `(G,X)`-manifold is `[SingularGXStructure G X M]` (a maximal a.e. atlas,
  DEC-25) together with the topological instances each theorem uses; `SingGXCat` bundles all of
  them. `Reg M` is the support of the atlas, `Sing M` its complement.
* **(d)** `prop:GX_sing_morph_local`: "`f|W` is an a.e. morphism" (`IsAEMorphismOn`) reads `W`
  with the induced a.e. structure: some `U ⊆ W` portly in `W` (Portly's subtype convention) on
  which `f` induces a `(G,X)`-morphism; "locally" means around every point, on an open `W`.
* **(e)** `lem:aepullback`: "`f` is a.e. a local homeomorphism" is `IsAELocalHomeomorph`, read
  from the proof's first line (portly `O ⊆ M`, `P ⊆ Reg N`, `f(O) ⊆ P`, `f` a local homeomorphism
  on `O`); uniqueness is among maximal a.e. atlases (it fails otherwise). `aePullback` is `∅`
  when no such structure exists.
* **(f)** "`f` is a local homeomorphism around `x`" is `IsLocalHomeomorphOn f {x}`;
  "preserves the regular and singular loci" is `f⁻¹(Reg N) = Reg M`, `f⁻¹(Sing N) = Sing M`.
* **(g)** `rem:though_may_tempted_include` is read as: `0 ∉ Reg(z ↦ z^p)` for `p ≠ 1`, whatever
  the a.e. atlases on `ℂ`; hence `z ↦ z^p` is an a.e. morphism for no structures regular at `0`
  and `0^p`. The sentence about Riemann surfaces is not formalized.
* **(h)** `rem:consequence_isomorphism_singular_manifolds`'s last sentence ("an isomorphism in
  every natural ways") is not formalized.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Builds on
`GX.Structure.Basic` (WP-24c) and `GX.Topology.Portly`.
-/

namespace GX

open Set Filter Topology

universe u v w y z

/-! ### Sub-charts, completion, thinness -/

section AEAtlas

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M]

/-- `e'` is a *sub-chart* of `e` (`RamcovGX.tex:406`): its source lies in that of `e`, and it is
`e` there — the paper's `(U', φ(U'), φ_{|U'})`. -/
def IsSubchart (e' e : OpenPartialHomeomorph M X) : Prop :=
  e'.source ⊆ e.source ∧ EqOn e' e e'.source

/-- The *completion* of an atlas (`RamcovGX.tex:406`): all sub-charts of its charts. -/
def completion (A : Set (OpenPartialHomeomorph M X)) : Set (OpenPartialHomeomorph M X) :=
  {e' | ∃ e ∈ A, IsSubchart e' e}

/-- A *complete* atlas (`RamcovGX.tex:406`): closed under sub-charts. -/
def IsComplete (A : Set (OpenPartialHomeomorph M X)) : Prop :=
  ∀ e ∈ A, ∀ e', IsSubchart e' e → e' ∈ A

variable (G) in
/-- **`def:almost_everywhere_atlas_topological`** (`RamcovGX.tex:402`): an *almost everywhere
`(G,X)`-atlas* is a `(G,X)`-atlas whose support is portly. (Supported "by some portly subset":
the support is open, so containing a portly subset and being portly are the same,
`isAEAtlas_iff_exists_isPortly`.) -/
def IsAEAtlas (A : Set (OpenPartialHomeomorph M X)) : Prop :=
  IsGXAtlas G A ∧ IsPortly (support A)

variable (G) in
/-- `A` is *thinner* than `B` (`RamcovGX.tex:406`): `supp A ⊆ supp B`, and for every point
`p ∈ supp A` and every chart `e'` of `B` at `p`, some chart `e` of `A` at `p` has its source in
that of `e'` and is `g ∘ e'` there for some `g ∈ G`. -/
def IsThinner (A B : Set (OpenPartialHomeomorph M X)) : Prop :=
  support A ⊆ support B ∧ ∀ p ∈ support A, ∀ e' ∈ B, p ∈ e'.source →
    ∃ g : G, ∃ e ∈ A, p ∈ e.source ∧ e.source ⊆ e'.source ∧ EqOn e (fun y => g • e' y) e.source

variable (G) in
/-- The order of `cor:maximal_atlas` (`RamcovGX.tex:461`): `A ≤ B` iff the completion of `A` is
thinner than `B`. -/
def AELe (A B : Set (OpenPartialHomeomorph M X)) : Prop :=
  IsThinner G (completion A) B

omit [ContinuousConstSMul G X] in
theorem isOpen_support (A : Set (OpenPartialHomeomorph M X)) : IsOpen (support A) :=
  isOpen_biUnion fun e _ => e.open_source

omit [ContinuousConstSMul G X] in
theorem support_mono {A B : Set (OpenPartialHomeomorph M X)} (h : A ⊆ B) :
    support A ⊆ support B :=
  biUnion_subset_biUnion_left h

omit [ContinuousConstSMul G X] in
theorem IsSubchart.refl (e : OpenPartialHomeomorph M X) : IsSubchart e e :=
  ⟨subset_rfl, fun _ _ => rfl⟩

omit [ContinuousConstSMul G X] in
theorem IsSubchart.trans {e e' e'' : OpenPartialHomeomorph M X} (h₁ : IsSubchart e e')
    (h₂ : IsSubchart e' e'') : IsSubchart e e'' :=
  ⟨h₁.1.trans h₂.1, fun _ hx => (h₁.2 hx).trans (h₂.2 (h₁.1 hx))⟩

omit [ContinuousConstSMul G X] in
theorem isSubchart_restrOpen (e : OpenPartialHomeomorph M X) {s : Set M} (hs : IsOpen s) :
    IsSubchart (e.restrOpen s hs) e :=
  ⟨by rw [OpenPartialHomeomorph.restrOpen_source]; exact inter_subset_left, fun _ _ => rfl⟩

omit [ContinuousConstSMul G X] in
theorem subset_completion (A : Set (OpenPartialHomeomorph M X)) : A ⊆ completion A :=
  fun e he => ⟨e, he, IsSubchart.refl e⟩

omit [ContinuousConstSMul G X] in
theorem support_completion (A : Set (OpenPartialHomeomorph M X)) :
    support (completion A) = support A := by
  refine Subset.antisymm ?_ (support_mono (subset_completion A))
  intro x hx
  obtain ⟨e', ⟨e, he, hsub⟩, hx⟩ := mem_support.1 hx
  exact mem_support.2 ⟨e, he, hsub.1 hx⟩

omit [ContinuousConstSMul G X] in
/-- `RamcovGX.tex:406`: "the completed atlas is" complete. -/
theorem isComplete_completion (A : Set (OpenPartialHomeomorph M X)) :
    IsComplete (completion A) := by
  rintro e' ⟨e, he, h⟩ e'' h'
  exact ⟨e, he, h'.trans h⟩

omit [ContinuousConstSMul G X] in
/-- `RamcovGX.tex:406`: "the completed atlas is still a `(G,X)`-atlas". -/
theorem IsGXAtlas.isGXAtlas_completion {A : Set (OpenPartialHomeomorph M X)} (hA : IsGXAtlas G A) :
    IsGXAtlas G (completion A) := by
  rintro e₁' ⟨e₁, he₁, h₁⟩ e₂' ⟨e₂, he₂, h₂⟩ x hx
  obtain ⟨g, hg⟩ := hA e₁ he₁ e₂ he₂ x ⟨h₁.1 hx.1, h₂.1 hx.2⟩
  refine ⟨g, fun y hy => ?_⟩
  have hy' := connectedComponentIn_subset _ _ hy
  rw [h₂.2 hy'.2, h₁.2 hy'.1]
  exact hg y (connectedComponentIn_mono x (inter_subset_inter h₁.1 h₂.1) hy)

omit [ContinuousConstSMul G X] in
theorem IsGXAtlas.mono {A B : Set (OpenPartialHomeomorph M X)} (hB : IsGXAtlas G B)
    (h : A ⊆ B) : IsGXAtlas G A :=
  fun e he e' he' => hB e (h he) e' (h he')

omit [ContinuousConstSMul G X] in
theorem IsAEAtlas.isAEAtlas_completion {A : Set (OpenPartialHomeomorph M X)} (hA : IsAEAtlas G A) :
    IsAEAtlas G (completion A) :=
  ⟨hA.1.isGXAtlas_completion, by rw [support_completion]; exact hA.2⟩

omit [ContinuousConstSMul G X] in
/-- `def:almost_everywhere_atlas_topological`, the paper's wording: supported by some portly
subset. -/
theorem isAEAtlas_iff_exists_isPortly {A : Set (OpenPartialHomeomorph M X)} :
    IsAEAtlas G A ↔ IsGXAtlas G A ∧ ∃ U : Set M, IsPortly U ∧ U ⊆ support A :=
  ⟨fun h => ⟨h.1, _, h.2, subset_rfl⟩, fun ⟨h, _, hU, hUA⟩ =>
    ⟨h, hU.mono hUA (isOpen_support A)⟩⟩

omit [ContinuousConstSMul G X] in
/-- `RamcovGX.tex:406`: "if such an `A` is thinner than such a `B` then the completion of `A` is
still thinner than `B`". -/
theorem IsThinner.isThinner_completion {A B : Set (OpenPartialHomeomorph M X)} (h : IsThinner G A B) :
    IsThinner G (GX.completion A) B := by
  refine ⟨by rw [support_completion]; exact h.1, fun p hp e' he' hpe' => ?_⟩
  rw [support_completion] at hp
  obtain ⟨g, e, he, hpe, hsub, heq⟩ := h.2 p hp e' he' hpe'
  exact ⟨g, e, subset_completion A he, hpe, hsub, heq⟩

/-- Near every point of an overlap, two charts of a `(G,X)`-atlas differ by an element of `G`
(when `X` is locally connected, the components of the overlap are open). -/
theorem IsGXAtlas.eventually_smul_eq [LocallyConnectedSpace X]
    {A : Set (OpenPartialHomeomorph M X)} (hA : IsGXAtlas G A) {e e' : OpenPartialHomeomorph M X}
    (he : e ∈ A) (he' : e' ∈ A) {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    ∃ g : G, ∀ᶠ y in 𝓝 x, e' y = g • e y :=
  eventually_smul_eq_of_mem_gxGroupoid (hA.symm_trans_mem he he') hx hx'

/-- A set of charts which, near every point of every overlap, differ by an element of `G`, is a
`(G,X)`-atlas (rigidity propagates the element along the components). -/
theorem isGXAtlas_of_eventually [IsRigidAction G X] {A : Set (OpenPartialHomeomorph M X)}
    (h : ∀ e ∈ A, ∀ e' ∈ A, ∀ x ∈ e.source ∩ e'.source, ∃ g : G, ∀ᶠ y in 𝓝 x, e' y = g • e y) :
    IsGXAtlas G A :=
  isGXAtlas_of_symm_trans_mem fun e he e' he' => symm_trans_mem_gxGroupoid (h e he e' he')

/-- If `A ⊆ B` and `B` is a `(G,X)`-atlas, the completion of `A` is thinner than `B`. -/
theorem IsGXAtlas.isThinner_completion_of_subset [LocallyConnectedSpace X]
    {A B : Set (OpenPartialHomeomorph M X)} (hB : IsGXAtlas G B) (h : A ⊆ B) :
    IsThinner G (GX.completion A) B := by
  refine ⟨by rw [support_completion]; exact support_mono h, fun p hp e' he' hpe' => ?_⟩
  rw [support_completion] at hp
  obtain ⟨b, hb, hpb⟩ := mem_support.1 hp
  obtain ⟨g, hg⟩ := hB.eventually_smul_eq (h hb) he' hpb hpe'
  obtain ⟨t, ht, hto, hpt⟩ := mem_nhds_iff.1 hg
  let s := t ∩ e'.source
  have hso : IsOpen s := hto.inter e'.open_source
  refine ⟨g⁻¹, b.restrOpen s hso, ⟨b, hb, isSubchart_restrOpen b hso⟩, ?_, ?_, fun y hy => ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]; exact ⟨hpb, hpt, hpe'⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]; exact fun y hy => hy.2.2
  · rw [OpenPartialHomeomorph.restrOpen_source] at hy
    show b y = g⁻¹ • e' y
    rw [ht hy.2.1, inv_smul_smul]

/-- `≤` is reflexive on `(G,X)`-atlases. -/
theorem IsGXAtlas.aeLe_refl [LocallyConnectedSpace X] {A : Set (OpenPartialHomeomorph M X)}
    (hA : IsGXAtlas G A) : AELe G A A :=
  hA.isThinner_completion_of_subset subset_rfl

omit [ContinuousConstSMul G X] in
/-- `≤` is transitive. -/
theorem AELe.trans {A B C : Set (OpenPartialHomeomorph M X)} (hAB : AELe G A B)
    (hBC : AELe G B C) : AELe G A C := by
  refine ⟨hAB.1.trans (by rw [← support_completion B]; exact hBC.1), fun p hp c hc hpc => ?_⟩
  have hpB : p ∈ support (completion B) := by rw [support_completion]; exact hAB.1 hp
  obtain ⟨g, b', ⟨b, hb, hb'b⟩, hpb', hb'c, hb'eq⟩ := hBC.2 p hpB c hc hpc
  obtain ⟨h, a', ha', hpa', ha'b, ha'eq⟩ := hAB.2 p hp b hb (hb'b.1 hpb')
  let a'' := a'.restrOpen b'.source b'.open_source
  have ha''s : a''.source = a'.source ∩ b'.source := rfl
  refine ⟨h * g, a'', (isComplete_completion A) a' ha' a''
    (isSubchart_restrOpen a' b'.open_source), by rw [ha''s]; exact ⟨hpa', hpb'⟩,
    by rw [ha''s]; exact fun y hy => hb'c hy.2, fun y hy => ?_⟩
  rw [ha''s] at hy
  show a' y = (h * g) • c y
  have h1 : a' y = h • b y := ha'eq hy.1
  have h2 : b' y = g • c y := hb'eq hy.2
  rw [h1, ← hb'b.2 hy.2, h2, mul_smul]

/-! ### Rigidity on a preconnected set -/

omit [ContinuousConstSMul G X] in
/-- **Rigidity on a preconnected set**: if `F` is, near every point of a preconnected `S` inside
the source of a chart `e`, a translate of `e`, then it is one translate of `e` on all of `S`. -/
theorem exists_smul_eq_on_of_isPreconnected [IsRigidAction G X] {e : OpenPartialHomeomorph M X}
    {F : M → X} {S : Set M} (hS : IsPreconnected S) (hSe : S ⊆ e.source)
    (hloc : ∀ x ∈ S, ∃ g : G, ∀ᶠ y in 𝓝 x, F y = g • e y) :
    ∃ g : G, ∀ y ∈ S, F y = g • e y := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact ⟨1, fun _ h => h.elim⟩
  obtain ⟨g₀, hg₀⟩ := hloc x hx
  let u : Set M := {y | ∀ᶠ z in 𝓝 y, F z = g₀ • e z}
  let v : Set M := {y | ∃ g : G, (∀ᶠ z in 𝓝 y, F z = g • e z) ∧ ∃ p : X, g • p ≠ g₀ • p}
  have hu : IsOpen u := isOpen_setOf_eventually_nhds
  have hv : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨g, hg, hne⟩
    filter_upwards [hg.eventually_nhds] with y' hy' using ⟨g, hy', hne⟩
  have hcover : S ⊆ u ∪ v := by
    intro y hy
    obtain ⟨g, hg⟩ := hloc y hy
    by_cases hgg : ∀ p : X, g • p = g₀ • p
    · left
      filter_upwards [hg] with z hz
      rw [hz, hgg]
    · right
      obtain ⟨p, hp⟩ := not_forall.1 hgg
      exact ⟨g, hg, p, hp⟩
  have hdisj : S ∩ (u ∩ v) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y ⟨hys, hyu, g, hg, p, hp⟩ => hp ?_
    have hev : ∀ᶠ z in 𝓝 y, g • e z = g₀ • e z ∧ z ∈ e.source := by
      filter_upwards [hyu, hg, e.open_source.mem_nhds (hSe hys)] with z h1 h2 h3
      exact ⟨by rw [← h2]; exact h1, h3⟩
    obtain ⟨t, ht, hto, hyt⟩ := mem_nhds_iff.1 hev
    exact IsRigidAction.smul_eq_of_eqOn
      (e.isOpen_image_of_subset_source hto fun z hz => (ht hz).2) ⟨e y, mem_image_of_mem e hyt⟩
      (by rintro _ ⟨z, hz, rfl⟩; exact (ht hz).1) p
  rcases isPreconnected_iff_subset_of_disjoint.1 hS u v hu hv hcover
    (by rw [hdisj]) with hSu | hSv
  · exact ⟨g₀, fun y hy => (hSu hy).self_of_nhds⟩
  · have : x ∈ S ∩ (u ∩ v) := ⟨hx, hg₀, hSv hx⟩
    rw [hdisj] at this
    exact this.elim

/-! ### `lem:GX_atlas_union` -/

/-- **`lem:GX_atlas_union`** (`RamcovGX.tex:412`), with the family nonempty: a nonempty family of
a.e. `(G,X)`-atlases, any two of which have a common thinner a.e. `(G,X)`-atlas, has an a.e.
`(G,X)`-atlas as union. The paper's `N` locally connected is not used (the charts make the
supports locally connected through `X`); `X` locally connected and Hausdorff and the action rigid
are used. For an empty family the statement fails (`not_isAEAtlas_iUnion_empty`). -/
theorem isAEAtlas_iUnion [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {K : Type z} [Nonempty K] {B : K → Set (OpenPartialHomeomorph M X)}
    (hB : ∀ k, IsAEAtlas G (B k))
    (hthin : ∀ k k', ∃ A, IsAEAtlas G A ∧ IsThinner G A (B k) ∧ IsThinner G A (B k')) :
    IsAEAtlas G (⋃ k, B k) := by
  refine ⟨?_, ?_⟩
  · intro e he e' he' x hx
    obtain ⟨k, hk⟩ := mem_iUnion.1 he
    obtain ⟨k', hk'⟩ := mem_iUnion.1 he'
    obtain ⟨A, hA, hAk, hAk'⟩ := hthin k k'
    set W := connectedComponentIn (e.source ∩ e'.source) x
    have hWo : IsOpen W := isOpen_connectedComponentIn_of_subset_source e
      (e.open_source.inter e'.open_source) inter_subset_left x
    have hWs : W ⊆ e.source ∩ e'.source := connectedComponentIn_subset _ _
    have hS : IsPreconnected (W ∩ support A) :=
      hA.2.isPreconnected_inter hWo isPreconnected_connectedComponentIn
    have hloc : ∀ p ∈ W ∩ support A, ∃ g : G, ∀ᶠ y in 𝓝 p, e' y = g • e y := by
      rintro p ⟨hpW, hpA⟩
      obtain ⟨g₁, a, ha, hpa, -, haeq⟩ := hAk.2 p hpA e hk (hWs hpW).1
      obtain ⟨g₂, b, hb, hpb, -, hbeq⟩ := hAk'.2 p hpA e' hk' (hWs hpW).2
      obtain ⟨c, hc⟩ := hA.1.eventually_smul_eq ha hb hpa hpb
      refine ⟨g₂⁻¹ * c * g₁, ?_⟩
      filter_upwards [hc, a.open_source.mem_nhds hpa, b.open_source.mem_nhds hpb]
        with y hy hya hyb
      have h1 : b y = g₂ • e' y := hbeq hyb
      have h2 : a y = g₁ • e y := haeq hya
      rw [h2, h1] at hy
      rw [mul_smul, mul_smul, ← hy, inv_smul_smul]
    obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isPreconnected hS
      (inter_subset_left.trans (hWs.trans inter_subset_left)) hloc
    refine ⟨g, ?_⟩
    have hcl : W ⊆ closure (W ∩ support A) := fun y hy =>
      hWo.inter_closure ⟨hy, hA.2.dense y⟩
    exact Set.EqOn.of_subset_closure hg (e'.continuousOn.mono (hWs.trans inter_subset_right))
      ((e.continuousOn.mono (hWs.trans inter_subset_left)).const_smul g) inter_subset_left hcl
  · obtain ⟨k₀⟩ := ‹Nonempty K›
    exact (hB k₀).2.mono (support_mono (subset_iUnion B k₀)) (isOpen_support _)

omit [ContinuousConstSMul G X] in
/-- `lem:GX_atlas_union` needs a nonempty family: the empty union is the empty atlas, whose
support `∅` is not portly in a nonempty space. -/
theorem not_isAEAtlas_iUnion_empty [Nonempty M] (B : Empty → Set (OpenPartialHomeomorph M X)) :
    ¬ IsAEAtlas G (⋃ k, B k) := by
  rintro ⟨-, h⟩
  have : support (⋃ k, B k) = ∅ := by simp [support]
  rw [this] at h
  obtain ⟨x⟩ := ‹Nonempty M›
  simpa using h.dense x

/-! ### `cor:maximal_atlas` -/

variable (G) in
/-- The maximum of `cor:maximal_atlas` (`RamcovGX.tex:458`): the union of all the a.e.
`(G,X)`-atlases `B ≥ A`. -/
def maximalAEAtlas (A : Set (OpenPartialHomeomorph M X)) : Set (OpenPartialHomeomorph M X) :=
  ⋃₀ {B | IsAEAtlas G B ∧ AELe G A B}

omit [ContinuousConstSMul G X] in
theorem subset_maximalAEAtlas {A B : Set (OpenPartialHomeomorph M X)} (hB : IsAEAtlas G B)
    (h : AELe G A B) : B ⊆ maximalAEAtlas G A :=
  subset_sUnion_of_mem ⟨hB, h⟩

/-- The maximum is an a.e. `(G,X)`-atlas (`lem:GX_atlas_union`, the completion of `A` being a
common thinner atlas). -/
theorem IsAEAtlas.maximalAEAtlas [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {A : Set (OpenPartialHomeomorph M X)} (hA : IsAEAtlas G A) :
    IsAEAtlas G (GX.maximalAEAtlas G A) := by
  have hne : Nonempty {B | IsAEAtlas G B ∧ AELe G A B} := ⟨⟨A, hA, hA.1.aeLe_refl⟩⟩
  rw [GX.maximalAEAtlas, sUnion_eq_iUnion]
  exact isAEAtlas_iUnion (fun B => B.2.1) fun B B' => ⟨_, hA.isAEAtlas_completion, B.2.2, B'.2.2⟩

theorem IsAEAtlas.subset_maximalAEAtlas [LocallyConnectedSpace X]
    {A : Set (OpenPartialHomeomorph M X)} (hA : IsAEAtlas G A) : A ⊆ GX.maximalAEAtlas G A :=
  GX.subset_maximalAEAtlas hA hA.1.aeLe_refl

/-- Every `B ≥ A` is `≤` the maximum. -/
theorem IsAEAtlas.aeLe_maximalAEAtlas [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {A B : Set (OpenPartialHomeomorph M X)} (hA : IsAEAtlas G A) (hB : IsAEAtlas G B)
    (h : AELe G A B) : AELe G B (GX.maximalAEAtlas G A) :=
  hA.maximalAEAtlas.1.isThinner_completion_of_subset (GX.subset_maximalAEAtlas hB h)

/-- **`cor:maximal_atlas`** (`RamcovGX.tex:458`): for every a.e. `(G,X)`-atlas `A`, the set of
a.e. `(G,X)`-atlases `B ≥ A` has a maximum for `≤`, namely `maximalAEAtlas G A`; it is moreover
the greatest such atlas for inclusion, hence unique. The paper's `M` locally connected Hausdorff
is not used. -/
theorem maximal_atlas [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {A : Set (OpenPartialHomeomorph M X)} (hA : IsAEAtlas G A) :
    (IsAEAtlas G (GX.maximalAEAtlas G A) ∧ AELe G A (GX.maximalAEAtlas G A) ∧
      ∀ B, IsAEAtlas G B → AELe G A B → AELe G B (GX.maximalAEAtlas G A)) ∧
    IsGreatest {B | IsAEAtlas G B ∧ AELe G A B} (GX.maximalAEAtlas G A) := by
  have h1 := hA.maximalAEAtlas
  have h2 : AELe G A (GX.maximalAEAtlas G A) :=
    hA.1.aeLe_refl.trans (hA.aeLe_maximalAEAtlas hA hA.1.aeLe_refl)
  exact ⟨⟨h1, h2, fun B hB h => hA.aeLe_maximalAEAtlas hB h⟩, ⟨h1, h2⟩,
    fun B hB => GX.subset_maximalAEAtlas hB.1 hB.2⟩

/-- Two a.e. atlases with `A ≤ B` have the same maximum: they define the same a.e.
`(G,X)`-structure. -/
theorem maximalAEAtlas_eq_of_aeLe [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {A B : Set (OpenPartialHomeomorph M X)} (hA : IsAEAtlas G A) (hB : IsAEAtlas G B)
    (h : AELe G A B) : GX.maximalAEAtlas G A = GX.maximalAEAtlas G B := by
  refine Subset.antisymm (GX.subset_maximalAEAtlas hA.maximalAEAtlas
    (hA.aeLe_maximalAEAtlas hB h)) (GX.subset_maximalAEAtlas hB.maximalAEAtlas ?_)
  exact h.trans (hB.1.aeLe_refl.trans (hB.aeLe_maximalAEAtlas hB hB.1.aeLe_refl))

variable (G) in
/-- An a.e. `(G,X)`-atlas *maximal in the sense of `cor:maximal_atlas`*: it contains every
a.e. `(G,X)`-atlas above it. -/
def IsMaximalAEAtlas (A : Set (OpenPartialHomeomorph M X)) : Prop :=
  IsAEAtlas G A ∧ ∀ B, IsAEAtlas G B → AELe G A B → B ⊆ A

theorem IsMaximalAEAtlas.maximalAEAtlas_eq {A : Set (OpenPartialHomeomorph M X)}
    (hA : IsMaximalAEAtlas G A) [LocallyConnectedSpace X] : GX.maximalAEAtlas G A = A :=
  Subset.antisymm (sUnion_subset fun B hB => hA.2 B hB.1 hB.2) hA.1.subset_maximalAEAtlas

theorem isMaximalAEAtlas_iff [LocallyConnectedSpace X] {A : Set (OpenPartialHomeomorph M X)} :
    IsMaximalAEAtlas G A ↔ IsAEAtlas G A ∧ GX.maximalAEAtlas G A = A :=
  ⟨fun h => ⟨h.1, h.maximalAEAtlas_eq⟩, fun ⟨h, heq⟩ =>
    ⟨h, fun _ hB hAB => heq ▸ GX.subset_maximalAEAtlas hB hAB⟩⟩

/-- The maximum of `cor:maximal_atlas` is maximal. -/
theorem IsAEAtlas.isMaximalAEAtlas_maximalAEAtlas [LocallyConnectedSpace X] [T2Space X]
    [IsRigidAction G X] {A : Set (OpenPartialHomeomorph M X)} (hA : IsAEAtlas G A) :
    IsMaximalAEAtlas G (GX.maximalAEAtlas G A) := by
  refine ⟨hA.maximalAEAtlas, fun B hB h => ?_⟩
  have hAm : AELe G A (GX.maximalAEAtlas G A) := (maximal_atlas hA).1.2.1
  exact GX.subset_maximalAEAtlas hB (hAm.trans h)

/-- **The maximal atlas absorbs every compatible chart**: a chart which, near every point of its
overlap with each chart of a maximal a.e. `(G,X)`-atlas `A`, differs from it by an element of
`G`, belongs to `A`. -/
theorem IsMaximalAEAtlas.mem_of_compatible [LocallyConnectedSpace X] [IsRigidAction G X]
    {A : Set (OpenPartialHomeomorph M X)} (hA : IsMaximalAEAtlas G A)
    {φ : OpenPartialHomeomorph M X}
    (h : ∀ c ∈ A, ∀ y ∈ φ.source ∩ c.source, ∃ g : G, ∀ᶠ z in 𝓝 y, c z = g • φ z) : φ ∈ A := by
  have hGX : IsGXAtlas G (insert φ A) := by
    refine isGXAtlas_of_eventually fun e he e' he' x hx => ?_
    rcases he with rfl | he <;> rcases he' with rfl | he'
    · exact ⟨1, Eventually.of_forall fun _ => (one_smul G _).symm⟩
    · exact h e' he' x hx
    · obtain ⟨g, hg⟩ := h e he x ⟨hx.2, hx.1⟩
      exact ⟨g⁻¹, by filter_upwards [hg] with z hz; rw [hz, inv_smul_smul]⟩
    · exact hA.1.1.eventually_smul_eq he he' hx.1 hx.2
  have hB : IsAEAtlas G (insert φ A) :=
    ⟨hGX, hA.1.2.mono (support_mono (subset_insert φ A)) (isOpen_support _)⟩
  exact hA.2 _ hB (hGX.isThinner_completion_of_subset (subset_insert φ A)) (mem_insert φ A)

/-- A maximal a.e. `(G,X)`-atlas is complete. -/
theorem IsMaximalAEAtlas.isComplete [LocallyConnectedSpace X] [IsRigidAction G X]
    {A : Set (OpenPartialHomeomorph M X)} (hA : IsMaximalAEAtlas G A) : IsComplete A := by
  intro e he e' he'
  refine hA.mem_of_compatible fun c hc y hy => ?_
  obtain ⟨g, hg⟩ := hA.1.1.eventually_smul_eq he hc (he'.1 hy.1) hy.2
  refine ⟨g, ?_⟩
  filter_upwards [hg, e'.open_source.mem_nhds hy.1] with z hz hz'
  rw [hz, he'.2 hz']

/-- A restriction of a chart of a maximal a.e. atlas is in the atlas. -/
theorem IsMaximalAEAtlas.restrOpen_mem [LocallyConnectedSpace X] [IsRigidAction G X]
    {A : Set (OpenPartialHomeomorph M X)} (hA : IsMaximalAEAtlas G A)
    {e : OpenPartialHomeomorph M X} (he : e ∈ A) {s : Set M} (hs : IsOpen s) :
    e.restrOpen s hs ∈ A :=
  hA.isComplete e he _ (isSubchart_restrOpen e hs)

end AEAtlas

/-! ### Maps inducing `(G,X)`-morphisms, and a.e. `(G,X)`-morphisms, for given atlases -/

section Morphism

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M] {N : Type y} [TopologicalSpace N]
  {P : Type*} [TopologicalSpace P]

variable (G) in
/-- `f` *induces a `(G,X)`-morphism* from the open set `U ⊆ supp A` into `supp B`: `f` is
continuous on `U`, maps it into `supp B`, and read in any charts of `A` at `x ∈ U` and of `B` at
`f x` it is, near `x`, the restriction of an element of `G` (the reading of a `(G,X)`-morphism of
`Structure/Basic.lean`, SCOPE (b), on the `(G,X)`-manifolds `U` and `supp B`). -/
structure IsRegularOn (A : Set (OpenPartialHomeomorph M X)) (B : Set (OpenPartialHomeomorph N X))
    (f : M → N) (U : Set M) : Prop where
  isOpen : IsOpen U
  subset_support : U ⊆ support A
  mapsTo : MapsTo f U (support B)
  continuousOn : ContinuousOn f U
  exists_smul_eq : ∀ x ∈ U, ∀ e ∈ A, ∀ e' ∈ B, x ∈ e.source → f x ∈ e'.source →
    ∃ g : G, ∀ᶠ y in 𝓝 x, e' (f y) = g • e y

omit [ContinuousConstSMul G X] in
theorem IsRegularOn.mono {A : Set (OpenPartialHomeomorph M X)} {B : Set (OpenPartialHomeomorph N X)}
    {f : M → N} {U V : Set M} (h : IsRegularOn G A B f U) (hVU : V ⊆ U) (hV : IsOpen V) :
    IsRegularOn G A B f V :=
  ⟨hV, hVU.trans h.subset_support, h.mapsTo.mono_left hVU, h.continuousOn.mono hVU,
    fun x hx => h.exists_smul_eq x (hVU hx)⟩

omit [ContinuousConstSMul G X] in
/-- Inducing a `(G,X)`-morphism is a local property: unions. -/
theorem isRegularOn_sUnion {A : Set (OpenPartialHomeomorph M X)}
    {B : Set (OpenPartialHomeomorph N X)} {f : M → N} {𝒰 : Set (Set M)}
    (h : ∀ U ∈ 𝒰, IsRegularOn G A B f U) : IsRegularOn G A B f (⋃₀ 𝒰) := by
  refine ⟨isOpen_sUnion fun U hU => (h U hU).isOpen, sUnion_subset fun U hU => (h U hU).2,
    fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨U, hU, hxU⟩ := mem_sUnion.1 hx; exact (h U hU).mapsTo hxU
  · obtain ⟨U, hU, hxU⟩ := mem_sUnion.1 hx
    exact ((h U hU).continuousOn.continuousAt ((h U hU).isOpen.mem_nhds hxU)).continuousWithinAt
  · obtain ⟨U, hU, hxU⟩ := mem_sUnion.1 hx; exact (h U hU).exists_smul_eq x hxU

omit [ContinuousConstSMul G X] in
theorem isRegularOn_iUnion {ι : Sort*} {A : Set (OpenPartialHomeomorph M X)}
    {B : Set (OpenPartialHomeomorph N X)} {f : M → N} {U : ι → Set M}
    (h : ∀ i, IsRegularOn G A B f (U i)) : IsRegularOn G A B f (⋃ i, U i) := by
  rw [← sUnion_range]
  exact isRegularOn_sUnion fun _ ⟨i, hi⟩ => hi ▸ h i

/-- **Chart independence**: over `(G,X)`-atlases, one pair of charts at every point suffices. -/
theorem IsRegularOn.of_exists [LocallyConnectedSpace X] {A : Set (OpenPartialHomeomorph M X)}
    {B : Set (OpenPartialHomeomorph N X)} (hA : IsGXAtlas G A) (hB : IsGXAtlas G B) {f : M → N}
    {U : Set M} (hU : IsOpen U) (hUA : U ⊆ support A) (hmaps : MapsTo f U (support B))
    (hcont : ContinuousOn f U)
    (h : ∀ x ∈ U, ∃ e ∈ A, ∃ e' ∈ B, x ∈ e.source ∧ f x ∈ e'.source ∧
      ∃ g : G, ∀ᶠ y in 𝓝 x, e' (f y) = g • e y) : IsRegularOn G A B f U := by
  refine ⟨hU, hUA, hmaps, hcont, fun x hx e₁ he₁ e₁' he₁' hx₁ hfx₁ => ?_⟩
  obtain ⟨e, he, e', he', hxe, hfxe, g, hg⟩ := h x hx
  obtain ⟨a, ha⟩ := hA.eventually_smul_eq he₁ he hx₁ hxe
  obtain ⟨b, hb⟩ := hB.eventually_smul_eq he' he₁' hfxe hfx₁
  refine ⟨b * g * a, ?_⟩
  filter_upwards [(hcont.continuousAt (hU.mem_nhds hx)).eventually hb, hg, ha] with y h1 h2 h3
  rw [h1, h2, h3, mul_smul, mul_smul]

/-- A map inducing a `(G,X)`-morphism on `U` is a local homeomorphism on `U`. -/
theorem IsRegularOn.isLocalHomeomorphOn {A : Set (OpenPartialHomeomorph M X)}
    {B : Set (OpenPartialHomeomorph N X)} {f : M → N} {U : Set M} (h : IsRegularOn G A B f U) :
    IsLocalHomeomorphOn f U := by
  refine IsLocalHomeomorphOn.mk f U fun x hx => ?_
  obtain ⟨e, he, hxe⟩ := mem_support.1 (h.subset_support hx)
  obtain ⟨e', he', hfxe'⟩ := mem_support.1 (h.mapsTo hx)
  obtain ⟨g, hg⟩ := h.exists_smul_eq x hx e he e' he' hxe hfxe'
  have hev : ∀ᶠ y in 𝓝 x, f y ∈ e'.source ∧ e' (f y) = g • e y :=
    ((h.continuousOn.continuousAt (h.isOpen.mem_nhds hx)).eventually
      (e'.open_source.mem_nhds hfxe')).and hg
  obtain ⟨O, hO, hOo, hxO⟩ := mem_nhds_iff.1 hev
  refine ⟨((e.transHomeomorph (Homeomorph.smul g)).trans e'.symm).restrOpen O hOo, ?_,
    fun y hy => ?_⟩
  · show (x ∈ e.source ∧ g • e x ∈ e'.target) ∧ x ∈ O
    refine ⟨⟨hxe, ?_⟩, hxO⟩
    rw [← (hO hxO).2]
    exact e'.map_source (hO hxO).1
  · have hyO : y ∈ O := hy.2
    show f y = e'.symm (g • e y)
    rw [← (hO hyO).2, e'.left_inv (hO hyO).1]

variable (G) in
/-- **`def:morphism`** (`RamcovGX.tex:480`), for given atlases: an *a.e. `(G,X)`-morphism* is a
continuous map with portly `U ⊆ supp A`, `V ⊆ supp B`, `f(U) ⊆ V`, such that `f` induces a
`(G,X)`-morphism `U → V`. -/
structure IsAEMorphismOf (A : Set (OpenPartialHomeomorph M X))
    (B : Set (OpenPartialHomeomorph N X)) (f : M → N) : Prop where
  continuous : Continuous f
  exists_isRegularOn : ∃ U : Set M, ∃ V : Set N, IsPortly U ∧ IsPortly V ∧ V ⊆ support B ∧
    MapsTo f U V ∧ IsRegularOn G A B f U

omit [ContinuousConstSMul G X] in
/-- The target portly set may be taken to be the whole regular locus `supp B`. -/
theorem isAEMorphismOf_iff {A : Set (OpenPartialHomeomorph M X)}
    {B : Set (OpenPartialHomeomorph N X)} (hB : IsAEAtlas G B) {f : M → N} :
    IsAEMorphismOf G A B f ↔ Continuous f ∧ ∃ U : Set M, IsPortly U ∧ IsRegularOn G A B f U :=
  ⟨fun ⟨hc, U, _, hU, _, _, _, h⟩ => ⟨hc, U, hU, h⟩, fun ⟨hc, U, hU, h⟩ =>
    ⟨hc, U, support B, hU, hB.2, subset_rfl, h.mapsTo, h⟩⟩

variable (G) in
/-- **`def:singular_manifolds_morphism_maximal`** (`RamcovGX.tex:518`), for given atlases: the
*regular locus* of `f`, the union of the open sets on which `f` induces a `(G,X)`-morphism. -/
def regLocusOf (A : Set (OpenPartialHomeomorph M X)) (B : Set (OpenPartialHomeomorph N X))
    (f : M → N) : Set M :=
  ⋃₀ {U | IsRegularOn G A B f U}

omit [ContinuousConstSMul G X] in
theorem isRegularOn_regLocusOf (A : Set (OpenPartialHomeomorph M X))
    (B : Set (OpenPartialHomeomorph N X)) (f : M → N) :
    IsRegularOn G A B f (regLocusOf G A B f) :=
  isRegularOn_sUnion fun _ h => h

omit [ContinuousConstSMul G X] in
/-- **`lem:singular_manifolds_morphism_set`** (`RamcovGX.tex:507`): the open sets `U ⊆ supp A`
on which `f` induces a `(G,X)`-morphism into `supp B` have a maximum for inclusion, the regular
locus of `f`. No hypothesis on `f` is used. -/
theorem isGreatest_regLocusOf (A : Set (OpenPartialHomeomorph M X))
    (B : Set (OpenPartialHomeomorph N X)) (f : M → N) :
    IsGreatest {U | IsRegularOn G A B f U} (regLocusOf G A B f) :=
  ⟨isRegularOn_regLocusOf (G := G) A B f, fun _ hU => subset_sUnion_of_mem hU⟩

omit [ContinuousConstSMul G X] in
theorem IsRegularOn.subset_regLocusOf {A : Set (OpenPartialHomeomorph M X)}
    {B : Set (OpenPartialHomeomorph N X)} {f : M → N} {U : Set M} (h : IsRegularOn G A B f U) :
    U ⊆ regLocusOf G A B f :=
  subset_sUnion_of_mem h

omit [ContinuousConstSMul G X] in
theorem regLocusOf_subset (A : Set (OpenPartialHomeomorph M X))
    (B : Set (OpenPartialHomeomorph N X)) (f : M → N) :
    regLocusOf G A B f ⊆ support A ∩ f ⁻¹' support B :=
  fun _ hx => ⟨(isRegularOn_regLocusOf (G := G) A B f).subset_support hx,
    (isRegularOn_regLocusOf (G := G) A B f).mapsTo hx⟩

omit [ContinuousConstSMul G X] in
/-- The regular locus of an a.e. morphism is portly. -/
theorem IsAEMorphismOf.isPortly_regLocusOf {A : Set (OpenPartialHomeomorph M X)}
    {B : Set (OpenPartialHomeomorph N X)} {f : M → N} (hf : IsAEMorphismOf G A B f) :
    IsPortly (regLocusOf G A B f) := by
  obtain ⟨U, -, hU, -, -, -, h⟩ := hf.exists_isRegularOn
  exact hU.mono h.subset_regLocusOf (isRegularOn_regLocusOf (G := G) A B f).isOpen

/-- **`lem:regf1`** (`RamcovGX.tex:523`): the regular locus of an a.e. `(G,X)`-morphism is
`supp A ∩ f⁻¹(supp B)`. -/
theorem IsAEMorphismOf.regLocusOf_eq [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {A : Set (OpenPartialHomeomorph M X)} {B : Set (OpenPartialHomeomorph N X)}
    (hA : IsAEAtlas G A) (hB : IsAEAtlas G B) {f : M → N} (hf : IsAEMorphismOf G A B f) :
    regLocusOf G A B f = support A ∩ f ⁻¹' support B := by
  refine Subset.antisymm (regLocusOf_subset A B f) ?_
  rintro x ⟨hxA, hxB⟩
  obtain ⟨e, he, hxe⟩ := mem_support.1 hxA
  obtain ⟨e', he', hfxe'⟩ := mem_support.1 hxB
  set R := regLocusOf G A B f
  have hR : IsPortly R := hf.isPortly_regLocusOf
  have hRreg := isRegularOn_regLocusOf (G := G) A B f
  set D := e.source ∩ f ⁻¹' e'.source
  have hDo : IsOpen D := e.open_source.inter (e'.open_source.preimage hf.continuous)
  set O := connectedComponentIn D x
  have hOo : IsOpen O := isOpen_connectedComponentIn_of_subset_source e hDo inter_subset_left x
  have hOD : O ⊆ D := connectedComponentIn_subset _ _
  have hxO : x ∈ O := mem_connectedComponentIn ⟨hxe, hfxe'⟩
  have hS : IsPreconnected (O ∩ R) := hR.isPreconnected_inter hOo isPreconnected_connectedComponentIn
  obtain ⟨g, hg⟩ := exists_smul_eq_on_of_isPreconnected (F := fun y => e' (f y)) hS
    (inter_subset_left.trans (hOD.trans inter_subset_left)) fun y hy =>
      hRreg.exists_smul_eq y hy.2 e he e' he' (hOD hy.1).1 (hOD hy.1).2
  have hcl : O ⊆ closure (O ∩ R) := fun y hy => hOo.inter_closure ⟨hy, hR.dense y⟩
  have hFc : ContinuousOn (fun y => e' (f y)) O :=
    e'.continuousOn.comp hf.continuous.continuousOn fun y hy => (hOD hy).2
  have hOeq : EqOn (fun y => e' (f y)) (fun y => g • e y) O :=
    Set.EqOn.of_subset_closure hg hFc ((e.continuousOn.mono (hOD.trans inter_subset_left)).const_smul g)
      inter_subset_left hcl
  have hOreg : IsRegularOn G A B f O := by
    refine IsRegularOn.of_exists hA.1 hB.1 hOo (fun y hy => mem_support.2 ⟨e, he, (hOD hy).1⟩)
      (fun y hy => mem_support.2 ⟨e', he', (hOD hy).2⟩) hf.continuous.continuousOn
      fun y hy => ⟨e, he, e', he', (hOD hy).1, (hOD hy).2, g, ?_⟩
    filter_upwards [hOo.mem_nhds hy] with z hz using hOeq hz
  exact hOreg.subset_regLocusOf hxO

/-- The identity is an a.e. `(G,X)`-morphism. -/
theorem isAEMorphismOf_id [LocallyConnectedSpace X] {A : Set (OpenPartialHomeomorph M X)}
    (hA : IsAEAtlas G A) : IsAEMorphismOf G A A id := by
  refine (isAEMorphismOf_iff hA).2 ⟨continuous_id, support A, hA.2, ?_⟩
  exact IsRegularOn.of_exists hA.1 hA.1 (isOpen_support A) subset_rfl (fun _ h => h)
    continuousOn_id fun x hx => by
      obtain ⟨e, he, hxe⟩ := mem_support.1 hx
      exact ⟨e, he, e, he, hxe, hxe, 1, Eventually.of_forall fun _ => (one_smul G _).symm⟩

omit [TopologicalSpace X] [Group G] [MulAction G X] [ContinuousConstSMul G X] in
/-- The trace of the preimage of a portly set under a map which is a local homeomorphism on a
portly `U` is portly (the subtype-free form of `RamcovGX.tex:389`). -/
theorem IsPortly.inter_preimage_of_isLocalHomeomorphOn [LocallyConnectedSpace M] {U : Set M}
    (hU : IsPortly U) {f : M → N} (hf : IsLocalHomeomorphOn f U) {V : Set N} (hV : IsPortly V) :
    IsPortly (U ∩ f ⁻¹' V) := by
  have hSo : IsOpen (U ∩ f ⁻¹' V) := hf.continuousOn.isOpen_inter_preimage hU.isOpen hV.isOpen
  have hSd : Dense (U ∩ f ⁻¹' V) := by
    refine dense_iff_inter_open.2 fun W hW hne => ?_
    obtain ⟨u, huW, huU⟩ := hU.dense.inter_open_nonempty W hW hne
    obtain ⟨e, hue, hfe⟩ := hf u huU
    have hT : IsOpen (W ∩ U ∩ e.source) := (hW.inter hU.isOpen).inter e.open_source
    obtain ⟨_, ⟨t, ht, rfl⟩, htV⟩ := hV.dense.inter_open_nonempty _
      (e.isOpen_image_of_subset_source hT inter_subset_right) ⟨e u, u, ⟨⟨huW, huU⟩, hue⟩, rfl⟩
    exact ⟨t, ht.1.1, ht.1.2, by rw [mem_preimage, hfe]; exact htV⟩
  refine ⟨hSo, hSd, fun W hW hWc => ?_⟩
  set W' := W ∩ U
  have hW'o : IsOpen W' := hW.inter hU.isOpen
  have hW'c : IsPreconnected W' := hU.isPreconnected_inter hW hWc
  have heq : W ∩ (U ∩ f ⁻¹' V) = W' ∩ f ⁻¹' V := (inter_assoc _ _ _).symm
  rw [heq]
  refine isPreconnected_of_local hW'c inter_subset_left (fun y hy => ?_) fun x hx => ?_
  · rw [← heq]; exact hW.inter_closure ⟨hy.1, hSd y⟩
  · obtain ⟨e, hxe, hfe⟩ := hf x hx.2
    set Nx := connectedComponentIn (W' ∩ e.source) x
    have hNo : IsOpen Nx := (hW'o.inter e.open_source).connectedComponentIn
    have hNs : Nx ⊆ W' ∩ e.source := connectedComponentIn_subset _ _
    refine ⟨Nx, hNo, mem_connectedComponentIn ⟨hx, hxe⟩, ?_⟩
    have hNe : Nx ⊆ e.source := hNs.trans inter_subset_right
    have h1 : IsPreconnected (e '' Nx ∩ V) :=
      hV.locallyConnectedIn _ (e.isOpen_image_of_subset_source hNo hNe)
        (isPreconnected_connectedComponentIn.image _ (e.continuousOn.mono hNe))
    have h2 : IsPreconnected (e.symm '' (e '' Nx ∩ V)) :=
      h1.image _ (e.continuousOn_symm.mono
        (inter_subset_left.trans (e.mapsTo.mono_left hNe).image_subset))
    convert h2 using 1
    rw [← image_inter_preimage]
    refine Eq.trans ?_ (e.toPartialEquiv.symm_image_image_of_subset_source
      (inter_subset_left.trans hNe : Nx ∩ e ⁻¹' V ⊆ e.source)).symm
    rw [hfe]
    ext y
    exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, (hNs a).1, c⟩⟩

/-- **`rem:composition_morphisms_morphisms_category`** (`RamcovGX.tex:487`), first sentence: a
composite of a.e. `(G,X)`-morphisms is an a.e. `(G,X)`-morphism. The source is locally connected
(as a singular `(G,X)`-manifold is). -/
theorem IsAEMorphismOf.comp [LocallyConnectedSpace M] {A : Set (OpenPartialHomeomorph M X)}
    {B : Set (OpenPartialHomeomorph N X)} {C : Set (OpenPartialHomeomorph P X)} {f : M → N}
    {f' : N → P} (hf' : IsAEMorphismOf G B C f') (hf : IsAEMorphismOf G A B f) :
    IsAEMorphismOf G A C (f' ∘ f) := by
  obtain ⟨U, -, hU, -, -, -, hUr⟩ := hf.exists_isRegularOn
  obtain ⟨U', V', hU', hV', hV'C, hmaps', hU'r⟩ := hf'.exists_isRegularOn
  have hS : IsPortly (U ∩ f ⁻¹' U') :=
    hU.inter_preimage_of_isLocalHomeomorphOn hUr.isLocalHomeomorphOn hU'
  refine ⟨hf'.continuous.comp hf.continuous, U ∩ f ⁻¹' U', V', hS, hV', hV'C,
    fun x hx => hmaps' hx.2, ⟨hS.isOpen, fun x hx => hUr.subset_support hx.1,
      fun x hx => hU'r.mapsTo hx.2, (hf'.continuous.comp hf.continuous).continuousOn,
      fun x hx e he e'' he'' hxe hfxe'' => ?_⟩⟩
  obtain ⟨e', he', hfxe'⟩ := mem_support.1 (hU'r.subset_support hx.2)
  obtain ⟨g, hg⟩ := hUr.exists_smul_eq x hx.1 e he e' he' hxe hfxe'
  obtain ⟨h, hh⟩ := hU'r.exists_smul_eq (f x) hx.2 e' he' e'' he'' hfxe' hfxe''
  refine ⟨h * g, ?_⟩
  filter_upwards [hf.continuous.continuousAt.eventually hh, hg] with y h1 h2
  simp only [Function.comp_apply]
  rw [h1, h2, mul_smul]

omit [ContinuousConstSMul G X] in
/-- **`rem:morphisms_analytical_two_equal`** (`RamcovGX.tex:491`), with `M` connected and the
open set nonempty: two a.e. `(G,X)`-morphisms into a Hausdorff space which agree on a nonempty
open set agree everywhere. Both added hypotheses are necessary (`analytic_counterexample_empty`,
`analytic_counterexample_disconnected`). -/
theorem IsAEMorphismOf.eq_of_eqOn [IsRigidAction G X] [PreconnectedSpace M] [T2Space N]
    {A : Set (OpenPartialHomeomorph M X)} {B : Set (OpenPartialHomeomorph N X)} {f₁ f₂ : M → N}
    (hf₁ : IsAEMorphismOf G A B f₁) (hf₂ : IsAEMorphismOf G A B f₂) {W : Set M} (hW : IsOpen W)
    (hne : W.Nonempty) (heq : EqOn f₁ f₂ W) : f₁ = f₂ := by
  obtain ⟨U₁, -, hU₁, -, -, -, h₁⟩ := hf₁.exists_isRegularOn
  obtain ⟨U₂, -, hU₂, -, -, -, h₂⟩ := hf₂.exists_isRegularOn
  set R := U₁ ∩ U₂
  have hR : IsPortly R := hU₁.inter hU₂
  have hr₁ := h₁.mono (inter_subset_left : R ⊆ U₁) hR.isOpen
  have hr₂ := h₂.mono (inter_subset_right : R ⊆ U₂) hR.isOpen
  set T := interior {x | f₁ x = f₂ x}
  have hTo : IsOpen T := isOpen_interior
  have hWT : W ⊆ T := interior_maximal (fun x hx => heq hx) hW
  have hclosed : IsClosed {x | f₁ x = f₂ x} := isClosed_eq hf₁.continuous hf₂.continuous
  have hkey : R ∩ closure T ⊆ T := by
    rintro x ⟨hxR, hxT⟩
    have hfx : f₁ x = f₂ x := hclosed.closure_subset (closure_mono interior_subset hxT)
    obtain ⟨e, he, hxe⟩ := mem_support.1 (hr₁.subset_support hxR)
    obtain ⟨e', he', hfxe'⟩ := mem_support.1 (hr₁.mapsTo hxR)
    have hfxe'₂ : f₂ x ∈ e'.source := hfx ▸ hfxe'
    obtain ⟨g₁, hg₁⟩ := hr₁.exists_smul_eq x hxR e he e' he' hxe hfxe'
    obtain ⟨g₂, hg₂⟩ := hr₂.exists_smul_eq x hxR e he e' he' hxe hfxe'₂
    have hev : ∀ᶠ y in 𝓝 x, (e' (f₁ y) = g₁ • e y ∧ e' (f₂ y) = g₂ • e y) ∧ y ∈ e.source ∧
        f₁ y ∈ e'.source ∧ f₂ y ∈ e'.source := by
      filter_upwards [hg₁, hg₂, e.open_source.mem_nhds hxe,
        hf₁.continuous.continuousAt.eventually (e'.open_source.mem_nhds hfxe'),
        hf₂.continuous.continuousAt.eventually (e'.open_source.mem_nhds hfxe'₂)]
        with y a b c d k
      exact ⟨⟨a, b⟩, c, d, k⟩
    obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 hev
    obtain ⟨z, hzt, hzT⟩ := mem_closure_iff.1 hxT t hto hxt
    have hsmul : ∀ q : X, g₁ • q = g₂ • q := by
      refine IsRigidAction.smul_eq_of_eqOn (e.isOpen_image_of_subset_source (hto.inter hTo)
        fun y hy => (ht hy.1).2.1) ⟨e z, mem_image_of_mem _ ⟨hzt, hzT⟩⟩ ?_
      rintro _ ⟨y, ⟨hyt, hyT⟩, rfl⟩
      have hy : f₁ y = f₂ y := interior_subset (s := {x | f₁ x = f₂ x}) hyT
      show g₁ • e y = g₂ • e y
      rw [← (ht hyt).1.1, ← (ht hyt).1.2, hy]
    have hts : t ⊆ {x | f₁ x = f₂ x} := fun y hy => by
      obtain ⟨⟨h1, h2⟩, -, h3, h4⟩ := ht hy
      exact e'.injOn h3 h4 (by rw [h1, h2, hsmul])
    exact mem_interior.2 ⟨t, hts, hto, hxt⟩
  have hRT : R ⊆ T := by
    rcases isPreconnected_iff_subset_of_disjoint.1 hR.isPreconnected T (closure T)ᶜ hTo
      isClosed_closure.isOpen_compl (fun x hx => by
        by_cases h : x ∈ closure T
        · exact Or.inl (hkey ⟨hx, h⟩)
        · exact Or.inr h)
      (by
        rw [← subset_empty_iff]
        rintro x ⟨-, hxT, hxc⟩
        exact hxc (subset_closure hxT)) with h | h
    · exact h
    · exfalso
      obtain ⟨x, hxW, hxR⟩ := hR.dense.inter_open_nonempty W hW hne
      exact h hxR (subset_closure (hWT hxW))
  exact Continuous.ext_on hR.dense hf₁.continuous hf₂.continuous fun x hx =>
    interior_subset (s := {x | f₁ x = f₂ x}) (hRT hx)

variable (G) in
/-- `f` restricted to the open set `W` is an a.e. `(G,X)`-morphism, for the a.e. structure `A`
induced on `W`: some `U ⊆ W`, portly in `W`, on which `f` induces a `(G,X)`-morphism (the
target portly set being `supp B` without loss of generality, `isAEMorphismOf_iff`). -/
def IsAEMorphismOn (A : Set (OpenPartialHomeomorph M X)) (B : Set (OpenPartialHomeomorph N X))
    (f : M → N) (W : Set M) : Prop :=
  ∃ U ⊆ W, IsPortly (((↑) : W → M) ⁻¹' U) ∧ IsRegularOn G A B f U

omit [ContinuousConstSMul G X] in
/-- **`prop:GX_sing_morph_local`** (`RamcovGX.tex:497`): for a continuous map between spaces
with a.e. `(G,X)`-atlases, the source locally connected, the following are equivalent:
(i) `f` is an a.e. `(G,X)`-morphism; (ii) `f` is locally an a.e. `(G,X)`-morphism; (iii) the
restriction of `f` to some portly set is an a.e. `(G,X)`-morphism. -/
theorem isAEMorphismOf_tfae [LocallyConnectedSpace M] {A : Set (OpenPartialHomeomorph M X)}
    {B : Set (OpenPartialHomeomorph N X)} (hB : IsAEAtlas G B) {f : M → N} (hf : Continuous f) :
    List.TFAE [IsAEMorphismOf G A B f,
      ∀ x : M, ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ IsAEMorphismOn G A B f W,
      ∃ U : Set M, IsPortly U ∧ IsAEMorphismOn G A B f U] := by
  tfae_have 1 → 2 := by
    intro h x
    obtain ⟨-, U, hU, hr⟩ := (isAEMorphismOf_iff hB).1 h
    exact ⟨univ, isOpen_univ, mem_univ x, U, subset_univ U, hU.subtype (subset_univ U), hr⟩
  tfae_have 1 → 3 := by
    intro h
    obtain ⟨-, U, hU, hr⟩ := (isAEMorphismOf_iff hB).1 h
    exact ⟨univ, isPortly_univ, U, subset_univ U, hU.subtype (subset_univ U), hr⟩
  tfae_have 3 → 1 := by
    rintro ⟨W, hW, U, hUW, hU, hr⟩
    exact (isAEMorphismOf_iff hB).2 ⟨hf, U, hU.of_subtype hUW hW, hr⟩
  tfae_have 2 → 1 := by
    intro h
    choose W hWo hxW U hUW hU hr using h
    have hcover : (⋃ x, W x) = univ := iUnion_eq_univ_iff.2 fun x => ⟨x, hxW x⟩
    have h1 := isPortly_iUnion_of_local hWo hUW hU
    have hWp : IsPortly (⋃ x, W x) := by rw [hcover]; exact isPortly_univ
    exact (isAEMorphismOf_iff hB).2 ⟨hf, ⋃ x, U x, h1.of_subtype (iUnion_mono hUW) hWp,
      isRegularOn_iUnion hr⟩
  tfae_finish

/-! ### `lem:aepullback` -/

/-- `f : M → N` is *almost everywhere a local homeomorphism* into the regular locus of `B`
(`RamcovGX.tex:545`, read from its proof): there are portly `O ⊆ M` and `P ⊆ supp B` with
`f(O) ⊆ P` and `f` a local homeomorphism on `O`. -/
def IsAELocalHomeomorph (B : Set (OpenPartialHomeomorph N X)) (f : M → N) : Prop :=
  ∃ O : Set M, ∃ P : Set N, IsPortly O ∧ IsPortly P ∧ P ⊆ support B ∧ MapsTo f O P ∧
    IsLocalHomeomorphOn f O

/-- **Uniqueness in `lem:aepullback`**: two maximal a.e. `(G,X)`-atlases on `M` for which `f` is
an a.e. `(G,X)`-morphism into `B` are equal. -/
theorem IsAEMorphismOf.eq_of_isMaximalAEAtlas [LocallyConnectedSpace X] [T2Space X]
    [IsRigidAction G X] {A₁ A₂ : Set (OpenPartialHomeomorph M X)}
    {B : Set (OpenPartialHomeomorph N X)} (h₁ : IsMaximalAEAtlas G A₁)
    (h₂ : IsMaximalAEAtlas G A₂) {f : M → N} (hf₁ : IsAEMorphismOf G A₁ B f)
    (hf₂ : IsAEMorphismOf G A₂ B f) : A₁ = A₂ := by
  obtain ⟨U₁, -, hU₁, -, -, -, hr₁⟩ := hf₁.exists_isRegularOn
  obtain ⟨U₂, -, hU₂, -, -, -, hr₂⟩ := hf₂.exists_isRegularOn
  have hU : IsPortly (U₁ ∩ U₂) := hU₁.inter hU₂
  set C := {e ∈ A₁ | e.source ⊆ U₁ ∩ U₂}
  have hCs : support C = U₁ ∩ U₂ := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
    · obtain ⟨e, he, hxe⟩ := mem_support.1 hx
      exact he.2 hxe
    · obtain ⟨e, he, hxe⟩ := mem_support.1 (hr₁.subset_support hx.1)
      exact mem_support.2 ⟨e.restrOpen _ hU.isOpen, ⟨h₁.restrOpen_mem he hU.isOpen,
        inter_subset_right⟩, ⟨hxe, hx⟩⟩
  have hC : IsAEAtlas G C := ⟨h₁.1.1.mono (sep_subset _ _), by rw [hCs]; exact hU⟩
  have hC₁ : AELe G C A₁ := h₁.1.1.isThinner_completion_of_subset (sep_subset _ _)
  have hC₂ : AELe G C A₂ := by
    refine ⟨by rw [support_completion, hCs]; exact inter_subset_right.trans hr₂.subset_support,
      fun p hp a' ha' hpa' => ?_⟩
    rw [support_completion, hCs] at hp
    obtain ⟨e₀, he₀, hpe₀⟩ := mem_support.1 (hr₁.subset_support hp.1)
    obtain ⟨c, hc, hfpc⟩ := mem_support.1 (hr₁.mapsTo hp.1)
    obtain ⟨g, hg⟩ := hr₁.exists_smul_eq p hp.1 e₀ he₀ c hc hpe₀ hfpc
    obtain ⟨h, hh⟩ := hr₂.exists_smul_eq p hp.2 a' ha' c hc hpa' hfpc
    have hev : ∀ᶠ y in 𝓝 p, e₀ y = (g⁻¹ * h) • a' y ∧ y ∈ U₁ ∩ U₂ ∧ y ∈ a'.source := by
      filter_upwards [hg, hh, hU.isOpen.mem_nhds hp, a'.open_source.mem_nhds hpa']
        with y h1 h2 h3 h4
      refine ⟨?_, h3, h4⟩
      rw [mul_smul, ← h2, h1, inv_smul_smul]
    obtain ⟨O, hO, hOo, hpO⟩ := mem_nhds_iff.1 hev
    refine ⟨g⁻¹ * h, e₀.restrOpen O hOo, subset_completion C
      ⟨h₁.restrOpen_mem he₀ hOo, fun y hy => (hO hy.2).2.1⟩, ⟨hpe₀, hpO⟩,
      fun y hy => (hO hy.2).2.2, fun y hy => (hO hy.2).1⟩
  rw [← h₁.maximalAEAtlas_eq, ← h₂.maximalAEAtlas_eq, ← maximalAEAtlas_eq_of_aeLe hC h₁.1 hC₁,
    ← maximalAEAtlas_eq_of_aeLe hC h₂.1 hC₂]

/-- **`lem:aepullback`** (`RamcovGX.tex:541`): if `f : M → N` is continuous and almost everywhere
a local homeomorphism into the regular locus of an a.e. `(G,X)`-atlas `B`, there is a unique
maximal a.e. `(G,X)`-atlas on `M` for which `f` is an a.e. `(G,X)`-morphism. The paper's `M`
locally connected Hausdorff, and the maximality of `B`, are not used. -/
theorem existsUnique_aePullback [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {B : Set (OpenPartialHomeomorph N X)} (hB : IsAEAtlas G B) {f : M → N} (hf : Continuous f)
    (hloc : IsAELocalHomeomorph B f) :
    ∃! A : Set (OpenPartialHomeomorph M X), IsMaximalAEAtlas G A ∧ IsAEMorphismOf G A B f := by
  obtain ⟨O, P, hO, hP, hPB, hOP, hOl⟩ := hloc
  set A₀ : Set (OpenPartialHomeomorph M X) := {e | e.source ⊆ O ∧ ∀ x ∈ e.source, ∃ c ∈ B,
    f x ∈ c.source ∧ ∃ g : G, ∀ᶠ y in 𝓝 x, c (f y) = g • e y}
  have hA₀GX : IsGXAtlas G A₀ := by
    refine isGXAtlas_of_eventually fun e₁ he₁ e₂ he₂ x hx => ?_
    obtain ⟨c₁, hc₁, hfx₁, g₁, hg₁⟩ := he₁.2 x hx.1
    obtain ⟨c₂, hc₂, hfx₂, g₂, hg₂⟩ := he₂.2 x hx.2
    obtain ⟨k, hk⟩ := hB.1.eventually_smul_eq hc₁ hc₂ hfx₁ hfx₂
    refine ⟨g₂⁻¹ * k * g₁, ?_⟩
    filter_upwards [hf.continuousAt.eventually hk, hg₁, hg₂] with y h1 h2 h3
    rw [mul_smul, mul_smul, ← h2, ← h1, h3, inv_smul_smul]
  have hA₀s : support A₀ = O := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
    · obtain ⟨e, he, hxe⟩ := mem_support.1 hx
      exact he.1 hxe
    · obtain ⟨φ, hxφ, hfφ⟩ := hOl x hx
      obtain ⟨c, hc, hfxc⟩ := mem_support.1 (hPB (hOP hx))
      set e := (φ.restrOpen O hO.isOpen).trans c
      have hes : e.source = (φ.source ∩ O) ∩ φ ⁻¹' c.source := rfl
      have hecoe : ∀ y, e y = c (f y) := fun y => by rw [hfφ]; rfl
      refine mem_support.2 ⟨e, ⟨fun y hy => (hes ▸ hy).1.2, fun x' hx' => ⟨c, hc, ?_, 1,
        Eventually.of_forall fun y => by rw [one_smul, hecoe]⟩⟩, ?_⟩
      · rw [hes] at hx'; rw [hfφ]; exact hx'.2
      · rw [hes]; exact ⟨⟨hxφ, hx⟩, by rw [mem_preimage, ← hfφ]; exact hfxc⟩
  have hA₀ : IsAEAtlas G A₀ := ⟨hA₀GX, by rw [hA₀s]; exact hO⟩
  have hAmax := hA₀.isMaximalAEAtlas_maximalAEAtlas
  have hsub : A₀ ⊆ maximalAEAtlas G A₀ := hA₀.subset_maximalAEAtlas
  have hmor : IsAEMorphismOf G (maximalAEAtlas G A₀) B f := by
    refine ⟨hf, O, P, hO, hP, hPB, hOP, IsRegularOn.of_exists hAmax.1.1 hB.1 hO.isOpen
      (hA₀s ▸ support_mono hsub) (hOP.mono_right hPB) hf.continuousOn fun x hx => ?_⟩
    rw [← hA₀s] at hx
    obtain ⟨e, he, hxe⟩ := mem_support.1 hx
    obtain ⟨c, hc, hfxc, g, hg⟩ := he.2 x hxe
    exact ⟨e, hsub he, c, hc, hxe, hfxc, g, hg⟩
  exact ⟨_, ⟨hAmax, hmor⟩, fun A' hA' => IsAEMorphismOf.eq_of_isMaximalAEAtlas hA'.1 hAmax hA'.2
    hmor⟩

end Morphism

/-! ### The pullback `f^*B`, and maps which are local homeomorphisms -/

section PullbackAE

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {L : Type*} [TopologicalSpace L] {M : Type u} [TopologicalSpace M]
  {N : Type y} [TopologicalSpace N]

open Classical in
variable (G) in
/-- **`def:notations_lemma_lem_aepullback`** (`RamcovGX.tex:554`): the pullback `f^*B`, the
unique maximal a.e. `(G,X)`-atlas on `M` making `f` an a.e. `(G,X)`-morphism into `B` when one
exists (`lem:aepullback`), and `∅` otherwise. -/
noncomputable def aePullback (B : Set (OpenPartialHomeomorph N X)) (f : M → N) :
    Set (OpenPartialHomeomorph M X) :=
  if h : ∃ A : Set (OpenPartialHomeomorph M X), IsMaximalAEAtlas G A ∧ IsAEMorphismOf G A B f
  then h.choose else ∅

omit [ContinuousConstSMul G X] in
theorem aePullback_spec {B : Set (OpenPartialHomeomorph N X)} {f : M → N}
    (h : ∃ A : Set (OpenPartialHomeomorph M X), IsMaximalAEAtlas G A ∧ IsAEMorphismOf G A B f) :
    IsMaximalAEAtlas G (aePullback G B f) ∧ IsAEMorphismOf G (aePullback G B f) B f := by
  rw [aePullback, dif_pos h]; exact h.choose_spec

/-- Every maximal a.e. `(G,X)`-atlas making `f` an a.e. morphism is the pullback. -/
theorem eq_aePullback [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {A : Set (OpenPartialHomeomorph M X)} {B : Set (OpenPartialHomeomorph N X)} {f : M → N}
    (hA : IsMaximalAEAtlas G A) (hf : IsAEMorphismOf G A B f) : A = aePullback G B f :=
  have h := aePullback_spec ⟨A, hA, hf⟩
  hf.eq_of_isMaximalAEAtlas hA h.1 h.2

/-- The pullback along an a.e. local homeomorphism is maximal and makes `f` an a.e. morphism. -/
theorem aePullback_spec_of_isAELocalHomeomorph [LocallyConnectedSpace X] [T2Space X]
    [IsRigidAction G X] {B : Set (OpenPartialHomeomorph N X)} (hB : IsAEAtlas G B) {f : M → N}
    (hf : Continuous f) (hloc : IsAELocalHomeomorph B f) :
    IsMaximalAEAtlas G (aePullback G B f) ∧ IsAEMorphismOf G (aePullback G B f) B f :=
  aePullback_spec (existsUnique_aePullback hB hf hloc).exists

/-- **`cor:locally_connected_hausdorff_topological`** (`RamcovGX.tex:558`): `f^* g^* B =
(g ∘ f)^* B`, for `g` and `f` continuous and almost everywhere local homeomorphisms (into the
regular loci of `B` and of `g^* B` respectively — the hypotheses under which the two pullbacks
are defined), `L` locally connected. -/
theorem aePullback_comp [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    [LocallyConnectedSpace L] {B : Set (OpenPartialHomeomorph N X)} (hB : IsAEAtlas G B)
    {g : M → N} (hg : Continuous g) (hgl : IsAELocalHomeomorph B g) {f : L → M}
    (hf : Continuous f) (hfl : IsAELocalHomeomorph (aePullback G B g) f) :
    aePullback G (aePullback G B g) f = aePullback G B (g ∘ f) := by
  have hM := aePullback_spec_of_isAELocalHomeomorph hB hg hgl
  have hL := aePullback_spec_of_isAELocalHomeomorph hM.1.1 hf hfl
  exact eq_aePullback hL.1 (hM.2.comp hL.2)

/-- An a.e. `(G,X)`-morphism which is a local homeomorphism at a regular point `x` sends it to a
regular point (the core of `lem:GX_sing_homeo_reg`). -/
theorem IsAEMorphismOf.mem_support_of_isLocalHomeomorphOn [LocallyConnectedSpace X] [T2Space X]
    [IsRigidAction G X] {A : Set (OpenPartialHomeomorph M X)} {B : Set (OpenPartialHomeomorph N X)}
    (hA : IsAEAtlas G A) (hB : IsMaximalAEAtlas G B) {f : M → N} (hf : IsAEMorphismOf G A B f)
    {x : M} (hxA : x ∈ support A) (hx : IsLocalHomeomorphOn f {x}) : f x ∈ support B := by
  obtain ⟨h, hxh, hfh⟩ := hx x rfl
  obtain ⟨e, he, hxe⟩ := mem_support.1 hxA
  have hreg := hf.regLocusOf_eq hA hB.1
  set ψ := h.symm.trans e
  have hψs : ψ.source = h.target ∩ h.symm ⁻¹' e.source := rfl
  have hψ : ψ ∈ B := by
    refine hB.mem_of_compatible fun c hc y hy => ?_
    rw [hψs] at hy
    set w := h.symm y
    have hfw : f w = y := by rw [hfh]; exact h.right_inv hy.1.1
    have hwR : w ∈ regLocusOf G A B f := by
      rw [hreg]
      exact ⟨mem_support.2 ⟨e, he, hy.1.2⟩, by rw [mem_preimage, hfw]; exact mem_support.2 ⟨c, hc, hy.2⟩⟩
    obtain ⟨g, hg⟩ := (isRegularOn_regLocusOf (G := G) A B f).exists_smul_eq w hwR e he c hc
      hy.1.2 (by rw [hfw]; exact hy.2)
    refine ⟨g, ?_⟩
    filter_upwards [(h.continuousAt_symm hy.1.1).eventually hg,
      h.eventually_right_inverse hy.1.1] with z hz1 hz2
    rw [hfh, hz2] at hz1
    exact hz1
  refine mem_support.2 ⟨ψ, hψ, ?_⟩
  rw [hψs]
  refine ⟨?_, ?_⟩
  · rw [hfh]; exact h.map_source hxh
  · rw [mem_preimage, hfh, h.left_inv hxh]; exact hxe

/-- Conversely, a point at which an a.e. `(G,X)`-morphism is a local homeomorphism onto a
regular point is regular. -/
theorem IsAEMorphismOf.mem_support_of_isLocalHomeomorphOn' [LocallyConnectedSpace X] [T2Space X]
    [IsRigidAction G X] {A : Set (OpenPartialHomeomorph M X)} {B : Set (OpenPartialHomeomorph N X)}
    (hA : IsMaximalAEAtlas G A) (hB : IsAEAtlas G B) {f : M → N} (hf : IsAEMorphismOf G A B f)
    {x : M} (hxB : f x ∈ support B) (hx : IsLocalHomeomorphOn f {x}) : x ∈ support A := by
  obtain ⟨h, hxh, hfh⟩ := hx x rfl
  obtain ⟨c, hc, hfxc⟩ := mem_support.1 hxB
  have hreg := hf.regLocusOf_eq hA.1 hB
  set φ := h.trans c
  have hφs : φ.source = h.source ∩ h ⁻¹' c.source := rfl
  have hφ : φ ∈ A := by
    refine hA.mem_of_compatible fun a ha y hy => ?_
    rw [hφs] at hy
    have hfy : f y ∈ c.source := by rw [hfh]; exact hy.1.2
    have hyR : y ∈ regLocusOf G A B f := by
      rw [hreg]; exact ⟨mem_support.2 ⟨a, ha, hy.2⟩, mem_support.2 ⟨c, hc, hfy⟩⟩
    obtain ⟨g, hg⟩ := (isRegularOn_regLocusOf (G := G) A B f).exists_smul_eq y hyR a ha c hc
      hy.2 hfy
    refine ⟨g⁻¹, ?_⟩
    filter_upwards [hg] with z hz
    show a z = g⁻¹ • c (h z)
    rw [← hfh, hz, inv_smul_smul]
  exact mem_support.2 ⟨φ, hφ, by
    rw [hφs]; exact ⟨hxh, by show h x ∈ c.source; rw [← hfh]; exact hfxc⟩⟩

/-- **`lem:GX_sing_homeo_reg`** (`RamcovGX.tex:592`): the regular locus of an a.e.
`(G,X)`-morphism into a singular `(G,X)`-manifold is the set of regular points of the source at
which it is a local homeomorphism. -/
theorem IsAEMorphismOf.regLocusOf_eq_inter_isLocalHomeomorphOn [LocallyConnectedSpace X]
    [T2Space X] [IsRigidAction G X] {A : Set (OpenPartialHomeomorph M X)}
    {B : Set (OpenPartialHomeomorph N X)} (hA : IsAEAtlas G A) (hB : IsMaximalAEAtlas G B)
    {f : M → N} (hf : IsAEMorphismOf G A B f) :
    regLocusOf G A B f = support A ∩ {x | IsLocalHomeomorphOn f {x}} := by
  refine Subset.antisymm (fun x hx => ⟨(regLocusOf_subset A B f hx).1, ?_⟩) fun x hx => ?_
  · exact (isRegularOn_regLocusOf (G := G) A B f).isLocalHomeomorphOn.mono
      (singleton_subset_iff.2 hx)
  · rw [hf.regLocusOf_eq hA hB.1]
    exact ⟨hx.1, hf.mem_support_of_isLocalHomeomorphOn hA hB hx.1 hx.2⟩

/-- **`cor:morphisms_also_local_homemorphism`** (`RamcovGX.tex:603`): an a.e. `(G,X)`-morphism
between singular `(G,X)`-manifolds which is a local homeomorphism preserves the regular and the
singular loci: `f⁻¹(Reg N) = Reg M` and `f⁻¹(Sing N) = Sing M`. -/
theorem IsAEMorphismOf.preimage_support_eq [LocallyConnectedSpace X] [T2Space X]
    [IsRigidAction G X] {A : Set (OpenPartialHomeomorph M X)} {B : Set (OpenPartialHomeomorph N X)}
    (hA : IsMaximalAEAtlas G A) (hB : IsMaximalAEAtlas G B) {f : M → N}
    (hf : IsAEMorphismOf G A B f) (hloc : IsLocalHomeomorph f) :
    f ⁻¹' support B = support A ∧ f ⁻¹' (support B)ᶜ = (support A)ᶜ := by
  have heq : f ⁻¹' support B = support A := by
    ext x
    have hx : IsLocalHomeomorphOn f {x} := hloc.isLocalHomeomorphOn
    exact ⟨fun h => hf.mem_support_of_isLocalHomeomorphOn' hA hB.1 h hx,
      fun h => hf.mem_support_of_isLocalHomeomorphOn hA.1 hB h hx⟩
  exact ⟨heq, by rw [preimage_compl, heq]⟩

/-- **`rem:consequence_isomorphism_singular_manifolds`** (`RamcovGX.tex:606`): for a
homeomorphism `φ` which is an a.e. `(G,X)`-morphism between singular `(G,X)`-manifolds, the
maximal a.e. atlas of the source is exactly the transport of that of the target: `e ∈ A` iff
`e ∘ φ⁻¹ ∈ B`; equivalently `A = φ^* B`. -/
theorem IsAEMorphismOf.mem_iff_of_homeomorph [LocallyConnectedSpace X] [T2Space X]
    [IsRigidAction G X] {A : Set (OpenPartialHomeomorph M X)} {B : Set (OpenPartialHomeomorph N X)}
    (hA : IsMaximalAEAtlas G A) (hB : IsMaximalAEAtlas G B) {φ : M ≃ₜ N}
    (hf : IsAEMorphismOf G A B φ) (e : OpenPartialHomeomorph M X) :
    e ∈ A ↔ φ.symm.toOpenPartialHomeomorph.trans e ∈ B := by
  have hreg := hf.regLocusOf_eq hA.1 hB.1
  have hRreg := isRegularOn_regLocusOf (G := G) A B φ
  constructor
  · intro he
    refine hB.mem_of_compatible fun c hc y hy => ?_
    have hy1 : φ.symm y ∈ e.source := hy.1.2
    have hwR : φ.symm y ∈ regLocusOf G A B φ := by
      rw [hreg]
      exact ⟨mem_support.2 ⟨e, he, hy1⟩, by
        rw [mem_preimage, φ.apply_symm_apply]; exact mem_support.2 ⟨c, hc, hy.2⟩⟩
    obtain ⟨g, hg⟩ := hRreg.exists_smul_eq _ hwR e he c hc hy1
      (by rw [φ.apply_symm_apply]; exact hy.2)
    refine ⟨g, ?_⟩
    filter_upwards [φ.symm.continuous.continuousAt.eventually hg] with z hz
    rw [φ.apply_symm_apply] at hz
    exact hz
  · intro hψ
    refine hA.mem_of_compatible fun a ha y hy => ?_
    have hyψ : φ y ∈ (φ.symm.toOpenPartialHomeomorph.trans e).source :=
      ⟨mem_univ _, by show φ.symm (φ y) ∈ e.source; rw [φ.symm_apply_apply]; exact hy.1⟩
    have hyR : y ∈ regLocusOf G A B φ := by
      rw [hreg]; exact ⟨mem_support.2 ⟨a, ha, hy.2⟩, mem_support.2 ⟨_, hψ, hyψ⟩⟩
    obtain ⟨g, hg⟩ := hRreg.exists_smul_eq y hyR a ha _ hψ hy.2 hyψ
    refine ⟨g⁻¹, ?_⟩
    filter_upwards [hg] with z hz
    have : (φ.symm.toOpenPartialHomeomorph.trans e) (φ z) = e z := by
      show e (φ.symm (φ z)) = e z
      rw [φ.symm_apply_apply]
    rw [this] at hz
    rw [hz, inv_smul_smul]

/-- `rem:consequence_isomorphism_singular_manifolds`: `A = φ^* B`. -/
theorem IsAEMorphismOf.eq_aePullback_of_homeomorph [LocallyConnectedSpace X] [T2Space X]
    [IsRigidAction G X] {A : Set (OpenPartialHomeomorph M X)} {B : Set (OpenPartialHomeomorph N X)}
    (hA : IsMaximalAEAtlas G A) {φ : M ≃ₜ N} (hf : IsAEMorphismOf G A B φ) :
    A = aePullback G B φ :=
  eq_aePullback hA hf

/-- `rem:composition_morphisms_morphisms_category`, last sentence: the inverse of a homeomorphism
which is an a.e. `(G,X)`-morphism is an a.e. `(G,X)`-morphism, so the isomorphisms of the
category are the homeomorphisms which are a.e. `(G,X)`-morphisms. -/
theorem IsAEMorphismOf.symm_of_homeomorph [LocallyConnectedSpace X] [T2Space X]
    [IsRigidAction G X] {A : Set (OpenPartialHomeomorph M X)} {B : Set (OpenPartialHomeomorph N X)}
    (hA : IsMaximalAEAtlas G A) (hB : IsMaximalAEAtlas G B) {φ : M ≃ₜ N}
    (hf : IsAEMorphismOf G A B φ) : IsAEMorphismOf G B A φ.symm := by
  have hpre := (hf.preimage_support_eq hA hB φ.isLocalHomeomorph).1
  have hmaps : MapsTo φ.symm (support B) (support A) := fun y hy => by
    rw [← hpre, mem_preimage, φ.apply_symm_apply]; exact hy
  refine (isAEMorphismOf_iff hA.1).2 ⟨φ.symm.continuous, support B, hB.1.2,
    IsRegularOn.of_exists hB.1.1 hA.1.1 (isOpen_support B) subset_rfl hmaps
      φ.symm.continuous.continuousOn fun y hy => ?_⟩
  obtain ⟨c, hc, hyc⟩ := mem_support.1 hy
  obtain ⟨e, he, hye⟩ := mem_support.1 (hmaps hy)
  have hψ := (hf.mem_iff_of_homeomorph hA hB e).1 he
  have hyψ : y ∈ (φ.symm.toOpenPartialHomeomorph.trans e).source := ⟨mem_univ _, hye⟩
  obtain ⟨g, hg⟩ := hB.1.1.eventually_smul_eq hc hψ hyc hyψ
  exact ⟨c, hc, e, he, hyc, hye, g, hg⟩

end PullbackAE

/-! ### `rem:though_may_tempted_include`: branched maps are not a.e. morphisms -/

section Branched

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X]

/-- `z ↦ z^p` is injective on no neighbourhood of `0` unless `p = 1`. -/
theorem not_injOn_pow_of_mem_nhds {p : ℕ} (hp : p ≠ 1) {t : Set ℂ} (ht : t ∈ 𝓝 (0 : ℂ)) :
    ¬ InjOn (fun z : ℂ => z ^ p) t := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ht
  intro hinj
  set r : ℂ := ((ε / 2 : ℝ) : ℂ)
  have hr0 : r ≠ 0 := by
    simp only [r, ne_eq, Complex.ofReal_eq_zero]; positivity
  have hrnorm : ‖r‖ = ε / 2 := by
    simp only [r, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
  have hrt : r ∈ t := hball (by rw [Metric.mem_ball, dist_zero_right, hrnorm]; linarith)
  rcases Nat.lt_or_ge p 2 with hp2 | hp2
  · have hp0 : p = 0 := by omega
    subst hp0
    have h0t : (0 : ℂ) ∈ t := hball (Metric.mem_ball_self hε)
    exact hr0 (hinj hrt h0t (by simp))
  · have hζ := Complex.isPrimitiveRoot_exp p (by omega)
    set ζ := Complex.exp (2 * Real.pi * Complex.I / p)
    have hζn : ‖ζ‖ = 1 := hζ.norm'_eq_one (by omega)
    have hrζ : r * ζ ∈ t := hball (by
      rw [Metric.mem_ball, dist_zero_right, norm_mul, hζn, mul_one, hrnorm]; linarith)
    have := hinj hrt hrζ (by simp only [mul_pow, hζ.pow_eq_one, mul_one])
    exact hζ.ne_one (by omega) (mul_left_cancel₀ hr0 (by rw [mul_one]; exact this.symm))

/-- **`rem:though_may_tempted_include`** (`RamcovGX.tex:538`): `0 ∉ Reg(z ↦ z^p)` unless
`p = 1`, whatever the a.e. `(G,X)`-atlases on `ℂ`. -/
theorem zero_notMem_regLocusOf_pow (A B : Set (OpenPartialHomeomorph ℂ X)) {p : ℕ} (hp : p ≠ 1) :
    (0 : ℂ) ∉ regLocusOf G A B (fun z : ℂ => z ^ p) := by
  intro h0
  obtain ⟨e, he0, hfe⟩ := (isRegularOn_regLocusOf (G := G) A B _).isLocalHomeomorphOn 0 h0
  exact not_injOn_pow_of_mem_nhds hp (e.open_source.mem_nhds he0) (hfe ▸ e.injOn)

/-- `rem:though_may_tempted_include`, with `lem:regf1`: for `p ≠ 1`, `z ↦ z^p` is an a.e.
`(G,X)`-morphism for no a.e. `(G,X)`-structures on `ℂ` regular at `0` and at `0^p`. In
particular no `(G,X)`-structure on `ℂ` (empty singular locus) makes a branched map
`z ↦ z^p`, `p ≥ 2`, an a.e. morphism. -/
theorem not_isAEMorphismOf_pow [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {A B : Set (OpenPartialHomeomorph ℂ X)} (hA : IsAEAtlas G A) (hB : IsAEAtlas G B) {p : ℕ}
    (hp : p ≠ 1) (h0A : (0 : ℂ) ∈ support A) (h0B : (0 : ℂ) ^ p ∈ support B) :
    ¬ IsAEMorphismOf G A B (fun z : ℂ => z ^ p) := fun hf =>
  zero_notMem_regLocusOf_pow A B hp (by rw [hf.regLocusOf_eq hA hB]; exact ⟨h0A, h0B⟩)

end Branched

/-! ### Regular `(G,X)`-manifolds are singular `(G,X)`-manifolds -/

section Regular

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M] {N : Type y} [TopologicalSpace N]
  [ChartedSpace X M] [HasGroupoid M (gxGroupoid G X)] [ChartedSpace X N]
  [HasGroupoid N (gxGroupoid G X)]

theorem support_maximalAtlas : support ((gxGroupoid G X).maximalAtlas M) = univ :=
  eq_univ_of_forall fun x => mem_support.2
    ⟨chartAt X x, (gxGroupoid G X).chart_mem_maximalAtlas x, mem_chart_source X x⟩

/-- **A `(G,X)`-manifold is a singular `(G,X)`-manifold with empty singular locus**: its maximal
atlas is a maximal a.e. `(G,X)`-atlas. -/
theorem isMaximalAEAtlas_maximalAtlas [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X] :
    IsMaximalAEAtlas G ((gxGroupoid G X).maximalAtlas M) := by
  have hA : IsAEAtlas G ((gxGroupoid G X).maximalAtlas M) :=
    ⟨isGXAtlas_maximalAtlas, by rw [support_maximalAtlas]; exact isPortly_univ⟩
  refine ⟨hA, fun B hB hAB e he => mem_maximalAtlas_iff_eventually.2 fun x hx => ?_⟩
  have hm := hA.maximalAEAtlas
  exact hm.1.eventually_smul_eq
    (hA.subset_maximalAEAtlas ((gxGroupoid G X).chart_mem_maximalAtlas x))
    (subset_maximalAEAtlas hB hAB he) (mem_chart_source X x) hx

/-- Between `(G,X)`-manifolds, a.e. `(G,X)`-morphisms are exactly the `(G,X)`-morphisms. -/
theorem isAEMorphismOf_maximalAtlas_iff [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {f : M → N} : IsAEMorphismOf G ((gxGroupoid G X).maximalAtlas M)
      ((gxGroupoid G X).maximalAtlas N) f ↔ IsGXMorphism G X f := by
  have hA := (isMaximalAEAtlas_maximalAtlas (G := G) (X := X) (M := M)).1
  have hB := (isMaximalAEAtlas_maximalAtlas (G := G) (X := X) (M := N)).1
  constructor
  · intro hf
    have hR := hf.regLocusOf_eq hA hB
    rw [support_maximalAtlas, support_maximalAtlas, preimage_univ, inter_univ] at hR
    refine ⟨hf.continuous, fun x => ?_⟩
    have hx : x ∈ regLocusOf G ((gxGroupoid G X).maximalAtlas M)
        ((gxGroupoid G X).maximalAtlas N) f := by rw [hR]; exact mem_univ x
    exact (isRegularOn_regLocusOf (G := G) _ _ f).exists_smul_eq x hx _
      ((gxGroupoid G X).chart_mem_maximalAtlas x) _
      ((gxGroupoid G X).chart_mem_maximalAtlas (f x)) (mem_chart_source X x)
      (mem_chart_source X (f x))
  · intro hf
    refine (isAEMorphismOf_iff hB).2 ⟨hf.continuous, univ, isPortly_univ,
      IsRegularOn.of_exists hA.1 hB.1 isOpen_univ (by rw [support_maximalAtlas])
        (by rw [support_maximalAtlas]; exact mapsTo_univ _ _) hf.continuous.continuousOn
        fun x _ => ⟨_, (gxGroupoid G X).chart_mem_maximalAtlas x, _,
          (gxGroupoid G X).chart_mem_maximalAtlas (f x), mem_chart_source X x,
          mem_chart_source X (f x), hf.exists_smul_eq x⟩⟩

end Regular

/-! ### Singular `(G,X)`-manifolds -/

section Singular

variable (G : Type w) (X : Type v) [TopologicalSpace X] [Group G] [MulAction G X]
  (M : Type u) [TopologicalSpace M]

/-- **`def:structure_topological_space_atlas`** (`RamcovGX.tex:471`): an a.e.
`(G,X)`-structure on a topological space is an a.e. `(G,X)`-atlas on it. -/
abbrev IsAEStructure (A : Set (OpenPartialHomeomorph M X)) : Prop := IsAEAtlas G A

/-- **`def:singular_manifold_locally_connected`** (`RamcovGX.tex:474`), the structure: a maximal
a.e. `(G,X)`-atlas (DEC-25). A *singular `(G,X)`-manifold* is a locally connected Hausdorff second
countable space carrying one: `[LocallyConnectedSpace M] [T2Space M] [SecondCountableTopology M]
[SingularGXStructure G X M]`, each theorem asking for the instances it uses (`SingGXCat` bundles
all of them). -/
class SingularGXStructure where
  /-- The maximal a.e. `(G,X)`-atlas. -/
  aeAtlas : Set (OpenPartialHomeomorph M X)
  isMaximalAEAtlas_aeAtlas : IsMaximalAEAtlas G aeAtlas

/-- The maximal a.e. `(G,X)`-atlas of a singular `(G,X)`-manifold. -/
def aeAtlas [SingularGXStructure G X M] : Set (OpenPartialHomeomorph M X) :=
  SingularGXStructure.aeAtlas (G := G)

theorem isMaximalAEAtlas_aeAtlas [SingularGXStructure G X M] :
    IsMaximalAEAtlas G (aeAtlas G X M) :=
  SingularGXStructure.isMaximalAEAtlas_aeAtlas

/-- `def:singular_manifold_locally_connected`: the *regular locus* `Reg(M)`, the support of the
maximal a.e. `(G,X)`-atlas. -/
def Reg [SingularGXStructure G X M] : Set M := support (aeAtlas G X M)

/-- `def:singular_manifold_locally_connected`: the *singular locus* `Sing(M)`, the complement of
the regular locus. -/
def Sing [SingularGXStructure G X M] : Set M := (Reg G X M)ᶜ

variable [SingularGXStructure G X M]

theorem isPortly_reg : IsPortly (Reg G X M) := (isMaximalAEAtlas_aeAtlas G X M).1.2

theorem isOpen_reg : IsOpen (Reg G X M) := (isPortly_reg G X M).isOpen

/-- The singular locus is skeletal. -/
theorem isSkeletal_sing : IsSkeletal (Sing G X M) := by
  rw [Sing, isSkeletal_compl_iff]; exact isPortly_reg G X M

theorem isClosed_sing : IsClosed (Sing G X M) := (isSkeletal_sing G X M).isClosed

/-- A `(G,X)`-manifold, as a singular `(G,X)`-manifold with empty singular locus. -/
@[reducible] noncomputable def SingularGXStructure.ofHasGroupoid [ContinuousConstSMul G X]
    [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X] [ChartedSpace X M]
    [HasGroupoid M (gxGroupoid G X)] : SingularGXStructure G X M :=
  ⟨_, isMaximalAEAtlas_maximalAtlas⟩

end Singular

section SingularMorphism

variable {G : Type w} {X : Type v} [TopologicalSpace X] [Group G] [MulAction G X]
  [ContinuousConstSMul G X] {M : Type u} [TopologicalSpace M] {N : Type y} [TopologicalSpace N]
  {P : Type z} [TopologicalSpace P] [SingularGXStructure G X M] [SingularGXStructure G X N]
  [SingularGXStructure G X P]

variable (G X) in
/-- **`def:morphism`** (`RamcovGX.tex:480`): an *a.e. `(G,X)`-morphism* between singular
`(G,X)`-manifolds. -/
def IsAEMorphism (f : M → N) : Prop := IsAEMorphismOf G (aeAtlas G X M) (aeAtlas G X N) f

variable (G X) in
/-- **`def:singular_manifolds_morphism_maximal`** (`RamcovGX.tex:518`): the regular locus
`Reg(f)` of a map between singular `(G,X)`-manifolds. -/
def regLocus (f : M → N) : Set M := regLocusOf G (aeAtlas G X M) (aeAtlas G X N) f

omit [ContinuousConstSMul G X] in
/-- `lem:singular_manifolds_morphism_set` (`RamcovGX.tex:507`), for singular manifolds. -/
theorem isGreatest_regLocus (f : M → N) :
    IsGreatest {U | IsRegularOn G (aeAtlas G X M) (aeAtlas G X N) f U} (regLocus G X f) :=
  isGreatest_regLocusOf _ _ f

theorem isAEMorphism_id [LocallyConnectedSpace X] : IsAEMorphism G X (id : M → M) :=
  isAEMorphismOf_id (isMaximalAEAtlas_aeAtlas G X M).1

/-- `rem:composition_morphisms_morphisms_category`, for singular manifolds. -/
theorem IsAEMorphism.comp [LocallyConnectedSpace M] {f : M → N} {f' : N → P}
    (hf' : IsAEMorphism G X f') (hf : IsAEMorphism G X f) : IsAEMorphism G X (f' ∘ f) :=
  IsAEMorphismOf.comp hf' hf

omit [ContinuousConstSMul G X] in
/-- `rem:morphisms_analytical_two_equal`, for singular manifolds (`M` connected, `W ≠ ∅`). -/
theorem IsAEMorphism.eq_of_eqOn [IsRigidAction G X] [PreconnectedSpace M] [T2Space N]
    {f₁ f₂ : M → N} (hf₁ : IsAEMorphism G X f₁) (hf₂ : IsAEMorphism G X f₂) {W : Set M}
    (hW : IsOpen W) (hne : W.Nonempty) (heq : EqOn f₁ f₂ W) : f₁ = f₂ :=
  IsAEMorphismOf.eq_of_eqOn hf₁ hf₂ hW hne heq

/-- **`lem:regf1`** (`RamcovGX.tex:523`): `Reg(f) = Reg(M) ∩ f⁻¹(Reg(N))`. -/
theorem IsAEMorphism.regLocus_eq [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {f : M → N} (hf : IsAEMorphism G X f) : regLocus G X f = Reg G X M ∩ f ⁻¹' Reg G X N :=
  IsAEMorphismOf.regLocusOf_eq (isMaximalAEAtlas_aeAtlas G X M).1
    (isMaximalAEAtlas_aeAtlas G X N).1 hf

/-- **`lem:GX_sing_homeo_reg`** (`RamcovGX.tex:592`): `Reg(f) = Reg(M) ∩ {x | f is a local
homeomorphism around x}`. -/
theorem IsAEMorphism.regLocus_eq_inter_isLocalHomeomorphOn [LocallyConnectedSpace X] [T2Space X]
    [IsRigidAction G X] {f : M → N} (hf : IsAEMorphism G X f) :
    regLocus G X f = Reg G X M ∩ {x | IsLocalHomeomorphOn f {x}} :=
  IsAEMorphismOf.regLocusOf_eq_inter_isLocalHomeomorphOn (isMaximalAEAtlas_aeAtlas G X M).1
    (isMaximalAEAtlas_aeAtlas G X N) hf

/-- **`cor:morphisms_also_local_homemorphism`** (`RamcovGX.tex:603`): an a.e. `(G,X)`-morphism
which is a local homeomorphism preserves the regular and the singular loci. -/
theorem IsAEMorphism.preimage_reg_sing [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {f : M → N} (hf : IsAEMorphism G X f) (hloc : IsLocalHomeomorph f) :
    f ⁻¹' Reg G X N = Reg G X M ∧ f ⁻¹' Sing G X N = Sing G X M :=
  IsAEMorphismOf.preimage_support_eq (isMaximalAEAtlas_aeAtlas G X M)
    (isMaximalAEAtlas_aeAtlas G X N) hf hloc

/-- **`rem:consequence_isomorphism_singular_manifolds`** (`RamcovGX.tex:606`): an isomorphism
(a homeomorphism which is an a.e. `(G,X)`-morphism) identifies the maximal a.e. atlases —
`e ∈ A` iff `e ∘ φ⁻¹ ∈ B` — and `A = φ^* B`. -/
theorem IsAEMorphism.aeAtlas_eq_of_homeomorph [LocallyConnectedSpace X] [T2Space X]
    [IsRigidAction G X] {φ : M ≃ₜ N} (hf : IsAEMorphism G X φ) :
    (∀ e : OpenPartialHomeomorph M X,
      e ∈ aeAtlas G X M ↔ φ.symm.toOpenPartialHomeomorph.trans e ∈ aeAtlas G X N) ∧
    aeAtlas G X M = aePullback G (aeAtlas G X N) φ :=
  ⟨IsAEMorphismOf.mem_iff_of_homeomorph (isMaximalAEAtlas_aeAtlas G X M)
    (isMaximalAEAtlas_aeAtlas G X N) hf,
   IsAEMorphismOf.eq_aePullback_of_homeomorph (isMaximalAEAtlas_aeAtlas G X M) hf⟩

/-- `rem:composition_morphisms_morphisms_category`: the inverse of an isomorphism of singular
`(G,X)`-manifolds is an a.e. `(G,X)`-morphism. -/
theorem IsAEMorphism.symm_of_homeomorph [LocallyConnectedSpace X] [T2Space X] [IsRigidAction G X]
    {φ : M ≃ₜ N} (hf : IsAEMorphism G X φ) : IsAEMorphism G X φ.symm :=
  IsAEMorphismOf.symm_of_homeomorph (isMaximalAEAtlas_aeAtlas G X M)
    (isMaximalAEAtlas_aeAtlas G X N) hf

end SingularMorphism

/-! ### The category `SingGX` -/

section Category

variable (G : Type w) (X : Type v) [TopologicalSpace X] [Group G] [MulAction G X]

/-- A singular `(G,X)`-manifold, bundled (`def:singular_manifold_locally_connected`): a locally
connected Hausdorff second countable space with a maximal a.e. `(G,X)`-atlas. -/
structure SingGXCat where
  /-- The underlying type. -/
  carrier : Type u
  [topologicalSpace : TopologicalSpace carrier]
  [singularGXStructure : SingularGXStructure G X carrier]
  [locallyConnectedSpace : LocallyConnectedSpace carrier]
  [t2Space : T2Space carrier]
  [secondCountableTopology : SecondCountableTopology carrier]

attribute [instance] SingGXCat.topologicalSpace SingGXCat.singularGXStructure
  SingGXCat.locallyConnectedSpace SingGXCat.t2Space SingGXCat.secondCountableTopology

instance : CoeSort (SingGXCat.{u} G X) (Type u) := ⟨SingGXCat.carrier⟩

/-- **`rem:composition_morphisms_morphisms_category`** (`RamcovGX.tex:487`): the category of
singular `(G,X)`-manifolds and a.e. `(G,X)`-morphisms. -/
instance [ContinuousConstSMul G X] [LocallyConnectedSpace X] :
    CategoryTheory.Category (SingGXCat.{u} G X) where
  Hom M N := {f : M → N // IsAEMorphism G X f}
  id _ := ⟨id, isAEMorphism_id⟩
  comp f g := ⟨g.1 ∘ f.1, g.2.comp f.2⟩
  id_comp _ := Subtype.ext rfl
  comp_id _ := Subtype.ext rfl
  assoc _ _ _ := Subtype.ext rfl

variable {G X}

/-- `rem:composition_morphisms_morphisms_category`: a homeomorphism which is an a.e.
`(G,X)`-morphism is an isomorphism of `SingGX`. -/
noncomputable def SingGXCat.isoOfHomeomorph [ContinuousConstSMul G X] [LocallyConnectedSpace X]
    [T2Space X] [IsRigidAction G X] {M N : SingGXCat.{u} G X} (φ : M ≃ₜ N)
    (hφ : IsAEMorphism G X φ) : M ≅ N where
  hom := ⟨φ, hφ⟩
  inv := ⟨φ.symm, hφ.symm_of_homeomorph⟩
  hom_inv_id := Subtype.ext (funext φ.symm_apply_apply)
  inv_hom_id := Subtype.ext (funext φ.apply_symm_apply)

/-- Conversely, an isomorphism of `SingGX` is a homeomorphism (whose forward map is an a.e.
`(G,X)`-morphism by definition). -/
def SingGXCat.homeomorphOfIso [ContinuousConstSMul G X] [LocallyConnectedSpace X]
    {M N : SingGXCat.{u} G X} (i : M ≅ N) : M ≃ₜ N where
  toFun := (i.hom : {f : M → N // IsAEMorphism G X f}).1
  invFun := (i.inv : {f : N → M // IsAEMorphism G X f}).1
  left_inv x := congr_fun (congr_arg Subtype.val i.hom_inv_id) x
  right_inv y := congr_fun (congr_arg Subtype.val i.inv_hom_id) y
  continuous_toFun := (i.hom : {f : M → N // IsAEMorphism G X f}).2.continuous
  continuous_invFun := (i.inv : {f : N → M // IsAEMorphism G X f}).2.continuous

end Category

/-! ### `rem:morphisms_analytical_two_equal` needs `M` connected and the open set nonempty -/

section Counterexamples

/-- The maximal atlas of `ℝ` for the translations, a maximal a.e. atlas. -/
abbrev translationAtlas : Set (OpenPartialHomeomorph ℝ ℝ) :=
  (gxGroupoid (Multiplicative ℝ) ℝ).maximalAtlas ℝ

/-- `rem:morphisms_analytical_two_equal` needs a NONEMPTY open set: on `ℝ` with the translations
(a singular `(G,X)`-manifold satisfying every hypothesis of the paper), the identity and the
translation by `1` are a.e. `(G,X)`-morphisms, agree on the open set `∅`, and differ. -/
theorem analytic_counterexample_empty :
    IsMaximalAEAtlas (Multiplicative ℝ) translationAtlas ∧
    ∃ f₁ f₂ : ℝ → ℝ, IsAEMorphismOf (Multiplicative ℝ) translationAtlas translationAtlas f₁ ∧
      IsAEMorphismOf (Multiplicative ℝ) translationAtlas translationAtlas f₂ ∧
      IsOpen (∅ : Set ℝ) ∧ EqOn f₁ f₂ ∅ ∧ f₁ ≠ f₂ := by
  refine ⟨isMaximalAEAtlas_maximalAtlas, id, fun p => Multiplicative.ofAdd (1 : ℝ) • p,
    isAEMorphismOf_maximalAtlas_iff.2 isGXMorphism_id,
    isAEMorphismOf_maximalAtlas_iff.2 (isGXMorphism_smul _), isOpen_empty, fun _ h => h.elim,
    fun h => ?_⟩
  have := congr_fun h 0
  simp at this

/-- The two-component space `ℝ ⊕ ℝ` with the translations: a `(G,X)`-manifold. -/
instance hasGroupoid_sum_translation :
    HasGroupoid (ℝ ⊕ ℝ) (gxGroupoid (Multiplicative ℝ) ℝ) := by
  refine ⟨fun {e e'} he he' => symm_trans_mem_gxGroupoid fun x hx => ?_⟩
  have key : ∀ {e e' : OpenPartialHomeomorph (ℝ ⊕ ℝ) ℝ}, e ∈ atlas ℝ (ℝ ⊕ ℝ) →
      e' ∈ atlas ℝ (ℝ ⊕ ℝ) → (e.source ∩ e'.source).Nonempty → e = e' := by
    intro e e' he he' ⟨y, hy, hy'⟩
    rcases ChartedSpace.mem_atlas_sum he with ⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩ <;>
      rcases ChartedSpace.mem_atlas_sum he' with ⟨f', hf', rfl⟩ | ⟨f', hf', rfl⟩ <;>
      rw [chartedSpaceSelf_atlas] at hf hf' <;> subst hf hf' <;>
      simp only [OpenPartialHomeomorph.lift_openEmbedding_source, mem_image] at hy hy' <;>
      first
        | rfl
        | (obtain ⟨_, -, rfl⟩ := hy; obtain ⟨_, -, h⟩ := hy'; exact absurd h (by simp))
  obtain rfl := key he he' ⟨x, hx⟩
  exact ⟨1, Eventually.of_forall fun _ => (one_smul _ _).symm⟩

/-- The maximal atlas of `ℝ ⊕ ℝ`. -/
abbrev sumTranslationAtlas : Set (OpenPartialHomeomorph (ℝ ⊕ ℝ) ℝ) :=
  (gxGroupoid (Multiplicative ℝ) ℝ).maximalAtlas (ℝ ⊕ ℝ)

/-- `rem:morphisms_analytical_two_equal` needs `M` CONNECTED: on `ℝ ⊕ ℝ` with the translations
(locally connected, Hausdorff, second countable, empty singular locus), the identity and the map
translating the second copy by `1` are a.e. `(G,X)`-morphisms which agree on the nonempty open
first copy, and differ. -/
theorem analytic_counterexample_disconnected :
    IsMaximalAEAtlas (Multiplicative ℝ) sumTranslationAtlas ∧
    ∃ f₁ f₂ : ℝ ⊕ ℝ → ℝ ⊕ ℝ,
      IsAEMorphismOf (Multiplicative ℝ) sumTranslationAtlas sumTranslationAtlas f₁ ∧
      IsAEMorphismOf (Multiplicative ℝ) sumTranslationAtlas sumTranslationAtlas f₂ ∧
      ∃ W : Set (ℝ ⊕ ℝ), IsOpen W ∧ W.Nonempty ∧ EqOn f₁ f₂ W ∧ f₁ ≠ f₂ := by
  set f₂ : ℝ ⊕ ℝ → ℝ ⊕ ℝ := Sum.map id fun p => Multiplicative.ofAdd (1 : ℝ) • p
  have hf₂ : IsGXMorphism (Multiplicative ℝ) ℝ f₂ := by
    refine ⟨continuous_id.sumMap (continuous_const_smul _), fun x => ?_⟩
    rcases x with a | a
    · refine ⟨1, ?_⟩
      filter_upwards [isOpen_range_inl.mem_nhds ⟨a, rfl⟩] with y hy
      obtain ⟨b, rfl⟩ := hy
      simp [f₂]
    · refine ⟨Multiplicative.ofAdd 1, ?_⟩
      filter_upwards [isOpen_range_inr.mem_nhds ⟨a, rfl⟩] with y hy
      obtain ⟨b, rfl⟩ := hy
      simp [f₂]
  refine ⟨isMaximalAEAtlas_maximalAtlas, id, f₂,
    isAEMorphismOf_maximalAtlas_iff.2 isGXMorphism_id, isAEMorphismOf_maximalAtlas_iff.2 hf₂,
    range Sum.inl, isOpen_range_inl, ⟨_, 0, rfl⟩, ?_, fun h => ?_⟩
  · rintro _ ⟨b, rfl⟩; simp [f₂]
  · have := congr_fun h (Sum.inr 0)
    simp [f₂] at this

/-- `lem:aepullback` asserts uniqueness of the a.e. `(G,X)`-STRUCTURE, and an a.e. structure is
an a.e. atlas (`def:structure_topological_space_atlas`); uniqueness holds only among MAXIMAL ones
(`IsAEMorphismOf.eq_of_isMaximalAEAtlas`), as the proof's appeal to maximality shows. Here two
different a.e. atlases on `ℝ` make `id` an a.e. morphism into the translation structure. -/
theorem aePullback_counterexample_nonmaximal :
    ∃ A A' : Set (OpenPartialHomeomorph ℝ ℝ), IsAEAtlas (Multiplicative ℝ) A ∧
      IsAEAtlas (Multiplicative ℝ) A' ∧
      IsAEMorphismOf (Multiplicative ℝ) A translationAtlas id ∧
      IsAEMorphismOf (Multiplicative ℝ) A' translationAtlas id ∧ A ≠ A' := by
  have hmax : IsMaximalAEAtlas (Multiplicative ℝ) translationAtlas := isMaximalAEAtlas_maximalAtlas
  have hs : support ({OpenPartialHomeomorph.refl ℝ} : Set (OpenPartialHomeomorph ℝ ℝ)) = univ :=
    eq_univ_of_forall fun x => mem_support.2 ⟨_, rfl, mem_univ x⟩
  have hA' : IsAEAtlas (Multiplicative ℝ) ({OpenPartialHomeomorph.refl ℝ} :
      Set (OpenPartialHomeomorph ℝ ℝ)) := by
    refine ⟨isGXAtlas_of_eventually fun e he e' he' x _ => ?_, by rw [hs]; exact isPortly_univ⟩
    rw [mem_singleton_iff] at he he'
    subst he he'
    exact ⟨1, Eventually.of_forall fun _ => (one_smul _ _).symm⟩
  refine ⟨translationAtlas, {OpenPartialHomeomorph.refl ℝ}, hmax.1, hA',
    isAEMorphismOf_maximalAtlas_iff.2 isGXMorphism_id, (isAEMorphismOf_iff hmax.1).2
      ⟨continuous_id, univ, isPortly_univ, IsRegularOn.of_exists hA'.1 hmax.1.1 isOpen_univ
        (by rw [hs]) (by rw [support_maximalAtlas]; exact mapsTo_univ _ _)
        continuous_id.continuousOn fun x _ => ⟨_, rfl, chartAt ℝ x,
          (gxGroupoid (Multiplicative ℝ) ℝ).chart_mem_maximalAtlas x, mem_univ x,
          mem_chart_source ℝ x, 1, Eventually.of_forall fun y => by simp⟩⟩, fun h => ?_⟩
  have hI : IsOpen (Ioo (0 : ℝ) 1) := isOpen_Ioo
  have hmem : (OpenPartialHomeomorph.refl ℝ).restrOpen _ hI ∈ translationAtlas :=
    hmax.restrOpen_mem (by
      have := (gxGroupoid (Multiplicative ℝ) ℝ).chart_mem_maximalAtlas (H := ℝ) (0 : ℝ)
      rwa [chartAt_self_eq] at this) hI
  rw [h, mem_singleton_iff] at hmem
  have : (2 : ℝ) ∈ ((OpenPartialHomeomorph.refl ℝ).restrOpen _ hI).source := by
    rw [hmem]; exact mem_univ _
  exact absurd this.2.2 (by norm_num)

end Counterexamples

end GX
