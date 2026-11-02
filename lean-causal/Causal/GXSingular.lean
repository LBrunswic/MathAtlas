import Causal.GXStructure

/-!
# The causality of a singular `(G,X)`-manifold, abstracted

`prop:GX_sing_espace_temps_topo` — `ETT.tex:616` (proof `ETT.tex:626`).
`rem:hypotheses_proposition_prop_gx` — `ETT.tex:635`.
Neither is marked: the singular structure is abstracted (SCOPE), the uniqueness is proved among
absolutely minimal causalities, and the remark only for unbranched maps at regular points.

**Graduated (DEC-73, 2026-11-02)** from the scaffold (`scaffold/CausalScaffold/GXSingular.lean`,
module `CausalScaffold.GXSingular`), sorry-free, unchanged but for this paragraph; so that the CBG
work (`Causal.CBG.FromModel`) can graduate. Its reconciliation with gx's DEC-25 (a.e.
morphisms of singular `(G,X)`-manifolds) is a follow-up, not done here.

> Let $(G,X,X_A)$ be an analytic singular structure and let $(M,\A)$ be a $(G,X,X_A)$-manifold.
> Assume moreover that (a) $X$ is a causally arc-connected Baire topological spacetime on which
> $G$ acts by morphisms of topological spacetimes; (b) for every $\alpha \in A$, the model space
> $X_\alpha$ is a causally arc-connected topological spacetime whose causality extends the
> natural causality of $\reg(X_\alpha)$ given by its $(G,X)$-manifold structure. Then $M$ admits
> a unique topological spacetime structure such that for every chart $(\U,Y,\V,\phi)$ of $\A$
> the homeomorphism $\phi:\U\rightarrow \V$ is an isomorphism of topological spacetimes.

> Under the hypotheses of Proposition \ref{prop:GX_sing_espace_temps_topo}, every branched
> $(G,X)$-morphism is a morphism of topological spacetimes.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| analytic singular structure `(G,X,X_A)` | ⚠ reading: abstracted (SCOPE); analyticity not used |
| (a) `X` causally arc-connected, `G` acts by morphisms | ✓ carried (strong morphisms, DEC-12) |
| (a) `X` Baire | **⚠ weakened: not used** (OQ-10) |
| (b) `X_α` causally arc-connected | ✓ carried |
| (b) its causality extends the natural one of `reg(X_α)` | ⚠ reading: every regular chart `r α k` is a `ChartIso` |
| topological spacetimes (second countable, Hausdorff) | ⚠ weakened: not used |
| uniqueness, as written | ⚠ strengthened: among absolutely minimal causalities; false as stated already for `J = ∅` (`GX_maximal_not_unique`) |
| remark: "branched `(G,X)`-morphism" | ⚠ strengthened: unbranched, regular points only (a chart into `X` at every point); source absolutely minimal |

## SCOPE (disclosed)

* **The singular structure is abstracted, the model spaces are not built.** Data: the model `X`
  with `G` acting; model spaces `Y α` with causalities `DY α`; charts `r α k : Y α → X` standing
  for the `(G,X)`-structure of `reg(Y α)` (sources inside the regular part, not otherwise used);
  an atlas of `M` made of charts `eX i` into `X` and `eY j` into `Y (β j)`. "Transition maps are
  restrictions of elements of `G` and of isomorphisms of the model spaces" is read as three
  hypotheses, each local on the overlaps: `hXX` (an element of `G`), `hXY` (an element of `G`
  followed by the inverse of a regular chart — the transition from `X` into `reg(Y α)`), `hYY`
  (a local isomorphism of model spaces: an open partial homeomorphism which is a `ChartIso`; a
  global `ModelIso` is a special case, `agreeOn_of_modelIso`).
* **Maximal atlas (DEC-16) not carried here.** The abstracted data have no single structure
  groupoid (charts land in different model spaces, and `hXY`, `hYY` are conditions on pairs of
  given charts), so mathlib's `maximalAtlas` does not apply; the theorem is over the given atlas.
  A maximal singular atlas is definable (all charts compatible under `hXX`/`hXY`/`hYY`) and is not
  carried: that a further compatible chart is an isomorphism, by the argument of
  `chartIso_of_mem_maximalAtlas`, is asserted here and not proved.
* **(b), second half**, is read: each regular chart is an isomorphism of `Y α` onto `X`. Since
  `Y α` is absolutely minimal on every open subset, this says the restriction of `DY α` to the
  regular part is the causality `prop:GX_espace_temps_topo` gives it. It is used in (B), for the
  `X`–`Y α` transitions (`agreeOn_of_regular`); the paper's proof cites (b) for (A) only.
* `rem:hypotheses_proposition_prop_gx`: "branched `(G,X)`-morphism" is not defined in the paper.
  Proved for unbranched maps at regular points only: an open continuous map which reads, near
  every point, in a chart into `X` on each side, as an element of `G` is a strong morphism
  (`strongMorphism_of_gxMorphism`, which needs a chart into `X` at every point of the source);
  generally an open continuous map locally matching relations is one
  (`strongMorphism_of_locally`). The source causality is absolutely minimal. Branch points and
  singular points are not covered.
* `causality_singularGX_line` lists the hypotheses, instantiated, as conjuncts: two models, a
  non-surjective regular chart, overlaps of `X`- and `Y`-charts and of the two `Y`-charts.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation Filter

universe u v v' w w₁ w₂ w₃

variable {M : Type u} [TopologicalSpace M]

/-! ### Isomorphisms of model spaces -/

section ModelIso

variable {Y : Type v} {Y' : Type v'} [TopologicalSpace Y] [TopologicalSpace Y']

/-- An **isomorphism of topological spacetimes** `(Y, D) → (Y', D')` (DEC-10): a strong morphism
with a two-sided inverse which is a strong morphism. -/
def ModelIso (D : Causality Y) (D' : Causality Y') (ψ : Y → Y') : Prop :=
  ∃ ψ' : Y' → Y, StrongMorphism D D' ψ ∧ StrongMorphism D' D ψ' ∧
    Function.LeftInverse ψ' ψ ∧ Function.RightInverse ψ' ψ

/-- The image of an open set under an open map, as an open set. -/
def imageOpensOf {ψ : Y → Y'} (hψ : IsOpenMap ψ) (V : Opens Y) : Opens Y' :=
  ⟨ψ '' V, hψ _ V.isOpen⟩

/-- An isomorphism of model spaces matches the relations of every open set with those of its
image. -/
theorem ModelIso.rel_iff {D : Causality Y} {D' : Causality Y'} {ψ : Y → Y'}
    (h : ModelIso D D' ψ) (hψ : IsOpenMap ψ) (V : Opens Y) (a b : Y) :
    (D'.le (imageOpensOf hψ V) (ψ a) (ψ b) ↔ D.le V a b) ∧
      (D'.lt (imageOpensOf hψ V) (ψ a) (ψ b) ↔ D.lt V a b) := by
  obtain ⟨ψ', h₁, h₂, hl, hr⟩ := h
  have hV : (imageOpensOf hψ V : Set Y') = ψ' ⁻¹' V := by
    show ψ '' V = ψ' ⁻¹' V
    rw [image_eq_preimage_of_inverse hl hr]
  have hV' : (V : Set Y) = ψ ⁻¹' (imageOpensOf hψ V) :=
    (hl.injective.preimage_image _).symm
  refine ⟨⟨fun h => ?_, fun h => h₁.map_le _ V hV' h⟩, ⟨fun h => ?_, fun h => h₁.map_lt _ V hV' h⟩⟩
  · simpa [hl a, hl b] using h₂.map_le V _ hV h
  · simpa [hl a, hl b] using h₂.map_lt V _ hV h

theorem ModelIso.isOpenMap {D : Causality Y} {D' : Causality Y'} {ψ : Y → Y'}
    (h : ModelIso D D' ψ) : IsOpenMap ψ := h.choose_spec.1.isOpenMap

end ModelIso

/-! ### Local agreement across the three kinds of transition maps -/

section Agreement

variable {X : Type v} [TopologicalSpace X] {G : Type w} [Group G] [MulAction G X]
  [ContinuousConstSMul G X]

/-- A transition map which is, near the points of `O`, the restriction of an isomorphism of the
model spaces: the two transported causalities agree on `O`. -/
theorem ChartIso.agreeOn_of_modelIso {Y : Type v} {Y' : Type v'} [TopologicalSpace Y]
    [TopologicalSpace Y'] {D : Causality Y} {D' : Causality Y'} {C₁ C₂ : Causality M}
    {e₁ : OpenPartialHomeomorph M Y} {e₂ : OpenPartialHomeomorph M Y'} (h₁ : ChartIso C₁ D e₁)
    (h₂ : ChartIso C₂ D' e₂) {ψ : Y → Y'} (hψ : ModelIso D D' ψ) {O : Opens M}
    (hO : O ≤ chartSource e₁ ⊓ chartSource e₂) (heq : ∀ z ∈ O, e₂ z = ψ (e₁ z)) :
    AgreeOn C₁ C₂ O := by
  intro V hV x y
  refine h₁.agree_of_rel h₂ (hO.trans inf_le_left) (hO.trans inf_le_right) ?_ hV x y
  intro V hV a ha b hb
  have himg : chartImage e₂ V = imageOpensOf hψ.isOpenMap (chartImage e₁ V) := by
    apply SetLike.coe_injective
    change (chartImage e₂ V : Set Y') = ψ '' (chartImage e₁ V : Set Y)
    rw [coe_chartImage_of_le (hV.trans (hO.trans inf_le_right)),
      coe_chartImage_of_le (hV.trans (hO.trans inf_le_left)), image_image]
    exact image_congr fun z hz => heq z (hV hz)
  rw [himg, heq a (hV ha), heq b (hV hb)]
  exact ⟨(hψ.rel_iff hψ.isOpenMap _ _ _).1.symm, (hψ.rel_iff hψ.isOpenMap _ _ _).2.symm⟩

/-- A transition from a chart into `X` to a chart into the model `Y` which is, near the points of
`O`, an element of `G` followed by the inverse of a regular chart `r` of `Y`, along which `Y`'s
causality is the one of `X` (hypothesis (b)): the two transported causalities agree on `O`. -/
theorem ChartIso.agreeOn_of_regular {Y : Type v'} [TopologicalSpace Y] {DX : Causality X}
    {DY : Causality Y} (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p) {C₁ C₂ : Causality M}
    {eX : OpenPartialHomeomorph M X} {eY : OpenPartialHomeomorph M Y}
    {r : OpenPartialHomeomorph Y X} (h₁ : ChartIso C₁ DX eX) (h₂ : ChartIso C₂ DY eY)
    (hr : ChartIso DY DX r) {g : G} {O : Opens M} (hO : O ≤ chartSource eX ⊓ chartSource eY)
    (heq : ∀ z ∈ O, eY z ∈ r.source ∧ r (eY z) = g • eX z) : AgreeOn C₁ C₂ O := by
  intro V hV x y
  refine h₁.agree_of_rel h₂ (hO.trans inf_le_left) (hO.trans inf_le_right) ?_ hV x y
  intro V hV a ha b hb
  have hVY : V ≤ chartSource eY := hV.trans (hO.trans inf_le_right)
  have hVX : V ≤ chartSource eX := hV.trans (hO.trans inf_le_left)
  have hW : chartImage eY V ≤ chartSource r := by
    intro p hp
    obtain ⟨z, -, hzV, rfl, -⟩ := exists_of_mem_chartImage hp
    exact (heq z (hV hzV)).1
  have himg : chartImage r (chartImage eY V) = smulOpens g (chartImage eX V) := by
    apply SetLike.coe_injective
    change (chartImage r (chartImage eY V) : Set X) = (fun p => g • p) '' (chartImage eX V : Set X)
    rw [coe_chartImage_of_le hW, coe_chartImage_of_le hVY, coe_chartImage_of_le hVX, image_image,
      image_image]
    exact image_congr fun z hz => (heq z (hV hz)).2
  have ha' := mem_chartImage_of_mem (hVY ha) ha
  have hb' := mem_chartImage_of_mem (hVY hb) hb
  have hiso := hr (chartImage eY V) hW _ ha' _ hb'
  rw [himg, (heq a (hV ha)).2, (heq b (hV hb)).2] at hiso
  rw [hiso.1, hiso.2]
  exact ⟨(smul_rel_iff hG g _ _ _).1.symm, (smul_rel_iff hG g _ _ _).2.symm⟩

/-- A transition map which is, near the points of `O`, a **local isomorphism of model spaces** —
an open partial homeomorphism `ψ` of `Y` into `Y'` which is a `ChartIso` — gives agreeing
transported causalities on `O`. A global `ModelIso` is the special case `agreeOn_of_modelIso`. -/
theorem ChartIso.agreeOn_of_localIso {Y : Type v} {Y' : Type v'} [TopologicalSpace Y]
    [TopologicalSpace Y'] {D : Causality Y} {D' : Causality Y'} {C₁ C₂ : Causality M}
    {e₁ : OpenPartialHomeomorph M Y} {e₂ : OpenPartialHomeomorph M Y'} (h₁ : ChartIso C₁ D e₁)
    (h₂ : ChartIso C₂ D' e₂) {ψ : OpenPartialHomeomorph Y Y'} (hψ : ChartIso D D' ψ)
    {O : Opens M} (hO : O ≤ chartSource e₁ ⊓ chartSource e₂)
    (heq : ∀ z ∈ O, e₁ z ∈ ψ.source ∧ ψ (e₁ z) = e₂ z) : AgreeOn C₁ C₂ O := by
  intro V hV x y
  refine h₁.agree_of_rel h₂ (hO.trans inf_le_left) (hO.trans inf_le_right) ?_ hV x y
  intro V hV a ha b hb
  have hV₁ : V ≤ chartSource e₁ := hV.trans (hO.trans inf_le_left)
  have hV₂ : V ≤ chartSource e₂ := hV.trans (hO.trans inf_le_right)
  have hW : chartImage e₁ V ≤ chartSource ψ := by
    intro p hp
    obtain ⟨z, -, hzV, rfl, -⟩ := exists_of_mem_chartImage hp
    exact (heq z (hV hzV)).1
  have himg : chartImage ψ (chartImage e₁ V) = chartImage e₂ V := by
    apply SetLike.coe_injective
    rw [coe_chartImage_of_le hW, coe_chartImage_of_le hV₁, coe_chartImage_of_le hV₂, image_image]
    exact image_congr fun z hz => (heq z (hV hz)).2
  have hiso := hψ (chartImage e₁ V) hW _ (mem_chartImage_of_mem (hV₁ ha) ha) _
    (mem_chartImage_of_mem (hV₁ hb) hb)
  rw [himg, (heq a (hV ha)).2, (heq b (hV hb)).2] at hiso
  exact hiso

end Agreement

/-! ### `prop:GX_sing_espace_temps_topo`, abstracted -/

/-- `prop:GX_sing_espace_temps_topo`, in the abstract form of SCOPE. The data: a model `X` with a
group `G` acting on it; model spaces `Y α`, `α ∈ A`, each with charts `r α k` of its regular part
into `X`; an atlas of `M` made of charts `eX i` into `X` and `eY j` into `Y (β j)`, whose transition
maps are, near every point of an overlap, the restriction of an element of `G` (`hXX`), an element
of `G` followed by the inverse of a regular chart (`hXY`), or an isomorphism of model spaces
(`hYY`). Under (a) and (b), `M` carries an absolutely minimal causality for which every chart is
an isomorphism of topological spacetimes, and it is the only absolutely minimal one. -/
theorem existsUnique_causality_singularGX {X : Type v} [TopologicalSpace X] {G : Type w} [Group G]
    [MulAction G X] [ContinuousConstSMul G X] {A : Type w₁} {Y : A → Type v'}
    [∀ α, TopologicalSpace (Y α)] {K : A → Type w₂} (r : ∀ α, K α → OpenPartialHomeomorph (Y α) X)
    {I : Type w₃} {J : Type w₃} (eX : I → OpenPartialHomeomorph M X) (β : J → A)
    (eY : ∀ j, OpenPartialHomeomorph M (Y (β j))) (DX : Causality X) (DY : ∀ α, Causality (Y α))
    -- (a)
    (ha : DX.CausallyArcConnected) (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p)
    -- (b)
    (hb : ∀ α, (DY α).CausallyArcConnected) (hreg : ∀ α k, ChartIso (DY α) DX (r α k))
    -- the singular atlas
    (hcover : ∀ x : M, (∃ i, x ∈ (eX i).source) ∨ ∃ j, x ∈ (eY j).source)
    (hXX : ∀ i i', (eX i).symm.trans (eX i') ∈ gxGroupoid G X)
    (hXY : ∀ i j, ∀ x ∈ (eX i).source, x ∈ (eY j).source → ∃ k : K (β j), ∃ g : G,
      ∃ O : Opens M, x ∈ O ∧ O ≤ chartSource (eX i) ⊓ chartSource (eY j) ∧
        ∀ z ∈ O, eY j z ∈ (r (β j) k).source ∧ r (β j) k (eY j z) = g • eX i z)
    (hYY : ∀ j j', ∀ x ∈ (eY j).source, x ∈ (eY j').source →
      ∃ ψ : OpenPartialHomeomorph (Y (β j)) (Y (β j')), ChartIso (DY (β j)) (DY (β j')) ψ ∧
        ∃ O : Opens M, x ∈ O ∧ O ≤ chartSource (eY j) ⊓ chartSource (eY j') ∧
          ∀ z ∈ O, eY j z ∈ ψ.source ∧ ψ (eY j z) = eY j' z) :
    ∃ C : Causality M, (∀ i, ChartIso C DX (eX i)) ∧ (∀ j, ChartIso C (DY (β j)) (eY j)) ∧
      C.AbsolutelyMinimal ∧
      ∀ C' : Causality M, (∀ i, ChartIso C' DX (eX i)) → (∀ j, ChartIso C' (DY (β j)) (eY j)) →
        C'.AbsolutelyMinimal → C' = C := by
  let U : I ⊕ J → Opens M := Sum.elim (fun i => chartSource (eX i)) fun j => chartSource (eY j)
  let Cl : I ⊕ J → Causality M :=
    Sum.elim (fun i => DX.chartTransport (eX i)) fun j => (DY (β j)).chartTransport (eY j)
  have hX : ∀ i, ChartIso (Cl (Sum.inl i)) DX (eX i) := fun i => DX.chartTransport_chartIso _
  have hY : ∀ j, ChartIso (Cl (Sum.inr j)) (DY (β j)) (eY j) := fun j =>
    (DY (β j)).chartTransport_chartIso _
  have hU : ∀ x : M, ∃ s, x ∈ U s := fun x => by
    rcases hcover x with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact ⟨Sum.inl i, hi⟩
    · exact ⟨Sum.inr j, hj⟩
  have hA : ∀ s, ∀ W : Opens M, W ≤ U s → (Cl s).AbsolutelyMinimalOn W := by
    rintro (i | j) W hW
    · exact (hX i).absolutelyMinimalOn hW (ha.absolutelyMinimalOn_all _)
    · exact (hY j).absolutelyMinimalOn hW ((hb _).absolutelyMinimalOn_all _)
  have hXYagree : ∀ i j, ∀ x ∈ (eX i).source, x ∈ (eY j).source →
      ∃ O : Opens M, x ∈ O ∧ AgreeOn (Cl (Sum.inl i)) (Cl (Sum.inr j)) O := by
    intro i j x hx hx'
    obtain ⟨k, g, O, hxO, hO, heq⟩ := hXY i j x hx hx'
    exact ⟨O, hxO, (hX i).agreeOn_of_regular hG (hY j) (hreg _ k) hO heq⟩
  have hB : ∀ s t, ∀ x ∈ U s ⊓ U t, ∃ O : Opens M, x ∈ O ∧ AgreeOn (Cl s) (Cl t) O := by
    rintro (i | j) (i' | j') x hx
    · obtain ⟨g, O, hxO, hO, heq⟩ := exists_smul_eq_of_mem_gxGroupoid (hXX i i') hx.1 hx.2
      exact ⟨O, hxO, (hX i).agreeOn_of_smul hG (hX i') hO heq⟩
    · exact hXYagree i j' x hx.1 hx.2
    · obtain ⟨O, hxO, hO⟩ := hXYagree i' j x hx.2 hx.1
      exact ⟨O, hxO, hO.symm⟩
    · obtain ⟨ψ, hψ, O, hxO, hO, heq⟩ := hYY j j' x hx.1 hx.2
      exact ⟨O, hxO, (hY j).agreeOn_of_localIso (hY j') hψ hO heq⟩
  obtain ⟨C, hC, hmin, huniq⟩ := existsUnique_absolutelyMinimal_of_agree_locally hU hA hB
  refine ⟨C, fun i => (hX i).congr (hC (Sum.inl i)), fun j => (hY j).congr (hC (Sum.inr j)),
    hmin, fun C' hCX hCY hmin' => huniq C' ?_ hmin'⟩
  rintro (i | j) V hV x y
  · exact (hCX i).agree (hX i) hV x y
  · exact (hCY j).agree (hY j) hV x y

/-! ### `rem:hypotheses_proposition_prop_gx`, unbranched -/

section Morphisms

variable {N : Type v} [TopologicalSpace N]

/-- An open continuous map which, near every point, maps the relations of the small open sets to
those of their images, is a strong morphism as soon as the source causality is absolutely
minimal. -/
theorem strongMorphism_of_locally {C : Causality M} {C' : Causality N} {f : M → N}
    (hc : Continuous f) (ho : IsOpenMap f) (hmin : C.AbsolutelyMinimal)
    (hloc : ∀ x : M, ∃ O : Opens M, x ∈ O ∧ ∀ V : Opens M, V ≤ O → ∀ a b,
      (C.le V a b → C'.le (imageOpensOf ho V) (f a) (f b)) ∧
        (C.lt V a b → C'.lt (imageOpensOf ho V) (f a) (f b))) :
    StrongMorphism C C' f := by
  choose O hxO hO using hloc
  have hmin' := Precausality.absolutelyMinimal_iff.1 hmin
  have hsub : ∀ (U : Opens N) (V : Opens M), (V : Set M) = f ⁻¹' U → ∀ z,
      imageOpensOf ho (V ⊓ O z) ≤ U := by
    intro U V hV z p hp
    obtain ⟨q, hq, rfl⟩ := hp
    have : q ∈ (V : Set M) := hq.1
    rw [hV] at this
    exact this
  refine ⟨hc, ho, fun U V hV a b hab => ?_, fun U V hV a b hab => ?_⟩
  · have hchain := hmin'.linkLe_of_family O (fun x _ => ⟨x, hxO x⟩) le_top hab
    clear hab
    induction hchain with
    | single hl =>
      obtain ⟨z, hz⟩ := hl
      exact C'.le_mono (hsub U V hV z) ((hO z _ inf_le_right _ _).1 hz)
    | tail _ hl ih =>
      obtain ⟨z, hz⟩ := hl
      exact C'.le_trans ih (C'.le_mono (hsub U V hV z) ((hO z _ inf_le_right _ _).1 hz))
  · have hchain := hmin'.linkLt_of_family O (fun x _ => ⟨x, hxO x⟩) le_top hab
    clear hab
    induction hchain with
    | single hl =>
      obtain ⟨z, hz⟩ := hl
      exact C'.lt_mono (hsub U V hV z) ((hO z _ inf_le_right _ _).2 hz)
    | tail _ hl ih =>
      obtain ⟨z, hz⟩ := hl
      exact C'.lt_trans ih (C'.lt_mono (hsub U V hV z) ((hO z _ inf_le_right _ _).2 hz))

variable {X : Type v'} [TopologicalSpace X] {G : Type w} [Group G] [MulAction G X]
  [ContinuousConstSMul G X]

/-- `rem:hypotheses_proposition_prop_gx`, for unbranched maps (SCOPE): a map between two spaces
charted in `X` which is open, continuous, and near every point reads in charts as an element of
`G`, is a strong morphism for causalities making the charts isomorphisms, the source one being
absolutely minimal. -/
theorem strongMorphism_of_gxMorphism {C : Causality M} {C' : Causality N} {DX : Causality X}
    (hG : ∀ g : G, StrongMorphism DX DX fun p => g • p) {f : M → N} (hc : Continuous f)
    (ho : IsOpenMap f) (hmin : C.AbsolutelyMinimal)
    (hf : ∀ x : M, ∃ e : OpenPartialHomeomorph M X, ∃ e' : OpenPartialHomeomorph N X,
      ChartIso C DX e ∧ ChartIso C' DX e' ∧ ∃ g : G, ∃ O : Opens M, x ∈ O ∧
        O ≤ chartSource e ∧ MapsTo f O e'.source ∧ ∀ z ∈ O, e' (f z) = g • e z) :
    StrongMorphism C C' f := by
  refine strongMorphism_of_locally hc ho hmin fun x => ?_
  obtain ⟨e, e', he, he', g, O, hxO, hO, hfO, heq⟩ := hf x
  refine ⟨O, hxO, fun V hV a b => ?_⟩
  have hVs : V ≤ chartSource e := hV.trans hO
  have hfV : imageOpensOf ho V ≤ chartSource e' := by
    rintro p ⟨q, hq, rfl⟩
    exact hfO (hV hq)
  have himg : chartImage e' (imageOpensOf ho V) = smulOpens g (chartImage e V) := by
    apply SetLike.coe_injective
    change (chartImage e' (imageOpensOf ho V) : Set X) =
      (fun p => g • p) '' (chartImage e V : Set X)
    rw [coe_chartImage_of_le hfV, coe_chartImage_of_le hVs]
    change e' '' (f '' V) = _
    rw [image_image, image_image]
    exact image_congr fun z hz => heq z (hV hz)
  have key : ∀ {a b : M}, a ∈ V → b ∈ V →
      (C.le V a b ↔ C'.le (imageOpensOf ho V) (f a) (f b)) ∧
        (C.lt V a b ↔ C'.lt (imageOpensOf ho V) (f a) (f b)) := by
    intro a b ha hb
    have hfa : f a ∈ imageOpensOf ho V := mem_image_of_mem f ha
    have hfb : f b ∈ imageOpensOf ho V := mem_image_of_mem f hb
    rw [(he V hVs a ha b hb).1, (he V hVs a ha b hb).2,
      (he' (imageOpensOf ho V) hfV _ hfa _ hfb).1, (he' (imageOpensOf ho V) hfV _ hfa _ hfb).2,
      himg, heq a (hV ha), heq b (hV hb)]
    exact ⟨(smul_rel_iff hG g _ _ _).1.symm, (smul_rel_iff hG g _ _ _).2.symm⟩
  exact ⟨fun h => (key (C.le_mem_left h) (C.le_mem_right h)).1.1 h,
    fun h => (key (C.lt_mem_left h) (C.lt_mem_right h)).2.1 h⟩

end Morphisms

/-! ### The hypotheses are satisfiable -/

section Line

attribute [local instance] continuousConstSMul_multiplicative_real

/-- The identity of `ℝ` restricted to an open set is an isomorphism of any causality onto itself. -/
theorem chartIso_refl_restrOpen (D : Causality ℝ) {s : Set ℝ} (hs : IsOpen s) :
    ChartIso D D ((OpenPartialHomeomorph.refl ℝ).restrOpen s hs) := by
  intro U hU a _ b _
  have himg : chartImage ((OpenPartialHomeomorph.refl ℝ).restrOpen s hs) U = U := by
    apply SetLike.coe_injective
    rw [coe_chartImage_of_le hU]
    simp
  rw [himg]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- The chart `]0, ∞[ → X` of `M = ℝ`, and the regular chart `]0, ∞[ → X` of each model: the
identity on `]0, ∞[`, not surjective. -/
def linePos : OpenPartialHomeomorph ℝ ℝ :=
  (OpenPartialHomeomorph.refl ℝ).restrOpen (Ioi 0) isOpen_Ioi

/-- The charts `]-∞, 1[ → Y b` of `M = ℝ`, one into each of the two models `b : Bool`. -/
def lineLow : OpenPartialHomeomorph ℝ ℝ :=
  (OpenPartialHomeomorph.refl ℝ).restrOpen (Iio 1) isOpen_Iio

theorem linePos_apply (z : ℝ) : linePos z = z := rfl

theorem lineLow_apply (z : ℝ) : lineLow z = z := rfl

theorem linePos_source : linePos.source = Ioi 0 := by simp [linePos]

theorem lineLow_source : lineLow.source = Iio 1 := by simp [lineLow]

/-- **The hypotheses of `existsUnique_causality_singularGX` are satisfiable, non-degenerately**,
and the causality produced is then the timelike line. Data on `M = ℝ`: the model `X = ℝ` with
the timelike line and the translations; two model spaces `Y true`, `Y false`, both the timelike
line, each with one regular chart `linePos`, whose target `]0, ∞[` is not all of `X`; one chart
`linePos` into `X` and two charts `lineLow` into `Y true` and `Y false`. The `X`-chart meets each
`Y`-chart on `]0, 1[`, and the two `Y`-charts overlap on `]-∞, 1[`. Each conjunct below is one
hypothesis of the theorem, in its order, instantiated. -/
theorem causality_singularGX_line :
    -- (a)
    timelikeLine.CausallyArcConnected ∧
    (∀ g : Multiplicative ℝ, StrongMorphism timelikeLine timelikeLine fun p : ℝ => g • p) ∧
    -- (b)
    (∀ _ : Bool, timelikeLine.CausallyArcConnected) ∧
    (∀ (_ : Bool) (_ : Unit), ChartIso timelikeLine timelikeLine linePos) ∧
    -- the atlas: cover, `hXX`, `hXY`, `hYY`
    (∀ x : ℝ, (∃ _ : Unit, x ∈ linePos.source) ∨ ∃ _ : Bool, x ∈ lineLow.source) ∧
    (∀ _ _ : Unit, linePos.symm.trans linePos ∈ gxGroupoid (Multiplicative ℝ) ℝ) ∧
    (∀ (_ : Unit) (_ : Bool), ∀ x ∈ linePos.source, x ∈ lineLow.source →
      ∃ _ : Unit, ∃ g : Multiplicative ℝ, ∃ O : Opens ℝ, x ∈ O ∧
        O ≤ chartSource linePos ⊓ chartSource lineLow ∧
          ∀ z ∈ O, lineLow z ∈ linePos.source ∧ linePos (lineLow z) = g • linePos z) ∧
    (∀ _ _ : Bool, ∀ x ∈ lineLow.source, x ∈ lineLow.source →
      ∃ ψ : OpenPartialHomeomorph ℝ ℝ, ChartIso timelikeLine timelikeLine ψ ∧
        ∃ O : Opens ℝ, x ∈ O ∧ O ≤ chartSource lineLow ⊓ chartSource lineLow ∧
          ∀ z ∈ O, lineLow z ∈ ψ.source ∧ ψ (lineLow z) = lineLow z) ∧
    -- non-degeneracy
    linePos.target ≠ univ ∧ (linePos.source ∩ lineLow.source).Nonempty ∧
    -- the conclusion: the unique absolutely minimal causality is the timelike line
    (∀ C : Causality ℝ, (∀ _ : Unit, ChartIso C timelikeLine linePos) →
      (∀ _ : Bool, ChartIso C timelikeLine lineLow) → C.AbsolutelyMinimal → C = timelikeLine) := by
  have hXX : linePos.symm.trans linePos ∈ gxGroupoid (Multiplicative ℝ) ℝ := by
    have hid : ∀ y : ℝ, (linePos.symm.trans linePos) y = (1 : Multiplicative ℝ) • y :=
      fun y => by simp [linePos]
    have hid' : ∀ y : ℝ, (linePos.symm.trans linePos).symm y = (1 : Multiplicative ℝ) • y :=
      fun y => by simp [linePos]
    exact mem_groupoid_of_pregroupoid.2 ⟨fun y _ => ⟨1, Eventually.of_forall hid⟩,
      fun y _ => ⟨1, Eventually.of_forall hid'⟩⟩
  have hcover : ∀ x : ℝ, (∃ _ : Unit, x ∈ linePos.source) ∨ ∃ _ : Bool, x ∈ lineLow.source := by
    intro x
    rcases lt_or_ge 0 x with h | h
    · exact Or.inl ⟨(), by rw [linePos_source]; exact h⟩
    · exact Or.inr ⟨true, by rw [lineLow_source]; exact lt_of_le_of_lt h one_pos⟩
  have hXY : ∀ (_ : Unit) (_ : Bool), ∀ x ∈ linePos.source, x ∈ lineLow.source →
      ∃ _ : Unit, ∃ g : Multiplicative ℝ, ∃ O : Opens ℝ, x ∈ O ∧
        O ≤ chartSource linePos ⊓ chartSource lineLow ∧
          ∀ z ∈ O, lineLow z ∈ linePos.source ∧ linePos (lineLow z) = g • linePos z := by
    intro _ _ x hx hx'
    refine ⟨(), 1, chartSource linePos ⊓ chartSource lineLow, ⟨hx, hx'⟩, le_rfl,
      fun z hz => ⟨?_, ?_⟩⟩
    · rw [lineLow_apply]; exact hz.1
    · rw [lineLow_apply, linePos_apply, one_smul]
  have hYY : ∀ _ _ : Bool, ∀ x ∈ lineLow.source, x ∈ lineLow.source →
      ∃ ψ : OpenPartialHomeomorph ℝ ℝ, ChartIso timelikeLine timelikeLine ψ ∧
        ∃ O : Opens ℝ, x ∈ O ∧ O ≤ chartSource lineLow ⊓ chartSource lineLow ∧
          ∀ z ∈ O, lineLow z ∈ ψ.source ∧ ψ (lineLow z) = lineLow z :=
    fun _ _ x hx _ => ⟨OpenPartialHomeomorph.refl ℝ, chartIso_refl _,
      chartSource lineLow ⊓ chartSource lineLow, ⟨hx, hx⟩, le_rfl, fun z _ => ⟨trivial, rfl⟩⟩
  have hreg : ChartIso timelikeLine timelikeLine linePos := chartIso_refl_restrOpen _ _
  have hlow : ChartIso timelikeLine timelikeLine lineLow := chartIso_refl_restrOpen _ _
  refine ⟨timelikeLine_causallyArcConnected, timelikeLine_strongMorphism_translation,
    fun _ => timelikeLine_causallyArcConnected, fun _ _ => hreg, hcover, fun _ _ => hXX, hXY,
    hYY, ?_, ?_, ?_⟩
  · intro h
    have : (0 : ℝ) ∈ linePos.target := h ▸ mem_univ 0
    simp [linePos] at this
  · exact ⟨1 / 2, by rw [linePos_source]; norm_num, by rw [lineLow_source]; norm_num⟩
  · intro C hCX hCY hmin
    obtain ⟨C₀, -, -, -, huniq⟩ := existsUnique_causality_singularGX (M := ℝ)
      (G := Multiplicative ℝ) (Y := fun _ : Bool => ℝ) (K := fun _ : Bool => Unit)
      (fun _ _ => linePos) (I := Unit) (J := Bool) (fun _ => linePos) id (fun _ => lineLow)
      timelikeLine (fun _ => timelikeLine)
      timelikeLine_causallyArcConnected timelikeLine_strongMorphism_translation
      (fun _ => timelikeLine_causallyArcConnected) (fun _ _ => hreg) hcover
      (fun _ _ => hXX) hXY hYY
    have h₁ := huniq C hCX hCY hmin
    have h₂ := huniq timelikeLine (fun _ => hreg) (fun _ => hlow)
      timelikeLine_causallyArcConnected.absolutelyMinimal
    rw [h₁, h₂]

end Line

end Causal
