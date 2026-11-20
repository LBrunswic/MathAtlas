import Causal.Pushout
import Causal.CBG.FamilyGluing
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Gluing along open embeddings is Hausdorff iff there are no corresponding boundary points

Programme target `T-abs-gluing-hausdorff` (`programme/roadmap.toml`; layer 1, pure topology, no
paper label, no causality). Its three assertions:

* **`T-abs-gluing-hausdorff/1-pushout-iff`** —
  `Gluing.t2Space_iff_forall_not_isCorrespondingBoundaryPair` (Sbierski 1309.7591, Thm 2.7,
  `references/sbierski/text/sbierski2013existence.txt:1064–1079`; Chruściel 1112.5779,
  Lemma 3.3, `chrusciel2013maximal.txt:866–880`). With no separation hypothesis:
  `Gluing.t2Space_iff_t2Space_and_forall_not_isCorrespondingBoundaryPair`.
* **`T-abs-gluing-hausdorff/2-family`** —
  `CBG.FamilyGlueData.t2Space_iff_forall_not_isCorrespondingBoundaryPair` (Sbierski Thm 2.8,
  `sbierski2013existence.txt:1172–1221`), hypothesis-free form `…t2Space_iff_t2Space_and_…`;
  directed and totally ordered families `t2Space_of_directed`, `t2Space_of_total` (Graf–Ling
  2307.11034 Lemma 29, `graf2023uniqueness.txt:1318–1325`; Chruściel Thm 2.2, the union of a
  chain, `chrusciel2013maximal.txt:349–357`).
* `T-abs-gluing-hausdorff/3-closed-nonhausdorff` — **not marked: false as stated.** Chruściel's
  `H` (`Gluing.nonHausdorffLeft`) lies in `∂O` (`nonHausdorffLeft_subset_frontier`) but need not
  be closed: `not_isClosed_nonHausdorffLeft_expGluing`, two copies of `ℝ²`. True forms: the set of
  corresponding *pairs* is closed in `X × Y` with no hypothesis (`isClosed_correspondingPairs`;
  ETT `prop:C_connexe`, second half); `H` is closed when the corresponding points over a
  neighbourhood of each boundary point stay in a compact set
  (`isClosed_nonHausdorffLeft_of_isCompact`), e.g. `Y` compact (`isClosed_nonHausdorffLeft`).

> Definition 3.5. Let U be a CGHD of M and M′, and let us denote the isometric embedding of U
> into M′ with ψ. Two points p ∈ ∂U ⊆ M and p′ ∈ ∂ψ(U) ⊆ M′ are called corresponding boundary
> points of U iff for all neighbourhoods V of p and for all neighbourhoods V′ of p′ one has
> ψ⁻¹(V′ ∩ ψ(U)) ∩ V ≠ ∅. (`sbierski2013existence.txt:707–711`;
> `papers/sbierski-mghd/legacy/labeled/Maximal_GHD2.tex:529–531`)

> So suppose we could not separate these two points in, without loss of generality, the case
> p ∈ ∂U and q ∈ ∂ψ(U). For all neighbourhoods V of p and V′ of p′, we then have
> (π∘j)(V) ∩ (π∘j′)(V′) ≠ ∅. This, however, implies that ψ⁻¹(V′ ∩ ψ(U)) ∩ V ≠ ∅, i.e., p and q
> are corresponding boundary points of U […]. Thus, M̃ is indeed Hausdorff. (`:1075–1079`;
> `Maximal_GHD2.tex:751`)

> Let H denote the set of non-Hausdorff points p in M1, thus p′ = iM1(p) ≡ [p] is
> non-Hausdorff in M′, where iM1 denotes the embedding of M1 into M′. By elementary topology H is
> closed (as its complement is open), and we have just seen that H ⊂ ∂O.
> (`chrusciel2013maximal.txt:877–880`)

The setting is `Causal.Gluing` (`Causal.Pushout`): `j₁ : W → X`, `j₂ : W → Y` open embeddings,
`O = W`, `∂O_X = frontier (range j₁)`, the gluing `Gluing j₁ j₂ = (X ⊔ Y)/∼`; for a family,
`CBG.FamilyGlueData` (`Causal.CBG.FamilyGluing`). **Corresponding boundary points**
(`Gluing.IsCorrespondingBoundaryPair j₁ j₂ x y`) is Sbierski's Def 3.5 with `j₁` the inclusion
of `U` and `j₂ = ψ`: `x ∈ ∂ j₁(W)`, `y ∈ ∂ j₂(W)`, and every `V ∋ x`, `V' ∋ y` have some `w`
with `j₁ w ∈ V`, `j₂ w ∈ V'`. Equivalently: `(x, y)` is in the closure of the graph
(`forall_nhds_iff_mem_closure_graph`); `x`, `y` are the limits of one filter (one net) of `W`
(`forall_nhds_iff_exists_filter`); of one sequence, under first countability
(`forall_nhds_iff_exists_seq`, the form of Chruściel's and ETT's proofs); with `X`, `Y`
Hausdorff, `[x]` and `[y]` are distinct and not separated in the gluing
(`isCorrespondingBoundaryPair_iff`, `correspondingPairs_eq_Cdist`).

## Hypothesis checklist

| source hypothesis | here |
|---|---|
| `M`, `M′` (`M₁`, `M₂`) GHDs / Lorentzian manifolds, Hausdorff | ⚠ weakened: topological spaces; `[T2Space X] [T2Space Y]` in the source forms of 1 and 3, dropped in the hypothesis-free forms of 1 and 2 |
| `U` (`O`) a CGHD, `ψ` an isometric embedding | ⚠ weakened: `j₁`, `j₂` open embeddings |
| `U` the MCGHD / `(O, Ψ_O)` maximal (Thm 3.13; Lemma 3.3) | not used: they are what proves "no corresponding boundary points"; here it is the criterion's right-hand side |
| Thm 2.8: (3.15) an equivalence relation (from MCGHD maximality) | ✓ carried: the fields of `FamilyGlueData` (`cocycle`, `φ_mem`, `U_self`, `φ_self`) |
| Graf–Ling: the family totally ordered | ⚠ weakened: directed (`t2Space_of_directed`) |
| Chruściel: `H` closed "by elementary topology" | ⚠ strengthened (finding): needs a compactness hypothesis, `isClosed_nonHausdorffLeft_of_isCompact` |

## SCOPE (disclosed)

* **What `Causal.Pushout` and `Causal.CBG.FamilyGluing` already proved, and what is new.**
  `Gluing.t2Space_iff_frontier` and `t2Space_iff_Cdist_eq_empty` are assertion 1 in the
  vocabulary of separation ("every pair of `∂j₁(W) × ∂j₂(W)` has separated images"), and
  `FamilyGlueData.t2Space_iff_Cdist_eq_empty` assertion 2 in that of `Cdist`; `Cdist_eq`,
  `C_eq_closure` give the closure of the graph. New here: the notion of corresponding boundary
  points as the sources define it, its four equivalent forms, assertions 1 and 2 in that
  vocabulary and their hypothesis-free forms, the directed and totally ordered families, and all
  of assertion 3 (definitions of `H`, its location, the counterexample, the true forms).
* **Assertion 3, side and topology.** `H` is taken on the `X` side (Chruściel's `M₁`), in the
  topology of `X`; as `∂O_X` is closed in `X`, closed in `X` and closed in `∂O_X` coincide for it.
  In the counterexample (`expLeft (a, c) = (a, eᶜ)`, `halfPlaneInc (a, c) = (a, c)` on
  `(0, ∞) × ℝ`) `H = {0} × (0, ∞)` and `(0, 0) ∈ closure H \ H`; the non-Hausdorff points of the
  gluing are not closed in the gluing either (`not_isClosed_nonHausdorffPoints_expGluing`). The
  failing step is "its complement is open": the set of Hausdorff points of a space need not be
  open. The `Y` side is symmetric (swap `j₁`, `j₂`).
* **Two more facts of the sources are not topological** (`shearLeft (a, c) = (a, a c)`): a
  boundary point can have a continuum of corresponding points (`shearGluing_not_unique`, against
  Sbierski Prop 3.7's "at most one", `:719–724`), and Sbierski's `C` need not be open in `∂U`
  (`shearGluing_not_isOpen_in_frontier`, against Lemma 3.8, `:787–788`, and ETT
  `prop:C_connexe`, first half, `ETT.tex:2240`). Both are proved there from the geometry; here
  they are localisation properties, not consequences of the gluing.
* **Family version of 3**: the non-Hausdorff points of `M i` in the family gluing are
  `⋃ j, C_{ij}` (`preimage_ι_nonHausdorffPoints`), inside `⋃ j, ∂U i j`. No closedness is
  claimed: each `C_{ij}` is the two-space `C` of `PairGluing D i j`, for which it fails (the
  counterexample is not re-encoded as a `FamilyGlueData`), and a union of closed sets need not be
  closed.
* Nets: a net and its filter of tails have the same limits; the filter form is stated.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace

universe u v w

/-! ### Non-Hausdorff points of a space -/

/-- The **non-Hausdorff points** of a space: the points `z` from which some other point `z'`
cannot be separated by disjoint neighbourhoods. -/
def nonHausdorffPoints (Z : Type*) [TopologicalSpace Z] : Set Z :=
  {z | ∃ z', z' ≠ z ∧ ¬ Disjoint (𝓝 z) (𝓝 z')}

theorem t2Space_iff_nonHausdorffPoints_eq_empty (Z : Type*) [TopologicalSpace Z] :
    T2Space Z ↔ nonHausdorffPoints Z = ∅ := by
  rw [t2Space_iff_disjoint_nhds, Set.eq_empty_iff_forall_notMem]
  simp only [nonHausdorffPoints, mem_setOf_eq, not_exists, not_and, not_not]
  exact ⟨fun h z z' hne => h (Ne.symm hne), fun h z z' hne => h z z' (Ne.symm hne)⟩

namespace Gluing

variable {X : Type u} {Y : Type v} {W : Type w}

section Corresponding

variable [TopologicalSpace X] [TopologicalSpace Y] {j₁ : W → X} {j₂ : W → Y}

variable (j₁ j₂) in
/-- **Corresponding boundary points** (Sbierski, Def 3.5): `x ∈ ∂ j₁(W)` and `y ∈ ∂ j₂(W)` such
that for every neighbourhood `V` of `x` and `V'` of `y` some `w ∈ W` has `j₁ w ∈ V` and
`j₂ w ∈ V'`. -/
def IsCorrespondingBoundaryPair (x : X) (y : Y) : Prop :=
  x ∈ frontier (range j₁) ∧ y ∈ frontier (range j₂) ∧
    ∀ V ∈ 𝓝 x, ∀ V' ∈ 𝓝 y, ∃ w, j₁ w ∈ V ∧ j₂ w ∈ V'

/-- The neighbourhood condition of Def 3.5 says `(x, y)` is in the closure of the graph. -/
theorem forall_nhds_iff_mem_closure_graph {x : X} {y : Y} :
    (∀ V ∈ 𝓝 x, ∀ V' ∈ 𝓝 y, ∃ w, j₁ w ∈ V ∧ j₂ w ∈ V') ↔ (x, y) ∈ closure (graph j₁ j₂) := by
  rw [mem_closure_iff_nhds]
  constructor
  · intro h t ht
    obtain ⟨V, hV, V', hV', hsub⟩ := mem_nhds_prod_iff.1 ht
    obtain ⟨w, h1, h2⟩ := h V hV V' hV'
    exact ⟨(j₁ w, j₂ w), hsub ⟨h1, h2⟩, w, rfl⟩
  · intro h V hV V' hV'
    obtain ⟨_, ⟨h1, h2⟩, w, rfl⟩ := h _ (prod_mem_nhds hV hV')
    exact ⟨w, h1, h2⟩

/-- The neighbourhood condition of Def 3.5 says `x` and `y` are the limits of one filter of
`W`. -/
theorem forall_nhds_iff_exists_filter {x : X} {y : Y} :
    (∀ V ∈ 𝓝 x, ∀ V' ∈ 𝓝 y, ∃ w, j₁ w ∈ V ∧ j₂ w ∈ V') ↔
      ∃ F : Filter W, F.NeBot ∧ Tendsto j₁ F (𝓝 x) ∧ Tendsto j₂ F (𝓝 y) := by
  constructor
  · intro h
    refine ⟨comap j₁ (𝓝 x) ⊓ comap j₂ (𝓝 y), ?_, tendsto_iff_comap.2 inf_le_left,
      tendsto_iff_comap.2 inf_le_right⟩
    rw [inf_neBot_iff]
    intro s hs s' hs'
    obtain ⟨t, ht, hts⟩ := mem_comap.1 hs
    obtain ⟨t', ht', hts'⟩ := mem_comap.1 hs'
    obtain ⟨w, h1, h2⟩ := h t ht t' ht'
    exact ⟨w, hts h1, hts' h2⟩
  · rintro ⟨F, hF, h1, h2⟩ V hV V' hV'
    have h1' : j₁ ⁻¹' V ∈ F := h1 hV
    have h2' : j₂ ⁻¹' V' ∈ F := h2 hV'
    obtain ⟨w, hw1, hw2⟩ := Filter.nonempty_of_mem (inter_mem h1' h2')
    exact ⟨w, hw1, hw2⟩

/-- Under first countability, the condition of Def 3.5 is the sequential one. -/
theorem forall_nhds_iff_exists_seq [FirstCountableTopology X] [FirstCountableTopology Y]
    {x : X} {y : Y} :
    (∀ V ∈ 𝓝 x, ∀ V' ∈ 𝓝 y, ∃ w, j₁ w ∈ V ∧ j₂ w ∈ V') ↔
      ∃ a : ℕ → W, Tendsto (j₁ ∘ a) atTop (𝓝 x) ∧ Tendsto (j₂ ∘ a) atTop (𝓝 y) := by
  rw [forall_nhds_iff_mem_closure_graph, mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨s, hs, hlim⟩
    choose a ha using hs
    have hs' : s = fun n => (j₁ (a n), j₂ (a n)) := funext fun n => (ha n).symm
    subst hs'
    exact ⟨a, (continuous_fst.tendsto _).comp hlim, (continuous_snd.tendsto _).comp hlim⟩
  · rintro ⟨a, h1, h2⟩
    exact ⟨fun n => (j₁ (a n), j₂ (a n)), fun n => ⟨a n, rfl⟩, h1.prodMk_nhds h2⟩

/-- A point of the closure of the graph off both images is a corresponding boundary pair. -/
theorem isCorrespondingBoundaryPair_of_mem_closure_graph {x : X} {y : Y} (hx : x ∉ range j₁)
    (hy : y ∉ range j₂) (h : (x, y) ∈ closure (graph j₁ j₂)) :
    IsCorrespondingBoundaryPair j₁ j₂ x y := by
  have hsub : graph j₁ j₂ ⊆ range j₁ ×ˢ range j₂ := by
    rintro _ ⟨w, rfl⟩; exact ⟨⟨w, rfl⟩, ⟨w, rfl⟩⟩
  have hcl := closure_mono hsub h
  rw [closure_prod_eq] at hcl
  exact ⟨⟨hcl.1, fun hi => hx (interior_subset hi)⟩, ⟨hcl.2, fun hi => hy (interior_subset hi)⟩,
    forall_nhds_iff_mem_closure_graph.2 h⟩

variable (j₁ j₂) in
/-- The set of corresponding boundary pairs. -/
def correspondingPairs : Set (X × Y) := {p | IsCorrespondingBoundaryPair j₁ j₂ p.1 p.2}

/-- The corresponding pairs are the closure of the graph inside `∂ j₁(W) × ∂ j₂(W)`. -/
theorem correspondingPairs_eq :
    correspondingPairs j₁ j₂ =
      closure (graph j₁ j₂) ∩ frontier (range j₁) ×ˢ frontier (range j₂) := by
  ext ⟨x, y⟩
  simp only [correspondingPairs, IsCorrespondingBoundaryPair, mem_setOf_eq,
    forall_nhds_iff_mem_closure_graph, mem_inter_iff, mem_prod]
  tauto

/-- **The corresponding pairs form a closed subset of `X × Y`**, contained in
`∂ j₁(W) × ∂ j₂(W)`. No hypothesis. -/
theorem isClosed_correspondingPairs : IsClosed (correspondingPairs j₁ j₂) := by
  rw [correspondingPairs_eq]
  exact isClosed_closure.inter (isClosed_frontier.prod isClosed_frontier)

theorem correspondingPairs_subset_frontier :
    correspondingPairs j₁ j₂ ⊆ frontier (range j₁) ×ˢ frontier (range j₂) := by
  intro p hp
  exact ⟨hp.1, hp.2.1⟩

variable (j₁ j₂) in
/-- Sbierski's `C`: the points of `∂ j₁(W)` having a corresponding boundary point. -/
def correspondingLeft : Set X := {x | ∃ y, IsCorrespondingBoundaryPair j₁ j₂ x y}

theorem correspondingLeft_eq_image :
    correspondingLeft j₁ j₂ = Prod.fst '' correspondingPairs j₁ j₂ := by
  ext x
  simp [correspondingLeft, correspondingPairs]

theorem correspondingLeft_subset_frontier : correspondingLeft j₁ j₂ ⊆ frontier (range j₁) := by
  rintro x ⟨y, h⟩
  exact h.1

/-- `correspondingLeft` is closed when the corresponding points over a neighbourhood of each
boundary point stay in a compact set. -/
theorem isClosed_correspondingLeft_of_isCompact
    (hK : ∀ x ∈ frontier (range j₁), ∃ V ∈ 𝓝 x, ∃ K : Set Y, IsCompact K ∧
      ∀ x' ∈ V, ∀ y, IsCorrespondingBoundaryPair j₁ j₂ x' y → y ∈ K) :
    IsClosed (correspondingLeft j₁ j₂) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  have hxf : x ∈ frontier (range j₁) :=
    closure_minimal correspondingLeft_subset_frontier isClosed_frontier hx
  obtain ⟨V, hV, K, hKc, hVK⟩ := hK x hxf
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  let S' : Set (X × K) := {p | IsCorrespondingBoundaryPair j₁ j₂ p.1 p.2}
  have hS' : IsClosed S' :=
    isClosed_correspondingPairs.preimage (continuous_id.prodMap continuous_subtype_val)
  have hcl : IsClosed (Prod.fst '' S') := isClosedMap_fst_of_compactSpace _ hS'
  have hsub : correspondingLeft j₁ j₂ ∩ V ⊆ Prod.fst '' S' := by
    rintro x' ⟨⟨y, hy⟩, hx'V⟩
    exact ⟨(x', ⟨y, hVK x' hx'V y hy⟩), hy, rfl⟩
  have hx' : x ∈ closure (correspondingLeft j₁ j₂ ∩ V) := by
    rw [mem_closure_iff_nhds] at hx ⊢
    intro t ht
    obtain ⟨z, ⟨hzt, hzV⟩, hzC⟩ := hx (t ∩ V) (inter_mem ht hV)
    exact ⟨z, hzt, hzC, hzV⟩
  obtain ⟨⟨x', y⟩, hy, rfl⟩ := hcl.closure_subset_iff.2 hsub hx'
  exact ⟨y, hy⟩

theorem isClosed_correspondingLeft [CompactSpace Y] : IsClosed (correspondingLeft j₁ j₂) := by
  exact isClosed_correspondingLeft_of_isCompact fun x _ =>
    ⟨univ, univ_mem, univ, isCompact_univ, fun _ _ _ _ => mem_univ _⟩

end Corresponding

section GluingSep

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W]
  {j₁ : W → X} {j₂ : W → Y}

/-- A corresponding boundary pair has distinct, non-separated images in the gluing (Sbierski,
proof of Thm 2.7, read backwards). No separation axiom. -/
theorem IsCorrespondingBoundaryPair.not_separated (hj₁ : IsOpenEmbedding j₁)
    (hj₂ : IsOpenEmbedding j₂) {x : X} {y : Y} (h : IsCorrespondingBoundaryPair j₁ j₂ x y) :
    ι₁ j₁ j₂ x ≠ ι₂ j₁ j₂ y ∧ ¬ Disjoint (𝓝 (ι₁ j₁ j₂ x)) (𝓝 (ι₂ j₁ j₂ y)) := by
  obtain ⟨hx, -, hc⟩ := h
  refine ⟨fun he => ?_, ?_⟩
  · obtain ⟨w, rfl, -⟩ := (ι₁_eq_ι₂_iff hj₁.injective hj₂.injective).1 he
    exact hx.2 (interior_maximal (range_subset_iff.2 fun w => mem_range_self w)
      hj₁.isOpen_range (mem_range_self w))
  · rw [disjoint_nhds_ι₁_ι₂_iff hj₁ hj₂, not_not]
    exact forall_nhds_iff_mem_closure_graph.1 hc

/-- For Hausdorff `X`, `Y`: `x`, `y` are corresponding boundary points iff their images in the
gluing are distinct and not separated. -/
theorem isCorrespondingBoundaryPair_iff [T2Space X] [T2Space Y] (hj₁ : IsOpenEmbedding j₁)
    (hj₂ : IsOpenEmbedding j₂) {x : X} {y : Y} :
    IsCorrespondingBoundaryPair j₁ j₂ x y ↔
      ι₁ j₁ j₂ x ≠ ι₂ j₁ j₂ y ∧ ¬ Disjoint (𝓝 (ι₁ j₁ j₂ x)) (𝓝 (ι₂ j₁ j₂ y)) := by
  refine ⟨fun h => h.not_separated hj₁ hj₂, fun ⟨hne, hns⟩ => ?_⟩
  have hC : (x, y) ∈ Cdist j₁ j₂ := ⟨hns, hne⟩
  obtain ⟨hx, hy⟩ := Cdist_subset_frontier hj₁ hj₂ hC
  refine ⟨hx, hy, forall_nhds_iff_mem_closure_graph.2 ?_⟩
  rw [← C_eq_closure hj₁ hj₂]
  exact hns

theorem correspondingPairs_eq_Cdist [T2Space X] [T2Space Y] (hj₁ : IsOpenEmbedding j₁)
    (hj₂ : IsOpenEmbedding j₂) : correspondingPairs j₁ j₂ = Cdist j₁ j₂ := by
  ext ⟨x, y⟩
  exact (isCorrespondingBoundaryPair_iff hj₁ hj₂).trans
    ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨b, a⟩ => ⟨a, b⟩⟩

/-- **Assertion 1** (Sbierski Thm 2.7, Chruściel Lemma 3.3): for Hausdorff `X` and `Y` and open
embeddings `j₁`, `j₂`, the gluing is Hausdorff iff there is no pair of corresponding boundary
points. -/
theorem t2Space_iff_forall_not_isCorrespondingBoundaryPair [T2Space X] [T2Space Y]
    (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) :
    T2Space (Gluing j₁ j₂) ↔ ∀ x y, ¬ IsCorrespondingBoundaryPair j₁ j₂ x y := by
  rw [t2Space_iff_Cdist_eq_empty hj₁ hj₂, ← correspondingPairs_eq_Cdist hj₁ hj₂,
    Set.eq_empty_iff_forall_notMem]
  exact ⟨fun h x y => h (x, y), fun h p => h p.1 p.2⟩

/-- **Assertion 1, with no separation hypothesis**: the gluing is Hausdorff iff `X` and `Y` are
and there is no pair of corresponding boundary points. -/
theorem t2Space_iff_t2Space_and_forall_not_isCorrespondingBoundaryPair
    (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) :
    T2Space (Gluing j₁ j₂) ↔
      T2Space X ∧ T2Space Y ∧ ∀ x y, ¬ IsCorrespondingBoundaryPair j₁ j₂ x y := by
  constructor
  · intro h
    have hX : T2Space X := (isOpenEmbedding_ι₁ hj₁ hj₂).isEmbedding.t2Space
    have hY : T2Space Y := (isOpenEmbedding_ι₂ hj₁ hj₂).isEmbedding.t2Space
    exact ⟨hX, hY, (t2Space_iff_forall_not_isCorrespondingBoundaryPair hj₁ hj₂).1 h⟩
  · rintro ⟨hX, hY, h⟩
    exact (t2Space_iff_forall_not_isCorrespondingBoundaryPair hj₁ hj₂).2 h

variable (j₁ j₂) in
/-- Chruściel's `H` (proof of Lemma 3.3): the points `p` of `X` whose image `[p]` is a
non-Hausdorff point of the gluing. -/
def nonHausdorffLeft : Set X := ι₁ j₁ j₂ ⁻¹' nonHausdorffPoints (Gluing j₁ j₂)

/-- For Hausdorff `X`, `Y`: Chruściel's `H` is Sbierski's `C`, the points having a corresponding
boundary point. -/
theorem nonHausdorffLeft_eq [T2Space X] [T2Space Y] (hj₁ : IsOpenEmbedding j₁)
    (hj₂ : IsOpenEmbedding j₂) : nonHausdorffLeft j₁ j₂ = correspondingLeft j₁ j₂ := by
  ext x
  simp only [nonHausdorffLeft, nonHausdorffPoints, mem_preimage, mem_setOf_eq, correspondingLeft]
  constructor
  · rintro ⟨z, hne, hns⟩
    rcases exists_ι z with ⟨x', rfl⟩ | ⟨y, rfl⟩
    · rw [disjoint_nhds_ι₁_ι₁ hj₁ hj₂, disjoint_nhds_nhds, not_not] at hns
      exact absurd (by rw [hns]) hne
    · exact ⟨y, (isCorrespondingBoundaryPair_iff hj₁ hj₂).2 ⟨hne.symm, hns⟩⟩
  · rintro ⟨y, h⟩
    obtain ⟨hne, hns⟩ := (isCorrespondingBoundaryPair_iff hj₁ hj₂).1 h
    exact ⟨_, hne.symm, hns⟩

/-- "We have just seen that `H ⊂ ∂O`" (Chruściel, proof of Lemma 3.3). -/
theorem nonHausdorffLeft_subset_frontier [T2Space X] [T2Space Y] (hj₁ : IsOpenEmbedding j₁)
    (hj₂ : IsOpenEmbedding j₂) : nonHausdorffLeft j₁ j₂ ⊆ frontier (range j₁) := by
  rw [nonHausdorffLeft_eq hj₁ hj₂]
  exact correspondingLeft_subset_frontier

/-- **Assertion 3, a true form for `H`**: `H` is closed when the corresponding points over a
neighbourhood of each boundary point stay in a compact set (the hypothesis Chruściel's "by
elementary topology" omits; `not_isClosed_nonHausdorffLeft_expGluing` shows it cannot be
dropped). -/
theorem isClosed_nonHausdorffLeft_of_isCompact [T2Space X] [T2Space Y] (hj₁ : IsOpenEmbedding j₁)
    (hj₂ : IsOpenEmbedding j₂)
    (hK : ∀ x ∈ frontier (range j₁), ∃ V ∈ 𝓝 x, ∃ K : Set Y, IsCompact K ∧
      ∀ x' ∈ V, ∀ y, IsCorrespondingBoundaryPair j₁ j₂ x' y → y ∈ K) :
    IsClosed (nonHausdorffLeft j₁ j₂) := by
  rw [nonHausdorffLeft_eq hj₁ hj₂]
  exact isClosed_correspondingLeft_of_isCompact hK

theorem isClosed_nonHausdorffLeft [T2Space X] [T2Space Y] [CompactSpace Y]
    (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) : IsClosed (nonHausdorffLeft j₁ j₂) := by
  rw [nonHausdorffLeft_eq hj₁ hj₂]
  exact isClosed_correspondingLeft

end GluingSep

/-! ### The counterexample: `H` need not be closed -/

/-- `j₁ (a, c) = (a, eᶜ)`, from `(0, ∞) × ℝ` onto the open quadrant of `ℝ²`. -/
noncomputable def expLeft : ↥(Ioi (0 : ℝ)) × ℝ → ℝ × ℝ := Prod.map Subtype.val Real.exp

/-- `j₂ (a, c) = (a, c)`, from `(0, ∞) × ℝ` onto the open half-plane of `ℝ²`. -/
def halfPlaneInc : ↥(Ioi (0 : ℝ)) × ℝ → ℝ × ℝ := Prod.map Subtype.val id

theorem isOpenEmbedding_expLeft : IsOpenEmbedding expLeft := by
  exact isOpen_Ioi.isOpenEmbedding_subtypeVal.prodMap Real.isOpenEmbedding_exp

theorem isOpenEmbedding_halfPlaneInc : IsOpenEmbedding halfPlaneInc := by
  exact isOpen_Ioi.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id

theorem expGluing_mem_nonHausdorffLeft (c : ℝ) :
    ((0 : ℝ), Real.exp c) ∈ nonHausdorffLeft expLeft halfPlaneInc := by
  rw [nonHausdorffLeft_eq isOpenEmbedding_expLeft isOpenEmbedding_halfPlaneInc]
  refine ⟨((0 : ℝ), c), isCorrespondingBoundaryPair_of_mem_closure_graph ?_ ?_ ?_⟩
  · rintro ⟨⟨a, b⟩, h⟩
    exact (ne_of_gt a.2) (congrArg Prod.fst h)
  · rintro ⟨⟨a, b⟩, h⟩
    exact (ne_of_gt a.2) (congrArg Prod.fst h)
  · have h0 : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact self_mem_Ici
    refine map_mem_closure (f := fun t : ℝ => ((t, Real.exp c), (t, c))) (by fun_prop) h0 ?_
    intro t ht
    exact ⟨(⟨t, ht⟩, c), rfl⟩

theorem expGluing_origin_not_mem : ((0 : ℝ), (0 : ℝ)) ∉ nonHausdorffLeft expLeft halfPlaneInc := by
  rw [nonHausdorffLeft_eq isOpenEmbedding_expLeft isOpenEmbedding_halfPlaneInc]
  rintro ⟨y, h⟩
  have hcl := forall_nhds_iff_mem_closure_graph.1 h.2.2
  have hS : IsClosed {p : (ℝ × ℝ) × (ℝ × ℝ) | p.1.2 = Real.exp p.2.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hsub : graph expLeft halfPlaneInc ⊆ {p : (ℝ × ℝ) × (ℝ × ℝ) | p.1.2 = Real.exp p.2.2} := by
    rintro _ ⟨w, rfl⟩
    rfl
  have h0 : (0 : ℝ) = Real.exp y.2 := hS.closure_subset_iff.2 hsub hcl
  exact (Real.exp_pos y.2).ne' h0.symm

theorem expGluing_origin_mem_closure :
    ((0 : ℝ), (0 : ℝ)) ∈ closure (nonHausdorffLeft expLeft halfPlaneInc) := by
  have h0 : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact self_mem_Ici
  refine map_mem_closure (f := fun t : ℝ => ((0 : ℝ), t)) (by fun_prop) h0 ?_
  intro t ht
  have := expGluing_mem_nonHausdorffLeft (Real.log t)
  rwa [Real.exp_log ht] at this

/-- **Assertion 3 is false as stated in pure topology**: two copies of `ℝ²` glued along open
embeddings of `(0, ∞) × ℝ`, and Chruściel's `H` is not closed. -/
theorem not_isClosed_nonHausdorffLeft_expGluing :
    ¬ IsClosed (nonHausdorffLeft expLeft halfPlaneInc) := by
  intro h
  exact expGluing_origin_not_mem (h.closure_subset expGluing_origin_mem_closure)

/-- Nor are the non-Hausdorff points of the gluing itself closed in the gluing. -/
theorem not_isClosed_nonHausdorffPoints_expGluing :
    ¬ IsClosed (nonHausdorffPoints (Gluing expLeft halfPlaneInc)) := fun h =>
  not_isClosed_nonHausdorffLeft_expGluing (h.preimage continuous_ι₁)

/-- The line with two origins (`Causal.Gluing.LineTwoOrigins`) has a corresponding boundary pair:
the two origins. -/
theorem lineTwoOrigins_isCorrespondingBoundaryPair :
    IsCorrespondingBoundaryPair lineTwoOriginsInc lineTwoOriginsInc (0 : ℝ) (0 : ℝ) := by
  have h := lineTwoOrigins_mem_Cdist
  rw [← correspondingPairs_eq_Cdist isOpenEmbedding_lineTwoOriginsInc
    isOpenEmbedding_lineTwoOriginsInc] at h
  exact h

/-! ### A second counterexample: corresponding points need not be unique, and `C` need not be
open in `∂O` -/

/-- The shear `(a, c) ↦ (a, a c)` of `(0, ∞) × ℝ`, a homeomorphism. -/
noncomputable def shear : (↥(Ioi (0 : ℝ)) × ℝ) ≃ₜ (↥(Ioi (0 : ℝ)) × ℝ) where
  toFun p := (p.1, (p.1 : ℝ) * p.2)
  invFun p := (p.1, p.2 / (p.1 : ℝ))
  left_inv p := Prod.ext rfl (mul_div_cancel_left₀ p.2 (ne_of_gt p.1.2))
  right_inv p := Prod.ext rfl (mul_div_cancel₀ p.2 (ne_of_gt p.1.2))
  continuous_toFun := by fun_prop
  continuous_invFun :=
    continuous_fst.prodMk (continuous_snd.div (continuous_subtype_val.comp continuous_fst)
      fun p => ne_of_gt p.1.2)

/-- `j₁ (a, c) = (a, a c)`, from `(0, ∞) × ℝ` onto the open half-plane of `ℝ²`. -/
noncomputable def shearLeft : ↥(Ioi (0 : ℝ)) × ℝ → ℝ × ℝ := halfPlaneInc ∘ shear

theorem shearLeft_apply (a : ↥(Ioi (0 : ℝ))) (c : ℝ) : shearLeft (a, c) = ((a : ℝ), a * c) :=
  rfl

theorem isOpenEmbedding_shearLeft : IsOpenEmbedding shearLeft :=
  isOpenEmbedding_halfPlaneInc.comp shear.isOpenEmbedding

/-- The graph of the shear gluing lies in `{((a, b), (a', c)) | b = a c}`. -/
theorem closure_graph_shear_subset :
    closure (graph shearLeft halfPlaneInc) ⊆ {p : (ℝ × ℝ) × (ℝ × ℝ) | p.1.2 = p.1.1 * p.2.2} := by
  refine (isClosed_eq (by fun_prop) (by fun_prop)).closure_subset_iff.2 ?_
  rintro _ ⟨w, rfl⟩
  rfl

/-- **The origin has a continuum of corresponding boundary points**: `(0, 0)` corresponds to
`(0, c)` for every `c` (Sbierski's Prop 3.7, "at most one corresponding boundary point", is not a
fact of topology). -/
theorem shearGluing_isCorrespondingBoundaryPair (c : ℝ) :
    IsCorrespondingBoundaryPair shearLeft halfPlaneInc ((0 : ℝ), (0 : ℝ)) ((0 : ℝ), c) := by
  refine isCorrespondingBoundaryPair_of_mem_closure_graph ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, h⟩
    exact (ne_of_gt a.2) (congrArg Prod.fst h)
  · rintro ⟨⟨a, b⟩, h⟩
    exact (ne_of_gt a.2) (congrArg Prod.fst h)
  · have h0 : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact self_mem_Ici
    have hf : Continuous fun t : ℝ => ((t, t * c), (t, c)) := by fun_prop
    have := map_mem_closure hf h0 (t := graph shearLeft halfPlaneInc)
      fun t ht => ⟨(⟨t, ht⟩, c), rfl⟩
    simpa using this

theorem shearGluing_not_unique :
    ∃ y y', y ≠ y' ∧ IsCorrespondingBoundaryPair shearLeft halfPlaneInc ((0 : ℝ), (0 : ℝ)) y ∧
      IsCorrespondingBoundaryPair shearLeft halfPlaneInc ((0 : ℝ), (0 : ℝ)) y' :=
  ⟨((0 : ℝ), 0), ((0 : ℝ), 1), by simp, shearGluing_isCorrespondingBoundaryPair 0,
    shearGluing_isCorrespondingBoundaryPair 1⟩

/-- `(0, t)` lies on `∂ j₁(W)`. -/
theorem shearGluing_mem_frontier (t : ℝ) : ((0 : ℝ), t) ∈ frontier (range shearLeft) := by
  have hnot : ((0 : ℝ), t) ∉ range shearLeft := by
    rintro ⟨⟨a, b⟩, h⟩
    exact (ne_of_gt a.2) (congrArg Prod.fst h)
  refine ⟨?_, fun hi => hnot (interior_subset hi)⟩
  have h0 : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact self_mem_Ici
  refine map_mem_closure (f := fun s : ℝ => (s, t)) (by fun_prop) h0 fun s hs => ?_
  refine ⟨(⟨s, hs⟩, t / s), ?_⟩
  rw [shearLeft_apply]
  exact Prod.ext rfl (mul_div_cancel₀ t (ne_of_gt hs))

/-- The only point of `∂ j₁(W)` with a corresponding boundary point is the origin. -/
theorem shearGluing_correspondingLeft :
    correspondingLeft shearLeft halfPlaneInc = {((0 : ℝ), (0 : ℝ))} := by
  ext ⟨a, b⟩
  simp only [correspondingLeft, mem_setOf_eq, mem_singleton_iff]
  constructor
  · rintro ⟨y, h⟩
    have hcl := closure_graph_shear_subset (forall_nhds_iff_mem_closure_graph.1 h.2.2)
    have ha : a = 0 := by
      by_contra ha'
      have hfr := h.1
      rw [isOpenEmbedding_shearLeft.isOpen_range.frontier_eq] at hfr
      have hcl1 : ((a, b) : ℝ × ℝ) ∈ closure (range shearLeft) := hfr.1
      have hsub : range shearLeft ⊆ {p : ℝ × ℝ | 0 ≤ p.1} := by
        rintro _ ⟨⟨a', c'⟩, rfl⟩
        exact le_of_lt (show (0 : ℝ) < (a' : ℝ) from a'.2)
      have hle : 0 ≤ a :=
        (isClosed_le continuous_const continuous_fst).closure_subset_iff.2 hsub hcl1
      have hpos : 0 < a := lt_of_le_of_ne hle (Ne.symm ha')
      exact hfr.2 ⟨(⟨a, hpos⟩, b / a), Prod.ext rfl (mul_div_cancel₀ b ha')⟩
    subst ha
    have hb : b = 0 * y.2 := hcl
    rw [hb, zero_mul]
  · intro h
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, shearGluing_isCorrespondingBoundaryPair 0⟩

/-- **`C` need not be open in `∂O`** (Sbierski Lemma 3.8, ETT `prop:C_connexe` first half, are not
facts of topology): no open set of `ℝ²` meets `∂ j₁(W)` in `C = {(0, 0)}`. -/
theorem shearGluing_not_isOpen_in_frontier :
    ¬ ∃ O : Set (ℝ × ℝ), IsOpen O ∧
      O ∩ frontier (range shearLeft) = correspondingLeft shearLeft halfPlaneInc := by
  rintro ⟨O, hO, hOC⟩
  rw [shearGluing_correspondingLeft] at hOC
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ O := (hOC.symm ▸ mem_singleton _ : _ ∈ O ∩ _).1
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ((0 : ℝ), t) ∈ O :=
    (Continuous.tendsto (f := fun t : ℝ => ((0 : ℝ), t)) (by fun_prop) 0) (hO.mem_nhds h0)
  obtain ⟨t, ht, htne⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := ({0}ᶜ : Set ℝ)))).exists
  have hmem : ((0 : ℝ), t) ∈ O ∩ frontier (range shearLeft) := ⟨ht, shearGluing_mem_frontier t⟩
  rw [hOC, mem_singleton_iff, Prod.mk.injEq] at hmem
  exact htne (mem_singleton_iff.2 hmem.2)

end Gluing

/-! ### The family version -/

namespace CBG.FamilyGlueData

variable {I : Type v} {M : I → Type u} [∀ i, TopologicalSpace (M i)] (D : FamilyGlueData I M)

/-- In the gluing of the family, `x ∈ M i` and `y ∈ M j` have distinct non-separated images iff
they are corresponding boundary points of `U i j` (Hausdorff pieces). -/
theorem isCorrespondingBoundaryPair_iff [∀ i, T2Space (M i)] {i j : I} {x : M i} {y : M j} :
    Gluing.IsCorrespondingBoundaryPair (Subtype.val : D.U i j → M i) (D.φ i j) x y ↔
      D.ι i x ≠ D.ι j y ∧ ¬ Disjoint (𝓝 (D.ι i x)) (𝓝 (D.ι j y)) := by
  have he := D.isOpenEmbedding_pair i j
  rw [Gluing.isCorrespondingBoundaryPair_iff (D.isOpenEmbedding_val i j) (D.isOpenEmbedding_φ i j),
    ← D.pair_ι₁ i j x, ← D.pair_ι₂ i j y, ← he.map_nhds_eq, ← he.map_nhds_eq,
    disjoint_map he.injective, he.injective.ne_iff]

/-- **Assertion 2** (Sbierski Thm 2.8): with Hausdorff pieces, the gluing of the family is
Hausdorff iff no pair of members has corresponding boundary points. -/
theorem t2Space_iff_forall_not_isCorrespondingBoundaryPair [∀ i, T2Space (M i)] :
    T2Space D.Glued ↔ ∀ i j (x : M i) (y : M j),
      ¬ Gluing.IsCorrespondingBoundaryPair (Subtype.val : D.U i j → M i) (D.φ i j) x y := by
  rw [D.t2Space_iff]
  exact forall_congr' fun i => forall_congr' fun j =>
    Gluing.t2Space_iff_forall_not_isCorrespondingBoundaryPair (D.isOpenEmbedding_val i j)
      (D.isOpenEmbedding_φ i j)

/-- **Assertion 2, with no separation hypothesis.** -/
theorem t2Space_iff_t2Space_and_forall_not_isCorrespondingBoundaryPair :
    T2Space D.Glued ↔ (∀ i, T2Space (M i)) ∧ ∀ i j (x : M i) (y : M j),
      ¬ Gluing.IsCorrespondingBoundaryPair (Subtype.val : D.U i j → M i) (D.φ i j) x y := by
  constructor
  · intro h
    have hM : ∀ i, T2Space (M i) := fun i => (D.isOpenEmbedding_ι i).isEmbedding.t2Space
    exact ⟨hM, D.t2Space_iff_forall_not_isCorrespondingBoundaryPair.1 h⟩
  · rintro ⟨hM, h⟩
    exact D.t2Space_iff_forall_not_isCorrespondingBoundaryPair.2 h

/-- The non-Hausdorff points of the family gluing seen in `M i`: the points of `M i` having a
corresponding boundary point in some `M j`. -/
theorem preimage_ι_nonHausdorffPoints [∀ i, T2Space (M i)] (i : I) :
    D.ι i ⁻¹' nonHausdorffPoints D.Glued =
      ⋃ j, Gluing.correspondingLeft (Subtype.val : D.U i j → M i) (D.φ i j) := by
  ext x
  simp only [mem_preimage, nonHausdorffPoints, mem_setOf_eq, mem_iUnion, Gluing.correspondingLeft]
  constructor
  · rintro ⟨z, hne, hns⟩
    obtain ⟨j, y, rfl⟩ := D.exists_ι z
    exact ⟨j, y, D.isCorrespondingBoundaryPair_iff.2 ⟨hne.symm, hns⟩⟩
  · rintro ⟨j, y, h⟩
    obtain ⟨hne, hns⟩ := D.isCorrespondingBoundaryPair_iff.1 h
    exact ⟨_, hne.symm, hns⟩

theorem preimage_ι_nonHausdorffPoints_subset [∀ i, T2Space (M i)] (i : I) :
    D.ι i ⁻¹' nonHausdorffPoints D.Glued ⊆ ⋃ j, frontier (D.U i j : Set (M i)) := by
  rw [D.preimage_ι_nonHausdorffPoints i]
  refine iUnion_mono fun j => Gluing.correspondingLeft_subset_frontier.trans ?_
  rw [Subtype.range_coe]

/-- **A directed family of Hausdorff spaces glues to a Hausdorff space** (Graf–Ling Lemma 29,
Chruściel's directed union): if any two members embed wholly in a third. -/
theorem t2Space_of_directed [∀ i, T2Space (M i)]
    (hdir : ∀ i j, ∃ k, D.U i k = ⊤ ∧ D.U j k = ⊤) : T2Space D.Glued := by
  rw [t2Space_iff_disjoint_nhds]
  intro z z' hzz'
  obtain ⟨i, x, rfl⟩ := D.exists_ι z
  obtain ⟨j, y, rfl⟩ := D.exists_ι z'
  obtain ⟨k, hik, hjk⟩ := hdir i j
  have hx : x ∈ D.U i k := by rw [hik]; trivial
  have hy : y ∈ D.U j k := by rw [hjk]; trivial
  have e₁ : D.ι i x = D.ι k (D.φ i k ⟨x, hx⟩) := (D.ι_φ i k ⟨x, hx⟩).symm
  have e₂ : D.ι j y = D.ι k (D.φ j k ⟨y, hy⟩) := (D.ι_φ j k ⟨y, hy⟩).symm
  rw [e₁, e₂] at hzz' ⊢
  rw [← (D.isOpenEmbedding_ι k).map_nhds_eq, ← (D.isOpenEmbedding_ι k).map_nhds_eq,
    disjoint_map (D.injective_ι k), disjoint_nhds_nhds]
  exact fun h => hzz' (congrArg _ h)

/-- In a directed family of Hausdorff spaces no pair of members has corresponding boundary
points. -/
theorem forall_not_isCorrespondingBoundaryPair_of_directed [∀ i, T2Space (M i)]
    (hdir : ∀ i j, ∃ k, D.U i k = ⊤ ∧ D.U j k = ⊤) (i j : I) (x : M i) (y : M j) :
    ¬ Gluing.IsCorrespondingBoundaryPair (Subtype.val : D.U i j → M i) (D.φ i j) x y :=
  haveI := D.t2Space_of_directed hdir
  D.t2Space_iff_forall_not_isCorrespondingBoundaryPair.1 this i j x y

/-- A totally ordered family (Graf–Ling: `N_α ≲ N_β` or `N_β ≲ N_α`) is directed. -/
theorem t2Space_of_total [∀ i, T2Space (M i)]
    (htot : ∀ i j, D.U i j = ⊤ ∨ D.U j i = ⊤) : T2Space D.Glued := by
  refine D.t2Space_of_directed fun i j => ?_
  rcases htot i j with h | h
  · exact ⟨j, h, D.U_self j⟩
  · exact ⟨i, D.U_self i, h⟩

end CBG.FamilyGlueData

end Causal
