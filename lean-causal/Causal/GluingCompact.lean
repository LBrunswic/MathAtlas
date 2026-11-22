import Causal.GluingHausdorff

/-!
# Corresponding points staying locally in a compact set: DEC-160's localisation property of a gluing

Programme target `T-abs-gluing-compact-def` (`programme/roadmap.toml`; layer 1, pure topology, no
paper label, no causality), on the ruling DEC-160 (OQ-40): of Chruściel's "H is closed", keep both
the pair form (no hypothesis) and the compact form, and make the compactness a localisation
property of the ladder. This file gives it a name and states the two forms against it.

* **`T-abs-gluing-compact-def/1-def`** — `Gluing.CorrespondingCompact j₁ j₂`, a predicate of the
  gluing datum `j₁ : W → X`, `j₂ : W → Y` alone: every point of `∂ j₁(W)` has a neighbourhood `V`
  and a compact `K ⊆ Y` holding every point corresponding to a point of `V`. It is exactly the
  inline hypothesis of `Gluing.isClosed_nonHausdorffLeft_of_isCompact`
  (`correspondingCompact_iff`, `Iff.rfl`); its other forms: at every point of `X`
  (`correspondingCompact_iff_forall`), and, for `X` weakly locally compact, *the projection of the
  corresponding pairs onto `X` is a proper map* (`correspondingCompact_iff_isProperMap`).
* **`T-abs-gluing-compact-def/2-compact-form`** — the theorem restated with it, beside the old
  one: `isClosed_nonHausdorffLeft_of_correspondingCompact` (and Sbierski's `C`,
  `isClosed_correspondingLeft_of_correspondingCompact`); with the property on both sides, the
  non-Hausdorff points of the gluing are closed
  (`isClosed_nonHausdorffPoints_of_correspondingCompact`); for a family,
  `CBG.FamilyGlueData.isClosed_preimage_ι_nonHausdorffPoints` (boundaries locally finite) and
  `…_of_finite`.
* **`T-abs-gluing-compact-def/3-pair-form`** — the pair form against it: the pairs are closed with
  no hypothesis, and the property is what makes their projection closed
  (`CorrespondingCompact.isClosed_image_fst`, `CorrespondingCompact.isProperMap`); the two forms in
  one statement, `isClosed_correspondingPairs_and_nonHausdorffLeft`. The step of ETT's proof of
  `prop:Cauchy_point_min` that uses `prop:C_connexe` (`ETT.tex:2303`, a connected piece of
  `∂ j₁(N)` meeting `C₁` lies in `C₁`) holds under the property
  (`CorrespondingCompact.subset_correspondingLeft_of_isPreconnected`) and fails as topology
  without it, both halves of `prop:C_connexe` holding (`expGluing_not_subset_correspondingLeft`).
* **`T-abs-gluing-compact-def/4-witnesses`** — the property fails and `H` is not closed
  (`expGluing_witness`, `not_correspondingCompact_expGluing`), while there the `Y`-side property
  holds (`correspondingCompact_expGluing_swap`); it fails and `H` is closed (`shearGluing_witness`:
  strictly stronger than the closedness of `H`); it holds, with a corresponding pair, on the line
  with two origins (`correspondingCompact_lineTwoOrigins`); it holds when `Y` is compact,
  `∂ j₂(W)` is compact, the gluing is Hausdorff, or the correspondence is locally a continuous map
  near the closure of `C`, on a locally compact `X` (`correspondingCompact_of_compactSpace`,
  `…_of_isCompact_frontier`, `…_of_t2Space`, `…_of_continuousOn`); a continuous map near every
  point of `C` itself is not enough (`expGluing_continuous_extension_witness`).

> Let H denote the set of non-Hausdorff points p in M1, thus p′ = iM1(p) ≡ [p] is
> non-Hausdorff in M′, where iM1 denotes the embedding of M1 into M′. By elementary topology H is
> closed (as its complement is open), and we have just seen that H ⊂ ∂O.
> (Chruściel 1112.5779, proof of Lemma 3.3, `chrusciel2013maximal.txt:877–880`)

> OQ-40 gluing: both the pair form (no hypothesis) and the compact form; that local compactness
> becomes a ladder localisation property; finding against Chruściel 1112.5779 Lemma 3.3 recorded.
> (DEC-160, `registers/DECISIONS.md:171`)

## Hypothesis checklist

| source hypothesis | here |
|---|---|
| Chruściel: `M₁`, `M₂` Hausdorff manifolds, `O` open, `Ψ_O` an injective isometry | ⚠ weakened: any spaces and maps `j₁`, `j₂` in the predicate; open embeddings and `[T2Space X] [T2Space Y]` only where `H` is read in the gluing |
| Chruściel: `H` closed "by elementary topology" | ⚠ strengthened (the finding of `Causal.GluingHausdorff`, ruled by DEC-160): `CorrespondingCompact j₁ j₂` added; it cannot be dropped (`expGluing_witness`) |

## SCOPE (disclosed)

* **Arguments.** The predicate takes the gluing datum only, `j₁ : W → X`, `j₂ : W → Y` (with the
  topologies of `X` and `Y`; none on `W`, which `IsCorrespondingBoundaryPair` does not read). Open
  embeddings are not part of it: they are hypotheses of the theorems that read `H` in the gluing.
* **One side.** It is the `X`-side property (Chruściel's `M₁`, the side of `nonHausdorffLeft`). The
  `Y`-side property is `CorrespondingCompact j₂ j₁` (`isCorrespondingBoundaryPair_swap` turns the
  pairs around; `preimage_ι₂_nonHausdorffPoints` is the `Y`-side `H`). Neither side implies the
  other: on the exponential datum the `X` side fails and the `Y` side holds, so the swapped datum
  has the `X` side and lacks the `Y` side.
* **Not a consequence of the gluing, and not the closedness of `H`.** The shear gluing has `H`
  closed (one point) and the property false (that point has a whole line of corresponding points),
  so the compact form's converse fails. The property is a hypothesis on the gluing datum, not on one
  causality; which ladder sort it takes is the keeper's (T-lad-gluing-nodes).
* **Extension at corresponding points.** The evidence of T-lad-gluing-nodes
  (`programme/roadmap.toml`) reads the property, in the CBG setting, as following from A3's
  continuous extension. As topology it does not: on the exponential gluing `j₂ ∘ j₁⁻¹` extends
  continuously across every point of `C` and the property fails at a point of `closure C \ C`
  (`expGluing_continuous_extension_witness`). What does give it is a continuous map near every
  point of `closure C` (`correspondingCompact_of_continuousOn`), so the closedness of `C` is again
  what is at stake.
* **The proper-map form** needs `X` weakly locally compact for `⇐`; `⇒` has no hypothesis. No
  metric notion is in a statement; boundedness in `ℝ` appears only inside the shear proof.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Topology Filter Function TopologicalSpace

universe u v w

namespace Gluing

variable {X : Type u} {Y : Type v} {W : Type w}

section Def

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- **The corresponding points stay locally in a compact set** (DEC-160's localisation property of
a gluing; the ladder's `corresponding_compact`). For the gluing datum `j₁ : W → X`, `j₂ : W → Y`:
every boundary point `x` of `j₁(W)` in `X` has a neighbourhood `V` and a compact set `K ⊆ Y` such
that every point `y` of `∂ j₂(W)` corresponding to a point `x'` of `V` (Sbierski Def 3.5,
`IsCorrespondingBoundaryPair j₁ j₂ x' y`) lies in `K`. In words: as the points of `∂ j₁(W)`
converge in `X`, their corresponding points cannot escape every compact set of `Y`. For `X` weakly
locally compact it says the projection of the corresponding pairs onto `X` is proper
(`correspondingCompact_iff_isProperMap`). It is the inline hypothesis of
`isClosed_nonHausdorffLeft_of_isCompact`, under which Chruściel's `H` is closed; the `Y`-side
property is `CorrespondingCompact j₂ j₁`. -/
def CorrespondingCompact (j₁ : W → X) (j₂ : W → Y) : Prop :=
  ∀ x ∈ frontier (range j₁), ∃ V ∈ 𝓝 x, ∃ K : Set Y, IsCompact K ∧
    ∀ x' ∈ V, ∀ y, IsCorrespondingBoundaryPair j₁ j₂ x' y → y ∈ K

variable {j₁ : W → X} {j₂ : W → Y}

/-- The predicate is exactly the inline hypothesis of `isClosed_nonHausdorffLeft_of_isCompact`. -/
theorem correspondingCompact_iff :
    CorrespondingCompact j₁ j₂ ↔ ∀ x ∈ frontier (range j₁), ∃ V ∈ 𝓝 x, ∃ K : Set Y,
      IsCompact K ∧ ∀ x' ∈ V, ∀ y, IsCorrespondingBoundaryPair j₁ j₂ x' y → y ∈ K :=
  Iff.rfl

/-- Corresponding boundary points, read from the other side. -/
theorem isCorrespondingBoundaryPair_swap {x : X} {y : Y} :
    IsCorrespondingBoundaryPair j₂ j₁ y x ↔ IsCorrespondingBoundaryPair j₁ j₂ x y := by
  constructor
  · rintro ⟨hy, hx, h⟩
    exact ⟨hx, hy, fun V hV V' hV' => (h V' hV' V hV).imp fun _ hw => ⟨hw.2, hw.1⟩⟩
  · rintro ⟨hx, hy, h⟩
    exact ⟨hy, hx, fun V hV V' hV' => (h V' hV' V hV).imp fun _ hw => ⟨hw.2, hw.1⟩⟩

/-- The restriction to boundary points is cosmetic: the property holds at every point of `X`. -/
theorem correspondingCompact_iff_forall :
    CorrespondingCompact j₁ j₂ ↔ ∀ x : X, ∃ V ∈ 𝓝 x, ∃ K : Set Y, IsCompact K ∧
      ∀ x' ∈ V, ∀ y, IsCorrespondingBoundaryPair j₁ j₂ x' y → y ∈ K := by
  constructor
  · intro h x
    by_cases hx : x ∈ frontier (range j₁)
    · exact h x hx
    · refine ⟨(frontier (range j₁))ᶜ, isClosed_frontier.isOpen_compl.mem_nhds hx, ∅,
        isCompact_empty, ?_⟩
      intro x' hx' y hy
      exact absurd hy.1 hx'
  · intro h x _
    exact h x

end Def

/-! ### The pair form against the property -/

section PairForm

variable [TopologicalSpace X] [TopologicalSpace Y] {j₁ : W → X} {j₂ : W → Y}

/-- **Under the property, a closed set of corresponding pairs projects to a closed set of `X`.**
The pairs themselves are closed with no hypothesis (`isClosed_correspondingPairs`). -/
theorem CorrespondingCompact.isClosed_image_fst (h : CorrespondingCompact j₁ j₂)
    {S : Set (X × Y)} (hS : IsClosed S) (hSC : S ⊆ correspondingPairs j₁ j₂) :
    IsClosed (Prod.fst '' S) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  have hSf : Prod.fst '' S ⊆ frontier (range j₁) := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hSC hp).1
  have hxf : x ∈ frontier (range j₁) := closure_minimal hSf isClosed_frontier hx
  obtain ⟨V, hV, K, hKc, hVK⟩ := h x hxf
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  let S' : Set (X × K) := {p | (p.1, (p.2 : Y)) ∈ S}
  have hS' : IsClosed S' := hS.preimage (continuous_id.prodMap continuous_subtype_val)
  have hcl : IsClosed (Prod.fst '' S') := isClosedMap_fst_of_compactSpace _ hS'
  have hsub : Prod.fst '' S ∩ V ⊆ Prod.fst '' S' := by
    rintro x' ⟨⟨p, hp, rfl⟩, hx'V⟩
    exact ⟨(p.1, ⟨p.2, hVK p.1 hx'V p.2 (hSC hp)⟩), hp, rfl⟩
  have hx' : x ∈ closure (Prod.fst '' S ∩ V) := by
    rw [mem_closure_iff_nhds] at hx ⊢
    intro t ht
    obtain ⟨z, ⟨hzt, hzV⟩, hzC⟩ := hx (t ∩ V) (inter_mem ht hV)
    exact ⟨z, hzt, hzC, hzV⟩
  obtain ⟨⟨x', y⟩, hy, rfl⟩ := hcl.closure_subset_iff.2 hsub hx'
  exact ⟨(x', (y : Y)), hy, rfl⟩

/-- **Under the property, the projection of the corresponding pairs onto `X` is proper.** -/
theorem CorrespondingCompact.isProperMap (h : CorrespondingCompact j₁ j₂) :
    IsProperMap (fun p : correspondingPairs j₁ j₂ => (p : X × Y).1) := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨continuous_fst.comp continuous_subtype_val, ?_, fun x => ?_⟩
  · intro F hF
    have hemb : IsClosedEmbedding (Subtype.val : correspondingPairs j₁ j₂ → X × Y) :=
      isClosed_correspondingPairs.isClosedEmbedding_subtypeVal
    have := h.isClosed_image_fst (hemb.isClosedMap F hF) (by rintro _ ⟨p, -, rfl⟩; exact p.2)
    rwa [image_image] at this
  · rw [Subtype.isCompact_iff]
    have heq : (Subtype.val '' ((fun p : correspondingPairs j₁ j₂ => (p : X × Y).1) ⁻¹' {x})) =
        {x} ×ˢ {y | IsCorrespondingBoundaryPair j₁ j₂ x y} := by
      ext ⟨a, b⟩
      constructor
      · rintro ⟨⟨⟨a', b'⟩, hp⟩, hpx, he⟩
        simp only [mem_preimage, mem_singleton_iff] at hpx
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        subst hpx
        exact ⟨rfl, hp⟩
      · rintro ⟨ha, hb⟩
        rw [mem_singleton_iff] at ha
        subst ha
        exact ⟨⟨(a, b), hb⟩, rfl, rfl⟩
    rw [heq]
    refine isCompact_singleton.prod ?_
    by_cases hx : x ∈ frontier (range j₁)
    · obtain ⟨V, hV, K, hK, hVK⟩ := h x hx
      refine hK.of_isClosed_subset ?_ fun y hy => hVK x (mem_of_mem_nhds hV) y hy
      exact isClosed_correspondingPairs.preimage (Continuous.prodMk_right x)
    · convert isCompact_empty
      ext y
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact fun hy => hx hy.1

/-- **For `X` weakly locally compact, the property is the properness of the projection of the
corresponding pairs onto `X`.** -/
theorem correspondingCompact_iff_isProperMap [WeaklyLocallyCompactSpace X] :
    CorrespondingCompact j₁ j₂ ↔
      IsProperMap (fun p : correspondingPairs j₁ j₂ => (p : X × Y).1) := by
  refine ⟨CorrespondingCompact.isProperMap, fun hp x _ => ?_⟩
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x
  refine ⟨N, hN, (fun p : correspondingPairs j₁ j₂ => (p : X × Y).2) ''
    ((fun p : correspondingPairs j₁ j₂ => (p : X × Y).1) ⁻¹' N),
    (hp.isCompact_preimage hNc).image (continuous_snd.comp continuous_subtype_val), ?_⟩
  intro x' hx' y hy
  exact ⟨⟨(x', y), hy⟩, hx', rfl⟩

/-- **Sbierski's `C` is closed under the property** (`isClosed_correspondingLeft_of_isCompact`
restated). -/
theorem isClosed_correspondingLeft_of_correspondingCompact (h : CorrespondingCompact j₁ j₂) :
    IsClosed (correspondingLeft j₁ j₂) := by
  exact isClosed_correspondingLeft_of_isCompact h

/-- **The connectedness step of ETT's proof of `prop:Cauchy_point_min`**, under the property
(`ETT.tex:2303`: "Proposition prop:C_connexe then shows that c_n is entirely contained in C_1"): if
Sbierski's `C` is open in `∂ j₁(W)` (the first half of `prop:C_connexe`), a preconnected subset of
`∂ j₁(W)` meeting `C` lies in `C`. Without the property the step fails as topology, both halves of
`prop:C_connexe` holding (`expGluing_not_subset_correspondingLeft`). -/
theorem CorrespondingCompact.subset_correspondingLeft_of_isPreconnected
    (h : CorrespondingCompact j₁ j₂)
    (hopen : ∃ O : Set X, IsOpen O ∧ O ∩ frontier (range j₁) = correspondingLeft j₁ j₂)
    {c : Set X} (hc : IsPreconnected c) (hcf : c ⊆ frontier (range j₁))
    (hmeet : (c ∩ correspondingLeft j₁ j₂).Nonempty) : c ⊆ correspondingLeft j₁ j₂ := by
  obtain ⟨O, hO, hOC⟩ := hopen
  have hcl := isClosed_correspondingLeft_of_correspondingCompact h
  have hcov : c ⊆ O ∪ (correspondingLeft j₁ j₂)ᶜ := by
    intro z hz
    by_cases hzC : z ∈ correspondingLeft j₁ j₂
    · left
      rw [← hOC] at hzC
      exact hzC.1
    · right
      exact hzC
  have hdis : c ∩ (O ∩ (correspondingLeft j₁ j₂)ᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzc, hzO, hzC⟩
    apply hzC
    rw [← hOC]
    exact ⟨hzO, hcf hzc⟩
  rcases isPreconnected_iff_subset_of_disjoint.1 hc O (correspondingLeft j₁ j₂)ᶜ hO
      hcl.isOpen_compl hcov hdis with hsub | hsub
  · intro z hz
    rw [← hOC]
    exact ⟨hsub hz, hcf hz⟩
  · obtain ⟨z, hzc, hzC⟩ := hmeet
    exact absurd hzC (hsub hzc)

end PairForm

/-! ### The compact form, restated -/

section CompactForm

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] {j₁ : W → X} {j₂ : W → Y}

/-- **The compact form** (`isClosed_nonHausdorffLeft_of_isCompact` restated with the named
property): for Hausdorff `X`, `Y` and open embeddings, Chruściel's `H` is closed when the
corresponding points stay locally in a compact set. -/
theorem isClosed_nonHausdorffLeft_of_correspondingCompact [T2Space X] [T2Space Y]
    (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) (h : CorrespondingCompact j₁ j₂) :
    IsClosed (nonHausdorffLeft j₁ j₂) := by
  exact isClosed_nonHausdorffLeft_of_isCompact hj₁ hj₂ h

/-- **DEC-160's two forms in one statement**: the corresponding pairs are closed with no hypothesis,
and `H` is closed under the property. -/
theorem isClosed_correspondingPairs_and_nonHausdorffLeft [T2Space X] [T2Space Y]
    (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) :
    IsClosed (correspondingPairs j₁ j₂) ∧
      (CorrespondingCompact j₁ j₂ → IsClosed (nonHausdorffLeft j₁ j₂)) := by
  exact ⟨isClosed_correspondingPairs, isClosed_nonHausdorffLeft_of_correspondingCompact hj₁ hj₂⟩

/-- The `Y`-side `H`: the points of `Y` whose image is a non-Hausdorff point of the gluing are
the points of `∂ j₂(W)` having a corresponding point (Hausdorff `X`, `Y`). -/
theorem preimage_ι₂_nonHausdorffPoints [T2Space X] [T2Space Y] (hj₁ : IsOpenEmbedding j₁)
    (hj₂ : IsOpenEmbedding j₂) :
    ι₂ j₁ j₂ ⁻¹' nonHausdorffPoints (Gluing j₁ j₂) = correspondingLeft j₂ j₁ := by
  ext y
  simp only [nonHausdorffPoints, mem_preimage, mem_setOf_eq, correspondingLeft]
  constructor
  · rintro ⟨z, hne, hns⟩
    rcases exists_ι z with ⟨x, rfl⟩ | ⟨y', rfl⟩
    · exact ⟨x, isCorrespondingBoundaryPair_swap.2
        ((isCorrespondingBoundaryPair_iff hj₁ hj₂).2 ⟨hne, fun hd => hns hd.symm⟩)⟩
    · rw [disjoint_nhds_ι₂_ι₂ hj₁ hj₂, disjoint_nhds_nhds, not_not] at hns
      exact absurd (by rw [hns]) hne
  · rintro ⟨x, h⟩
    obtain ⟨hne, hns⟩ :=
      (isCorrespondingBoundaryPair_iff hj₁ hj₂).1 (isCorrespondingBoundaryPair_swap.1 h)
    exact ⟨_, hne, fun hd => hns hd.symm⟩

/-- **Both sides**: for Hausdorff `X`, `Y` and open embeddings, if the property holds on the `X`
side and on the `Y` side, the non-Hausdorff points of the gluing form a closed set (against
`not_isClosed_nonHausdorffPoints_expGluing`, where the `X` side fails). -/
theorem isClosed_nonHausdorffPoints_of_correspondingCompact [T2Space X] [T2Space Y]
    (hj₁ : IsOpenEmbedding j₁) (hj₂ : IsOpenEmbedding j₂) (h₁ : CorrespondingCompact j₁ j₂)
    (h₂ : CorrespondingCompact j₂ j₁) : IsClosed (nonHausdorffPoints (Gluing j₁ j₂)) := by
  rw [← isOpen_compl_iff, isOpen_iff, preimage_compl, preimage_compl, isOpen_compl_iff,
    isOpen_compl_iff]
  refine ⟨isClosed_nonHausdorffLeft_of_correspondingCompact hj₁ hj₂ h₁, ?_⟩
  rw [preimage_ι₂_nonHausdorffPoints hj₁ hj₂]
  exact isClosed_correspondingLeft_of_correspondingCompact h₂

end CompactForm

/-! ### What implies the property -/

section Sufficient

variable [TopologicalSpace X] [TopologicalSpace Y] {j₁ : W → X} {j₂ : W → Y}

/-- No corresponding pair: the property holds with `K = ∅`. -/
theorem correspondingCompact_of_forall_not (h : ∀ x y, ¬ IsCorrespondingBoundaryPair j₁ j₂ x y) :
    CorrespondingCompact j₁ j₂ := by
  exact fun _ _ => ⟨univ, univ_mem, ∅, isCompact_empty, fun x' _ y hy => (h x' y hy).elim⟩

/-- `∂ j₂(W)` compact: the property holds with `K = ∂ j₂(W)`. -/
theorem correspondingCompact_of_isCompact_frontier (h : IsCompact (frontier (range j₂))) :
    CorrespondingCompact j₁ j₂ := by
  exact fun _ _ => ⟨univ, univ_mem, _, h, fun _ _ _ hy => hy.2.1⟩

/-- `Y` compact (the hypothesis of `isClosed_nonHausdorffLeft`). -/
theorem correspondingCompact_of_compactSpace [CompactSpace Y] : CorrespondingCompact j₁ j₂ := by
  exact correspondingCompact_of_isCompact_frontier isClosed_frontier.isCompact

/-- **The correspondence is locally a continuous map**: on a locally compact `X`, if near each
point of the closure of Sbierski's `C` the corresponding points are the values of a map continuous
there, the property holds (elsewhere on `∂ j₁(W)` a neighbourhood meets no point of `C`). This is
the shape of the extension in Sbierski's Lemma 3.8 (the ladder's A3, `germ_extension`); that A3
provides it is not proved here. -/
theorem correspondingCompact_of_continuousOn [LocallyCompactSpace X]
    (h : ∀ x ∈ closure (correspondingLeft j₁ j₂), ∃ V ∈ 𝓝 x, ∃ g : X → Y, ContinuousOn g V ∧
      ∀ x' ∈ V, ∀ y, IsCorrespondingBoundaryPair j₁ j₂ x' y → y = g x') :
    CorrespondingCompact j₁ j₂ := by
  intro x _
  by_cases hx : x ∈ closure (correspondingLeft j₁ j₂)
  · obtain ⟨V, hV, g, hg, hVg⟩ := h x hx
    obtain ⟨N, hN, hNV, hNc⟩ := local_compact_nhds hV
    exact ⟨N, hN, g '' N, hNc.image_of_continuousOn (hg.mono hNV),
      fun x' hx' y hy => ⟨x', hx', (hVg x' (hNV hx') y hy).symm⟩⟩
  · refine ⟨(closure (correspondingLeft j₁ j₂))ᶜ, isClosed_closure.isOpen_compl.mem_nhds hx, ∅,
      isCompact_empty, fun x' hx' y hy => (hx' (subset_closure ⟨y, hy⟩)).elim⟩

/-- A Hausdorff gluing along open embeddings has the property (it has no corresponding pair). -/
theorem correspondingCompact_of_t2Space [TopologicalSpace W] (hj₁ : IsOpenEmbedding j₁)
    (hj₂ : IsOpenEmbedding j₂) [T2Space (Gluing j₁ j₂)] : CorrespondingCompact j₁ j₂ := by
  exact correspondingCompact_of_forall_not
    ((t2Space_iff_t2Space_and_forall_not_isCorrespondingBoundaryPair hj₁ hj₂).1 ‹_›).2.2

end Sufficient

/-! ### Witnesses -/

/-- **A non-Hausdorff gluing with the property**: the line with two origins (its two origins
correspond, `lineTwoOrigins_isCorrespondingBoundaryPair`). -/
theorem correspondingCompact_lineTwoOrigins :
    CorrespondingCompact lineTwoOriginsInc lineTwoOriginsInc := by
  refine correspondingCompact_of_continuousOn fun _ _ =>
    ⟨univ, univ_mem, id, continuousOn_id, fun x' _ y hy => ?_⟩
  have hcl := forall_nhds_iff_mem_closure_graph.1 hy.2.2
  have hsub : graph lineTwoOriginsInc lineTwoOriginsInc ⊆ {p : ℝ × ℝ | p.2 = p.1} := by
    rintro _ ⟨w, rfl⟩
    rfl
  exact (isClosed_eq continuous_snd continuous_fst).closure_subset_iff.2 hsub hcl

/-- On the line with two origins the non-Hausdorff points (the two origins) form a closed set. -/
theorem isClosed_nonHausdorffPoints_lineTwoOrigins :
    IsClosed (nonHausdorffPoints LineTwoOrigins) :=
  isClosed_nonHausdorffPoints_of_correspondingCompact isOpenEmbedding_lineTwoOriginsInc
    isOpenEmbedding_lineTwoOriginsInc correspondingCompact_lineTwoOrigins
    correspondingCompact_lineTwoOrigins

/-- **The property fails on the exponential gluing** (`j₁ (a, c) = (a, eᶜ)`, `j₂ (a, c) = (a, c)`
on `(0, ∞) × ℝ`): the point corresponding to `(0, b)` is `(0, log b)`, which escapes as `b → 0⁺`. -/
theorem not_correspondingCompact_expGluing : ¬ CorrespondingCompact expLeft halfPlaneInc := by
  exact fun h => not_isClosed_nonHausdorffLeft_expGluing
    (isClosed_nonHausdorffLeft_of_correspondingCompact isOpenEmbedding_expLeft
      isOpenEmbedding_halfPlaneInc h)

/-- **The exponential gluing against the two forms**: its corresponding pairs are closed, the
property fails, and `H` is not closed. -/
theorem expGluing_witness :
    IsClosed (correspondingPairs expLeft halfPlaneInc) ∧
      ¬ CorrespondingCompact expLeft halfPlaneInc ∧
        ¬ IsClosed (nonHausdorffLeft expLeft halfPlaneInc) := by
  exact ⟨isClosed_correspondingPairs, not_correspondingCompact_expGluing,
    not_isClosed_nonHausdorffLeft_expGluing⟩

/-- `(0, b)`, `b ≥ 0`, lies on `∂ j₁(W)` for the exponential gluing. -/
theorem expGluing_mem_frontier {b : ℝ} (hb : 0 ≤ b) : ((0 : ℝ), b) ∈ frontier (range expLeft) := by
  rw [isOpenEmbedding_expLeft.isOpen_range.frontier_eq]
  refine ⟨?_, ?_⟩
  · have h0 : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by rw [closure_Ioi]; exact self_mem_Ici
    have := map_mem_closure (f := fun s : ℝ => (s, b + s)) (by fun_prop) h0
      (t := range expLeft) fun s hs => ⟨(⟨s, hs⟩, Real.log (b + s)), by
        have hpos : (0 : ℝ) < b + s := by have := mem_Ioi.1 hs; linarith
        simp [expLeft, Real.exp_log hpos]⟩
    simp only [add_zero] at this
    exact this
  · rintro ⟨⟨a, c⟩, h⟩
    exact (ne_of_gt a.2) (congrArg Prod.fst h)

/-- Sbierski's `C` of the exponential gluing is `{0} × (0, ∞)`. -/
theorem expGluing_correspondingLeft :
    correspondingLeft expLeft halfPlaneInc = {x : ℝ × ℝ | x.1 = 0 ∧ 0 < x.2} := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨y, hy⟩
    have hcl := forall_nhds_iff_mem_closure_graph.1 hy.2.2
    have hS : IsClosed {p : (ℝ × ℝ) × (ℝ × ℝ) | p.1 = (p.2.1, Real.exp p.2.2)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hsub : graph expLeft halfPlaneInc ⊆
        {p : (ℝ × ℝ) × (ℝ × ℝ) | p.1 = (p.2.1, Real.exp p.2.2)} := by
      rintro _ ⟨w, rfl⟩
      rfl
    have he : ((a, b) : ℝ × ℝ) = (y.1, Real.exp y.2) := hS.closure_subset_iff.2 hsub hcl
    have hy1 : y.1 = 0 := by
      have hfr := hy.2.1
      rw [isOpenEmbedding_halfPlaneInc.isOpen_range.frontier_eq] at hfr
      have hsub' : range halfPlaneInc ⊆ {p : ℝ × ℝ | 0 ≤ p.1} := by
        rintro _ ⟨⟨a', c'⟩, rfl⟩
        exact le_of_lt (show (0 : ℝ) < (a' : ℝ) from a'.2)
      have hle : 0 ≤ y.1 :=
        (isClosed_le continuous_const continuous_fst).closure_subset_iff.2 hsub' hfr.1
      by_contra hne
      exact hfr.2 ⟨(⟨y.1, lt_of_le_of_ne hle (Ne.symm hne)⟩, y.2), rfl⟩
    rw [Prod.mk.injEq] at he
    refine ⟨he.1.trans hy1, ?_⟩
    rw [he.2]
    exact Real.exp_pos _
  · rintro ⟨ha, hb⟩
    simp only at ha hb
    subst ha
    have := expGluing_mem_nonHausdorffLeft (Real.log b)
    rwa [Real.exp_log hb, nonHausdorffLeft_eq isOpenEmbedding_expLeft
      isOpenEmbedding_halfPlaneInc] at this

/-- On the exponential gluing, `C` is open in `∂ j₁(W)`: it is its trace on the upper half-plane. -/
theorem expGluing_isOpen_in_frontier :
    ∃ O : Set (ℝ × ℝ), IsOpen O ∧
      O ∩ frontier (range expLeft) = correspondingLeft expLeft halfPlaneInc := by
  refine ⟨{x | 0 < x.2}, isOpen_lt continuous_const continuous_snd, ?_⟩
  rw [expGluing_correspondingLeft]
  ext ⟨a, b⟩
  simp only [mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨hb, hfr⟩
    refine ⟨?_, hb⟩
    rw [isOpenEmbedding_expLeft.isOpen_range.frontier_eq] at hfr
    have hsub' : range expLeft ⊆ {p : ℝ × ℝ | 0 ≤ p.1} := by
      rintro _ ⟨⟨a', c'⟩, rfl⟩
      exact le_of_lt (show (0 : ℝ) < (a' : ℝ) from a'.2)
    have hle : 0 ≤ a :=
      (isClosed_le continuous_const continuous_fst).closure_subset_iff.2 hsub' hfr.1
    by_contra hne
    exact hfr.2 ⟨(⟨a, lt_of_le_of_ne hle (Ne.symm hne)⟩, Real.log b),
      by simp [expLeft, Real.exp_log hb]⟩
  · rintro ⟨ha, hb⟩
    refine ⟨hb, ?_⟩
    subst ha
    exact expGluing_mem_frontier hb.le

/-- **The connectedness step at `ETT.tex:2303` is not topology**: on the exponential gluing both
halves of `prop:C_connexe` hold (`C` open in `∂ j₁(W)`, the corresponding pairs closed), and the
segment `{0} × [0, 1]` of `∂ j₁(W)` is connected, meets `C` and is not contained in it. The
property is what the step needs
(`CorrespondingCompact.subset_correspondingLeft_of_isPreconnected`). -/
theorem expGluing_not_subset_correspondingLeft :
    (∃ O : Set (ℝ × ℝ), IsOpen O ∧
        O ∩ frontier (range expLeft) = correspondingLeft expLeft halfPlaneInc) ∧
      IsClosed (correspondingPairs expLeft halfPlaneInc) ∧
      ∃ c : Set (ℝ × ℝ), IsPreconnected c ∧ c ⊆ frontier (range expLeft) ∧
        (c ∩ correspondingLeft expLeft halfPlaneInc).Nonempty ∧
        ¬ c ⊆ correspondingLeft expLeft halfPlaneInc := by
  refine ⟨expGluing_isOpen_in_frontier, isClosed_correspondingPairs,
    (fun s : ℝ => ((0 : ℝ), s)) '' Icc 0 1,
    isPreconnected_Icc.image _ (by fun_prop : Continuous fun s : ℝ => ((0 : ℝ), s)).continuousOn,
    ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact expGluing_mem_frontier hs.1
  · refine ⟨((0 : ℝ), 1), ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩, ?_⟩
    rw [expGluing_correspondingLeft]
    exact ⟨rfl, one_pos⟩
  · intro hsub
    have := hsub ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    rw [expGluing_correspondingLeft] at this
    exact lt_irrefl _ this.2

/-- **A continuous extension across every corresponding point does not give the property**: on
the exponential gluing, near every point of `C` the corresponding points are the values of the
continuous map `(a, b) ↦ (a, log b)` of the upper half-plane (it is `j₂ ∘ j₁⁻¹` extended, though
the statement asks only that the corresponding points be its values), and the property fails, at
`(0, 0) ∈ closure C \ C`. So `correspondingCompact_of_continuousOn` cannot ask
its hypothesis on `C` only, and an extension property at corresponding points (the ladder's A3,
as topology) does not imply the property. -/
theorem expGluing_continuous_extension_witness :
    (∀ x ∈ correspondingLeft expLeft halfPlaneInc, ∃ V ∈ 𝓝 x, ∃ g : ℝ × ℝ → ℝ × ℝ,
      ContinuousOn g V ∧
        ∀ x' ∈ V, ∀ y, IsCorrespondingBoundaryPair expLeft halfPlaneInc x' y → y = g x') ∧
      ¬ CorrespondingCompact expLeft halfPlaneInc := by
  refine ⟨fun x hx => ?_, not_correspondingCompact_expGluing⟩
  rw [expGluing_correspondingLeft] at hx
  refine ⟨{p : ℝ × ℝ | 0 < p.2}, (isOpen_lt continuous_const continuous_snd).mem_nhds hx.2,
    fun p => (p.1, Real.log p.2),
    continuousOn_fst.prodMk (Real.continuousOn_log.comp continuousOn_snd fun p hp => ne_of_gt hp),
    fun x' _ y hy => ?_⟩
  have hcl := forall_nhds_iff_mem_closure_graph.1 hy.2.2
  have hS : IsClosed {p : (ℝ × ℝ) × (ℝ × ℝ) | p.1 = (p.2.1, Real.exp p.2.2)} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hsub : graph expLeft halfPlaneInc ⊆
      {p : (ℝ × ℝ) × (ℝ × ℝ) | p.1 = (p.2.1, Real.exp p.2.2)} := by
    rintro _ ⟨w, rfl⟩
    rfl
  have he : x' = (y.1, Real.exp y.2) := hS.closure_subset_iff.2 hsub hcl
  rw [he]
  exact Prod.ext rfl (Real.log_exp y.2).symm

/-- **The property is one-sided**: on the exponential gluing the `Y`-side property holds (the point
of `X` corresponding to `(0, c)` is `(0, eᶜ)`, continuous in `c`). -/
theorem correspondingCompact_expGluing_swap : CorrespondingCompact halfPlaneInc expLeft := by
  refine correspondingCompact_of_continuousOn fun _ _ =>
    ⟨univ, univ_mem, fun p : ℝ × ℝ => (p.1, Real.exp p.2),
      (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1, Real.exp p.2)).continuousOn,
      fun x' _ y hy => ?_⟩
  have hcl := forall_nhds_iff_mem_closure_graph.1 hy.2.2
  have hS : IsClosed {q : (ℝ × ℝ) × (ℝ × ℝ) | q.2 = (q.1.1, Real.exp q.1.2)} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hsub : graph halfPlaneInc expLeft ⊆
      {q : (ℝ × ℝ) × (ℝ × ℝ) | q.2 = (q.1.1, Real.exp q.1.2)} := by
    rintro _ ⟨w, rfl⟩
    rfl
  exact hS.closure_subset_iff.2 hsub hcl

/-- **The property fails on the shear gluing** (`j₁ (a, c) = (a, a c)`): the origin corresponds to
every point of `{0} × ℝ`. -/
theorem not_correspondingCompact_shearGluing : ¬ CorrespondingCompact shearLeft halfPlaneInc := by
  intro h
  obtain ⟨V, hV, K, hK, hVK⟩ := h _ (shearGluing_mem_frontier 0)
  have hmem : ∀ c : ℝ, ((0 : ℝ), c) ∈ K := fun c =>
    hVK _ (mem_of_mem_nhds hV) _ (shearGluing_isCorrespondingBoundaryPair c)
  obtain ⟨b, hb⟩ := (hK.image continuous_snd).bddAbove
  have : b + 1 ≤ b := hb ⟨((0 : ℝ), b + 1), hmem (b + 1), rfl⟩
  linarith

/-- On the shear gluing, Chruściel's `H` is the origin, a closed set. -/
theorem isClosed_nonHausdorffLeft_shearGluing :
    IsClosed (nonHausdorffLeft shearLeft halfPlaneInc) := by
  rw [nonHausdorffLeft_eq isOpenEmbedding_shearLeft isOpenEmbedding_halfPlaneInc,
    shearGluing_correspondingLeft]
  exact isClosed_singleton

/-- **The compact form's converse fails**: on the shear gluing `H` is closed and the property
fails, so the property is strictly stronger than the closedness of `H`. -/
theorem shearGluing_witness :
    IsClosed (nonHausdorffLeft shearLeft halfPlaneInc) ∧
      ¬ CorrespondingCompact shearLeft halfPlaneInc := by
  exact ⟨isClosed_nonHausdorffLeft_shearGluing, not_correspondingCompact_shearGluing⟩

end Gluing

/-! ### The family form -/

namespace CBG.FamilyGlueData

variable {I : Type v} {M : I → Type u} [∀ i, TopologicalSpace (M i)] (D : FamilyGlueData I M)

/-- **The compact form for a family**: the non-Hausdorff points of the family gluing seen in `M i`
are closed when every pair `(i, j)` has the property and the boundaries `∂ U i j` are locally
finite in `M i` (Hausdorff pieces). -/
theorem isClosed_preimage_ι_nonHausdorffPoints [∀ i, T2Space (M i)] (i : I)
    (hlf : LocallyFinite fun j => frontier (D.U i j : Set (M i)))
    (h : ∀ j, Gluing.CorrespondingCompact (Subtype.val : D.U i j → M i) (D.φ i j)) :
    IsClosed (D.ι i ⁻¹' nonHausdorffPoints D.Glued) := by
  rw [D.preimage_ι_nonHausdorffPoints i]
  refine (hlf.subset fun j => ?_).isClosed_iUnion fun j =>
    Gluing.isClosed_correspondingLeft_of_correspondingCompact (h j)
  have := Gluing.correspondingLeft_subset_frontier (j₁ := (Subtype.val : D.U i j → M i))
    (j₂ := D.φ i j)
  rwa [Subtype.range_coe] at this

/-- The same, for finitely many pieces. -/
theorem isClosed_preimage_ι_nonHausdorffPoints_of_finite [∀ i, T2Space (M i)] [Finite I] (i : I)
    (h : ∀ j, Gluing.CorrespondingCompact (Subtype.val : D.U i j → M i) (D.φ i j)) :
    IsClosed (D.ι i ⁻¹' nonHausdorffPoints D.Glued) := by
  exact D.isClosed_preimage_ι_nonHausdorffPoints i (locallyFinite_of_finite _) h

end CBG.FamilyGlueData

end Causal
