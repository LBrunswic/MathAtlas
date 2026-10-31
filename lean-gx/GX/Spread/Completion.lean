import GX.Spread.Basic

/-!
# Complete spreads, Fox's completion theorem, and the fibres of a spread

The end of §3.1 of `papers/gx` (`RamcovGX.tex:903–948`), with Fox's completion built (DEC-23).

* **`def:complete_spread_spread_completion`** — `RamcovGX.tex:903`: the set `X_y` of ends
  `GX.SpreadEnd` (`base = y`), `GX.IsCompleteSpread`, completions `GX.IsSpreadCompletion`.
* `theo:Fox_completion_functor` — `RamcovGX.tex:914` (partial, false as written): the space of
  ends with `GX.SpreadEnd.ofPoint` is a Fox completion (`GX.SpreadEnd.isFoxCompletion_base`:
  complete spread, embedding, dense, locally connected in, Hausdorff); **uniqueness** up to a
  unique isomorphism `GX.IsSpreadCompletion.existsUnique_homeomorph`; **existence iff the image
  is open** `GX.exists_isSpreadCompletion_iff` (no completion in any universe otherwise,
  `GX.not_isSpreadCompletion_of_not_isOpen`), refuted in general by
  `GX.not_exists_isSpreadCompletion_foxSeq`, `GX.not_isSpreadCompletion_foxSeq`;
  **functoriality** `GX.SpreadEnd.map` (unique, `GX.SpreadEnd.eq_map`, `map_id`, `map_comp`),
  on arbitrary completions `GX.IsFoxCompletion.existsUnique_extend`,
  `GX.foxCompletionFunctor`, **faithful**, **not full** `GX.not_full_foxCompletionFunctor`,
  `GX.completion_not_full`; as an endofunctor of its domain `GX.foxCompletionEndofunctor`
  (`GX.isLCSpread_foxCompletion`, `GX.not_full_foxCompletionEndofunctor`).
* `prop:spread_fiber` — `RamcovGX.tex:924` (partial): `GX.fiberMap` into the inverse limit
  `GX.FiberThread`, injective and an embedding (`GX.isEmbedding_fiberMap`), onto iff every thread
  has a common point (`GX.surjective_fiberMap_iff_threads`); complete iff onto for every `b`
  (`GX.isCompleteSpread_iff_forall_surjective_fiberMap`, one basis per point suffices:
  `GX.isCompleteSpread_iff_forall_exists_surjective_fiberMap`; `GX.fiberHomeomorph`); the
  fixed-`b` "iff" is false (`GX.fiberMap_exp_bijective_not_complete`); the literal "open map"
  is false (`GX.not_isOpenMap_fiberMap_comb`, the comb); the embedding also for any
  neighbourhood basis, open or not (`GX.isEmbedding_fiberMapNhds`).
* **`cor:totdiscont`** — `RamcovGX.tex:947`: `GX.isTotallyDisconnected_fiber`.
* Facts used later: the completion is Hausdorff, first countable, second countable, locally
  path-connected (`GX.SpreadEnd.t2Space`, `GX.SpreadEnd.firstCountableTopology`,
  `GX.SpreadEnd.secondCountableTopology`, `GX.SpreadEnd.locPathConnectedSpace`);
  completion of a covering over an open (e.g. portly) subset
  `GX.SpreadEnd.isSpreadCompletion_base_of_subset_ordY`; a complete spread is its own completion
  `GX.SpreadEnd.isSpreadCompletion_id`.

> For $y\in \overline{p(X)}$, consider the set $X_y$ of maps $\chi : \{\U\subset Y ~ \text{ open
> and connected neighborhood of }y\} \rightarrow \{\V\subset X ~ \text{open connected}\}$
> increasing for the inclusion and such that $\chi(\U)$ is a connected component of
> $p^{-1}(\U)$ for all $\U$. The spread $X\xrightarrow{p} Y$ is complete if for all
> $y\in \overline{p(X)}$ and all $\chi \in X_y$, the intersection of $\chi(\U)$ for $\U$ going
> through all open connected neighborhood of $y$ is non empty. A completion of a spread
> $X\xrightarrow{p} Y$ is a spread $X'\xrightarrow{p'} Y$ together with a spread morphism
> $(Id_Y,\iota)$ […] such that $\iota$ is an embedding, $X'$ is complete and the image of $\iota$
> is portly.
>
> Every spread admits a unique completion up to isomorphism, furthermore the completion of
> spread is a fully faithful functor from $\CatSpread$ to itself.
>
> Then, the natural map $p^{-1}(b) \rightarrow \varprojlim_{\U\in \boldsymbol{\U}}X_\U$ is
> injective open. Furthermore, it is an homeomorphism if and only if the spread
> $X\xrightarrow{p}Y$ is complete.
>
> Let $X\xrightarrow{p} Y$ be a spread, then the fibers of $p$ are totally discontinuous.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| §3 standing: `Y` Hausdorff, locally path-connected | ⚠ weakened: `T2Space Y` (uniqueness, Hausdorffness), `T1Space Y` (realising ends), `LocallyConnectedSpace Y` |
| §3 standing: `X`, `X'` Hausdorff | ⚠ weakened: `T0Space` (embedding of `X`; injectivity into `X'`; `cor:totdiscont`) |
| §3 standing: first countable | ⚠ weakened: used only for local path-connectedness of the completion (preserved when assumed: instance) |
| §3 standing: locally path-connected | ⚠ weakened: `LocPathConnectedSpace X` + `LocallyConnectedSpace Y` + `FirstCountableTopology Y` give it for the completion; elsewhere local connectedness |
| `theo:Fox_completion_functor`: existence for every spread | ⚠ strengthened: iff `range ι` open in the space of ends (finding) |
| `theo:Fox_completion_functor`: functor on `Spread` | ⚠ strengthened: on the spreads with `LocallyConnectedSpace Y`, `T2Space Y`, `T0Space X`, an endofunctor of that full subcategory |
| `prop:spread_fiber`: `𝓤` a connected neighbourhood basis | ⚠ reading: OPEN connected neighbourhoods for the comparison with ends; the embedding is also proved for ANY neighbourhood basis (`fiberMapNhds`) |
| `prop:spread_fiber`: "open" | ✗ false as an open map (comb, `GX.not_isOpenMap_fiberMap_comb`); true: open onto its image (embedding); open map iff image open |
| `prop:spread_fiber`: "homeomorphism iff complete" | ⚠ corrected: iff for every `b` (fixed-`b` false) |

## SCOPE (disclosed)

* Ends (`X_y`) are functions on all subsets of `Y`, normalised to `∅` off the open connected
  neighbourhoods of the base; "connected" is `IsPreconnected` (same for sets containing `y`).
* `theo:Fox_completion_functor`. Existence is false as written: `ℂ ∖ {1/(n+1)} → ℂ` (a spread
  with Hausdorff, locally path-connected, second countable source) has no completion. The true
  forms: the Fox completion (ends) always exists with a dense, locally-connected-in image
  (`IsFoxCompletion`, Fox's notion); it is a completion in the paper's sense iff that image is
  open, e.g. over an open subset of the ordinary locus. Uniqueness holds among Fox completions.
  "Fully faithful" is false: the functor is faithful, not full.
* `prop:spread_fiber`. The paper's step `φ(V ∩ p⁻¹(b)) = π_U⁻¹(V)` holds only for complete
  spreads; the literal "open map into the limit" is equivalent to the image being open
  (`GX.isOpenMap_fiberMap_iff`) and is false: `GX.not_isOpenMap_fiberMap_comb` proves it for the
  comb `GX.combSet` (the `x`-axis with the arms `(t, r_n - t)`, `0 < t ≤ r_n`, `r_n = 2⁻ⁿ`; a
  Hausdorff, second countable, locally path-connected subspace of `ℝ²`) projected to the first
  coordinate, at `b = 0`, over the basis `{(-ρ, ρ)}`.
* `prop:spread_fiber`, the basis `𝓤`. "Connected neighbourhood basis" is READ as a family of
  OPEN connected neighbourhoods (`IsCNbhd`). This is a reading, not a necessity: continuity and
  the embedding only use that components of `p⁻¹(U)` are neighbourhoods, which holds for any
  connected neighbourhood `U` since `X` is locally connected; the reading is kept because the
  comparison with ends (`surjective_fiberMap_iff_ends`) uses the ends' open connected
  neighbourhoods. The wider reading is covered for the embedding: `GX.fiberMapNhds` over any
  family of neighbourhoods forming a basis at `b` (`GX.isEmbedding_fiberMapNhds`,
  `GX.mem_range_fiberMapNhds_iff`), equal to `GX.fiberMap` on open connected ones
  (`GX.fiberMap_eq_fiberMapNhds`).
* Local path-connectedness of the completion is proved under a locally path-connected source and
  a first countable locally connected base (paths to an end are infinite concatenations,
  `GX.Path.exists_infConcat`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

noncomputable section

open Set Filter Topology Function

namespace GX

universe u v

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Connected open neighbourhoods -/

/-- An open connected neighbourhood of `y` (connectedness read as `IsPreconnected`, which is the
same thing for a set containing `y`). -/
def IsCNbhd (y : Y) (U : Set Y) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧ y ∈ U

theorem IsCNbhd.isOpen {y : Y} {U : Set Y} (h : IsCNbhd y U) : IsOpen U := h.1
theorem IsCNbhd.isPreconnected {y : Y} {U : Set Y} (h : IsCNbhd y U) : IsPreconnected U := h.2.1
theorem IsCNbhd.mem {y : Y} {U : Set Y} (h : IsCNbhd y U) : y ∈ U := h.2.2

/-- A connected open neighbourhood of `y` is one of each of its points. -/
theorem IsCNbhd.of_mem {y z : Y} {U : Set Y} (h : IsCNbhd y U) (hz : z ∈ U) : IsCNbhd z U :=
  ⟨h.1, h.2.1, hz⟩

/-- In a locally connected space, every open neighbourhood contains a connected one. -/
theorem exists_isCNbhd_subset [LocallyConnectedSpace Y] {y : Y} {U : Set Y} (hU : IsOpen U)
    (hy : y ∈ U) : ∃ W, IsCNbhd y W ∧ W ⊆ U :=
  ⟨connectedComponentIn U y, ⟨hU.connectedComponentIn, isPreconnected_connectedComponentIn,
    mem_connectedComponentIn hy⟩, connectedComponentIn_subset _ _⟩

theorem exists_isCNbhd_subset_inter [LocallyConnectedSpace Y] {y : Y} {U V : Set Y}
    (hU : IsCNbhd y U) (hV : IsCNbhd y V) : ∃ W, IsCNbhd y W ∧ W ⊆ U ∧ W ⊆ V := by
  obtain ⟨W, hW, hWUV⟩ := exists_isCNbhd_subset (hU.1.inter hV.1) ⟨hU.2.2, hV.2.2⟩
  exact ⟨W, hW, hWUV.trans inter_subset_left, hWUV.trans inter_subset_right⟩

/-- The connected open neighbourhoods of `y` form a basis of `𝓝 y`. -/
theorem hasBasis_nhds_isCNbhd [LocallyConnectedSpace Y] (y : Y) :
    (𝓝 y).HasBasis (IsCNbhd y) id := by
  refine ⟨fun N => ⟨fun hN => ?_, fun ⟨W, hW, hWN⟩ => mem_of_superset (hW.1.mem_nhds hW.2.2) hWN⟩⟩
  obtain ⟨O, hON, hO, hyO⟩ := mem_nhds_iff.1 hN
  obtain ⟨W, hW, hWO⟩ := exists_isCNbhd_subset hO hyO
  exact ⟨W, hW, hWO.trans hON⟩

/-- In a T1 locally connected space, the connected open neighbourhoods of `y` meet in `{y}`. -/
theorem eq_of_forall_isCNbhd [T1Space Y] [LocallyConnectedSpace Y] {y z : Y}
    (h : ∀ U, IsCNbhd y U → z ∈ U) : z = y := by
  by_contra hne
  obtain ⟨W, hW, hWU⟩ := exists_isCNbhd_subset (isOpen_compl_singleton (x := z))
    (Ne.symm hne : y ≠ z)
  exact hWU (h W hW) rfl

/-! ### Components of preimages -/

/-- The predicate "`C` is a connected component of `p ⁻¹' U`". -/
def IsCompOf (p : X → Y) (U : Set Y) (C : Set X) : Prop :=
  ∃ x, p x ∈ U ∧ C = connectedComponentIn (p ⁻¹' U) x

theorem IsCompOf.nonempty {p : X → Y} {U : Set Y} {C : Set X} (h : IsCompOf p U C) :
    C.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, mem_connectedComponentIn hx⟩

theorem IsCompOf.subset {p : X → Y} {U : Set Y} {C : Set X} (h : IsCompOf p U C) :
    C ⊆ p ⁻¹' U := by
  obtain ⟨x, -, rfl⟩ := h
  exact connectedComponentIn_subset _ _

theorem IsCompOf.isPreconnected {p : X → Y} {U : Set Y} {C : Set X} (h : IsCompOf p U C) :
    IsPreconnected C := by
  obtain ⟨x, -, rfl⟩ := h
  exact isPreconnected_connectedComponentIn

theorem IsCompOf.eq_of_mem {p : X → Y} {U : Set Y} {C : Set X} (h : IsCompOf p U C) {z : X}
    (hz : z ∈ C) : C = connectedComponentIn (p ⁻¹' U) z := by
  obtain ⟨x, -, rfl⟩ := h
  exact (connectedComponentIn_eq hz)

/-- A preconnected subset of `p ⁻¹' U` meeting a component is contained in it. -/
theorem IsCompOf.subset_of_meets {p : X → Y} {U : Set Y} {C S : Set X} (h : IsCompOf p U C)
    (hS : IsPreconnected S) (hSU : S ⊆ p ⁻¹' U) (hSC : (S ∩ C).Nonempty) : S ⊆ C := by
  obtain ⟨z, hzS, hzC⟩ := hSC
  rw [h.eq_of_mem hzC]
  exact hS.subset_connectedComponentIn hzS hSU

/-- Two components which meet are equal. -/
theorem IsCompOf.eq_of_meets {p : X → Y} {U : Set Y} {C D : Set X} (hC : IsCompOf p U C)
    (hD : IsCompOf p U D) (h : (C ∩ D).Nonempty) : C = D := by
  obtain ⟨z, hzC, hzD⟩ := h
  rw [hC.eq_of_mem hzC, hD.eq_of_mem hzD]

theorem isCompOf_connectedComponentIn {p : X → Y} {U : Set Y} {x : X} (hx : p x ∈ U) :
    IsCompOf p U (connectedComponentIn (p ⁻¹' U) x) :=
  ⟨x, hx, rfl⟩

/-! ### Ends: the set `X_y` of `def:complete_spread_spread_completion` -/

/-- `def:complete_spread_spread_completion`. An *end* of `p` at `base` (an element of the set
`X_y` of the paper, `y = base`): a choice `χ(U)` of a connected component of `p ⁻¹' U` for every
open connected neighbourhood `U` of `base`, increasing for the inclusion. For convenience `χ` is a
function on all subsets of `Y`, normalised to `∅` off the connected open neighbourhoods (so that
an end is determined by its values on them). -/
@[ext]
structure SpreadEnd (p : X → Y) where
  /-- The point of `Y` the end lies over. -/
  base : Y
  /-- The choice of components. -/
  toFun : Set Y → Set X
  isCompOf : ∀ U, IsCNbhd base U → IsCompOf p U (toFun U)
  mono : ∀ U V, IsCNbhd base U → IsCNbhd base V → U ⊆ V → toFun U ⊆ toFun V
  eq_empty : ∀ U, ¬ IsCNbhd base U → toFun U = ∅

namespace SpreadEnd

variable {p : X → Y}

instance : CoeFun (SpreadEnd p) (fun _ => Set Y → Set X) := ⟨SpreadEnd.toFun⟩

theorem nonempty (e : SpreadEnd p) {U : Set Y} (hU : IsCNbhd e.base U) : (e U).Nonempty :=
  (e.isCompOf U hU).nonempty

theorem subset_preimage (e : SpreadEnd p) {U : Set Y} (hU : IsCNbhd e.base U) :
    e U ⊆ p ⁻¹' U :=
  (e.isCompOf U hU).subset

theorem isPreconnected (e : SpreadEnd p) {U : Set Y} (hU : IsCNbhd e.base U) :
    IsPreconnected (e U) :=
  (e.isCompOf U hU).isPreconnected

/-- Two ends over the same point agreeing on the connected open neighbourhoods are equal. -/
theorem ext_of_isCNbhd {e e' : SpreadEnd p} (hb : e.base = e'.base)
    (h : ∀ U, IsCNbhd e.base U → e U = e' U) : e = e' := by
  refine SpreadEnd.ext hb (funext fun U => ?_)
  by_cases hU : IsCNbhd e.base U
  · exact h U hU
  · rw [e.eq_empty U hU, e'.eq_empty U (hb ▸ hU)]

/-- The end of a point: `U ↦` the component of `x` in `p ⁻¹' U`. -/
def ofPoint (p : X → Y) (x : X) : SpreadEnd p :=
  { base := p x
    toFun := fun U => if IsCNbhd (p x) U then connectedComponentIn (p ⁻¹' U) x else ∅
    isCompOf := fun U hU => by
      rw [if_pos hU]; exact isCompOf_connectedComponentIn hU.mem
    mono := fun U V hU hV hUV => by
      rw [if_pos hU, if_pos hV]; exact connectedComponentIn_mono _ (preimage_mono hUV)
    eq_empty := fun U hU => by rw [if_neg hU] }

@[simp] theorem ofPoint_base (x : X) : (ofPoint p x).base = p x := rfl

theorem ofPoint_apply {x : X} {U : Set Y} (hU : IsCNbhd (p x) U) :
    ofPoint p x U = connectedComponentIn (p ⁻¹' U) x := by
  show (if IsCNbhd (p x) U then _ else _) = _
  rw [if_pos hU]

theorem mem_ofPoint {x : X} {U : Set Y} (hU : IsCNbhd (p x) U) : x ∈ ofPoint p x U := by
  rw [ofPoint_apply hU]; exact mem_connectedComponentIn hU.mem

/-- An end is the end of a point `x` iff `x` lies in all its components. -/
theorem eq_ofPoint_iff [T1Space Y] [LocallyConnectedSpace Y] (e : SpreadEnd p) (x : X) :
    ofPoint p x = e ↔ ∀ U, IsCNbhd e.base U → x ∈ e U := by
  constructor
  · rintro rfl U hU; exact mem_ofPoint hU
  · intro h
    have hb : p x = e.base :=
      eq_of_forall_isCNbhd fun U hU => e.subset_preimage hU (h U hU)
    refine ext_of_isCNbhd hb fun U hU => ?_
    have hU' : IsCNbhd e.base U := by rw [← hb]; exact hU
    rw [ofPoint_apply (p := p) (x := x) hU, (e.isCompOf U hU').eq_of_mem (h U hU')]

/-- The base of an end lies in the closure of the image. -/
theorem base_mem_closure [LocallyConnectedSpace Y] (e : SpreadEnd p) :
    e.base ∈ closure (range p) := by
  rw [mem_closure_iff_nhds_basis (hasBasis_nhds_isCNbhd e.base)]
  intro W hW
  obtain ⟨x, hx⟩ := e.nonempty hW
  exact ⟨p x, mem_range_self x, e.subset_preimage hW hx⟩

/-- For two connected neighbourhoods `V ⊆ U` of the base, `e V ⊆ e U`. -/
theorem subset_of_subset (e : SpreadEnd p) {U V : Set Y} (hU : IsCNbhd e.base U)
    (hV : IsCNbhd e.base V) (h : V ⊆ U) : e V ⊆ e U :=
  e.mono V U hV hU h

end SpreadEnd

/-- `def:complete_spread_spread_completion`. A spread (any map) is *complete* if for every
`y ∈ closure (p X)` and every end `χ ∈ X_y`, the intersection of the `χ(U)` over the open connected
neighbourhoods `U` of `y` is non-empty. -/
def IsCompleteSpread (p : X → Y) : Prop :=
  ∀ e : SpreadEnd p, e.base ∈ closure (range p) →
    ∃ x, ∀ U, IsCNbhd e.base U → x ∈ e U

/-- Over a locally connected base the closure condition is automatic. -/
theorem isCompleteSpread_iff [LocallyConnectedSpace Y] {p : X → Y} :
    IsCompleteSpread p ↔ ∀ e : SpreadEnd p, ∃ x, ∀ U, IsCNbhd e.base U → x ∈ e U :=
  ⟨fun h e => h e e.base_mem_closure, fun h e _ => h e⟩

/-! ### The Fox completion: the space of ends -/

namespace SpreadEnd

variable {p : X → Y}

/-- The basic open sets of the Fox completion: the ends whose components eventually lie in `C`,
over an open `U`. -/
def basicSet (p : X → Y) (U : Set Y) (C : Set X) : Set (SpreadEnd p) :=
  {e | ∃ W, IsCNbhd e.base W ∧ W ⊆ U ∧ e W ⊆ C}

/-- The topology of the Fox completion, generated by the basic sets. -/
instance : TopologicalSpace (SpreadEnd p) :=
  TopologicalSpace.generateFrom {s | ∃ U C, IsOpen U ∧ s = basicSet p U C}

theorem isOpen_basicSet {U : Set Y} (hU : IsOpen U) (C : Set X) : IsOpen (basicSet p U C) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, C, hU, rfl⟩

theorem mem_basicSet_self (e : SpreadEnd p) {W : Set Y} (hW : IsCNbhd e.base W) :
    e ∈ basicSet p W (e W) :=
  ⟨W, hW, subset_rfl, subset_rfl⟩

theorem basicSet_subset_basicSet {e : SpreadEnd p} {U : Set Y} {C : Set X}
    (he : e ∈ basicSet p U C) :
    ∃ W, IsCNbhd e.base W ∧ W ⊆ U ∧ basicSet p W (e W) ⊆ basicSet p U C := by
  obtain ⟨W, hW, hWU, hWC⟩ := he
  exact ⟨W, hW, hWU, fun e' ⟨V, hV, hVW, hVe⟩ => ⟨V, hV, hVW.trans hWU, hVe.trans hWC⟩⟩

theorem basicSet_mono (e : SpreadEnd p) {V W : Set Y} (hV : IsCNbhd e.base V)
    (hW : IsCNbhd e.base W) (hVW : V ⊆ W) : basicSet p V (e V) ⊆ basicSet p W (e W) :=
  fun _ ⟨V', hV', hV'V, h⟩ => ⟨V', hV', hV'V.trans hVW, h.trans (e.mono V W hV hW hVW)⟩

theorem base_mem_of_mem_basicSet {e : SpreadEnd p} {U : Set Y} {C : Set X}
    (he : e ∈ basicSet p U C) : e.base ∈ U := by
  obtain ⟨W, hW, hWU, -⟩ := he
  exact hWU hW.mem

/-- Every open set contains, around each of its points `e`, a basic set `basicSet W (e W)` with
`W` a connected open neighbourhood of the base. -/
theorem exists_basicSet_subset [LocallyConnectedSpace Y] {O : Set (SpreadEnd p)} (hO : IsOpen O)
    {e : SpreadEnd p} (he : e ∈ O) : ∃ W, IsCNbhd e.base W ∧ basicSet p W (e W) ⊆ O := by
  induction hO generalizing e with
  | basic s hs =>
    obtain ⟨U, C, -, rfl⟩ := hs
    obtain ⟨W, hW, -, h⟩ := basicSet_subset_basicSet he
    exact ⟨W, hW, h⟩
  | univ =>
    obtain ⟨W, hW, -⟩ := exists_isCNbhd_subset isOpen_univ (mem_univ e.base)
    exact ⟨W, hW, subset_univ _⟩
  | inter s t _ _ ihs iht =>
    obtain ⟨W₁, hW₁, h₁⟩ := ihs he.1
    obtain ⟨W₂, hW₂, h₂⟩ := iht he.2
    obtain ⟨W, hW, hW1, hW2⟩ := exists_isCNbhd_subset_inter hW₁ hW₂
    exact ⟨W, hW, subset_inter ((basicSet_mono e hW hW₁ hW1).trans h₁)
      ((basicSet_mono e hW hW₂ hW2).trans h₂)⟩
  | sUnion S _ ih =>
    obtain ⟨s, hsS, hes⟩ := mem_sUnion.1 he
    obtain ⟨W, hW, h⟩ := ih s hsS hes
    exact ⟨W, hW, h.trans (subset_sUnion_of_mem hsS)⟩

/-- The neighbourhoods of an end: the basic sets over its connected open neighbourhoods. -/
theorem hasBasis_nhds [LocallyConnectedSpace Y] (e : SpreadEnd p) :
    (𝓝 e).HasBasis (IsCNbhd e.base) (fun W => basicSet p W (e W)) := by
  refine ⟨fun N => ⟨fun hN => ?_, fun ⟨W, hW, h⟩ =>
    mem_of_superset ((isOpen_basicSet hW.1 _).mem_nhds (mem_basicSet_self e hW)) h⟩⟩
  obtain ⟨O, hON, hO, heO⟩ := mem_nhds_iff.1 hN
  obtain ⟨W, hW, h⟩ := exists_basicSet_subset hO heO
  exact ⟨W, hW, h.trans hON⟩

/-- An end in the basic set of a component `D` of `p ⁻¹' W` (with `W` a connected open
neighbourhood of its base) chooses `D` at `W`. -/
theorem eq_of_mem_basicSet {e : SpreadEnd p} {W : Set Y} {D : Set X} (hD : IsCompOf p W D)
    (hW : IsCNbhd e.base W) (he : e ∈ basicSet p W D) : e W = D := by
  obtain ⟨V, hV, hVW, hVD⟩ := he
  obtain ⟨z, hz⟩ := e.nonempty hV
  exact (e.isCompOf W hW).eq_of_meets hD ⟨z, e.mono V W hV hW hVW hz, hVD hz⟩

theorem mem_basicSet_iff {e : SpreadEnd p} {W : Set Y} {D : Set X} (hD : IsCompOf p W D)
    (hW : IsCNbhd e.base W) : e ∈ basicSet p W D ↔ e W = D :=
  ⟨eq_of_mem_basicSet hD hW, fun h => ⟨W, hW, subset_rfl, h.le⟩⟩

/-- The projection of the Fox completion to `Y` is continuous. -/
theorem continuous_base [LocallyConnectedSpace Y] :
    Continuous (SpreadEnd.base : SpreadEnd p → Y) := by
  refine continuous_def.2 fun U hU => ?_
  have : (SpreadEnd.base : SpreadEnd p → Y) ⁻¹' U = basicSet p U univ := by
    ext e
    refine ⟨fun h => ?_, fun h => base_mem_of_mem_basicSet h⟩
    obtain ⟨W, hW, hWU⟩ := exists_isCNbhd_subset hU h
    exact ⟨W, hW, hWU, subset_univ _⟩
  rw [this]; exact isOpen_basicSet hU _

theorem ofPoint_mem_basicSet_iff {e : SpreadEnd p} {W : Set Y} (hW : IsCNbhd e.base W) {x : X} :
    ofPoint p x ∈ basicSet p W (e W) ↔ x ∈ e W := by
  constructor
  · rintro ⟨V, hV, -, h⟩; exact h (mem_ofPoint hV)
  · intro hx
    have hxW : IsCNbhd (p x) W := hW.of_mem (e.subset_preimage hW hx)
    refine ⟨W, hxW, subset_rfl, ?_⟩
    rw [ofPoint_apply hxW, ← (e.isCompOf W hW).eq_of_mem hx]

theorem preimage_ofPoint_basicSet {e : SpreadEnd p} {W : Set Y} (hW : IsCNbhd e.base W) :
    ofPoint p ⁻¹' basicSet p W (e W) = e W :=
  ext fun _ => ofPoint_mem_basicSet_iff hW

/-- The embedding `ι : X → X̄` is continuous. -/
theorem continuous_ofPoint [LocallyConnectedSpace Y] (hp : IsSpread p) :
    Continuous (ofPoint p) := by
  haveI := hp.locallyConnectedSpace
  refine continuous_iff_continuousAt.2 fun x => ((hasBasis_nhds (ofPoint p x)).tendsto_right_iff).2
    fun W hW => ?_
  have hW' : IsCNbhd (p x) W := hW
  refine mem_of_superset ((hW'.1.preimage hp.continuous).connectedComponentIn.mem_nhds
    (mem_connectedComponentIn hW'.mem)) fun x' hx' => ?_
  show ofPoint p x' ∈ basicSet p W (ofPoint p x W)
  rw [ofPoint_mem_basicSet_iff hW, ofPoint_apply hW']
  exact hx'

/-- The embedding `ι : X → X̄` is inducing. -/
theorem isInducing_ofPoint [LocallyConnectedSpace Y] (hp : IsSpread p) :
    IsInducing (ofPoint p) := by
  refine isInducing_iff_nhds.2 fun x => le_antisymm ((continuous_ofPoint hp).tendsto x).le_comap ?_
  intro O hO
  obtain ⟨O', hO'O, hO', hxO'⟩ := mem_nhds_iff.1 hO
  obtain ⟨U, hU, hxU, hcomp⟩ := (isSpread_iff.1 hp).2.2 x O' hO' hxO'
  obtain ⟨W, hW, hWU⟩ := exists_isCNbhd_subset hU hxU
  refine mem_comap.2 ⟨basicSet p W (ofPoint p x W),
    (isOpen_basicSet hW.1 _).mem_nhds (mem_basicSet_self _ hW), ?_⟩
  rw [preimage_ofPoint_basicSet (e := ofPoint p x) hW, ofPoint_apply hW]
  exact ((connectedComponentIn_mono x (preimage_mono hWU)).trans hcomp).trans hO'O

/-- The embedding `ι : X → X̄` is an embedding (for a T0 source). -/
theorem isEmbedding_ofPoint [LocallyConnectedSpace Y] [T0Space X] (hp : IsSpread p) :
    IsEmbedding (ofPoint p) :=
  ⟨isInducing_ofPoint hp, (isInducing_ofPoint hp).injective⟩

/-- The image of `ι : X → X̄` is dense. -/
theorem denseRange_ofPoint [LocallyConnectedSpace Y] : DenseRange (ofPoint p) := fun e =>
  (mem_closure_iff_nhds_basis (hasBasis_nhds e)).2 fun _ hW =>
    let ⟨x, hx⟩ := e.nonempty hW
    ⟨_, mem_range_self x, (ofPoint_mem_basicSet_iff hW).2 hx⟩

theorem image_ofPoint_subset_basicSet {e : SpreadEnd p} {W : Set Y} (hW : IsCNbhd e.base W) :
    ofPoint p '' (e W) ⊆ basicSet p W (e W) := by
  rintro _ ⟨x, hx, rfl⟩; exact (ofPoint_mem_basicSet_iff hW).2 hx

theorem basicSet_subset_closure_image [LocallyConnectedSpace Y] {e : SpreadEnd p} {W : Set Y}
    (_hW : IsCNbhd e.base W) : basicSet p W (e W) ⊆ closure (ofPoint p '' (e W)) := by
  intro e' he'
  obtain ⟨V₀, hV₀, hV₀W, hV₀e⟩ := he'
  refine (mem_closure_iff_nhds_basis (hasBasis_nhds e')).2 fun V hV => ?_
  obtain ⟨V₁, hV₁, hV₁V, hV₁V₀⟩ := exists_isCNbhd_subset_inter hV hV₀
  obtain ⟨x, hx⟩ := e'.nonempty hV₁
  exact ⟨_, ⟨x, hV₀e (e'.mono V₁ V₀ hV₁ hV₀ hV₁V₀ hx), rfl⟩,
    (ofPoint_mem_basicSet_iff hV).2 (e'.mono V₁ V hV₁ hV hV₁V hx)⟩

/-- The basic sets are connected. -/
theorem isPreconnected_basicSet [LocallyConnectedSpace Y] (hp : IsSpread p) {e : SpreadEnd p}
    {W : Set Y} (hW : IsCNbhd e.base W) : IsPreconnected (basicSet p W (e W)) :=
  ((e.isPreconnected hW).image _ (continuous_ofPoint hp).continuousOn).subset_closure
    (image_ofPoint_subset_basicSet hW) (basicSet_subset_closure_image hW)

/-- The Fox completion is locally connected. -/
theorem locallyConnectedSpace [LocallyConnectedSpace Y] (hp : IsSpread p) :
    LocallyConnectedSpace (SpreadEnd p) :=
  locallyConnectedSpace_of_connected_bases _ _ hasBasis_nhds
    fun _ _ hW => isPreconnected_basicSet hp hW

/-- The components of the preimage of a connected open `W` in the Fox completion are the basic
sets `basicSet W D`. -/
theorem connectedComponentIn_base_preimage [LocallyConnectedSpace Y] (hp : IsSpread p)
    {e : SpreadEnd p} {W : Set Y} (hW : IsCNbhd e.base W) :
    connectedComponentIn (SpreadEnd.base ⁻¹' W) e = basicSet p W (e W) := by
  have hsub : basicSet p W (e W) ⊆ SpreadEnd.base ⁻¹' W := fun _ h => base_mem_of_mem_basicSet h
  refine subset_antisymm ?_ ((isPreconnected_basicSet hp hW).subset_connectedComponentIn
    (mem_basicSet_self e hW) hsub)
  set R : Set (SpreadEnd p) := {e' | e'.base ∈ W ∧ e' W ≠ e W} with hR
  have hRopen : IsOpen R := by
    refine isOpen_iff_forall_mem_open.2 fun e' he' => ?_
    have hW' : IsCNbhd e'.base W := hW.of_mem he'.1
    refine ⟨basicSet p W (e' W), fun e'' he'' => ?_, isOpen_basicSet hW.1 _,
      mem_basicSet_self e' hW'⟩
    have hb := base_mem_of_mem_basicSet he''
    refine ⟨hb, ?_⟩
    rw [eq_of_mem_basicSet (e'.isCompOf W hW') (hW.of_mem hb) he'']
    exact he'.2
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union
    (isOpen_basicSet hW.1 _) hRopen ?_ ?_ ⟨e, mem_connectedComponentIn hW.mem,
      mem_basicSet_self e hW⟩
  · rw [Set.disjoint_left]
    intro e' h1 h2
    exact h2.2 (eq_of_mem_basicSet (e.isCompOf W hW) (hW.of_mem h2.1) h1)
  · intro e' he'
    have hb : e'.base ∈ W := connectedComponentIn_subset (SpreadEnd.base ⁻¹' W) e he'
    by_cases h : e' W = e W
    · exact Or.inl ⟨W, hW.of_mem hb, subset_rfl, h.le⟩
    · exact Or.inr ⟨hb, h⟩

/-- The projection of the Fox completion is a spread. -/
theorem isSpread_base [LocallyConnectedSpace Y] (hp : IsSpread p) :
    IsSpread (SpreadEnd.base : SpreadEnd p → Y) := by
  haveI := locallyConnectedSpace hp
  refine isSpread_iff_of_locallyConnectedSpace.2 ⟨continuous_base, fun e O hO he => ?_⟩
  obtain ⟨W, hW, hWO⟩ := exists_basicSet_subset hO he
  exact ⟨W, hW.1, hW.mem, by rw [connectedComponentIn_base_preimage hp hW]; exact hWO⟩

/-- The Fox completion is complete. -/
theorem isCompleteSpread_base [LocallyConnectedSpace Y] (hp : IsSpread p) :
    IsCompleteSpread (SpreadEnd.base : SpreadEnd p → Y) := by
  intro E _
  have key : ∀ U, IsCNbhd E.base U → ∃ e₀ : SpreadEnd p, IsCNbhd e₀.base U ∧
      E U = basicSet p U (e₀ U) := by
    intro U hU
    obtain ⟨e₀, he₀, hEU⟩ := E.isCompOf U hU
    exact ⟨e₀, hU.of_mem he₀, by rw [hEU, connectedComponentIn_base_preimage hp (hU.of_mem he₀)]⟩
  let e : SpreadEnd p :=
    { base := E.base
      toFun := fun U => if IsCNbhd E.base U then ofPoint p ⁻¹' E U else ∅
      isCompOf := fun U hU => by
        obtain ⟨e₀, he₀, hEU⟩ := key U hU
        show IsCompOf p U (if IsCNbhd E.base U then _ else _)
        rw [if_pos hU, hEU, preimage_ofPoint_basicSet he₀]
        exact e₀.isCompOf U he₀
      mono := fun U V hU hV hUV => by
        show (if IsCNbhd E.base U then ofPoint p ⁻¹' E U else (∅ : Set X)) ⊆
          (if IsCNbhd E.base V then ofPoint p ⁻¹' E V else ∅)
        rw [if_pos hU, if_pos hV]
        exact preimage_mono (E.mono U V hU hV hUV)
      eq_empty := fun U hU => by
        show (if IsCNbhd E.base U then _ else _) = _
        rw [if_neg hU] }
  refine ⟨e, fun U hU => ?_⟩
  obtain ⟨e₀, he₀, hEU⟩ := key U hU
  rw [hEU, mem_basicSet_iff (e₀.isCompOf U he₀) hU]
  show (if IsCNbhd E.base U then _ else _) = _
  rw [if_pos hU, hEU, preimage_ofPoint_basicSet he₀]

/-- The Fox completion of a spread over a Hausdorff base is Hausdorff. -/
instance t2Space [T2Space Y] [LocallyConnectedSpace Y] : T2Space (SpreadEnd p) := by
  refine ⟨fun e e' hne => ?_⟩
  by_cases hb : e.base = e'.base
  · have : ∃ U, IsCNbhd e.base U ∧ e U ≠ e' U := by
      by_contra h
      exact hne (ext_of_isCNbhd hb fun U hU => by
        by_contra h'
        exact h ⟨U, hU, h'⟩)
    obtain ⟨U, hU, hne'⟩ := this
    have hU' : IsCNbhd e'.base U := hb ▸ hU
    refine ⟨basicSet p U (e U), basicSet p U (e' U), isOpen_basicSet hU.1 _,
      isOpen_basicSet hU.1 _, mem_basicSet_self e hU, mem_basicSet_self e' hU', ?_⟩
    rw [Set.disjoint_left]
    intro e'' h1 h2
    have hb'' := hU.of_mem (base_mem_of_mem_basicSet h1)
    exact hne' ((eq_of_mem_basicSet (e.isCompOf U hU) hb'' h1).symm.trans
      (eq_of_mem_basicSet (e'.isCompOf U hU') hb'' h2))
  · obtain ⟨u, v, hu, hv, hbu, hbv, huv⟩ := t2_separation hb
    exact ⟨_, _, hu.preimage continuous_base, hv.preimage continuous_base, hbu, hbv,
      huv.preimage _⟩

end SpreadEnd

/-! ### Completions -/

/-- Fox's notion of a completion (the hypotheses the uniqueness argument uses): a complete spread
`p' : X' → Y` with an embedding `ι : X → X'` over `Y` whose image is dense and locally connected
in `X'`. The paper's completion (`IsSpreadCompletion`) asks moreover that the image be open. -/
structure IsFoxCompletion (p : X → Y) {X' : Type*} [TopologicalSpace X'] (p' : X' → Y)
    (ι : X → X') : Prop where
  isSpread : IsSpread p'
  comm : ∀ x, p' (ι x) = p x
  isEmbedding : IsEmbedding ι
  isComplete : IsCompleteSpread p'
  dense : Dense (range ι)
  isLocallyConnectedIn : IsLocallyConnectedIn (range ι)

/-- `def:complete_spread_spread_completion`. A completion of a spread `p : X → Y`: a spread
`p' : X' → Y` with a spread morphism `(id_Y, ι)` such that `ι` is an embedding, `p'` is complete
and the image of `ι` is portly. -/
structure IsSpreadCompletion (p : X → Y) {X' : Type*} [TopologicalSpace X'] (p' : X' → Y)
    (ι : X → X') : Prop where
  isSpread : IsSpread p'
  comm : ∀ x, p' (ι x) = p x
  isEmbedding : IsEmbedding ι
  isComplete : IsCompleteSpread p'
  isPortly : IsPortly (range ι)

theorem IsSpreadCompletion.toIsFoxCompletion {p : X → Y} {X' : Type*} [TopologicalSpace X']
    {p' : X' → Y} {ι : X → X'} (h : IsSpreadCompletion p p' ι) : IsFoxCompletion p p' ι :=
  ⟨h.isSpread, h.comm, h.isEmbedding, h.isComplete, h.isPortly.dense,
    h.isPortly.locallyConnectedIn⟩

theorem isSpreadCompletion_iff {p : X → Y} {X' : Type*} [TopologicalSpace X'] {p' : X' → Y}
    {ι : X → X'} : IsSpreadCompletion p p' ι ↔ IsFoxCompletion p p' ι ∧ IsOpen (range ι) :=
  ⟨fun h => ⟨h.toIsFoxCompletion, h.isPortly.isOpen⟩, fun ⟨h, ho⟩ =>
    ⟨h.isSpread, h.comm, h.isEmbedding, h.isComplete, ⟨ho, h.dense, h.isLocallyConnectedIn⟩⟩⟩

namespace SpreadEnd

variable {p : X → Y}

/-- The image of `ι` is locally connected in the Fox completion. -/
theorem isLocallyConnectedIn_range_ofPoint [LocallyConnectedSpace Y] (hp : IsSpread p) :
    IsLocallyConnectedIn (range (ofPoint p)) := by
  intro O hO hOc
  refine isPreconnected_of_local hOc inter_subset_left
    (denseRange_ofPoint.open_subset_closure_inter hO) fun e he => ?_
  obtain ⟨W, hW, hWO⟩ := exists_basicSet_subset hO he
  refine ⟨basicSet p W (e W), isOpen_basicSet hW.1 _, mem_basicSet_self e hW, ?_⟩
  have : basicSet p W (e W) ∩ (O ∩ range (ofPoint p)) = ofPoint p '' (e W) := by
    ext e'
    constructor
    · rintro ⟨h1, -, x, rfl⟩
      exact ⟨x, (ofPoint_mem_basicSet_iff hW).1 h1, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have h1 := (ofPoint_mem_basicSet_iff hW).2 hx
      exact ⟨h1, hWO h1, x, rfl⟩
  rw [this]
  exact (e.isPreconnected hW).image _ (continuous_ofPoint hp).continuousOn

/-- **Fox's completion, existence part (Fox's sense).** The space of ends, with `ι = ofPoint`, is
a completion in Fox's sense of any spread with a T0 source over a locally connected base. -/
theorem isFoxCompletion_base [LocallyConnectedSpace Y] [T0Space X] (hp : IsSpread p) :
    IsFoxCompletion p (SpreadEnd.base : SpreadEnd p → Y) (ofPoint p) :=
  ⟨isSpread_base hp, fun _ => rfl, isEmbedding_ofPoint hp, isCompleteSpread_base hp,
    denseRange_ofPoint, isLocallyConnectedIn_range_ofPoint hp⟩

/-- The space of ends is a completion in the paper's sense iff the image of `ι` is open. -/
theorem isSpreadCompletion_base_iff [LocallyConnectedSpace Y] [T0Space X] (hp : IsSpread p) :
    IsSpreadCompletion p (SpreadEnd.base : SpreadEnd p → Y) (ofPoint p) ↔
      IsOpen (range (ofPoint p)) :=
  isSpreadCompletion_iff.trans (and_iff_right (isFoxCompletion_base hp))

end SpreadEnd

namespace IsFoxCompletion

variable {p : X → Y} {X' : Type*} [TopologicalSpace X'] {p' : X' → Y} {ι : X → X'}

/-- Pulling back a component of `p' ⁻¹' U` along `ι` gives a component of `p ⁻¹' U`. -/
theorem isCompOf_preimage (h : IsFoxCompletion p p' ι) {U : Set Y} (hU : IsOpen U) {x' : X'}
    (hx' : p' x' ∈ U) : IsCompOf p U (ι ⁻¹' connectedComponentIn (p' ⁻¹' U) x') := by
  haveI := h.isSpread.locallyConnectedSpace
  set C' := connectedComponentIn (p' ⁻¹' U) x' with hC'
  have hC'open : IsOpen C' := (hU.preimage h.isSpread.continuous).connectedComponentIn
  obtain ⟨_, hz, x₀, rfl⟩ := h.dense.inter_open_nonempty C' hC'open
    ⟨x', mem_connectedComponentIn hx'⟩
  have hx₀U : p x₀ ∈ U := by
    rw [← h.comm]; exact connectedComponentIn_subset (p' ⁻¹' U) x' hz
  refine ⟨x₀, hx₀U, subset_antisymm ?_ ?_⟩
  · have hpc : IsPreconnected (ι ⁻¹' C') := by
      rw [← h.isEmbedding.isInducing.isPreconnected_image, image_preimage_eq_inter_range]
      exact h.isLocallyConnectedIn C' hC'open isPreconnected_connectedComponentIn
    refine hpc.subset_connectedComponentIn hz fun x hx => ?_
    show p x ∈ U
    rw [← h.comm]; exact connectedComponentIn_subset (p' ⁻¹' U) x' hx
  · rw [← image_subset_iff, hC', connectedComponentIn_eq hz]
    refine (isPreconnected_connectedComponentIn.image _
      h.isEmbedding.continuous.continuousOn).subset_connectedComponentIn
      ⟨x₀, mem_connectedComponentIn hx₀U, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    show p' (ι x) ∈ U
    rw [h.comm]; exact connectedComponentIn_subset (p ⁻¹' U) x₀ hx

/-- The comparison map `X' → X̄` of a completion in Fox's sense to the space of ends. -/
def toEnd (h : IsFoxCompletion p p' ι) (x' : X') : SpreadEnd p where
  base := p' x'
  toFun U := if IsCNbhd (p' x') U then ι ⁻¹' connectedComponentIn (p' ⁻¹' U) x' else ∅
  isCompOf U hU := by
    show IsCompOf p U (if IsCNbhd (p' x') U then _ else _)
    rw [if_pos hU]; exact h.isCompOf_preimage hU.1 hU.mem
  mono U V hU hV hUV := by
    show (if IsCNbhd (p' x') U then ι ⁻¹' connectedComponentIn (p' ⁻¹' U) x' else (∅ : Set X))
      ⊆ (if IsCNbhd (p' x') V then ι ⁻¹' connectedComponentIn (p' ⁻¹' V) x' else ∅)
    rw [if_pos hU, if_pos hV]
    exact preimage_mono (connectedComponentIn_mono _ (preimage_mono hUV))
  eq_empty U hU := by
    show (if IsCNbhd (p' x') U then _ else _) = _
    rw [if_neg hU]

theorem toEnd_base (h : IsFoxCompletion p p' ι) (x' : X') : (h.toEnd x').base = p' x' := rfl

theorem toEnd_apply (h : IsFoxCompletion p p' ι) {x' : X'} {U : Set Y} (hU : IsCNbhd (p' x') U) :
    h.toEnd x' U = ι ⁻¹' connectedComponentIn (p' ⁻¹' U) x' := by
  show (if IsCNbhd (p' x') U then _ else _) = _
  rw [if_pos hU]

theorem toEnd_comp (h : IsFoxCompletion p p' ι) (x : X) : h.toEnd (ι x) = SpreadEnd.ofPoint p x := by
  refine SpreadEnd.ext_of_isCNbhd (h.comm x) fun U hU => ?_
  have hU' : IsCNbhd (p x) U := by rw [← h.comm]; exact hU
  rw [h.toEnd_apply hU, SpreadEnd.ofPoint_apply hU']
  exact (h.isCompOf_preimage hU.1 hU.mem).eq_of_mem (mem_connectedComponentIn hU.mem)

theorem continuous_toEnd [LocallyConnectedSpace Y] (h : IsFoxCompletion p p' ι) :
    Continuous h.toEnd := by
  haveI := h.isSpread.locallyConnectedSpace
  refine continuous_iff_continuousAt.2 fun x' =>
    ((SpreadEnd.hasBasis_nhds (h.toEnd x')).tendsto_right_iff).2 fun W hW => ?_
  have hW' : IsCNbhd (p' x') W := hW
  refine mem_of_superset ((hW'.1.preimage h.isSpread.continuous).connectedComponentIn.mem_nhds
    (mem_connectedComponentIn hW'.mem)) fun x'' hx'' => ?_
  have hW'' : IsCNbhd (p' x'') W :=
    hW'.of_mem (connectedComponentIn_subset (p' ⁻¹' W) x' hx'')
  show h.toEnd x'' ∈ SpreadEnd.basicSet p W (h.toEnd x' W)
  refine ⟨W, hW'', subset_rfl, ?_⟩
  rw [h.toEnd_apply hW'', h.toEnd_apply hW', connectedComponentIn_eq hx'']

theorem isInducing_toEnd [LocallyConnectedSpace Y] (h : IsFoxCompletion p p' ι) :
    IsInducing h.toEnd := by
  haveI := h.isSpread.locallyConnectedSpace
  refine isInducing_iff_nhds.2 fun x' =>
    le_antisymm (h.continuous_toEnd.tendsto x').le_comap ?_
  intro O hO
  obtain ⟨O', hO'O, hO', hxO'⟩ := mem_nhds_iff.1 hO
  obtain ⟨U, hU, hxU, hcomp⟩ := (isSpread_iff.1 h.isSpread).2.2 x' O' hO' hxO'
  obtain ⟨W, hW, hWU⟩ := exists_isCNbhd_subset hU hxU
  refine mem_comap.2 ⟨SpreadEnd.basicSet p W (h.toEnd x' W),
    (SpreadEnd.isOpen_basicSet hW.1 _).mem_nhds (SpreadEnd.mem_basicSet_self _ hW), ?_⟩
  rintro x'' ⟨V, hV, hVW, hVsub⟩
  have hV' : IsCNbhd (p' x'') V := hV
  rw [h.toEnd_apply hV', h.toEnd_apply hW] at hVsub
  have hopen : IsOpen (connectedComponentIn (p' ⁻¹' V) x'') :=
    (hV'.1.preimage h.isSpread.continuous).connectedComponentIn
  obtain ⟨_, hz, z, rfl⟩ := h.dense.inter_open_nonempty _ hopen
    ⟨x'', mem_connectedComponentIn hV'.mem⟩
  have hzW := hVsub (show z ∈ ι ⁻¹' _ from hz)
  have : connectedComponentIn (p' ⁻¹' V) x'' ⊆ connectedComponentIn (p' ⁻¹' W) x' := by
    rw [connectedComponentIn_eq hzW]
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hz
      ((connectedComponentIn_subset _ _).trans (preimage_mono hVW))
  exact hO'O (hcomp (connectedComponentIn_mono _ (preimage_mono hWU)
    (this (mem_connectedComponentIn hV'.mem))))

theorem comp_eq_of_mem (h : IsFoxCompletion p p' ι) {e : SpreadEnd p} {U : Set Y}
    (hU : IsCNbhd e.base U) {z₁ z₂ : X} (hz₁ : z₁ ∈ e U) (hz₂ : z₂ ∈ e U) :
    connectedComponentIn (p' ⁻¹' U) (ι z₁) = connectedComponentIn (p' ⁻¹' U) (ι z₂) :=
  connectedComponentIn_eq (((e.isPreconnected hU).image ι
    h.isEmbedding.continuous.continuousOn).subset_connectedComponentIn ⟨z₁, hz₁, rfl⟩
    (image_subset_iff.2 fun z hz => by
      show p' (ι z) ∈ U
      rw [h.comm]; exact e.subset_preimage hU hz) ⟨z₂, hz₂, rfl⟩)

/-- The comparison map is surjective: every end of `p` is realised in a completion. -/
theorem surjective_toEnd [T1Space Y] [LocallyConnectedSpace Y] (h : IsFoxCompletion p p' ι) :
    Surjective h.toEnd := by
  intro e
  let E : SpreadEnd p' :=
    { base := e.base
      toFun := fun U => if hU : IsCNbhd e.base U then
        connectedComponentIn (p' ⁻¹' U) (ι (e.nonempty hU).some) else ∅
      isCompOf := fun U hU => by
        show IsCompOf p' U (if hU : IsCNbhd e.base U then _ else _)
        rw [dif_pos hU]
        refine isCompOf_connectedComponentIn ?_
        rw [h.comm]; exact e.subset_preimage hU (e.nonempty hU).some_mem
      mono := fun U V hU hV hUV => by
        show (if hU : IsCNbhd e.base U then
            connectedComponentIn (p' ⁻¹' U) (ι (e.nonempty hU).some) else (∅ : Set X')) ⊆
          (if hV : IsCNbhd e.base V then
            connectedComponentIn (p' ⁻¹' V) (ι (e.nonempty hV).some) else ∅)
        rw [dif_pos hU, dif_pos hV,
          h.comp_eq_of_mem hV (e.nonempty hV).some_mem
            (e.mono U V hU hV hUV (e.nonempty hU).some_mem)]
        exact connectedComponentIn_mono _ (preimage_mono hUV)
      eq_empty := fun U hU => by
        show (if hU : IsCNbhd e.base U then _ else _) = _
        rw [dif_neg hU] }
  have hE : ∀ U (hU : IsCNbhd e.base U), E U =
      connectedComponentIn (p' ⁻¹' U) (ι (e.nonempty hU).some) := fun U hU => by
    show (if hU : IsCNbhd e.base U then _ else _) = _
    rw [dif_pos hU]
  have hcl : E.base ∈ closure (range p') :=
    closure_mono (by rintro _ ⟨x, rfl⟩; exact ⟨ι x, h.comm x⟩) e.base_mem_closure
  obtain ⟨x', hx'⟩ := h.isComplete E hcl
  have hb : p' x' = e.base :=
    eq_of_forall_isCNbhd fun U hU => E.subset_preimage hU (hx' U hU)
  refine ⟨x', SpreadEnd.ext_of_isCNbhd hb fun U hU => ?_⟩
  have hU' : IsCNbhd e.base U := by rw [← hb]; exact hU
  have hx'U : x' ∈ E U := hx' U hU'
  rw [hE U hU'] at hx'U
  rw [h.toEnd_apply hU, ← connectedComponentIn_eq hx'U]
  exact ((h.isCompOf_preimage hU'.1 (by
      rw [h.comm]; exact e.subset_preimage hU' (e.nonempty hU').some_mem)).eq_of_mem
    (show (e.nonempty hU').some ∈ ι ⁻¹' _ from mem_connectedComponentIn (by
      show p' (ι _) ∈ U
      rw [h.comm]; exact e.subset_preimage hU' (e.nonempty hU').some_mem))).trans
    ((e.isCompOf U hU').eq_of_mem (e.nonempty hU').some_mem).symm

/-- A completion in Fox's sense is homeomorphic to the space of ends, over `Y` and under `X`. -/
def homeomorph [T1Space Y] [LocallyConnectedSpace Y] [T0Space X']
    (h : IsFoxCompletion p p' ι) : X' ≃ₜ SpreadEnd p :=
  (Equiv.ofBijective h.toEnd ⟨h.isInducing_toEnd.injective, h.surjective_toEnd⟩)
    |>.toHomeomorphOfIsInducing h.isInducing_toEnd

@[simp] theorem homeomorph_apply [T1Space Y] [LocallyConnectedSpace Y] [T0Space X']
    (h : IsFoxCompletion p p' ι) (x' : X') : h.homeomorph x' = h.toEnd x' := rfl

end IsFoxCompletion

/-! ### Uniqueness and existence -/

namespace IsFoxCompletion

variable {p : X → Y}

/-- **Fox's completion theorem, uniqueness.** Two completions (in Fox's sense, a fortiori in the
paper's) of the same spread are isomorphic over `Y` and under `X`, by a unique homeomorphism. -/
theorem existsUnique_homeomorph [T2Space Y] [LocallyConnectedSpace Y] {X₁ X₂ : Type*}
    [TopologicalSpace X₁] [TopologicalSpace X₂] [T0Space X₁] [T0Space X₂] {p₁ : X₁ → Y}
    {p₂ : X₂ → Y} {ι₁ : X → X₁} {ι₂ : X → X₂} (h₁ : IsFoxCompletion p p₁ ι₁)
    (h₂ : IsFoxCompletion p p₂ ι₂) :
    ∃! φ : X₁ ≃ₜ X₂, (∀ x, p₂ (φ x) = p₁ x) ∧ ∀ x, φ (ι₁ x) = ι₂ x := by
  refine ⟨h₁.homeomorph.trans h₂.homeomorph.symm, ⟨fun x => ?_, fun x => ?_⟩, ?_⟩
  · show p₂ (h₂.homeomorph.symm (h₁.homeomorph x)) = p₁ x
    rw [← h₂.toEnd_base, ← h₂.homeomorph_apply, h₂.homeomorph.apply_symm_apply]
    rfl
  · show h₂.homeomorph.symm (h₁.homeomorph (ι₁ x)) = ι₂ x
    rw [Homeomorph.symm_apply_eq, homeomorph_apply, homeomorph_apply, toEnd_comp, toEnd_comp]
  · rintro φ ⟨-, hφ⟩
    haveI : T2Space X₂ := h₂.homeomorph.symm.t2Space
    have hψ : ∀ x, (h₁.homeomorph.trans h₂.homeomorph.symm) (ι₁ x) = ι₂ x := fun x => by
      show h₂.homeomorph.symm (h₁.homeomorph (ι₁ x)) = ι₂ x
      rw [Homeomorph.symm_apply_eq, homeomorph_apply, homeomorph_apply, toEnd_comp, toEnd_comp]
    have := DenseRange.equalizer h₁.dense φ.continuous
      (h₁.homeomorph.trans h₂.homeomorph.symm).continuous
      (funext fun x => (hφ x).trans (hψ x).symm)
    exact Homeomorph.ext (congrFun this)

end IsFoxCompletion

/-- **Fox's completion theorem, uniqueness (paper's completions).** -/
theorem IsSpreadCompletion.existsUnique_homeomorph [T2Space Y] [LocallyConnectedSpace Y]
    {p : X → Y} {X₁ X₂ : Type*} [TopologicalSpace X₁] [TopologicalSpace X₂] [T0Space X₁]
    [T0Space X₂] {p₁ : X₁ → Y} {p₂ : X₂ → Y} {ι₁ : X → X₁} {ι₂ : X → X₂}
    (h₁ : IsSpreadCompletion p p₁ ι₁) (h₂ : IsSpreadCompletion p p₂ ι₂) :
    ∃! φ : X₁ ≃ₜ X₂, (∀ x, p₂ (φ x) = p₁ x) ∧ ∀ x, φ (ι₁ x) = ι₂ x :=
  h₁.toIsFoxCompletion.existsUnique_homeomorph h₂.toIsFoxCompletion

/-- If a spread has a completion (paper's sense), the image of `X` in its space of ends is
open. -/
theorem IsSpreadCompletion.isOpen_range_ofPoint [T1Space Y] [LocallyConnectedSpace Y]
    {p : X → Y} {X' : Type*} [TopologicalSpace X'] [T0Space X'] {p' : X' → Y} {ι : X → X'}
    (h : IsSpreadCompletion p p' ι) : IsOpen (range (SpreadEnd.ofPoint p)) := by
  have : range (SpreadEnd.ofPoint p) = h.toIsFoxCompletion.homeomorph '' range ι := by
    rw [← range_comp]
    congr 1
    funext x
    exact (h.toIsFoxCompletion.toEnd_comp x).symm
  rw [this]
  exact h.toIsFoxCompletion.homeomorph.isOpenMap _ h.isPortly.isOpen

/-- **Fox's completion theorem, existence (corrected).** A spread (T0 source, Hausdorff locally
connected base) admits a completion in the paper's sense iff the image of `X` in its space of ends
is open; the space of ends is then one. -/
theorem exists_isSpreadCompletion_iff {X₀ : Type u} {Y₀ : Type v} [TopologicalSpace X₀]
    [TopologicalSpace Y₀] [T0Space X₀] [T2Space Y₀] [LocallyConnectedSpace Y₀] {p : X₀ → Y₀}
    (hp : IsSpread p) :
    (∃ (X' : Type (max u v)) (_ : TopologicalSpace X') (_ : T0Space X') (p' : X' → Y₀)
      (ι : X₀ → X'),
      IsSpreadCompletion p p' ι) ↔ IsOpen (range (SpreadEnd.ofPoint p)) := by
  constructor
  · rintro ⟨X', _, _, p', ι, h⟩
    exact h.isOpen_range_ofPoint
  · intro ho
    exact ⟨SpreadEnd p, inferInstance, inferInstance, SpreadEnd.base, SpreadEnd.ofPoint p,
      (SpreadEnd.isSpreadCompletion_base_iff hp).2 ho⟩

/-- **Fox's completion theorem, non-existence (any universe).** If the image of `X` in its space
of ends is not open, the spread has no completion in the paper's sense, in any universe. -/
theorem not_isSpreadCompletion_of_not_isOpen [T1Space Y] [LocallyConnectedSpace Y] {p : X → Y}
    (h : ¬ IsOpen (range (SpreadEnd.ofPoint p))) {X' : Type*} [TopologicalSpace X'] [T0Space X']
    (p' : X' → Y) (ι : X → X') : ¬ IsSpreadCompletion p p' ι :=
  fun hc => h hc.isOpen_range_ofPoint

/-- In a second countable space, the components of an open set (of a locally connected space)
are countably many. -/
theorem countable_isCompOf {Z B : Type*} [TopologicalSpace Z] [TopologicalSpace B]
    [SecondCountableTopology Z] [LocallyConnectedSpace Z] {q : Z → B} (hq : Continuous q)
    {U : Set B} (hU : IsOpen U) : {C : Set Z | IsCompOf q U C}.Countable := by
  refine Set.PairwiseDisjoint.countable_of_isOpen (s := id) ?_ ?_ fun C hC => hC.nonempty
  · intro C hC D hD hne
    rw [onFun, id, id, Set.disjoint_iff_inter_eq_empty]
    by_contra h
    exact hne (hC.eq_of_meets hD (nonempty_iff_ne_empty.2 h))
  · rintro C ⟨x, -, rfl⟩
    exact (hU.preimage hq).connectedComponentIn

namespace SpreadEnd

variable {p : X → Y}

/-- A sufficient condition for the existence of a completion: `p` lands in an open `V` over which
every end is realised. -/
theorem isOpen_range_ofPoint_of_forall [T1Space Y] [LocallyConnectedSpace Y] {V : Set Y}
    (hV : IsOpen V) (hpV : range p ⊆ V)
    (hc : ∀ e : SpreadEnd p, e.base ∈ V → ∃ x, ∀ U, IsCNbhd e.base U → x ∈ e U) :
    IsOpen (range (ofPoint p)) := by
  have : range (ofPoint p) = SpreadEnd.base ⁻¹' V := by
    ext e
    constructor
    · rintro ⟨x, rfl⟩; exact hpV (mem_range_self x)
    · intro he
      obtain ⟨x, hx⟩ := hc e he
      exact ⟨x, (eq_ofPoint_iff e x).2 hx⟩
  rw [this]; exact hV.preimage continuous_base

/-- An end over a point with an evenly covered neighbourhood is realised. -/
theorem exists_mem_of_isEvenlyCoveredSet [LocallyConnectedSpace Y] (e : SpreadEnd p)
    {U : Set Y} (hU : IsOpen U) (heU : e.base ∈ U) (hcov : IsEvenlyCoveredSet p U) :
    ∃ x, ∀ V, IsCNbhd e.base V → x ∈ e V := by
  obtain ⟨W, hW, hWU⟩ := exists_isCNbhd_subset hU heU
  obtain ⟨x₀, hx₀⟩ := e.nonempty hW
  have hx₀U : x₀ ∈ p ⁻¹' U := hWU (e.subset_preimage hW hx₀)
  obtain ⟨φ, hφ⟩ := hcov x₀ hx₀U
  set z : X := (φ.symm ⟨e.base, heU⟩ : X) with hz
  have hzS : z ∈ (connectedComponentIn (p ⁻¹' U) x₀) := (φ.symm ⟨e.base, heU⟩).2
  have hpz : p z = e.base := by
    have := hφ (φ.symm ⟨e.base, heU⟩)
    rw [φ.apply_symm_apply] at this
    exact this.symm
  have heW : e W ⊆ (connectedComponentIn (p ⁻¹' U) x₀) := (e.isPreconnected hW).subset_connectedComponentIn hx₀
    fun x hx => hWU (e.subset_preimage hW hx)
  refine ⟨z, fun V hV => ?_⟩
  obtain ⟨V', hV', hV'V, hV'W⟩ := exists_isCNbhd_subset_inter hV hW
  have hT : IsPreconnected (connectedComponentIn (p ⁻¹' U) x₀ ∩ p ⁻¹' V') := by
    have hA : IsPreconnected ((↑) ⁻¹' V' : Set U) := by
      rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
        inter_eq_right.2 (hV'W.trans hWU)]
      exact hV'.isPreconnected
    have hset : (connectedComponentIn (p ⁻¹' U) x₀) ∩ p ⁻¹' V' = (↑) '' (φ ⁻¹' ((↑) ⁻¹' V' : Set U)) := by
      ext x
      constructor
      · rintro ⟨hxS, hxV⟩
        refine ⟨⟨x, hxS⟩, ?_, rfl⟩
        show ((φ ⟨x, hxS⟩ : U) : Y) ∈ V'
        rw [hφ]; exact hxV
      · rintro ⟨s, hs, rfl⟩
        refine ⟨s.2, ?_⟩
        show p s ∈ V'
        rw [← hφ]; exact hs
    rw [hset, ← φ.image_symm]
    exact (hA.image _ φ.symm.continuous.continuousOn).image _ continuous_subtype_val.continuousOn
  obtain ⟨x₁, hx₁⟩ := e.nonempty hV'
  have hsub : (connectedComponentIn (p ⁻¹' U) x₀) ∩ p ⁻¹' V' ⊆ e V' := by
    rw [(e.isCompOf V' hV').eq_of_mem hx₁]
    exact hT.subset_connectedComponentIn ⟨heW (e.mono _ _ hV' hW hV'W hx₁),
      e.subset_preimage hV' hx₁⟩ inter_subset_right
  exact e.mono V' V hV' hV hV'V (hsub ⟨hzS, show p z ∈ V' by rw [hpz]; exact hV'.mem⟩)

/-- **The completion of an ordinary covering.** If `p` lands in an open `V` contained in its
ordinary locus (e.g. `p` restricts to a covering `X → V` of an open — for instance portly —
`V ⊆ Y`), then the space of ends is a completion of `p` in the paper's sense. -/
theorem isSpreadCompletion_base_of_subset_ordY [T1Space Y] [LocallyConnectedSpace Y] [T0Space X]
    (hp : IsSpread p) {V : Set Y} (hV : IsOpen V) (hpV : range p ⊆ V) (hVord : V ⊆ ordY p) :
    IsSpreadCompletion p (SpreadEnd.base : SpreadEnd p → Y) (ofPoint p) := by
  refine (isSpreadCompletion_base_iff hp).2 (isOpen_range_ofPoint_of_forall hV hpV fun e he => ?_)
  obtain ⟨U, hU, heU, -, hcov⟩ := hVord he
  exact e.exists_mem_of_isEvenlyCoveredSet hU heU hcov

/-- A complete spread is its own completion. -/
theorem isSpreadCompletion_id [T0Space X] (hp : IsSpread p) (hc : IsCompleteSpread p) :
    IsSpreadCompletion p p id :=
  ⟨hp, fun _ => rfl, IsEmbedding.id, hc, by rw [range_id]; exact isPortly_univ⟩

/-- For a complete spread, `ι : X → X̄` is a homeomorphism onto the space of ends. -/
theorem surjective_ofPoint_of_isCompleteSpread [T1Space Y] [LocallyConnectedSpace Y]
    (hc : IsCompleteSpread p) : Surjective (ofPoint p) := fun e =>
  let ⟨x, hx⟩ := hc e e.base_mem_closure
  ⟨x, (eq_ofPoint_iff e x).2 hx⟩

/-! ### Countability axioms -/

/-- The Fox completion of a spread over a first countable base is first countable. -/
instance firstCountableTopology [LocallyConnectedSpace Y] [FirstCountableTopology Y] :
    FirstCountableTopology (SpreadEnd p) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨s, hs⟩ := (𝓝 e.base).exists_antitone_basis
  have hW : ∀ n, ∃ W, IsCNbhd e.base W ∧ W ⊆ s n := fun n =>
    (hasBasis_nhds_isCNbhd e.base).mem_iff.1 (hs.mem n)
  choose W hWc hWs using hW
  have hb : (𝓝 e).HasBasis (fun _ : ℕ => True) (fun n => basicSet p (W n) (e (W n))) := by
    refine (hasBasis_nhds e).to_hasBasis (fun V hV => ?_) fun n _ => ⟨W n, hWc n, subset_rfl⟩
    obtain ⟨n, -, hn⟩ := hs.toHasBasis.mem_iff.1 (hV.1.mem_nhds hV.mem)
    exact ⟨n, trivial, basicSet_mono e (hWc n) hV ((hWs n).trans hn)⟩
  exact hb.isCountablyGenerated

/-- The Fox completion of a spread with a second countable source over a second countable base
is second countable. -/
theorem secondCountableTopology [LocallyConnectedSpace Y] [SecondCountableTopology Y]
    [SecondCountableTopology X] (hp : IsSpread p) : SecondCountableTopology (SpreadEnd p) := by
  haveI := hp.locallyConnectedSpace
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis Y
  set 𝓑 : Set (Set Y) := ⋃ B ∈ b, {C | IsCompOf id B C} with h𝓑
  have h𝓑c : 𝓑.Countable := hbc.biUnion fun B hB =>
    countable_isCompOf continuous_id (hb.isOpen hB)
  set 𝓒 : Set (Set (SpreadEnd p)) :=
    ⋃ W ∈ 𝓑, (fun D => basicSet p W D) '' {D | IsCompOf p W D} with h𝓒
  have hW𝓑 : ∀ W ∈ 𝓑, IsOpen W := by
    intro W hW
    obtain ⟨B, hB, y, -, rfl⟩ := mem_iUnion₂.1 hW
    exact (hb.isOpen hB).connectedComponentIn
  refine (TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (s := 𝓒) ?_ ?_).secondCountableTopology
    (h𝓑c.biUnion fun W hW => (countable_isCompOf hp.continuous (hW𝓑 W hW)).image _)
  · intro O hO
    obtain ⟨W, hW, D, -, rfl⟩ := mem_iUnion₂.1 hO
    exact isOpen_basicSet (hW𝓑 W hW) D
  · intro e O heO hO
    obtain ⟨W, hW, hWO⟩ := exists_basicSet_subset hO heO
    obtain ⟨B, hB, heB, hBW⟩ := hb.exists_subset_of_mem_open hW.mem hW.1
    set W' := connectedComponentIn B e.base
    have hW' : IsCNbhd e.base W' := ⟨(hb.isOpen hB).connectedComponentIn,
      isPreconnected_connectedComponentIn, mem_connectedComponentIn heB⟩
    refine ⟨basicSet p W' (e W'), mem_iUnion₂.2 ⟨W', mem_iUnion₂.2 ⟨B, hB, e.base, heB, rfl⟩,
      e W', e.isCompOf W' hW', rfl⟩, mem_basicSet_self e hW', ?_⟩
    exact (basicSet_mono e hW' hW ((connectedComponentIn_subset _ _).trans hBW)).trans hWO

/-! ### Local path-connectedness -/

/-- In a locally path-connected source, the components chosen by an end are path-connected. -/
theorem isPathConnected_apply [LocPathConnectedSpace X] (hp : IsSpread p) (e : SpreadEnd p)
    {U : Set Y} (hU : IsCNbhd e.base U) : IsPathConnected (e U) := by
  obtain ⟨x, hx, hxe⟩ := e.isCompOf U hU
  rw [hxe]
  exact ((hU.1.preimage hp.continuous).connectedComponentIn).isConnected_iff_isPathConnected.1
    (isConnected_connectedComponentIn_iff.2 hx)

/-- Every end of a basic set `basicSet W (e W)` is joined, inside it, to a point of `X`. -/
theorem exists_joinedIn_ofPoint [LocPathConnectedSpace X] [LocallyConnectedSpace Y]
    [FirstCountableTopology Y] (hp : IsSpread p) {e : SpreadEnd p} {W : Set Y}
    (hW : IsCNbhd e.base W) {e' : SpreadEnd p} (he' : e' ∈ basicSet p W (e W)) :
    ∃ x ∈ e W, JoinedIn (basicSet p W (e W)) (ofPoint p x) e' := by
  have hb' : e'.base ∈ W := base_mem_of_mem_basicSet he'
  have hW' : IsCNbhd e'.base W := hW.of_mem hb'
  have he'W : e' W = e W := eq_of_mem_basicSet (e.isCompOf W hW) hW' he'
  obtain ⟨s, hs⟩ := (𝓝 e'.base).exists_antitone_basis
  set V : ℕ → Set Y := fun n => connectedComponentIn (interior (s n) ∩ W) e'.base with hVdef
  have hV : ∀ n, IsCNbhd e'.base (V n) := fun n =>
    ⟨(isOpen_interior.inter hW.1).connectedComponentIn, isPreconnected_connectedComponentIn,
      mem_connectedComponentIn ⟨mem_interior_iff_mem_nhds.2 (hs.mem n), hb'⟩⟩
  have hVW : ∀ n, V n ⊆ W := fun n => (connectedComponentIn_subset _ _).trans inter_subset_right
  have hVs : ∀ n, V n ⊆ s n := fun n =>
    (connectedComponentIn_subset _ _).trans (inter_subset_left.trans interior_subset)
  have hVanti : Antitone V := fun m n hmn =>
    connectedComponentIn_mono _ (inter_subset_inter_left _ (interior_mono (hs.antitone hmn)))
  choose c hc using fun n => e'.nonempty (hV n)
  have hpath : ∀ n, JoinedIn (e' (V n)) (c n) (c (n + 1)) := fun n =>
    (isPathConnected_apply hp e' (hV n)).joinedIn _ (hc n) _
      (e'.mono _ _ (hV (n + 1)) (hV n) (hVanti n.le_succ) (hc (n + 1)))
  set φ : ∀ n, Path (ofPoint p (c n)) (ofPoint p (c (n + 1))) := fun n =>
    (hpath n).somePath.map (continuous_ofPoint hp)
  have hφmem : ∀ n t, φ n t ∈ basicSet p (V n) (e' (V n)) := fun n t =>
    (ofPoint_mem_basicSet_iff (hV n)).2 ((hpath n).somePath_mem t)
  have hφ : ∀ N ∈ 𝓝 e', ∀ᶠ n in atTop, ∀ t, φ n t ∈ N := by
    intro N hN
    obtain ⟨U, hU, hUN⟩ := (hasBasis_nhds e').mem_iff.1 hN
    obtain ⟨k, hk⟩ := hs.toHasBasis.mem_iff.1 (hU.1.mem_nhds hU.mem)
    refine eventually_atTop.2 ⟨k, fun n hn t => hUN ?_⟩
    exact basicSet_mono e' (hV n) hU ((hVs n).trans ((hs.antitone hn).trans hk.2)) (hφmem n t)
  obtain ⟨γ, hγ⟩ := Path.exists_infConcat φ hφ
  refine ⟨c 0, he'W ▸ e'.mono _ _ (hV 0) hW' (hVW 0) (hc 0), γ, fun t => ?_⟩
  rcases (t.2.2 : (t : ℝ) ≤ 1).lt_or_eq with ht | ht
  · obtain ⟨n, u, hu⟩ := hγ t ht
    rw [hu]
    have := basicSet_mono e' (hV n) hW' (hVW n) (hφmem n u)
    rwa [he'W] at this
  · have : t = 1 := Subtype.ext ht
    rw [this, γ.target]
    exact he'

/-- The basic sets of the Fox completion are path-connected (locally path-connected source, first
countable locally connected base). -/
theorem isPathConnected_basicSet [LocPathConnectedSpace X] [LocallyConnectedSpace Y]
    [FirstCountableTopology Y] (hp : IsSpread p) {e : SpreadEnd p} {W : Set Y}
    (hW : IsCNbhd e.base W) : IsPathConnected (basicSet p W (e W)) := by
  obtain ⟨x₀, hx₀⟩ := e.nonempty hW
  refine ⟨ofPoint p x₀, (ofPoint_mem_basicSet_iff hW).2 hx₀, fun e' he' => ?_⟩
  obtain ⟨x, hx, hj⟩ := exists_joinedIn_ofPoint hp hW he'
  refine JoinedIn.trans ?_ hj
  exact (((isPathConnected_apply hp e hW).joinedIn _ hx₀ _ hx).map
    (continuous_ofPoint hp)).mono (image_ofPoint_subset_basicSet hW)

/-- **The Fox completion is locally path-connected** (locally path-connected source, first
countable locally connected base). -/
theorem locPathConnectedSpace [LocPathConnectedSpace X] [LocallyConnectedSpace Y]
    [FirstCountableTopology Y] (hp : IsSpread p) : LocPathConnectedSpace (SpreadEnd p) :=
  LocPathConnectedSpace.of_bases hasBasis_nhds fun _ _ hW => isPathConnected_basicSet hp hW

end SpreadEnd

/-! ### Functoriality: extension of spread morphisms to completions -/

namespace SpreadEnd

variable {X₁ Y₁ X₂ Y₂ : Type*} [TopologicalSpace X₁] [TopologicalSpace Y₁] [TopologicalSpace X₂]
  [TopologicalSpace Y₂] {p₁ : X₁ → Y₁} {p₂ : X₂ → Y₂} {f : Y₁ → Y₂} {g : X₁ → X₂}

/-- The connected component of `y` in `f ⁻¹' V`, a connected open neighbourhood of `y`. -/
theorem isCNbhd_connectedComponentIn_preimage [LocallyConnectedSpace Y₁] (hf : Continuous f)
    {y : Y₁} {V : Set Y₂} (hV : IsCNbhd (f y) V) :
    IsCNbhd y (connectedComponentIn (f ⁻¹' V) y) :=
  ⟨(hV.1.preimage hf).connectedComponentIn, isPreconnected_connectedComponentIn,
    mem_connectedComponentIn hV.mem⟩

theorem comp_eq_of_mem_image (hg : Continuous g) (hcomm : ∀ x, p₂ (g x) = f (p₁ x))
    {S : Set X₁} (hS : IsPreconnected S) {V : Set Y₂} (hSV : S ⊆ p₁ ⁻¹' (f ⁻¹' V)) {z₁ z₂ : X₁}
    (hz₁ : z₁ ∈ S) (hz₂ : z₂ ∈ S) :
    connectedComponentIn (p₂ ⁻¹' V) (g z₁) = connectedComponentIn (p₂ ⁻¹' V) (g z₂) :=
  connectedComponentIn_eq ((hS.image g hg.continuousOn).subset_connectedComponentIn
    ⟨z₁, hz₁, rfl⟩ (image_subset_iff.2 fun z hz => by
      show p₂ (g z) ∈ V
      rw [hcomm]; exact hSV hz) ⟨z₂, hz₂, rfl⟩)

/-- The extension of a spread morphism `(f, g)` to the spaces of ends. -/
def map [LocallyConnectedSpace Y₁] (hf : Continuous f) (hg : Continuous g)
    (hcomm : ∀ x, p₂ (g x) = f (p₁ x)) (e : SpreadEnd p₁) : SpreadEnd p₂ where
  base := f e.base
  toFun V := if hV : IsCNbhd (f e.base) V then connectedComponentIn (p₂ ⁻¹' V)
      (g (e.nonempty (isCNbhd_connectedComponentIn_preimage hf hV)).some) else ∅
  isCompOf V hV := by
    show IsCompOf p₂ V (if hV : IsCNbhd (f e.base) V then _ else _)
    rw [dif_pos hV]
    refine isCompOf_connectedComponentIn ?_
    rw [hcomm]
    exact connectedComponentIn_subset (f ⁻¹' V) e.base (e.subset_preimage
      (isCNbhd_connectedComponentIn_preimage hf hV)
      (e.nonempty (isCNbhd_connectedComponentIn_preimage hf hV)).some_mem)
  mono V V' hV hV' hVV' := by
    show (if hV : IsCNbhd (f e.base) V then connectedComponentIn (p₂ ⁻¹' V)
      (g (e.nonempty (isCNbhd_connectedComponentIn_preimage hf hV)).some) else (∅ : Set X₂)) ⊆
      (if hV : IsCNbhd (f e.base) V' then connectedComponentIn (p₂ ⁻¹' V')
      (g (e.nonempty (isCNbhd_connectedComponentIn_preimage hf hV)).some) else ∅)
    rw [dif_pos hV, dif_pos hV']
    have hW := isCNbhd_connectedComponentIn_preimage hf hV
    have hW' := isCNbhd_connectedComponentIn_preimage hf hV'
    have hWW' : connectedComponentIn (f ⁻¹' V) e.base ⊆ connectedComponentIn (f ⁻¹' V') e.base :=
      connectedComponentIn_mono _ (preimage_mono hVV')
    rw [comp_eq_of_mem_image hg hcomm (e.isPreconnected hW')
      (fun x hx => connectedComponentIn_subset (f ⁻¹' V') e.base (e.subset_preimage hW' hx))
      (e.nonempty hW').some_mem (e.mono _ _ hW hW' hWW' (e.nonempty hW).some_mem)]
    exact connectedComponentIn_mono _ (preimage_mono hVV')
  eq_empty V hV := by
    show (if hV : IsCNbhd (f e.base) V then _ else _) = _
    rw [dif_neg hV]

@[simp] theorem map_base [LocallyConnectedSpace Y₁] (hf : Continuous f) (hg : Continuous g)
    (hcomm : ∀ x, p₂ (g x) = f (p₁ x)) (e : SpreadEnd p₁) :
    (map hf hg hcomm e).base = f e.base := rfl

/-- The value of the extension: the component containing `g(χ(W))` for any connected open
neighbourhood `W ⊆ f ⁻¹' V` of the base. -/
theorem map_apply [LocallyConnectedSpace Y₁] (hf : Continuous f) (hg : Continuous g)
    (hcomm : ∀ x, p₂ (g x) = f (p₁ x)) (e : SpreadEnd p₁) {V : Set Y₂}
    (hV : IsCNbhd (f e.base) V) {W : Set Y₁} (hW : IsCNbhd e.base W) (hWV : W ⊆ f ⁻¹' V)
    {x : X₁} (hx : x ∈ e W) : map hf hg hcomm e V = connectedComponentIn (p₂ ⁻¹' V) (g x) := by
  show (if hV : IsCNbhd (f e.base) V then _ else _) = _
  rw [dif_pos hV]
  have hW₀ := isCNbhd_connectedComponentIn_preimage hf hV
  obtain ⟨W'', hW'', hW''1, hW''2⟩ := exists_isCNbhd_subset_inter hW hW₀
  obtain ⟨z, hz⟩ := e.nonempty hW''
  rw [comp_eq_of_mem_image hg hcomm (e.isPreconnected hW₀)
      (fun x hx => connectedComponentIn_subset (f ⁻¹' V) e.base (e.subset_preimage hW₀ hx))
      (e.nonempty hW₀).some_mem (e.mono _ _ hW'' hW₀ hW''2 hz),
    comp_eq_of_mem_image hg hcomm (e.isPreconnected hW)
      (fun x hx => hWV (e.subset_preimage hW hx)) (e.mono _ _ hW'' hW hW''1 hz) hx]

/-- The extension extends: `ḡ ∘ ι₁ = ι₂ ∘ g`. -/
theorem map_ofPoint [LocallyConnectedSpace Y₁] (hf : Continuous f) (hg : Continuous g)
    (hcomm : ∀ x, p₂ (g x) = f (p₁ x)) (x : X₁) :
    map hf hg hcomm (ofPoint p₁ x) = ofPoint p₂ (g x) := by
  refine ext_of_isCNbhd (hcomm x).symm fun V hV => ?_
  have hV' : IsCNbhd (p₂ (g x)) V := by rw [hcomm]; exact hV
  have hW := isCNbhd_connectedComponentIn_preimage hf hV
  rw [map_apply hf hg hcomm _ hV hW (connectedComponentIn_subset _ _) (mem_ofPoint hW),
    ofPoint_apply hV']

/-- The extension is continuous. -/
theorem continuous_map [LocallyConnectedSpace Y₁] [LocallyConnectedSpace Y₂] (hf : Continuous f)
    (hg : Continuous g) (hcomm : ∀ x, p₂ (g x) = f (p₁ x)) :
    Continuous (map hf hg hcomm) := by
  refine continuous_iff_continuousAt.2 fun e =>
    ((hasBasis_nhds (map hf hg hcomm e)).tendsto_right_iff).2 fun V hV => ?_
  have hV' : IsCNbhd (f e.base) V := hV
  have hW := isCNbhd_connectedComponentIn_preimage hf hV'
  set W := connectedComponentIn (f ⁻¹' V) e.base
  refine mem_of_superset ((isOpen_basicSet hW.1 _).mem_nhds (mem_basicSet_self e hW))
    fun e₁ he₁ => ?_
  have hb₁ : e₁.base ∈ W := base_mem_of_mem_basicSet he₁
  have hW₁ : IsCNbhd e₁.base W := hW.of_mem hb₁
  have he₁W : e₁ W = e W := eq_of_mem_basicSet (e.isCompOf W hW) hW₁ he₁
  have hV₁ : IsCNbhd (f e₁.base) V :=
    hV'.of_mem (connectedComponentIn_subset (f ⁻¹' V) e.base hb₁)
  show map hf hg hcomm e₁ ∈ basicSet p₂ V (map hf hg hcomm e V)
  refine ⟨V, hV₁, subset_rfl, ?_⟩
  obtain ⟨x, hx⟩ := e₁.nonempty hW₁
  have hWV : W ⊆ f ⁻¹' V := connectedComponentIn_subset _ _
  rw [map_apply hf hg hcomm e₁ hV₁ hW₁ hWV hx,
    map_apply hf hg hcomm e hV' hW hWV (he₁W ▸ hx)]

/-- The extension commutes with the projections. -/
theorem base_map [LocallyConnectedSpace Y₁] (hf : Continuous f) (hg : Continuous g)
    (hcomm : ∀ x, p₂ (g x) = f (p₁ x)) (e : SpreadEnd p₁) :
    (map hf hg hcomm e).base = f e.base := rfl

/-- Uniqueness of the extension: a continuous map of the spaces of ends extending `g` is
`map`. -/
theorem eq_map [LocallyConnectedSpace Y₁] [LocallyConnectedSpace Y₂] [T2Space Y₂]
    (hf : Continuous f) (hg : Continuous g) (hcomm : ∀ x, p₂ (g x) = f (p₁ x))
    {G : SpreadEnd p₁ → SpreadEnd p₂} (hG : Continuous G)
    (hGι : ∀ x, G (ofPoint p₁ x) = ofPoint p₂ (g x)) : G = map hf hg hcomm :=
  denseRange_ofPoint.equalizer hG (continuous_map hf hg hcomm)
    (funext fun x => (hGι x).trans (map_ofPoint hf hg hcomm x).symm)

/-- Functoriality: identities. -/
theorem map_id [LocallyConnectedSpace Y₁] [T2Space Y₁] :
    map (p₁ := p₁) (p₂ := p₁) continuous_id continuous_id (fun _ => rfl) = id :=
  (eq_map (p₁ := p₁) (p₂ := p₁) (f := id) (g := id) continuous_id continuous_id (fun _ => rfl)
    continuous_id fun _ => rfl).symm

/-- Functoriality: composition. -/
theorem map_comp {X₃ Y₃ : Type*} [TopologicalSpace X₃] [TopologicalSpace Y₃] {p₃ : X₃ → Y₃}
    [LocallyConnectedSpace Y₁] [LocallyConnectedSpace Y₂] [LocallyConnectedSpace Y₃]
    [T2Space Y₃] {f' : Y₂ → Y₃} {g' : X₂ → X₃} (hf : Continuous f) (hg : Continuous g)
    (hcomm : ∀ x, p₂ (g x) = f (p₁ x)) (hf' : Continuous f') (hg' : Continuous g')
    (hcomm' : ∀ x, p₃ (g' x) = f' (p₂ x)) :
    map (hf'.comp hf) (hg'.comp hg) (fun x => by simp [hcomm, hcomm']) =
      map hf' hg' hcomm' ∘ map hf hg hcomm :=
  (eq_map _ _ _ ((continuous_map hf' hg' hcomm').comp (continuous_map hf hg hcomm))
    fun x => by simp [map_ofPoint]).symm

/-- Faithfulness: the extension determines the morphism (T0 target). -/
theorem map_injective [LocallyConnectedSpace Y₁] [LocallyConnectedSpace Y₂] [T0Space X₂]
    (hp₂ : IsSpread p₂) (hf : Continuous f) {g g' : X₁ → X₂} (hg : Continuous g)
    (hg' : Continuous g') (hcomm : ∀ x, p₂ (g x) = f (p₁ x))
    (hcomm' : ∀ x, p₂ (g' x) = f (p₁ x)) (h : map hf hg hcomm = map hf hg' hcomm') : g = g' :=
  funext fun x => (isEmbedding_ofPoint hp₂).injective (by
    rw [← map_ofPoint hf hg hcomm, ← map_ofPoint hf hg' hcomm', h])

end SpreadEnd

namespace IsFoxCompletion

variable {X₁ Y₁ X₂ Y₂ : Type*} [TopologicalSpace X₁] [TopologicalSpace Y₁] [TopologicalSpace X₂]
  [TopologicalSpace Y₂] {p₁ : X₁ → Y₁} {p₂ : X₂ → Y₂} {f : Y₁ → Y₂} {g : X₁ → X₂}
  {X₁' X₂' : Type*} [TopologicalSpace X₁'] [TopologicalSpace X₂'] {p₁' : X₁' → Y₁}
  {p₂' : X₂' → Y₂} {ι₁ : X₁ → X₁'} {ι₂ : X₂ → X₂'}

/-- **Functoriality on arbitrary completions.** A spread morphism `(f, g)` extends to any two
completions (in Fox's sense, a fortiori in the paper's): the transport of `SpreadEnd.map`
through the comparison homeomorphisms. -/
def extend [T1Space Y₁] [LocallyConnectedSpace Y₁] [T1Space Y₂] [LocallyConnectedSpace Y₂]
    [T0Space X₁'] [T0Space X₂'] (h₁ : IsFoxCompletion p₁ p₁' ι₁) (h₂ : IsFoxCompletion p₂ p₂' ι₂)
    (hf : Continuous f) (hg : Continuous g) (hcomm : ∀ x, p₂ (g x) = f (p₁ x)) : X₁' → X₂' :=
  fun x' => h₂.homeomorph.symm (SpreadEnd.map hf hg hcomm (h₁.homeomorph x'))

theorem continuous_extend [T1Space Y₁] [LocallyConnectedSpace Y₁] [T1Space Y₂]
    [LocallyConnectedSpace Y₂] [T0Space X₁'] [T0Space X₂'] (h₁ : IsFoxCompletion p₁ p₁' ι₁)
    (h₂ : IsFoxCompletion p₂ p₂' ι₂) (hf : Continuous f) (hg : Continuous g)
    (hcomm : ∀ x, p₂ (g x) = f (p₁ x)) : Continuous (h₁.extend h₂ hf hg hcomm) :=
  h₂.homeomorph.symm.continuous.comp
    ((SpreadEnd.continuous_map hf hg hcomm).comp h₁.homeomorph.continuous)

theorem extend_comm [T1Space Y₁] [LocallyConnectedSpace Y₁] [T1Space Y₂]
    [LocallyConnectedSpace Y₂] [T0Space X₁'] [T0Space X₂'] (h₁ : IsFoxCompletion p₁ p₁' ι₁)
    (h₂ : IsFoxCompletion p₂ p₂' ι₂) (hf : Continuous f) (hg : Continuous g)
    (hcomm : ∀ x, p₂ (g x) = f (p₁ x)) (x' : X₁') :
    p₂' (h₁.extend h₂ hf hg hcomm x') = f (p₁' x') := by
  have := congrArg SpreadEnd.base
    (h₂.homeomorph.apply_symm_apply (SpreadEnd.map hf hg hcomm (h₁.homeomorph x')))
  rw [homeomorph_apply, toEnd_base] at this
  exact this

theorem extend_comp [T1Space Y₁] [LocallyConnectedSpace Y₁] [T1Space Y₂]
    [LocallyConnectedSpace Y₂] [T0Space X₁'] [T0Space X₂'] (h₁ : IsFoxCompletion p₁ p₁' ι₁)
    (h₂ : IsFoxCompletion p₂ p₂' ι₂) (hf : Continuous f) (hg : Continuous g)
    (hcomm : ∀ x, p₂ (g x) = f (p₁ x)) (x : X₁) :
    h₁.extend h₂ hf hg hcomm (ι₁ x) = ι₂ (g x) := by
  show h₂.homeomorph.symm (SpreadEnd.map hf hg hcomm (h₁.homeomorph (ι₁ x))) = ι₂ (g x)
  rw [Homeomorph.symm_apply_eq, homeomorph_apply, homeomorph_apply, toEnd_comp, toEnd_comp,
    SpreadEnd.map_ofPoint]

/-- **Functoriality on arbitrary completions, existence and uniqueness.** A spread morphism
`(f, g)` extends uniquely to a continuous `ḡ : X₁' → X₂'` with `p₂' ∘ ḡ = f ∘ p₁'` and
`ḡ ∘ ι₁ = ι₂ ∘ g` (Hausdorff target base for uniqueness). -/
theorem existsUnique_extend [T1Space Y₁] [LocallyConnectedSpace Y₁] [T2Space Y₂]
    [LocallyConnectedSpace Y₂] [T0Space X₁'] [T0Space X₂'] (h₁ : IsFoxCompletion p₁ p₁' ι₁)
    (h₂ : IsFoxCompletion p₂ p₂' ι₂) (hf : Continuous f) (hg : Continuous g)
    (hcomm : ∀ x, p₂ (g x) = f (p₁ x)) :
    ∃! G : X₁' → X₂', Continuous G ∧ (∀ x', p₂' (G x') = f (p₁' x')) ∧
      ∀ x, G (ι₁ x) = ι₂ (g x) := by
  refine ⟨h₁.extend h₂ hf hg hcomm, ⟨h₁.continuous_extend h₂ hf hg hcomm,
    h₁.extend_comm h₂ hf hg hcomm, h₁.extend_comp h₂ hf hg hcomm⟩, ?_⟩
  rintro G ⟨hG, -, hGι⟩
  haveI : T2Space X₂' := h₂.homeomorph.symm.t2Space
  exact DenseRange.equalizer h₁.dense hG (h₁.continuous_extend h₂ hf hg hcomm)
    (funext fun x => (hGι x).trans (h₁.extend_comp h₂ hf hg hcomm x).symm)

end IsFoxCompletion

/-! ### The fibre of a spread as an inverse limit (`prop:spread_fiber`) -/

/-- Subsets of `X` with the discrete topology: the factor `X_U` of the inverse limit. -/
def DiscreteSets (X : Type*) : Type _ := Set X

instance (X : Type*) : TopologicalSpace (DiscreteSets X) := ⊥

instance (X : Type*) : DiscreteTopology (DiscreteSets X) := ⟨rfl⟩

/-- `prop:spread_fiber`. The inverse limit `lim_{U ∈ 𝓤} X_U` of the discrete spaces of components
of the `p ⁻¹' U`, `U ∈ 𝓤`: the compatible families (for `U ⊆ V` the bonding map sends the
component `s U` to the component of `p ⁻¹' V` containing it, i.e. `s U ⊆ s V`). -/
@[ext]
structure FiberThread (p : X → Y) (𝓤 : Set (Set Y)) where
  /-- The family of components. -/
  toFun : 𝓤 → Set X
  isCompOf : ∀ U : 𝓤, IsCompOf p U (toFun U)
  mono : ∀ U V : 𝓤, (U : Set Y) ⊆ V → toFun U ⊆ toFun V

namespace FiberThread

variable {p : X → Y} {𝓤 : Set (Set Y)}

/-- The coordinates of a thread, in the discrete spaces `X_U`. -/
def coords (s : FiberThread p 𝓤) : 𝓤 → DiscreteSets X := s.toFun

/-- The inverse limit topology: induced by the product of the discrete `X_U`. -/
instance : TopologicalSpace (FiberThread p 𝓤) :=
  TopologicalSpace.induced (coords : FiberThread p 𝓤 → 𝓤 → DiscreteSets X) inferInstance

theorem continuous_coord (U : 𝓤) :
    Continuous (fun s : FiberThread p 𝓤 => s.coords U) := by
  have : Continuous (fun c : 𝓤 → DiscreteSets X => c U) := continuous_apply U
  exact this.comp continuous_induced_dom

/-- The cylinder sets `π_U⁻¹ {C}` are open. -/
theorem isOpen_cylinder (U : 𝓤) (C : Set X) :
    IsOpen {s : FiberThread p 𝓤 | s.toFun U = C} :=
  (isOpen_discrete ({C} : Set (DiscreteSets X))).preimage (continuous_coord U)

end FiberThread

variable {p : X → Y} {𝓤 : Set (Set Y)} {b : Y}

/-- `prop:spread_fiber`. The natural map `p⁻¹(b) → lim X_U`, `x ↦ (x_U)_U`. -/
def fiberMap (p : X → Y) (𝓤 : Set (Set Y)) (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U) (x : p ⁻¹' {b}) :
    FiberThread p 𝓤 where
  toFun U := connectedComponentIn (p ⁻¹' U) x
  isCompOf U := isCompOf_connectedComponentIn (by
    rw [show p x = b from x.2]; exact (h𝓤 U U.2).mem)
  mono _ _ h := connectedComponentIn_mono _ (preimage_mono h)

theorem continuous_fiberMap (hp : IsSpread p) (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U) :
    Continuous (fiberMap p 𝓤 h𝓤) := by
  haveI := hp.locallyConnectedSpace
  refine continuous_induced_rng.2 (continuous_pi fun U => continuous_discrete_rng.2 fun C => ?_)
  change IsOpen {x : p ⁻¹' {b} | (connectedComponentIn (p ⁻¹' U) (x : X) : DiscreteSets X) ∈
    ({C} : Set (DiscreteSets X))}
  refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
  have hxU : (x : X) ∈ p ⁻¹' (U : Set Y) := by
    show p x ∈ (U : Set Y); rw [show p x = b from x.2]; exact (h𝓤 U U.2).mem
  refine ⟨(Subtype.val : p ⁻¹' {b} → X) ⁻¹' connectedComponentIn (p ⁻¹' U) x, fun x' hx' => ?_,
    (((h𝓤 U U.2).1.preimage hp.continuous).connectedComponentIn).preimage continuous_subtype_val,
    mem_connectedComponentIn hxU⟩
  have : connectedComponentIn (p ⁻¹' U) (x' : X) = connectedComponentIn (p ⁻¹' U) x :=
    (connectedComponentIn_eq hx').symm
  show (connectedComponentIn (p ⁻¹' U) (x' : X) : DiscreteSets X) ∈ ({C} : Set (DiscreteSets X))
  rw [this]; exact hx

/-- `prop:spread_fiber`. The natural map is inducing ("open onto its image"). -/
theorem isInducing_fiberMap (hp : IsSpread p) (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U)
    (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) : IsInducing (fiberMap p 𝓤 h𝓤) := by
  refine isInducing_iff_nhds.2 fun x =>
    le_antisymm ((continuous_fiberMap hp h𝓤).tendsto x).le_comap ?_
  intro O hO
  obtain ⟨t, htO, ht, hxt⟩ := mem_nhds_iff.1 hO
  obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 ht
  obtain ⟨U', hU', hxU', hcomp⟩ := (isSpread_iff.1 hp).2.2 x O' hO' hxt
  obtain ⟨U, hU, hUU'⟩ := hbasis U' (hU'.mem_nhds (by rw [← show p x = b from x.2]; exact hxU'))
  refine mem_comap.2 ⟨{s | s.toFun ⟨U, hU⟩ = connectedComponentIn (p ⁻¹' U) x},
    (FiberThread.isOpen_cylinder _ _).mem_nhds rfl, fun x' hx' => htO ?_⟩
  have hx'U : (x' : X) ∈ p ⁻¹' U := by
    show p x' ∈ U; rw [show p x' = b from x'.2]; exact (h𝓤 U hU).mem
  have h1 : connectedComponentIn (p ⁻¹' U) (x' : X) = connectedComponentIn (p ⁻¹' U) x := hx'
  have h2 : (x' : X) ∈ connectedComponentIn (p ⁻¹' U) x := h1 ▸ mem_connectedComponentIn hx'U
  exact hcomp (connectedComponentIn_mono _ (preimage_mono hUU') h2)

/-- `prop:spread_fiber`. The natural map is injective (T0 source). -/
theorem injective_fiberMap [T0Space X] (hp : IsSpread p) (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U)
    (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) : Injective (fiberMap p 𝓤 h𝓤) :=
  (isInducing_fiberMap hp h𝓤 hbasis).injective

/-- `prop:spread_fiber`. The natural map is an embedding. -/
theorem isEmbedding_fiberMap [T0Space X] (hp : IsSpread p) (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U)
    (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) : IsEmbedding (fiberMap p 𝓤 h𝓤) :=
  ⟨isInducing_fiberMap hp h𝓤 hbasis, injective_fiberMap hp h𝓤 hbasis⟩

/-- The natural map is an open map iff its image is open (for an embedding). -/
theorem isOpenMap_fiberMap_iff [T0Space X] (hp : IsSpread p) (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U)
    (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) :
    IsOpenMap (fiberMap p 𝓤 h𝓤) ↔ IsOpen (range (fiberMap p 𝓤 h𝓤)) :=
  ⟨fun h => h.isOpen_range, fun h => (IsOpenEmbedding.mk
    (isEmbedding_fiberMap hp h𝓤 hbasis) h).isOpenMap⟩

/-! #### The wider reading of the basis: arbitrary neighbourhoods

`prop:spread_fiber` reads "connected neighbourhood basis" as open connected neighbourhoods
(`IsCNbhd`). The embedding part survives the widest reading: `𝓤` any family of neighbourhoods of
`b` (neither open nor connected) forming a basis of `𝓝 b`. -/

/-- The natural map `p⁻¹(b) → lim X_U` over any family `𝓤` of neighbourhoods of `b`. -/
def fiberMapNhds (p : X → Y) (𝓤 : Set (Set Y)) (h𝓤 : ∀ U ∈ 𝓤, U ∈ 𝓝 b) (x : p ⁻¹' {b}) :
    FiberThread p 𝓤 where
  toFun U := connectedComponentIn (p ⁻¹' U) x
  isCompOf U := isCompOf_connectedComponentIn (by
    rw [show p x = b from x.2]; exact mem_of_mem_nhds (h𝓤 U U.2))
  mono _ _ h := connectedComponentIn_mono _ (preimage_mono h)

/-- Over open connected neighbourhoods, `fiberMapNhds` is `fiberMap`. -/
theorem fiberMap_eq_fiberMapNhds (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U) :
    fiberMap p 𝓤 h𝓤 =
      fiberMapNhds p 𝓤 (fun U hU => (h𝓤 U hU).1.mem_nhds (h𝓤 U hU).mem) := rfl

theorem continuous_fiberMapNhds (hp : IsSpread p) (h𝓤 : ∀ U ∈ 𝓤, U ∈ 𝓝 b) :
    Continuous (fiberMapNhds p 𝓤 h𝓤) := by
  haveI := hp.locallyConnectedSpace
  refine continuous_induced_rng.2 (continuous_pi fun U => continuous_discrete_rng.2 fun C => ?_)
  change IsOpen {x : p ⁻¹' {b} | (connectedComponentIn (p ⁻¹' U) (x : X) : DiscreteSets X) ∈
    ({C} : Set (DiscreteSets X))}
  refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
  have hbV : b ∈ interior (U : Set Y) := mem_interior_iff_mem_nhds.2 (h𝓤 U U.2)
  have hxV : (x : X) ∈ p ⁻¹' interior (U : Set Y) := by
    show p x ∈ interior (U : Set Y); rw [show p x = b from x.2]; exact hbV
  refine ⟨(Subtype.val : p ⁻¹' {b} → X) ⁻¹' connectedComponentIn (p ⁻¹' interior U) x,
    fun x' hx' => ?_,
    ((isOpen_interior.preimage hp.continuous).connectedComponentIn).preimage
      continuous_subtype_val, mem_connectedComponentIn hxV⟩
  have hx'U : (x' : X) ∈ connectedComponentIn (p ⁻¹' U) x :=
    connectedComponentIn_mono _ (preimage_mono interior_subset) hx'
  have : connectedComponentIn (p ⁻¹' U) (x' : X) = connectedComponentIn (p ⁻¹' U) x :=
    (connectedComponentIn_eq hx'U).symm
  show (connectedComponentIn (p ⁻¹' U) (x' : X) : DiscreteSets X) ∈ ({C} : Set (DiscreteSets X))
  rw [this]; exact hx

/-- `prop:spread_fiber`, wider reading: the natural map is inducing for any neighbourhood
basis `𝓤` of `b`. -/
theorem isInducing_fiberMapNhds (hp : IsSpread p) (h𝓤 : ∀ U ∈ 𝓤, U ∈ 𝓝 b)
    (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) : IsInducing (fiberMapNhds p 𝓤 h𝓤) := by
  refine isInducing_iff_nhds.2 fun x =>
    le_antisymm ((continuous_fiberMapNhds hp h𝓤).tendsto x).le_comap ?_
  intro O hO
  obtain ⟨t, htO, ht, hxt⟩ := mem_nhds_iff.1 hO
  obtain ⟨O', hO', rfl⟩ := isOpen_induced_iff.1 ht
  obtain ⟨U', hU', hxU', hcomp⟩ := (isSpread_iff.1 hp).2.2 x O' hO' hxt
  obtain ⟨U, hU, hUU'⟩ := hbasis U' (hU'.mem_nhds (by rw [← show p x = b from x.2]; exact hxU'))
  refine mem_comap.2 ⟨{s | s.toFun ⟨U, hU⟩ = connectedComponentIn (p ⁻¹' U) x},
    (FiberThread.isOpen_cylinder _ _).mem_nhds rfl, fun x' hx' => htO ?_⟩
  have hx'U : (x' : X) ∈ p ⁻¹' U := by
    show p x' ∈ U; rw [show p x' = b from x'.2]; exact mem_of_mem_nhds (h𝓤 U hU)
  have h1 : connectedComponentIn (p ⁻¹' U) (x' : X) = connectedComponentIn (p ⁻¹' U) x := hx'
  have h2 : (x' : X) ∈ connectedComponentIn (p ⁻¹' U) x := h1 ▸ mem_connectedComponentIn hx'U
  exact hcomp (connectedComponentIn_mono _ (preimage_mono hUU') h2)

/-- `prop:spread_fiber`, wider reading: the natural map is an embedding (T0 source) for any
neighbourhood basis `𝓤` of `b`. -/
theorem isEmbedding_fiberMapNhds [T0Space X] (hp : IsSpread p) (h𝓤 : ∀ U ∈ 𝓤, U ∈ 𝓝 b)
    (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) : IsEmbedding (fiberMapNhds p 𝓤 h𝓤) :=
  ⟨isInducing_fiberMapNhds hp h𝓤 hbasis, (isInducing_fiberMapNhds hp h𝓤 hbasis).injective⟩

/-- Wider reading: a thread is in the image iff its components have a common point. -/
theorem mem_range_fiberMapNhds_iff [T1Space Y] (h𝓤 : ∀ U ∈ 𝓤, U ∈ 𝓝 b)
    (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) (s : FiberThread p 𝓤) :
    s ∈ range (fiberMapNhds p 𝓤 h𝓤) ↔ ∃ x : X, ∀ U : 𝓤, x ∈ s.toFun U := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, fun U => mem_connectedComponentIn ?_⟩
    show p x ∈ (U : Set Y); rw [show p x = b from x.2]; exact mem_of_mem_nhds (h𝓤 U U.2)
  · rintro ⟨x, hx⟩
    have hpx : p x = b := by
      by_contra hne
      obtain ⟨U, hU, hUN⟩ := hbasis _ (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
      exact hUN ((s.isCompOf ⟨U, hU⟩).subset (hx ⟨U, hU⟩)) rfl
    exact ⟨⟨x, hpx⟩, FiberThread.ext (funext fun U =>
      ((s.isCompOf U).eq_of_mem (hx U)).symm)⟩

/-- A thread is in the image iff its components have a common point (`∩ x̂_U ≠ ∅`). -/
theorem mem_range_fiberMap_iff [T1Space Y] (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U)
    (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) (s : FiberThread p 𝓤) :
    s ∈ range (fiberMap p 𝓤 h𝓤) ↔ ∃ x : X, ∀ U : 𝓤, x ∈ s.toFun U := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x, fun U => mem_connectedComponentIn ?_⟩
    show p x ∈ (U : Set Y); rw [show p x = b from x.2]; exact (h𝓤 U U.2).mem
  · rintro ⟨x, hx⟩
    have hpx : p x = b := by
      by_contra hne
      obtain ⟨U, hU, hUN⟩ := hbasis _ (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
      exact hUN ((s.isCompOf ⟨U, hU⟩).subset (hx ⟨U, hU⟩)) rfl
    exact ⟨⟨x, hpx⟩, FiberThread.ext (funext fun U =>
      ((s.isCompOf U).eq_of_mem (hx U)).symm)⟩

/-- **`prop:spread_fiber`, the paper's form of surjectivity.** The natural map is onto iff every
thread has a common point. -/
theorem surjective_fiberMap_iff_threads [T1Space Y] (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U)
    (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) :
    Surjective (fiberMap p 𝓤 h𝓤) ↔ ∀ s : FiberThread p 𝓤, ∃ x : X, ∀ U : 𝓤, x ∈ s.toFun U :=
  ⟨fun h s => (mem_range_fiberMap_iff h𝓤 hbasis s).1 (h s),
    fun h s => (mem_range_fiberMap_iff h𝓤 hbasis s).2 (h s)⟩

/-- A member of the basis inside a given connected open neighbourhood. -/
def FiberThread.pick (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) {V : Set Y} (hV : IsCNbhd b V) : 𝓤 :=
  ⟨_, (hbasis V (hV.1.mem_nhds hV.mem)).choose_spec.1⟩

theorem FiberThread.pick_subset (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) {V : Set Y}
    (hV : IsCNbhd b V) : (FiberThread.pick hbasis hV : Set Y) ⊆ V :=
  (hbasis V (hV.1.mem_nhds hV.mem)).choose_spec.2

/-- Points of `s U₁`, `s U₂` with `U₁, U₂ ⊆ V` lie in the same component of `p ⁻¹' V`. -/
theorem FiberThread.comp_eq (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U) (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N)
    (s : FiberThread p 𝓤) {V : Set Y} {U₁ U₂ : 𝓤} (h₁ : (U₁ : Set Y) ⊆ V)
    (h₂ : (U₂ : Set Y) ⊆ V) {z₁ z₂ : X} (hz₁ : z₁ ∈ s.toFun U₁) (hz₂ : z₂ ∈ s.toFun U₂) :
    connectedComponentIn (p ⁻¹' V) z₁ = connectedComponentIn (p ⁻¹' V) z₂ := by
  obtain ⟨U₃, hU₃, hU₃s⟩ := hbasis ((U₁ : Set Y) ∩ U₂) (inter_mem
    ((h𝓤 _ U₁.2).1.mem_nhds (h𝓤 _ U₁.2).mem) ((h𝓤 _ U₂.2).1.mem_nhds (h𝓤 _ U₂.2).mem))
  obtain ⟨w, hw⟩ := (s.isCompOf ⟨U₃, hU₃⟩).nonempty
  have hw₁ := s.mono ⟨U₃, hU₃⟩ U₁ (hU₃s.trans inter_subset_left) hw
  have hw₂ := s.mono ⟨U₃, hU₃⟩ U₂ (hU₃s.trans inter_subset_right) hw
  have e₁ := connectedComponentIn_eq ((s.isCompOf U₁).isPreconnected.subset_connectedComponentIn
    hz₁ ((s.isCompOf U₁).subset.trans (preimage_mono h₁)) hw₁)
  have e₂ := connectedComponentIn_eq ((s.isCompOf U₂).isPreconnected.subset_connectedComponentIn
    hz₂ ((s.isCompOf U₂).subset.trans (preimage_mono h₂)) hw₂)
  rw [e₁, e₂]

/-- The end of `p` at `b` extending a thread over a basis. -/
def FiberThread.toEnd (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U) (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N)
    (s : FiberThread p 𝓤) : SpreadEnd p where
  base := b
  toFun V := if hV : IsCNbhd b V then connectedComponentIn (p ⁻¹' V)
    (s.isCompOf (FiberThread.pick hbasis hV)).nonempty.some else ∅
  isCompOf V hV := by
    show IsCompOf p V (if hV : IsCNbhd b V then _ else _)
    rw [dif_pos hV]
    exact isCompOf_connectedComponentIn (FiberThread.pick_subset hbasis hV
      ((s.isCompOf (FiberThread.pick hbasis hV)).subset
        (s.isCompOf (FiberThread.pick hbasis hV)).nonempty.some_mem))
  mono V V' hV hV' hVV' := by
    show (if hV : IsCNbhd b V then connectedComponentIn (p ⁻¹' V)
      (s.isCompOf (FiberThread.pick hbasis hV)).nonempty.some else (∅ : Set X)) ⊆
      (if hV : IsCNbhd b V' then connectedComponentIn (p ⁻¹' V')
      (s.isCompOf (FiberThread.pick hbasis hV)).nonempty.some else ∅)
    rw [dif_pos hV, dif_pos hV', ← FiberThread.comp_eq h𝓤 hbasis s
      (V := V') ((FiberThread.pick_subset hbasis hV).trans hVV')
      (FiberThread.pick_subset hbasis hV')
      (s.isCompOf _).nonempty.some_mem (s.isCompOf _).nonempty.some_mem]
    exact connectedComponentIn_mono _ (preimage_mono hVV')
  eq_empty V hV := by
    show (if hV : IsCNbhd b V then _ else _) = _
    rw [dif_neg hV]

theorem FiberThread.toEnd_apply (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U)
    (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) (s : FiberThread p 𝓤) (U : 𝓤) :
    s.toEnd h𝓤 hbasis U = s.toFun U := by
  have hV := h𝓤 U U.2
  show (if hV : IsCNbhd b U then _ else _) = _
  rw [dif_pos hV]
  obtain ⟨z, hz⟩ := (s.isCompOf U).nonempty
  rw [FiberThread.comp_eq h𝓤 hbasis s (FiberThread.pick_subset hbasis hV) subset_rfl
    (s.isCompOf _).nonempty.some_mem hz]
  exact ((s.isCompOf U).eq_of_mem hz).symm

/-- **`prop:spread_fiber`, surjectivity in terms of ends.** For a fixed `b`, the natural map is
onto iff every end of `p` at `b` is realised by a point. -/
theorem surjective_fiberMap_iff_ends [T1Space Y] (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U)
    (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) :
    Surjective (fiberMap p 𝓤 h𝓤) ↔
      ∀ e : SpreadEnd p, e.base = b → ∃ x, ∀ U, IsCNbhd e.base U → x ∈ e U := by
  rw [surjective_fiberMap_iff_threads h𝓤 hbasis]
  constructor
  · intro h e he
    subst he
    let s : FiberThread p 𝓤 :=
      { toFun := fun U => e U
        isCompOf := fun U => e.isCompOf U (h𝓤 U U.2)
        mono := fun U V hUV => e.mono U V (h𝓤 U U.2) (h𝓤 V V.2) hUV }
    obtain ⟨x, hx⟩ := h s
    refine ⟨x, fun V hV => ?_⟩
    obtain ⟨U, hU, hUV⟩ := hbasis V (hV.1.mem_nhds hV.mem)
    exact e.mono U V (h𝓤 U hU) hV hUV (hx ⟨U, hU⟩)
  · intro h s
    obtain ⟨x, hx⟩ := h (s.toEnd h𝓤 hbasis) rfl
    exact ⟨x, fun U => (FiberThread.toEnd_apply h𝓤 hbasis s U) ▸ hx U (h𝓤 U U.2)⟩

/-- **`prop:spread_fiber`, homeomorphism iff complete (corrected).** A spread is complete iff
for every `b` and every basis `𝓤` of open connected neighbourhoods of `b`, the natural map
`p⁻¹(b) → lim X_U` is onto (it is then a homeomorphism, `isEmbedding_fiberMap`). -/
theorem isCompleteSpread_iff_forall_surjective_fiberMap [T1Space Y] [LocallyConnectedSpace Y] :
    IsCompleteSpread p ↔ ∀ (b : Y) (𝓤 : Set (Set Y)) (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U)
      (_ : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N), Surjective (fiberMap p 𝓤 h𝓤) := by
  rw [isCompleteSpread_iff]
  constructor
  · intro h b 𝓤 h𝓤 hbasis
    exact (surjective_fiberMap_iff_ends h𝓤 hbasis).2 fun e _ => h e
  · intro h e
    have h𝓤 : ∀ U ∈ {U | IsCNbhd e.base U}, IsCNbhd e.base U := fun _ h => h
    have hbasis : ∀ N ∈ 𝓝 e.base, ∃ U ∈ {U | IsCNbhd e.base U}, U ⊆ N := fun N hN =>
      (hasBasis_nhds_isCNbhd e.base).mem_iff.1 hN
    exact (surjective_fiberMap_iff_ends h𝓤 hbasis).1 (h _ _ h𝓤 hbasis) e rfl

/-- **`prop:spread_fiber`, complete iff onto for SOME basis at each point.** Surjectivity does
not depend on the basis (`surjective_fiberMap_iff_ends`), so one basis per point suffices. -/
theorem isCompleteSpread_iff_forall_exists_surjective_fiberMap [T1Space Y]
    [LocallyConnectedSpace Y] :
    IsCompleteSpread p ↔ ∀ b : Y, ∃ (𝓤 : Set (Set Y)) (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U)
      (_ : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N), Surjective (fiberMap p 𝓤 h𝓤) := by
  constructor
  · intro h b
    have hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ {U | IsCNbhd b U}, U ⊆ N := fun N hN =>
      (hasBasis_nhds_isCNbhd b).mem_iff.1 hN
    exact ⟨{U | IsCNbhd b U}, fun _ h => h, hbasis,
      isCompleteSpread_iff_forall_surjective_fiberMap.1 h b _ _ hbasis⟩
  · intro h
    rw [isCompleteSpread_iff]
    intro e
    obtain ⟨𝓤, h𝓤, hbasis, hs⟩ := h e.base
    exact (surjective_fiberMap_iff_ends h𝓤 hbasis).1 hs e rfl

/-- `prop:spread_fiber`, the homeomorphism of a complete spread. -/
def fiberHomeomorph [T0Space X] [T1Space Y] [LocallyConnectedSpace Y] (hp : IsSpread p)
    (hc : IsCompleteSpread p) (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd b U)
    (hbasis : ∀ N ∈ 𝓝 b, ∃ U ∈ 𝓤, U ⊆ N) : p ⁻¹' {b} ≃ₜ FiberThread p 𝓤 :=
  (Equiv.ofBijective _ ⟨injective_fiberMap hp h𝓤 hbasis,
    isCompleteSpread_iff_forall_surjective_fiberMap.1 hc b 𝓤 h𝓤 hbasis⟩).toHomeomorphOfIsInducing
    (isInducing_fiberMap hp h𝓤 hbasis)

/-! ### `cor:totdiscont` -/

/-- **`cor:totdiscont`.** The fibres of a spread (with a T0 source) are totally disconnected. -/
theorem isTotallyDisconnected_fiber [T0Space X] (hp : IsSpread p) (b : Y) :
    IsTotallyDisconnected (p ⁻¹' {b}) := by
  intro t hts ht x hx x' hx'
  refine Inseparable.eq (inseparable_iff_forall_isOpen.2 fun O hO => ?_)
  have key : ∀ z ∈ t, ∀ z' ∈ t, z ∈ O → z' ∈ O := by
    intro z hz z' hz' hzO
    obtain ⟨U, hU, hzU, hcomp⟩ := (isSpread_iff.1 hp).2.2 z O hO hzO
    have htU : t ⊆ p ⁻¹' U := fun w hw => by
      show p w ∈ U
      rw [show p w = b from hts hw, ← show p z = b from hts hz]; exact hzU
    exact hcomp (ht.subset_connectedComponentIn hz htU hz')
  exact ⟨key x hx x' hx', key x' hx' x hx⟩

/-! ### The identity is a complete spread -/

/-- The identity of a locally connected space is a complete spread. -/
theorem isCompleteSpread_id [LocallyConnectedSpace Y] : IsCompleteSpread (id : Y → Y) := by
  intro e _
  refine ⟨e.base, fun U hU => ?_⟩
  obtain ⟨x, hx, hxe⟩ := e.isCompOf U hU
  rw [hxe, preimage_id_eq, id, hU.isPreconnected.connectedComponentIn (show x ∈ U from hx)]
  exact hU.mem

theorem isSpread_id [LocallyConnectedSpace Y] : IsSpread (id : Y → Y) :=
  IsSpread.of_isInducing IsInducing.id

/-! ### Counterexamples in the plane -/

section Plane

open Metric

/-- A ball of `ℂ` minus a countable set is connected. -/
theorem isPreconnected_ball_diff_countable_complex {S : Set ℂ} (hS : S.Countable) (c : ℂ) (r : ℝ) :
    IsPreconnected (ball c r \ S) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr, empty_sdiff]; exact isPreconnected_empty
  set φ := OpenPartialHomeomorph.univBall c r
  have hsrc : φ.source = univ := OpenPartialHomeomorph.univBall_source c r
  have hφc : Continuous φ := continuousOn_univ.1 (hsrc ▸ φ.continuousOn)
  have hcount : (φ ⁻¹' S).Countable :=
    hS.preimage_of_injOn (φ.injOn.mono (by rw [hsrc]; exact subset_univ _))
  have hconn : IsConnected (φ ⁻¹' S)ᶜ :=
    hcount.isConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
  have : ball c r \ S = φ '' (φ ⁻¹' S)ᶜ := by
    rw [image_compl_preimage, ← image_univ, ← hsrc, φ.image_source_eq_target,
      OpenPartialHomeomorph.univBall_target c hr]
  rw [this]
  exact hconn.isPreconnected.image _ hφc.continuousOn

/-- An open connected subset of `ℂ` minus a countable set is connected. -/
theorem isPreconnected_diff_countable {S : Set ℂ} (hS : S.Countable) {W : Set ℂ} (hW : IsOpen W)
    (hWc : IsPreconnected W) : IsPreconnected (W \ S) := by
  refine isPreconnected_of_local hWc sdiff_subset ?_ fun x hx => ?_
  · rw [sdiff_eq]
    exact (hS.dense_compl ℂ).open_subset_closure_inter hW
  · obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW x hx
    refine ⟨ball x ε, isOpen_ball, mem_ball_self hε, ?_⟩
    rw [show ball x ε ∩ (W \ S) = ball x ε \ S by
      rw [← inter_sdiff_assoc, inter_eq_left.2 hεW]]
    exact isPreconnected_ball_diff_countable_complex hS x ε

/-- A subspace of `ℂ` with countable complement is locally connected. -/
theorem locallyConnectedSpace_compl_countable {S : Set ℂ} (hS : S.Countable) :
    LocallyConnectedSpace (Sᶜ : Set ℂ) := by
  refine locallyConnectedSpace_of_connected_bases (fun x (r : ℝ) =>
      (Subtype.val : (Sᶜ : Set ℂ) → ℂ) ⁻¹' ball (x : ℂ) r) (fun _ r => 0 < r)
    (fun x => ?_) fun x r _ => ?_
  · rw [nhds_induced]
    exact Metric.nhds_basis_ball.comap _
  · rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe, inter_comm,
      ← sdiff_eq]
    exact isPreconnected_ball_diff_countable_complex hS _ _

/-- A ball of `ℂ` minus a countable set is path-connected. -/
theorem isPathConnected_ball_diff_countable {S : Set ℂ} (hS : S.Countable) (c : ℂ) {r : ℝ}
    (hr : 0 < r) : IsPathConnected (ball c r \ S) := by
  set φ := OpenPartialHomeomorph.univBall c r
  have hsrc : φ.source = univ := OpenPartialHomeomorph.univBall_source c r
  have hφc : Continuous φ := continuousOn_univ.1 (hsrc ▸ φ.continuousOn)
  have hcount : (φ ⁻¹' S).Countable :=
    hS.preimage_of_injOn (φ.injOn.mono (by rw [hsrc]; exact subset_univ _))
  have hconn : IsPathConnected (φ ⁻¹' S)ᶜ :=
    hcount.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
  have : ball c r \ S = φ '' (φ ⁻¹' S)ᶜ := by
    rw [image_compl_preimage, ← image_univ, ← hsrc, φ.image_source_eq_target,
      OpenPartialHomeomorph.univBall_target c hr]
  rw [this]
  exact hconn.image hφc

/-- A subspace of `ℂ` with countable complement is locally path-connected. -/
theorem locPathConnectedSpace_compl_countable {S : Set ℂ} (hS : S.Countable) :
    LocPathConnectedSpace (Sᶜ : Set ℂ) := by
  refine LocPathConnectedSpace.of_bases (p := fun _ (r : ℝ) => 0 < r)
    (s := fun x (r : ℝ) => (Subtype.val : (Sᶜ : Set ℂ) → ℂ) ⁻¹' ball (x : ℂ) r)
    (fun x => ?_) fun x r hr => ?_
  · rw [nhds_induced]
    exact Metric.nhds_basis_ball.comap _
  · rw [IsInducing.subtypeVal.isPathConnected_iff, Subtype.image_preimage_coe, inter_comm,
      ← sdiff_eq]
    exact isPathConnected_ball_diff_countable hS _ hr

/-- `Sᶜ` for a countable `S ⊆ ℂ` is portly in `ℂ`; its inclusion is completed by `id_ℂ`. -/
theorem isFoxCompletion_compl_countable {S : Set ℂ} (hS : S.Countable) :
    IsFoxCompletion (Subtype.val : (Sᶜ : Set ℂ) → ℂ) id Subtype.val := by
  refine ⟨isSpread_id, fun _ => rfl, IsEmbedding.subtypeVal, isCompleteSpread_id, ?_, ?_⟩
  · rw [Subtype.range_coe]; exact hS.dense_compl ℂ
  · intro W hW hWc
    rw [Subtype.range_coe, ← sdiff_eq]
    exact isPreconnected_diff_countable hS hW hWc

theorem isSpread_val_compl_countable {S : Set ℂ} (hS : S.Countable) :
    IsSpread (Subtype.val : (Sᶜ : Set ℂ) → ℂ) := by
  haveI := locallyConnectedSpace_compl_countable hS
  exact IsSpread.of_isInducing IsInducing.subtypeVal

/-- The sequence `1/(n+1)` in `ℂ`. -/
def foxSeq : Set ℂ := range fun n : ℕ => 1 / ((n : ℂ) + 1)

theorem zero_notMem_foxSeq : (0 : ℂ) ∉ foxSeq := by
  rintro ⟨n, hn⟩
  exact one_div_ne_zero (Nat.cast_add_one_ne_zero n) hn

theorem not_isOpen_compl_foxSeq : ¬ IsOpen (foxSeqᶜ) := by
  intro h
  exact zero_notMem_foxSeq (isOpen_compl_iff.1 h |>.mem_of_tendsto
    tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall fun n => mem_range_self n))

/-- **Counterexample to the existence part of `theo:Fox_completion_functor`.** The inclusion of
`ℂ ∖ {1/(n+1) : n ∈ ℕ}` into `ℂ` is a spread (its source is locally connected, a ball minus a
countable set being connected) with a Hausdorff source over a Hausdorff locally connected base,
and it has **no completion** in the paper's sense: by uniqueness every completion is `id_ℂ`, in
which the image of `X` is not open (`0 ∈ X` is a limit of the removed points). -/
theorem not_exists_isSpreadCompletion_foxSeq :
    IsSpread (Subtype.val : (foxSeqᶜ : Set ℂ) → ℂ) ∧
      ¬ ∃ (X' : Type) (_ : TopologicalSpace X') (_ : T0Space X') (p' : X' → ℂ)
        (ι : (foxSeqᶜ : Set ℂ) → X'), IsSpreadCompletion Subtype.val p' ι := by
  have hS : foxSeq.Countable := countable_range _
  have hp := isSpread_val_compl_countable hS
  refine ⟨hp, fun hex => ?_⟩
  have ho := (exists_isSpreadCompletion_iff hp).1 hex
  have hF := isFoxCompletion_compl_countable hS
  have : (foxSeqᶜ : Set ℂ) = hF.homeomorph ⁻¹' range (SpreadEnd.ofPoint Subtype.val) := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨z, hz⟩, (hF.toEnd_comp ⟨z, hz⟩).symm⟩
    · rintro ⟨x, hx⟩
      have h1 : hF.homeomorph (x : ℂ) = hF.homeomorph z := by
        rw [IsFoxCompletion.homeomorph_apply, IsFoxCompletion.homeomorph_apply]
        exact (hF.toEnd_comp x).trans hx
      rw [← hF.homeomorph.injective h1]; exact x.2
  exact not_isOpen_compl_foxSeq (this ▸ ho.preimage hF.homeomorph.continuous)

/-- **Counterexample to the existence part, in every universe.** No space `X'` of any universe
carries a completion of `ℂ ∖ {1/(n+1)} → ℂ`. -/
theorem not_isSpreadCompletion_foxSeq {X' : Type*} [TopologicalSpace X'] [T0Space X']
    (p' : X' → ℂ) (ι : (foxSeqᶜ : Set ℂ) → X') : ¬ IsSpreadCompletion Subtype.val p' ι := by
  have hS : foxSeq.Countable := countable_range _
  have hp := isSpread_val_compl_countable hS
  refine not_isSpreadCompletion_of_not_isOpen (fun ho => ?_) p' ι
  exact not_exists_isSpreadCompletion_foxSeq.2
    ((exists_isSpreadCompletion_iff hp).2 ho)

/-- The inclusion of `ℂ ∖ {a}` is completed by `id_ℂ` (paper's sense). -/
theorem isSpreadCompletion_compl_singleton (a : ℂ) :
    IsSpreadCompletion (Subtype.val : ({a}ᶜ : Set ℂ) → ℂ) id Subtype.val := by
  refine isSpreadCompletion_iff.2 ⟨isFoxCompletion_compl_countable (countable_singleton a), ?_⟩
  rw [Subtype.range_coe]; exact isOpen_compl_singleton

/-- **Counterexample to "fully faithful" in `theo:Fox_completion_functor`.** The inclusions of
`ℂ ∖ {0}` and `ℂ ∖ {1}` both have completion `id_ℂ`, and the identity morphism `(id, id)` between
the completions is not the extension of any morphism of the spreads: no map
`g : ℂ ∖ {0} → ℂ ∖ {1}` satisfies `ι₂ ∘ g = id ∘ ι₁`. The completion is not full. -/
theorem completion_not_full :
    IsSpreadCompletion (Subtype.val : ({0}ᶜ : Set ℂ) → ℂ) id Subtype.val ∧
      IsSpreadCompletion (Subtype.val : ({1}ᶜ : Set ℂ) → ℂ) id Subtype.val ∧
      ¬ ∃ g : ({0}ᶜ : Set ℂ) → ({1}ᶜ : Set ℂ), ∀ x, (g x : ℂ) = id (x : ℂ) := by
  refine ⟨isSpreadCompletion_compl_singleton 0, isSpreadCompletion_compl_singleton 1, ?_⟩
  rintro ⟨g, hg⟩
  have h1 : (1 : ℂ) ∈ ({0}ᶜ : Set ℂ) := by simp
  exact (g ⟨1, h1⟩).2 (by rw [hg]; rfl)

end Plane

/-! ### `prop:spread_fiber` for a fixed `b`: the exponential -/

section Exp

theorem isSpread_exp : IsSpread Real.exp :=
  IsSpread.of_isInducing Real.isOpenEmbedding_exp.isInducing

theorem isPreconnected_preimage_exp {U : Set ℝ} (hU : IsPreconnected U) :
    IsPreconnected (Real.exp ⁻¹' U) :=
  isPreconnected_iff_ordConnected.2
    ((isPreconnected_iff_ordConnected.1 hU).preimage_mono Real.exp_monotone)

/-- The exponential is not a complete spread: the end at `0` (`U ↦ exp⁻¹ U`) is not realised. -/
theorem not_isCompleteSpread_exp : ¬ IsCompleteSpread Real.exp := by
  intro h
  let e : SpreadEnd Real.exp :=
    { base := 0
      toFun := fun U => if IsCNbhd (0 : ℝ) U then Real.exp ⁻¹' U else ∅
      isCompOf := fun U hU => by
        show IsCompOf _ U (if IsCNbhd (0 : ℝ) U then _ else _)
        rw [if_pos hU]
        obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU.1 0 hU.mem
        have hx : Real.exp (Real.log (ε / 2)) ∈ U := by
          rw [Real.exp_log (half_pos hε)]
          exact hεU (by rw [Metric.mem_ball, Real.dist_eq, sub_zero,
            abs_of_pos (half_pos hε)]; linarith)
        exact ⟨_, hx, ((isPreconnected_preimage_exp hU.isPreconnected).connectedComponentIn
          hx).symm⟩
      mono := fun U V hU hV hUV => by
        show (if IsCNbhd (0 : ℝ) U then Real.exp ⁻¹' U else (∅ : Set ℝ)) ⊆
          (if IsCNbhd (0 : ℝ) V then Real.exp ⁻¹' V else ∅)
        rw [if_pos hU, if_pos hV]; exact preimage_mono hUV
      eq_empty := fun U hU => by
        show (if IsCNbhd (0 : ℝ) U then _ else _) = _
        rw [if_neg hU] }
  obtain ⟨x, hx⟩ := h e e.base_mem_closure
  have hU : IsCNbhd (0 : ℝ) (Metric.ball 0 (Real.exp x)) :=
    ⟨Metric.isOpen_ball, (convex_ball _ _).isPreconnected, Metric.mem_ball_self (Real.exp_pos x)⟩
  have := hx _ hU
  change x ∈ (if IsCNbhd (0 : ℝ) (Metric.ball 0 (Real.exp x)) then _ else _) at this
  rw [if_pos hU] at this
  have h' : Real.exp x ∈ Metric.ball (0 : ℝ) (Real.exp x) := this
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (Real.exp_pos x)] at h'
  exact lt_irrefl _ h'

/-- Every end of the exponential at `1` is realised (by `0`). -/
theorem exp_ends_at_one (e : SpreadEnd Real.exp) (he : e.base = 1) :
    ∃ x, ∀ U, IsCNbhd e.base U → x ∈ e U := by
  refine ⟨0, fun U hU => ?_⟩
  obtain ⟨z, hz, hze⟩ := e.isCompOf U hU
  have h0 : Real.exp 0 ∈ U := by rw [Real.exp_zero, ← he]; exact hU.mem
  rw [hze, (isPreconnected_preimage_exp hU.isPreconnected).connectedComponentIn hz]
  exact h0

/-- **Counterexample to the fixed-`b` reading of `prop:spread_fiber`.** For `p = exp` and
`b = 1`, the natural map `p⁻¹(b) → lim X_U` is a homeomorphism for every basis `𝓤` of open
connected neighbourhoods of `1`, yet `exp` is not a complete spread. -/
theorem fiberMap_exp_bijective_not_complete :
    IsSpread Real.exp ∧ ¬ IsCompleteSpread Real.exp ∧
      ∀ (𝓤 : Set (Set ℝ)) (h𝓤 : ∀ U ∈ 𝓤, IsCNbhd (1 : ℝ) U)
        (_ : ∀ N ∈ 𝓝 (1 : ℝ), ∃ U ∈ 𝓤, U ⊆ N),
        Bijective (fiberMap Real.exp 𝓤 h𝓤) := by
  refine ⟨isSpread_exp, not_isCompleteSpread_exp, fun 𝓤 h𝓤 hbasis =>
    ⟨injective_fiberMap isSpread_exp h𝓤 hbasis, ?_⟩⟩
  exact (surjective_fiberMap_iff_ends h𝓤 hbasis).2 exp_ends_at_one

end Exp

section Comb

open Metric

/-! ### The comb: a counterexample to the "open" of `prop:spread_fiber` -/

/-- The heights `r n = 2⁻ⁿ` of the arms of the comb. -/
def combR (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

theorem combR_pos (n : ℕ) : 0 < combR n := pow_pos (by norm_num) n

theorem combR_succ (n : ℕ) : combR (n + 1) = combR n / 2 := by
  simp only [combR, pow_succ]; ring

theorem combR_anti {m n : ℕ} (h : m ≤ n) : combR n ≤ combR m :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- `r n` is the only `r m` in `(r n / 2, 2 r n)`. -/
theorem combR_eq_of_mem {m n : ℕ} (h : combR m ∈ Ioo (combR n / 2) (2 * combR n)) : m = n := by
  rcases lt_trichotomy m n with hmn | hmn | hmn
  · have : combR n ≤ combR (m + 1) := combR_anti hmn
    rw [combR_succ] at this
    linarith [h.2]
  · exact hmn
  · have : combR m ≤ combR (n + 1) := combR_anti hmn
    rw [combR_succ] at this
    linarith [h.1]

/-- The comb: the `x`-axis together with the arms `{(t, r n - t) : 0 < t ≤ r n}` (each arm
accumulating on the axis at `(r n, 0)`, and open at its upper end `(0, r n)`). -/
def combSet : Set (ℝ × ℝ) :=
  {q | q.2 = 0} ∪ {q | ∃ n, 0 < q.1 ∧ q.1 ≤ combR n ∧ q.2 = combR n - q.1}

/-- The first projection of the comb to `ℝ`. -/
def combProj (q : combSet) : ℝ := (q : ℝ × ℝ).1

theorem continuous_combProj : Continuous combProj :=
  continuous_fst.comp continuous_subtype_val

theorem combSet_snd_nonneg (q : combSet) : 0 ≤ (q : ℝ × ℝ).2 := by
  rcases q.2 with h | ⟨n, -, h1, h2⟩
  · rw [show (q : ℝ × ℝ).2 = 0 from h]
  · rw [h2]; linarith

theorem combSet_arm_of_pos (q : combSet) (h : 0 < (q : ℝ × ℝ).2) :
    ∃ n, 0 < (q : ℝ × ℝ).1 ∧ (q : ℝ × ℝ).1 < combR n ∧
      (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 = combR n := by
  rcases q.2 with h0 | ⟨n, h0, -, h2⟩
  · exact absurd (show (q : ℝ × ℝ).2 = 0 from h0) h.ne'
  · exact ⟨n, h0, by linarith, by linarith⟩

/-- The (open) arm `n`. -/
def combArm (n : ℕ) : Set combSet :=
  {q | 0 < (q : ℝ × ℝ).2 ∧ (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 = combR n}

theorem isOpen_combArm (n : ℕ) : IsOpen (combArm n) := by
  have : combArm n = {q : combSet | 0 < (q : ℝ × ℝ).2 ∧
      (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 ∈ Ioo (combR n / 2) (2 * combR n)} := by
    ext q
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_, ?_⟩ <;> rw [h2] <;> linarith [combR_pos n]
    · rintro ⟨h1, h2⟩
      obtain ⟨m, -, -, hm⟩ := combSet_arm_of_pos q h1
      rw [hm] at h2
      rw [combR_eq_of_mem h2] at hm
      exact ⟨h1, hm⟩
  rw [this]
  have hc1 : Continuous fun q : combSet => (q : ℝ × ℝ).2 :=
    continuous_snd.comp continuous_subtype_val
  have hc2 : Continuous fun q : combSet => (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 :=
    (continuous_fst.comp continuous_subtype_val).add hc1
  exact (isOpen_lt continuous_const hc1).inter (isOpen_Ioo.preimage hc2)

/-- Over a set `V` not containing `r n`, a component of `p⁻¹ V` meeting the arm `n` lies in it. -/
theorem connectedComponentIn_subset_combArm {V : Set ℝ} {n : ℕ} (hn : combR n ∉ V)
    {x : combSet} (hxV : x ∈ combProj ⁻¹' V) (hx : x ∈ combArm n) :
    connectedComponentIn (combProj ⁻¹' V) x ⊆ combArm n := by
  have hv : IsOpen {q : combSet | (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 ≠ combR n} :=
    isOpen_ne_fun ((continuous_fst.comp continuous_subtype_val).add
      (continuous_snd.comp continuous_subtype_val)) continuous_const
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union (isOpen_combArm n) hv
    ?_ ?_ ⟨x, mem_connectedComponentIn hxV, hx⟩
  · rw [Set.disjoint_left]
    exact fun q hq hq' => hq' hq.2
  · intro q hq
    have hqV : combProj q ∈ V := connectedComponentIn_subset (combProj ⁻¹' V) x hq
    by_cases hF : (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 = combR n
    · refine Or.inl ⟨?_, hF⟩
      rcases (combSet_snd_nonneg q).lt_or_eq with h | h
      · exact h
      · exfalso; apply hn
        have : (q : ℝ × ℝ).1 = combR n := by rw [← h] at hF; linarith
        rw [← this]; exact hqV
    · exact Or.inr hF

/-- Over an open `V`, the component of `p⁻¹ V` through a point of the axis lies in
`{q₁ + q₂ ∈ V}`. -/
theorem connectedComponentIn_subset_combAxis {V : Set ℝ} (hV : IsOpen V) {x : combSet}
    (hxV : x ∈ combProj ⁻¹' V) (hx : (x : ℝ × ℝ).2 = 0) :
    connectedComponentIn (combProj ⁻¹' V) x ⊆
      {q | (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 ∈ V} := by
  have hF : Continuous fun q : combSet => (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 :=
    (continuous_fst.comp continuous_subtype_val).add (continuous_snd.comp continuous_subtype_val)
  have hv : IsOpen {q : combSet | 0 < (q : ℝ × ℝ).2 ∧ (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 ∉ V} := by
    refine isOpen_iff_forall_mem_open.2 fun q hq => ?_
    obtain ⟨n, -, -, hn⟩ := combSet_arm_of_pos q hq.1
    refine ⟨combArm n, fun q' hq' => ⟨hq'.1, ?_⟩, isOpen_combArm n, ⟨hq.1, hn⟩⟩
    rw [hq'.2, ← hn]; exact hq.2
  refine isPreconnected_connectedComponentIn.subset_left_of_subset_union (hV.preimage hF) hv
    ?_ ?_ ⟨x, mem_connectedComponentIn hxV, ?_⟩
  · rw [Set.disjoint_left]
    exact fun q hq hq' => hq'.2 hq
  · intro q hq
    have hqV : combProj q ∈ V := connectedComponentIn_subset (combProj ⁻¹' V) x hq
    by_cases hF : (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 ∈ V
    · exact Or.inl hF
    · refine Or.inr ⟨?_, hF⟩
      rcases (combSet_snd_nonneg q).lt_or_eq with h | h
      · exact h
      · exfalso; apply hF
        rw [← h, add_zero]; exact hqV
  · show (x : ℝ × ℝ).1 + (x : ℝ × ℝ).2 ∈ V
    rw [hx, add_zero]; exact hxV

/-- Path-connected subsets of the plane inside the comb are path-connected in the comb. -/
theorem isPathConnected_preimage_combSet {S : Set (ℝ × ℝ)} (hS : S ⊆ combSet)
    (h : IsPathConnected S) : IsPathConnected ((↑) ⁻¹' S : Set combSet) := by
  rw [IsInducing.subtypeVal.isPathConnected_iff, Subtype.image_preimage_coe,
    inter_eq_right.2 hS]
  exact h

theorem combAxisSeg_subset (J : Set ℝ) : (fun t : ℝ => (t, (0 : ℝ))) '' J ⊆ combSet := by
  rintro _ ⟨t, -, rfl⟩; exact Or.inl rfl

theorem combArmSeg_subset (n : ℕ) {J : Set ℝ} (hJ : J ⊆ Ioc 0 (combR n)) :
    (fun t : ℝ => (t, combR n - t)) '' J ⊆ combSet := by
  rintro _ ⟨t, ht, rfl⟩; exact Or.inr ⟨n, (hJ ht).1, (hJ ht).2, rfl⟩

theorem isPathConnected_combAxisSeg {J : Set ℝ} (hJ : Convex ℝ J) (hne : J.Nonempty) :
    IsPathConnected (((↑) : combSet → ℝ × ℝ) ⁻¹' ((fun t : ℝ => (t, (0 : ℝ))) '' J)) :=
  isPathConnected_preimage_combSet (combAxisSeg_subset J)
    ((hJ.isPathConnected hne).image (by fun_prop))

theorem isPathConnected_combArmSeg (n : ℕ) {J : Set ℝ} (hJ : Convex ℝ J) (hne : J.Nonempty)
    (hJn : J ⊆ Ioc 0 (combR n)) :
    IsPathConnected (((↑) : combSet → ℝ × ℝ) ⁻¹' ((fun t : ℝ => (t, combR n - t)) '' J)) :=
  isPathConnected_preimage_combSet (combArmSeg_subset n hJn)
    ((hJ.isPathConnected hne).image (by fun_prop))

/-- An arm segment closed at the axis together with an axis segment through its foot. -/
theorem isPathConnected_combAxisArm (n : ℕ) {J K : Set ℝ} (hJ : Convex ℝ J) (hK : Convex ℝ K)
    (hKn : K ⊆ Ioc 0 (combR n)) (hJr : combR n ∈ J) (hKr : combR n ∈ K) :
    IsPathConnected (((↑) : combSet → ℝ × ℝ) ⁻¹' ((fun t : ℝ => (t, (0 : ℝ))) '' J ∪
      (fun t : ℝ => (t, combR n - t)) '' K)) := by
  refine isPathConnected_preimage_combSet (union_subset (combAxisSeg_subset J)
    (combArmSeg_subset n hKn)) ?_
  refine ((hJ.isPathConnected ⟨_, hJr⟩).image (by fun_prop)).union
    ((hK.isPathConnected ⟨_, hKr⟩).image (by fun_prop)) ⟨(combR n, 0), ⟨_, hJr, rfl⟩, ⟨_, hKr, ?_⟩⟩
  simp

/-- A base point joined to every point through path-connected subsets. -/
theorem isPathConnected_of_forall_mem {Z : Type*} [TopologicalSpace Z] {G : Set Z} {x : Z}
    (hx : x ∈ G) (h : ∀ y ∈ G, ∃ T ⊆ G, x ∈ T ∧ y ∈ T ∧ IsPathConnected T) :
    IsPathConnected G :=
  ⟨x, hx, fun y hy =>
    let ⟨_, hTG, hxT, hyT, hT⟩ := h y hy
    (hT.joinedIn _ hxT _ hyT).mono hTG⟩

/-- The basic neighbourhoods of the comb. -/
def combNbhd (x : combSet) (δ : ℝ) : Set combSet :=
  if (x : ℝ × ℝ).2 = 0 then
    {q | (q : ℝ × ℝ).1 ∈ ball (x : ℝ × ℝ).1 δ ∧ (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 ∈ ball (x : ℝ × ℝ).1 δ}
  else
    {q | (q : ℝ × ℝ).1 ∈ ball (x : ℝ × ℝ).1 δ ∧ 0 < (q : ℝ × ℝ).2 ∧
      (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 = (x : ℝ × ℝ).1 + (x : ℝ × ℝ).2}

theorem isOpen_combNbhd (x : combSet) (δ : ℝ) : IsOpen (combNbhd x δ) := by
  have h1 : Continuous fun q : combSet => (q : ℝ × ℝ).1 := continuous_fst.comp continuous_subtype_val
  have hF : Continuous fun q : combSet => (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 :=
    h1.add (continuous_snd.comp continuous_subtype_val)
  unfold combNbhd
  split_ifs with hx
  · exact (isOpen_ball.preimage h1).inter (isOpen_ball.preimage hF)
  · obtain ⟨n, -, -, hn⟩ := combSet_arm_of_pos x ((combSet_snd_nonneg x).lt_of_ne' hx)
    rw [hn]
    exact (isOpen_ball.preimage h1).inter (isOpen_combArm n)

theorem mem_combNbhd (x : combSet) {δ : ℝ} (hδ : 0 < δ) : x ∈ combNbhd x δ := by
  unfold combNbhd
  split_ifs with hx
  · exact ⟨mem_ball_self hδ, by rw [hx, add_zero]; exact mem_ball_self hδ⟩
  · exact ⟨mem_ball_self hδ, (combSet_snd_nonneg x).lt_of_ne' hx, rfl⟩

theorem combNbhd_subset_ball (x : combSet) (δ : ℝ) : combNbhd x δ ⊆ ball x (2 * δ) := by
  intro q hq
  rw [mem_ball, Subtype.dist_eq, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  unfold combNbhd at hq
  split_ifs at hq with hx
  · obtain ⟨h1, h2⟩ := hq
    rw [mem_ball, Real.dist_eq] at h1 h2
    rw [hx, sub_zero]
    refine ⟨by linarith [abs_nonneg ((q : ℝ × ℝ).1 - (x : ℝ × ℝ).1)], ?_⟩
    have := abs_sub (((q : ℝ × ℝ).1 + (q : ℝ × ℝ).2) - (x : ℝ × ℝ).1)
      ((q : ℝ × ℝ).1 - (x : ℝ × ℝ).1)
    rw [show ((q : ℝ × ℝ).1 + (q : ℝ × ℝ).2) - (x : ℝ × ℝ).1 - ((q : ℝ × ℝ).1 - (x : ℝ × ℝ).1)
      = (q : ℝ × ℝ).2 by ring] at this
    linarith
  · obtain ⟨h1, -, h3⟩ := hq
    rw [mem_ball, Real.dist_eq] at h1
    have : (q : ℝ × ℝ).2 - (x : ℝ × ℝ).2 = -((q : ℝ × ℝ).1 - (x : ℝ × ℝ).1) := by linarith
    rw [this, abs_neg]
    have h0 : 0 ≤ δ := (abs_nonneg _).trans h1.le
    exact ⟨by linarith, by linarith⟩

theorem isPathConnected_combNbhd (x : combSet) {δ : ℝ} (hδ : 0 < δ) :
    IsPathConnected (combNbhd x δ) := by
  have hmem := mem_combNbhd x hδ
  unfold combNbhd at hmem ⊢
  split_ifs with hx
  · rw [if_pos hx] at hmem
    refine isPathConnected_of_forall_mem hmem fun y hy => ?_
    have hxa : x ∈ ((↑) : combSet → ℝ × ℝ) ⁻¹' ((fun t : ℝ => (t, (0 : ℝ))) ''
        ball (x : ℝ × ℝ).1 δ) := ⟨_, mem_ball_self hδ, by rw [← hx]⟩
    rcases (combSet_snd_nonneg y).lt_or_eq with hy0 | hy0
    · obtain ⟨n, hn0, hn1, hn⟩ := combSet_arm_of_pos y hy0
      have hrn : combR n ∈ ball (x : ℝ × ℝ).1 δ := hn ▸ hy.2
      refine ⟨_, ?_, Or.inl hxa, Or.inr ⟨(y : ℝ × ℝ).1, ⟨hy.1, hn0, hn1.le⟩, ?_⟩,
        isPathConnected_combAxisArm n (convex_ball _ _)
          ((convex_ball _ _).inter (convex_Ioc 0 (combR n))) inter_subset_right hrn
          ⟨hrn, combR_pos n, le_rfl⟩⟩
      · rintro q (⟨t, ht, hq⟩ | ⟨t, ⟨ht, -⟩, hq⟩)
        · refine ⟨?_, ?_⟩ <;> rw [← hq] <;> simpa using ht
        · refine ⟨?_, ?_⟩ <;> rw [← hq]
          · exact ht
          · simpa using hrn
      · rw [Prod.ext_iff]; exact ⟨rfl, by simp; linarith⟩
    · refine ⟨_, ?_, hxa, ⟨_, hy.1, by rw [hy0]⟩,
        isPathConnected_combAxisSeg (convex_ball _ _) ⟨_, mem_ball_self hδ⟩⟩
      rintro q ⟨t, ht, hq⟩
      refine ⟨?_, ?_⟩ <;> rw [← hq] <;> simpa using ht
  · rw [if_neg hx] at hmem
    obtain ⟨n, hn0, hn1, hn⟩ := combSet_arm_of_pos x ((combSet_snd_nonneg x).lt_of_ne' hx)
    refine isPathConnected_of_forall_mem hmem fun y hy => ?_
    have hyn : (y : ℝ × ℝ).1 + (y : ℝ × ℝ).2 = combR n := hy.2.2.trans hn
    obtain ⟨m, hm0, hm1, hm⟩ := combSet_arm_of_pos y hy.2.1
    have hmn : combR m = combR n := hm.symm.trans hyn
    have hT : ((↑) : combSet → ℝ × ℝ) ⁻¹' ((fun t : ℝ => (t, combR n - t)) ''
        (ball (x : ℝ × ℝ).1 δ ∩ Ioo 0 (combR n))) ⊆ {q : combSet | (q : ℝ × ℝ).1 ∈ ball (x : ℝ × ℝ).1 δ ∧
          0 < (q : ℝ × ℝ).2 ∧ (q : ℝ × ℝ).1 + (q : ℝ × ℝ).2 = (x : ℝ × ℝ).1 + (x : ℝ × ℝ).2} := by
      rintro q ⟨t, ⟨ht, ht0, ht1⟩, hq⟩
      refine ⟨by rw [← hq]; exact ht, by rw [← hq]; simp; linarith, ?_⟩
      rw [← hq, hn]; simp
    refine ⟨_, hT, ⟨(x : ℝ × ℝ).1, ⟨mem_ball_self hδ, hn0, hn1⟩, ?_⟩,
      ⟨(y : ℝ × ℝ).1, ⟨hy.1, hm0, hmn ▸ hm1⟩, ?_⟩,
      isPathConnected_combArmSeg n ((convex_ball _ _).inter (convex_Ioo _ _))
        ⟨_, mem_ball_self hδ, hn0, hn1⟩ fun t ht => ⟨ht.2.1, ht.2.2.le⟩⟩
    · rw [Prod.ext_iff]; exact ⟨rfl, by simp; linarith⟩
    · rw [Prod.ext_iff]; exact ⟨rfl, by simp; linarith⟩

theorem hasBasis_nhds_combNbhd (x : combSet) :
    (𝓝 x).HasBasis (fun δ : ℝ => 0 < δ) (combNbhd x) :=
  nhds_basis_ball.to_hasBasis' (fun ε hε => ⟨ε / 2, half_pos hε, by
      have := combNbhd_subset_ball x (ε / 2); rwa [mul_div_cancel₀ _ two_ne_zero] at this⟩)
    fun δ hδ => (isOpen_combNbhd x δ).mem_nhds (mem_combNbhd x hδ)

/-- The comb is locally path-connected. -/
instance : LocPathConnectedSpace combSet :=
  LocPathConnectedSpace.of_bases hasBasis_nhds_combNbhd fun x _ hδ => isPathConnected_combNbhd x hδ

/-- The first projection of the comb is a spread. -/
theorem isSpread_combProj : IsSpread combProj := by
  refine isSpread_iff_of_locallyConnectedSpace.2 ⟨continuous_combProj, fun x O hO hxO => ?_⟩
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO x hxO
  rcases (combSet_snd_nonneg x).lt_or_eq with hx | hx
  · obtain ⟨n, hn0, hn1, hn⟩ := combSet_arm_of_pos x hx
    set δ := min (ε / 2) (combR n - (x : ℝ × ℝ).1)
    have hδ : 0 < δ := lt_min (half_pos hε) (by linarith)
    refine ⟨ball (x : ℝ × ℝ).1 δ, isOpen_ball, mem_ball_self hδ, fun q hq => hεO ?_⟩
    have hrn : combR n ∉ ball (x : ℝ × ℝ).1 δ := by
      rw [mem_ball, Real.dist_eq, abs_of_pos (by linarith), not_lt]
      exact min_le_right _ _
    have hq' := connectedComponentIn_subset_combArm hrn (mem_ball_self hδ) ⟨hx, hn⟩ hq
    have hq'' : combProj q ∈ ball (x : ℝ × ℝ).1 δ :=
      connectedComponentIn_subset (combProj ⁻¹' ball (x : ℝ × ℝ).1 δ) x hq
    have hmem : q ∈ combNbhd x δ := by
      unfold combNbhd
      rw [if_neg hx.ne']
      exact ⟨hq'', hq'.1, hq'.2.trans hn.symm⟩
    exact ball_subset_ball (by linarith [min_le_left (ε / 2) (combR n - (x : ℝ × ℝ).1)])
      (combNbhd_subset_ball x δ hmem)
  · refine ⟨ball (x : ℝ × ℝ).1 (ε / 2), isOpen_ball, mem_ball_self (half_pos hε),
      fun q hq => hεO ?_⟩
    have hq' := connectedComponentIn_subset_combAxis isOpen_ball
      (mem_ball_self (half_pos hε)) hx.symm hq
    have hq'' : combProj q ∈ ball (x : ℝ × ℝ).1 (ε / 2) :=
      connectedComponentIn_subset (combProj ⁻¹' ball (x : ℝ × ℝ).1 (ε / 2)) x hq
    have hmem : q ∈ combNbhd x (ε / 2) := by
      unfold combNbhd
      rw [if_pos hx.symm]
      exact ⟨hq'', hq'⟩
    have := combNbhd_subset_ball x (ε / 2) hmem
    rwa [mul_div_cancel₀ _ two_ne_zero] at this

/-- The basis `{(-ρ, ρ) : ρ > 0}` of connected open neighbourhoods of `0 ∈ ℝ`. -/
def combBasis : Set (Set ℝ) := {U | ∃ ρ, 0 < ρ ∧ U = Ioo (-ρ) ρ}

theorem combBasis_isCNbhd : ∀ U ∈ combBasis, IsCNbhd (0 : ℝ) U := by
  rintro _ ⟨ρ, hρ, rfl⟩
  exact ⟨isOpen_Ioo, isPreconnected_Ioo, by simp [hρ]⟩

theorem combBasis_basis : ∀ N ∈ 𝓝 (0 : ℝ), ∃ U ∈ combBasis, U ⊆ N := by
  intro N hN
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
  exact ⟨Ioo (-ε) ε, ⟨ε, hε, rfl⟩, by
    rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hεN; exact hεN⟩

/-- The radius of a member of `combBasis`. -/
def combRad (U : combBasis) : ℝ := Classical.choose U.2

theorem combRad_pos (U : combBasis) : 0 < combRad U := (Classical.choose_spec U.2).1

theorem combRad_eq (U : combBasis) : (U : Set ℝ) = Ioo (-combRad U) (combRad U) :=
  (Classical.choose_spec U.2).2

/-- The point of the arm `n` at abscissa `t ∈ (0, r n]`. -/
def combArmPt (n : ℕ) (t : ℝ) (h0 : 0 < t) (h1 : t ≤ combR n) : combSet :=
  ⟨(t, combR n - t), Or.inr ⟨n, h0, h1, rfl⟩⟩

/-- The abscissa of the point of the arm `n` chosen over `U`. -/
def combAbs (n : ℕ) (U : combBasis) : ℝ := min (combRad U) (combR n) / 2

theorem combAbs_pos (n : ℕ) (U : combBasis) : 0 < combAbs n U :=
  half_pos (lt_min (combRad_pos U) (combR_pos n))

theorem combAbs_lt (n : ℕ) (U : combBasis) : combAbs n U < combR n := by
  have := min_le_right (combRad U) (combR n)
  have := combAbs_pos n U
  unfold combAbs at *; linarith

theorem combAbs_mem (n : ℕ) (U : combBasis) : combAbs n U ∈ (U : Set ℝ) := by
  rw [combRad_eq]
  have := min_le_left (combRad U) (combR n)
  have := combAbs_pos n U
  refine ⟨by linarith [combRad_pos U], ?_⟩
  unfold combAbs at *; linarith

/-- The point of the arm `n` over `U`. -/
def combPt (n : ℕ) (U : combBasis) : combSet :=
  combArmPt n (combAbs n U) (combAbs_pos n U) (combAbs_lt n U).le

theorem combPt_mem (n : ℕ) (U : combBasis) : combPt n U ∈ combProj ⁻¹' (U : Set ℝ) :=
  combAbs_mem n U

/-- Over `U ⊆ V` the points of the arm `n` lie in one component of `p⁻¹ V`. -/
theorem combPt_mem_connectedComponentIn (n : ℕ) {U V : combBasis} (hUV : (U : Set ℝ) ⊆ V) :
    combPt n V ∈ connectedComponentIn (combProj ⁻¹' (V : Set ℝ)) (combPt n U) := by
  have hVc : Convex ℝ ((V : Set ℝ) ∩ Ioo 0 (combR n)) := by
    rw [combRad_eq]; exact (convex_Ioo _ _).inter (convex_Ioo _ _)
  have hT := isPathConnected_combArmSeg n hVc
    ⟨_, combAbs_mem n V, combAbs_pos n V, combAbs_lt n V⟩ fun t ht => ⟨ht.2.1, ht.2.2.le⟩
  refine hT.isConnected.isPreconnected.subset_connectedComponentIn
    ⟨combAbs n U, ⟨hUV (combAbs_mem n U), combAbs_pos n U, combAbs_lt n U⟩, rfl⟩ ?_
    ⟨combAbs n V, ⟨combAbs_mem n V, combAbs_pos n V, combAbs_lt n V⟩, rfl⟩
  rintro q ⟨t, ⟨ht, -⟩, hq⟩
  show (q : ℝ × ℝ).1 ∈ (V : Set ℝ)
  rw [← hq]; exact ht

/-- The thread of the arm `n`: the components of the `p⁻¹ U` containing the arm `n` near `0`.
It is not realised by a point of the fibre (`combThread_ne`). -/
def combThread (n : ℕ) : FiberThread combProj combBasis where
  toFun U := connectedComponentIn (combProj ⁻¹' (U : Set ℝ)) (combPt n U)
  isCompOf U := isCompOf_connectedComponentIn (combPt_mem n U)
  mono U V hUV := by
    rw [← connectedComponentIn_eq (combPt_mem_connectedComponentIn n hUV)]
    exact connectedComponentIn_mono _ (preimage_mono hUV)

/-- The origin, the only point of the fibre over `0`. -/
def combOrigin : combProj ⁻¹' {(0 : ℝ)} := ⟨⟨(0, 0), Or.inl rfl⟩, rfl⟩

theorem combFiber_eq (x : combProj ⁻¹' {(0 : ℝ)}) : x = combOrigin := by
  have h1 : ((x : combSet) : ℝ × ℝ).1 = 0 := x.2
  have h2 : ((x : combSet) : ℝ × ℝ).2 = 0 := by
    rcases (combSet_snd_nonneg x).lt_or_eq with h | h
    · obtain ⟨n, hn, -⟩ := combSet_arm_of_pos x h
      linarith
    · exact h.symm
  exact Subtype.ext (Subtype.ext (Prod.ext h1 h2))

/-- Over a neighbourhood wider than the arm `n`, its thread agrees with the origin's. -/
theorem combThread_eq_of_lt (n : ℕ) (U : combBasis) (h : combR n < combRad U) :
    (combThread n).toFun U =
      (fiberMap combProj combBasis combBasis_isCNbhd combOrigin).toFun U := by
  show connectedComponentIn _ (combPt n U) = connectedComponentIn _ ((combOrigin : combSet))
  have hT := isPathConnected_combAxisArm n (convex_Icc 0 (combR n)) (convex_Ioc 0 (combR n))
    subset_rfl ⟨(combR_pos n).le, le_rfl⟩ ⟨combR_pos n, le_rfl⟩
  set S : Set combSet := ((↑) : combSet → ℝ × ℝ) ⁻¹' ((fun t : ℝ => (t, (0 : ℝ))) '' Icc 0 (combR n) ∪
      (fun t : ℝ => (t, combR n - t)) '' Ioc 0 (combR n)) with hS
  have hsub : S ⊆ combProj ⁻¹' (U : Set ℝ) := by
    have hU := combRad_eq U
    rintro q (⟨t, ht, hq⟩ | ⟨t, ht, hq⟩) <;>
    · show (q : ℝ × ℝ).1 ∈ (U : Set ℝ)
      rw [hU, ← hq]
      exact ⟨by linarith [ht.1, combRad_pos U], by linarith [ht.2]⟩
  have hpt : combPt n U ∈ S := Or.inr ⟨combAbs n U, ⟨combAbs_pos n U, (combAbs_lt n U).le⟩, rfl⟩
  have := hT.isConnected.isPreconnected.subset_connectedComponentIn
    (x := (combOrigin : combSet)) (Or.inl ⟨0, ⟨le_rfl, (combR_pos n).le⟩, rfl⟩) hsub hpt
  exact (connectedComponentIn_eq this).symm

/-- Over `(-r n, r n)` the thread of the arm `n` does not contain the origin. -/
theorem combThread_ne (n : ℕ) :
    combThread n ≠ fiberMap combProj combBasis combBasis_isCNbhd combOrigin := by
  intro h
  set U₀ : combBasis := ⟨Ioo (-combR n) (combR n), combR n, combR_pos n, rfl⟩
  have h1 := congrArg (fun s : FiberThread combProj combBasis => s.toFun U₀) h
  have hO : (combOrigin : combSet) ∈
      (fiberMap combProj combBasis combBasis_isCNbhd combOrigin).toFun U₀ :=
    mem_connectedComponentIn (show (0 : ℝ) ∈ Ioo (-combR n) (combR n) by
      simp [combR_pos n])
  rw [← h1] at hO
  have hrn : combR n ∉ (U₀ : Set ℝ) := fun h => lt_irrefl _ h.2
  have hpt : combPt n U₀ ∈ combArm n := by
    refine ⟨?_, ?_⟩
    · show 0 < combR n - combAbs n U₀
      linarith [combAbs_lt n U₀]
    · show combAbs n U₀ + (combR n - combAbs n U₀) = combR n
      ring
  have := connectedComponentIn_subset_combArm hrn (combPt_mem n U₀) hpt hO
  exact lt_irrefl _ this.1

/-- **Counterexample to the "open" of `prop:spread_fiber` (l.928).** The first projection of the
comb (a locally path-connected, Hausdorff, second countable subspace of `ℝ²`) is a spread over
`ℝ`, and for the basis `{(-ρ, ρ)}` of connected open neighbourhoods of `0` the natural map
`p⁻¹(0) → lim X_U` is not an open map: its image `{φ(0,0)}` is not open, since every cylinder
around `φ(0,0)` contains the unrealised thread of some arm. -/
theorem not_isOpenMap_fiberMap_comb :
    IsSpread combProj ∧ (∀ N ∈ 𝓝 (0 : ℝ), ∃ U ∈ combBasis, U ⊆ N) ∧
      ¬ IsOpenMap (fiberMap combProj combBasis combBasis_isCNbhd) := by
  refine ⟨isSpread_combProj, combBasis_basis, fun h => ?_⟩
  obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.1 h.isOpen_range
  set T := fiberMap combProj combBasis combBasis_isCNbhd combOrigin
  have hcT : T.coords ∈ t := by
    have : T ∈ FiberThread.coords ⁻¹' t := by rw [hpre]; exact mem_range_self _
    exact this
  obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.1 ht _ hcT
  have hev : ∀ᶠ n in atTop, ∀ U ∈ I, combR n < combRad U :=
    (eventually_all_finset I).2 fun U _ =>
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
        (gt_mem_nhds (combRad_pos U))
  obtain ⟨n, hn⟩ := hev.exists
  have hs : (combThread n).coords ∈ t := hIu fun U hU => by
    show (combThread n).toFun U ∈ u U
    rw [combThread_eq_of_lt n U (hn U hU)]
    exact (hu U hU).2
  have : combThread n ∈ range (fiberMap combProj combBasis combBasis_isCNbhd) := by
    rw [← hpre]; exact hs
  obtain ⟨x, hx⟩ := this
  rw [combFiber_eq x] at hx
  exact combThread_ne n hx.symm

end Comb

/-! ### The completion functor -/

section Functor

open CategoryTheory

/-- The spreads the completion is a functor on: Hausdorff locally connected base, T0 source. -/
def IsLCSpread : ObjectProperty Spread.{u} := fun S =>
  LocallyConnectedSpace S.Y ∧ T2Space S.Y ∧ T0Space S.X

/-- The Fox completion of a spread over a locally connected base, as an object of `Spread`. -/
def Spread.foxCompletion (S : Spread.{u}) [LocallyConnectedSpace S.Y] : Spread.{u} where
  X := SpreadEnd S.p
  Y := S.Y
  p := SpreadEnd.base
  isSpread := SpreadEnd.isSpread_base S.isSpread

/-- **`theo:Fox_completion_functor`, functoriality.** The Fox completion is a functor from the
spreads over Hausdorff locally connected bases (T0 sources) to `Spread`: a morphism `(f, g)`
goes to `(f, ḡ)`, `ḡ` the unique continuous extension of `g` (`SpreadEnd.eq_map`). -/
def foxCompletionFunctor : IsLCSpread.{u}.FullSubcategory ⥤ Spread.{u} where
  obj S := haveI := S.property.1; S.obj.foxCompletion
  map {S T} φ := by
    haveI := S.property.1; haveI := T.property.1
    exact ⟨⟨SpreadEnd.map φ.hom.f.continuous φ.hom.g.continuous φ.hom.comm,
      SpreadEnd.continuous_map _ _ _⟩, φ.hom.f, fun _ => rfl⟩
  map_id S := by
    haveI := S.property.1; haveI := S.property.2.1
    refine Spread.Hom.ext ?_ rfl
    ext e : 1
    exact congrFun (SpreadEnd.map_id (p₁ := S.obj.p)) e
  map_comp {S T R} φ ψ := by
    haveI := S.property.1; haveI := T.property.1; haveI := R.property.1
    haveI := R.property.2.1
    refine Spread.Hom.ext ?_ rfl
    ext e : 1
    exact congrFun (SpreadEnd.map_comp φ.hom.f.continuous φ.hom.g.continuous φ.hom.comm
      ψ.hom.f.continuous ψ.hom.g.continuous ψ.hom.comm) e

theorem foxCompletionFunctor_map_ofPoint {S T : IsLCSpread.{u}.FullSubcategory} (φ : S ⟶ T)
    (x : S.obj.X) : haveI := S.property.1
    (foxCompletionFunctor.map φ).g (SpreadEnd.ofPoint S.obj.p x) =
      SpreadEnd.ofPoint T.obj.p (φ.hom.g x) := by
  haveI := S.property.1
  exact SpreadEnd.map_ofPoint φ.hom.f.continuous φ.hom.g.continuous φ.hom.comm x

/-- The completion functor is faithful. -/
instance : foxCompletionFunctor.{u}.Faithful where
  map_injective {S T} φ ψ h := by
    haveI := S.property.1; haveI := T.property.1; haveI := T.property.2.2
    apply ObjectProperty.hom_ext
    apply Spread.Hom.ext
    · ext x
      have h1 := congrArg (fun m : foxCompletionFunctor.obj S ⟶ foxCompletionFunctor.obj T =>
        m.g (SpreadEnd.ofPoint S.obj.p x)) h
      simp only [foxCompletionFunctor_map_ofPoint] at h1
      exact (SpreadEnd.isEmbedding_ofPoint T.obj.isSpread).injective h1
    · exact congrArg (fun m : foxCompletionFunctor.obj S ⟶ foxCompletionFunctor.obj T => m.f) h

/-- The spread `ℂ ∖ {a} → ℂ`, an object of the domain of the completion functor. -/
def planeMinus (a : ℂ) : IsLCSpread.{0}.FullSubcategory :=
  ⟨⟨({a}ᶜ : Set ℂ), ℂ, Subtype.val,
    isSpread_val_compl_countable (countable_singleton a)⟩, inferInstance, inferInstance,
    inferInstance⟩

/-- **`theo:Fox_completion_functor`: the completion functor is not full.** -/
theorem not_full_foxCompletionFunctor : ¬ foxCompletionFunctor.{0}.Full := by
  intro hfull
  have h₀ := isFoxCompletion_compl_countable (countable_singleton (0 : ℂ))
  have h₁ := isFoxCompletion_compl_countable (countable_singleton (1 : ℂ))
  let G : foxCompletionFunctor.obj (planeMinus 0) ⟶ foxCompletionFunctor.obj (planeMinus 1) :=
    ⟨⟨fun e => h₁.homeomorph (h₀.homeomorph.symm e),
      h₁.homeomorph.continuous.comp h₀.homeomorph.symm.continuous⟩,
      ContinuousMap.id ℂ, fun e => by
        show (h₁.toEnd (h₀.homeomorph.symm e)).base = e.base
        rw [IsFoxCompletion.toEnd_base]
        have := congrArg SpreadEnd.base (h₀.homeomorph.apply_symm_apply e)
        rw [IsFoxCompletion.homeomorph_apply, IsFoxCompletion.toEnd_base] at this
        exact this⟩
  obtain ⟨φ, hφ⟩ := foxCompletionFunctor.map_surjective G
  have hone : (1 : ℂ) ∈ ({0}ᶜ : Set ℂ) := by simp
  set x : (planeMinus 0).obj.X := ⟨1, hone⟩
  have key := congrArg (fun m : foxCompletionFunctor.obj (planeMinus 0) ⟶
    foxCompletionFunctor.obj (planeMinus 1) => m.g (SpreadEnd.ofPoint (planeMinus 0).obj.p x)) hφ
  simp only [foxCompletionFunctor_map_ofPoint] at key
  have hx₀ : h₀.homeomorph.symm (SpreadEnd.ofPoint (planeMinus 0).obj.p x) = (1 : ℂ) := by
    rw [Homeomorph.symm_apply_eq, IsFoxCompletion.homeomorph_apply]
    exact (h₀.toEnd_comp x).symm
  change SpreadEnd.ofPoint (planeMinus 1).obj.p (φ.hom.g x) =
    h₁.homeomorph (h₀.homeomorph.symm (SpreadEnd.ofPoint (planeMinus 0).obj.p x)) at key
  rw [hx₀, IsFoxCompletion.homeomorph_apply] at key
  let y : ({1}ᶜ : Set ℂ) := φ.hom.g x
  have k2 : h₁.toEnd (y : ℂ) = h₁.toEnd 1 := (h₁.toEnd_comp y).trans key
  have : (y : ℂ) = 1 := h₁.homeomorph.injective k2
  exact y.2 this

/-- The Fox completion of a spread in `IsLCSpread` is again in `IsLCSpread`: same Hausdorff locally
connected base, and the space of ends is Hausdorff (`SpreadEnd.t2Space`), hence T0. -/
theorem isLCSpread_foxCompletion (S : IsLCSpread.{u}.FullSubcategory) :
    IsLCSpread (foxCompletionFunctor.obj S) := by
  haveI := S.property.1; haveI := S.property.2.1
  haveI : T2Space (SpreadEnd S.obj.p) := SpreadEnd.t2Space
  exact ⟨S.property.1, S.property.2.1, inferInstanceAs (T0Space (SpreadEnd S.obj.p))⟩

/-- **`theo:Fox_completion_functor`, "from `Spread` to itself".** The Fox completion as an
endofunctor of the full subcategory `IsLCSpread` (spreads over Hausdorff locally connected bases
with T0 sources), lifted from `foxCompletionFunctor`. -/
def foxCompletionEndofunctor : IsLCSpread.{u}.FullSubcategory ⥤ IsLCSpread.{u}.FullSubcategory :=
  IsLCSpread.lift foxCompletionFunctor isLCSpread_foxCompletion

theorem foxCompletionEndofunctor_comp_ι :
    foxCompletionEndofunctor.{u} ⋙ IsLCSpread.ι = foxCompletionFunctor.{u} := rfl

/-- The completion endofunctor is faithful. -/
instance : foxCompletionEndofunctor.{u}.Faithful := by
  unfold foxCompletionEndofunctor; infer_instance

/-- The completion endofunctor is not full (`ℂ ∖ {0}`, `ℂ ∖ {1}`). -/
theorem not_full_foxCompletionEndofunctor : ¬ foxCompletionEndofunctor.{0}.Full := by
  intro h
  apply not_full_foxCompletionFunctor
  rw [← foxCompletionEndofunctor_comp_ι]
  infer_instance

end Functor

end GX
