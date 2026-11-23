import Causal.LocateExtension
import Causal.LadderLocal

/-!
# Chronal neighbours at a point in `M` and in every open set: the bridge

Programme target `T-abs-chronal-neighbour-bridge` (`programme/roadmap.toml:571–583`; layer 1, no
label of `ETT.tex`; ETT-layer imports only, no model, no metric notion). It joins
`HasChronalNeighbour` of `Causal.LocateExtension` (one point, one side, chronology in `M`;
`LocateExtension.lean:138`) and `ChronalNeighbours` of `Causal.LadderLocal` (every point, both
sides, chronology in every open `V`; `LadderLocal.lean:178`), through two named forms of chronology
in `M`: `HasChronalNeighbourEverywhere` (every point, one side) and `NonemptyChronalCones` (every
point, both sides).

* **`T-abs-chronal-neighbour-bridge/0-everywhere`** — `ChronalNeighbours.hasChronalNeighbour`,
  `ChronalNeighbours.hasChronalNeighbourEverywhere`: chronal neighbours in every open set give a
  chronal neighbour at every point; in fact both sides in `M` (`ChronalNeighbours.nonemptyChronalCones`)
  and in every open `V ∋ p` (`ChronalPastNeighbours.Iminus_nonempty_of_mem`, and the future base
  `ChronalFutureNeighbours.Iplus_nonempty_of_mem`).
* **`T-abs-chronal-neighbour-bridge/1-minimal`** — `AbsolutelyMinimal.chronalNeighbours_iff`:
  under absolute minimality on a `T1` space, `ChronalNeighbours` iff `I⁺(x)` and `I⁻(x)` are
  non-empty for every `x`; also `CausallyArcConnected.chronalNeighbours_iff` (no separation, one
  side each: `CausallyArcConnected.chronalPastNeighbours_iff`, `…chronalFutureNeighbours_iff`) and
  `AbsolutelyMinimal.chronalNeighbours_iff_Z`. Neither hypothesis can be dropped: `globalLine_separates`
  (`T2`, not absolutely minimal), `sierpinskiCausality_separates` (absolutely minimal, not `T1`);
  the latter also shows that `T1` cannot be dropped from `AbsolutelyMinimal.chronalPastNeighbours_iff`
  (`not_chronalPastNeighbours_of_absolutelyMinimal_bare`).
* **`T-abs-chronal-neighbour-bridge/2-leaving`** — `exists_leaving_of_chronalNeighbours`,
  `exists_leaving_of_isOpenEmbedding_of_chronalNeighbours`,
  `futureBoundary_union_pastBoundary_nonempty_of_chronalNeighbours`,
  `frontier_subset_closure_boundary_of_chronalNeighbours`: the leaving theorems with
  `ChronalNeighbours`; with chronology in every open, local causal arc-connectedness suffices
  (`exists_leaving_of_locallyCausallyArcConnected`, one side: `…_of_chronalPastNeighbours`).
* **`T-abs-chronal-neighbour-bridge/3-converse`** — `not_chronalNeighbours_of_hasChronalNeighbourEverywhere_bare`:
  the converse fails. The closed half-line is `T1`, preconnected, causally arc-connected and every
  point has a chronal neighbour, but `I⁻(0) = ∅` (`closedHalfLine_separates_chronalNeighbours`).

> Bridge between LocateExtension's HasChronalNeighbour (one point, one side, chronology in M) and
> LadderLocal's ChronalNeighbours (every point, both sides, chronology in every open V):
> ChronalNeighbours gives HasChronalNeighbour everywhere; under absolute minimality on a T1 space
> ChronalNeighbours is 'I⁺(x) and I⁻(x) non-empty for every x'; exists_leaving restated with
> ChronalNeighbours (`programme/roadmap.toml:572`, the target's title)

> It is not `HasChronalNeighbour` of the `Causal.LocateExtension` (one point, one side,
> chronology in `M`). (`Causal/LadderLocal.lean:100–101`, SCOPE)

## Hypothesis checklist

| target hypothesis | here |
|---|---|
| (0) `ChronalNeighbours` | ✓ carried; one half suffices for the one-sided conclusion (the proof uses the future one) |
| (1) absolute minimality, `T1` | ✓ carried, both necessary (`globalLine_separates`, `sierpinskiCausality_separates`); ⚠ an alternative: causal arc-connectedness alone, no separation (`CausallyArcConnected.chronalNeighbours_iff`) |
| (2) `exists_leaving`'s: `M` preconnected, causally arc-connected, `O` open, non-empty, proper; `HasChronalNeighbour` on `∂O` | ✓ carried, the last replaced by `ChronalNeighbours` (stronger: a corollary); ⚠ weakened in `exists_leaving_of_locallyCausallyArcConnected`: local causal arc-connectedness, past neighbours only |
| (2) `exists_leaving_of_isOpenEmbedding`'s: `ι` open embedding, `N` non-empty, `range ι ≠ univ` | ✓ carried |

## SCOPE (disclosed)

* **Three strengths of chronology.** `ChronalNeighbours` ⇒ `NonemptyChronalCones` ⇒
  `HasChronalNeighbourEverywhere`, both strict: `globalLine` (`≪` only in `ℝ` itself) has non-empty
  cones without chronal neighbours; the closed half-line has a chronal neighbour everywhere and
  `I⁻(0) = ∅`. The first arrow reverses under absolute minimality on a `T1` space or under causal
  arc-connectedness; the second never does by those hypotheses (the half-line has both).
  `exists_leaving` asks still less: `HasChronalNeighbour` on `∂O` only.
* **The two names are not ladder nodes.** `HasChronalNeighbourEverywhere` and `NonemptyChronalCones`
  are defined here for the keeper (OQ-51 asks whether the one-sided form becomes a node);
  `NonemptyChronalCones` is, up to the bound name, the inline `hI` of
  `Causality.Zplus_Zminus_eq_univ` (`Causal.Remarks.BTZPoints`), `Causality.K_lorentzien` and
  `Causality.K_eq_I_of_pushUp` (`Causal.Remarks.Tarentin`), modules not imported here.
* **The local leaving form** needs neither absolute minimality nor causal arc-connectedness of `M`;
  local arc-connectedness with absolute minimality is arc-connectedness
  (`LocallyCausallyArcConnected.causallyArcConnected`), so it is more general only on a
  non-absolutely-minimal spacetime with chronal neighbours; no such example is given here.
* **The Sierpiński space** (`Prop`, `{True}` open) is not one of ETT's spacetimes (not `T1`): it
  shows only that the separation axiom of `chronalNeighbours_iff` and of the strict
  `AbsolutelyMinimal.chronalPastNeighbours_iff` is used. Every cover of it contains `⊤`, so every
  causality on it is absolutely minimal. `globalLine` and the closed half-line are Hausdorff and
  second countable; `globalLine` is moreover causal, causally open and has push-up, so it also
  separates these from absolute minimality (`globalLine_separates`).
* Non-vacuity: the timelike line has `ChronalNeighbours` (`timelikeLine_chronalNeighbours`), hence
  every hypothesis of part 2. Ladder witnesses for the new names: `lightlikeLine_separates_hasChronalNeighbour`,
  `isolatedLine_separates_chronalNeighbours` (the latter also settles `causally_plain ⇏
  chronal_neighbours`). No `sorry`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u v

variable {M : Type u} [TopologicalSpace M]

namespace Causality

/-! ## Two named forms of chronology in `M` -/

section Defs

variable (C : Causality M)

/-- **A chronal neighbour at every point** (proposed ladder `has_chronal_neighbour`; OQ-51):
every point `p` is chronologically related to some point of `M`, to the future or to the past
(`HasChronalNeighbour` of `Causal.LocateExtension` at every point). One-sided: the endpoint of the
closed half-line qualifies (`closedHalfLine_hasChronalNeighbourEverywhere`). -/
def HasChronalNeighbourEverywhere : Prop := ∀ p : M, C.HasChronalNeighbour p

/-- **Non-empty chronological cones** (proposed ladder `nonempty_chronal_cones`): every point has
a non-empty chronological future and a non-empty chronological past in `M`. Verbatim the
hypothesis `hI` of `rem:lorentz_tarentin` and `cor:K_lorentzien` in the library
(`Causality.Zplus_Zminus_eq_univ`, `Causality.K_lorentzien`). Under absolute minimality on a `T1`
space, or under causal arc-connectedness, it is `ChronalNeighbours`. -/
def NonemptyChronalCones : Prop :=
  ∀ x : M, (C.Iplus ⊤ {x}).Nonempty ∧ (C.Iminus ⊤ {x}).Nonempty

end Defs

variable {C : Causality M} {O : Set M} {p : M}

theorem dual_hasChronalNeighbourEverywhere :
    C.dual.HasChronalNeighbourEverywhere ↔ C.HasChronalNeighbourEverywhere :=
  forall_congr' fun _ => dual_hasChronalNeighbour

theorem dual_nonemptyChronalCones : C.dual.NonemptyChronalCones ↔ C.NonemptyChronalCones :=
  forall_congr' fun _ => And.comm

/-- Non-empty chronological cones give a chronal neighbour at every point. -/
theorem NonemptyChronalCones.hasChronalNeighbourEverywhere (h : C.NonemptyChronalCones) :
    C.HasChronalNeighbourEverywhere :=
  fun x => Or.inl (h x).1

/-! ## `ChronalNeighbours` gives a chronal neighbour at every point -/

/-- With chronal past neighbours, every point of an open `V` has a chronological past in `V`. -/
theorem ChronalPastNeighbours.Iminus_nonempty_of_mem (h : C.ChronalPastNeighbours) {V : Opens M}
    (hp : p ∈ V) : (C.Iminus V {p}).Nonempty := by
  obtain ⟨q, -, hq⟩ := h V p hp
  exact ⟨q, Precausality.mem_Iminus_singleton.2 hq⟩

/-- With chronal past neighbours, every point has a chronological past in `M`. -/
theorem ChronalPastNeighbours.Iminus_nonempty (h : C.ChronalPastNeighbours) (x : M) :
    (C.Iminus ⊤ {x}).Nonempty :=
  h.Iminus_nonempty_of_mem (V := ⊤) trivial

/-- With chronal future neighbours, every point of an open `V` has a chronological future in `V`
(`ChronalPastNeighbours.Iminus_nonempty_of_mem` for `C.dual`). -/
theorem ChronalFutureNeighbours.Iplus_nonempty_of_mem (h : C.ChronalFutureNeighbours)
    {V : Opens M} (hp : p ∈ V) : (C.Iplus V {p}).Nonempty :=
  ChronalPastNeighbours.Iminus_nonempty_of_mem (C := C.dual) h hp

/-- With chronal future neighbours, every point has a chronological future in `M`. -/
theorem ChronalFutureNeighbours.Iplus_nonempty (h : C.ChronalFutureNeighbours) (x : M) :
    (C.Iplus ⊤ {x}).Nonempty :=
  ChronalPastNeighbours.Iminus_nonempty (C := C.dual) h x

theorem ChronalNeighbours.Iminus_nonempty (h : C.ChronalNeighbours) (x : M) :
    (C.Iminus ⊤ {x}).Nonempty :=
  h.1.Iminus_nonempty x

theorem ChronalNeighbours.Iplus_nonempty (h : C.ChronalNeighbours) (x : M) :
    (C.Iplus ⊤ {x}).Nonempty :=
  ChronalPastNeighbours.Iminus_nonempty (C := C.dual) h.2 x

/-- **Chronal neighbours in every open set give non-empty chronological cones**
(`chronal_neighbours ⇒ nonempty_chronal_cones`): the open `V = M`. -/
theorem ChronalNeighbours.nonemptyChronalCones (h : C.ChronalNeighbours) :
    C.NonemptyChronalCones :=
  fun x => ⟨h.Iplus_nonempty x, h.Iminus_nonempty x⟩

/-- **`ChronalNeighbours` gives `HasChronalNeighbour` at every point**, through its future side
(its past side gives it as well). -/
theorem ChronalNeighbours.hasChronalNeighbour (h : C.ChronalNeighbours) (p : M) :
    C.HasChronalNeighbour p :=
  Or.inl (h.Iplus_nonempty p)

/-- `chronal_neighbours ⇒ has_chronal_neighbour`. -/
theorem ChronalNeighbours.hasChronalNeighbourEverywhere (h : C.ChronalNeighbours) :
    C.HasChronalNeighbourEverywhere :=
  h.hasChronalNeighbour

/-! ## Characterisations of `ChronalNeighbours` -/

/-- **Under absolute minimality on a `T1` space, chronal neighbours in every open set are
non-empty chronological cones at every point**: both sides of
`AbsolutelyMinimal.chronalPastNeighbours_iff` (`Causal.LadderLocal`), the future one through
`C.dual`. Neither hypothesis can be dropped (`globalLine_separates`,
`sierpinskiCausality_separates`). -/
theorem AbsolutelyMinimal.chronalNeighbours_iff [T1Space M] (h : C.AbsolutelyMinimal) :
    C.ChronalNeighbours ↔ ∀ x : M, (C.Iplus ⊤ {x}).Nonempty ∧ (C.Iminus ⊤ {x}).Nonempty := by
  rw [ChronalNeighbours, AbsolutelyMinimal.chronalPastNeighbours_iff h,
    AbsolutelyMinimal.chronalFutureNeighbours_iff h, ← forall_and]
  exact forall_congr' fun _ => And.comm

/-- The same with the name `NonemptyChronalCones`. -/
theorem AbsolutelyMinimal.chronalNeighbours_iff_nonemptyChronalCones [T1Space M]
    (h : C.AbsolutelyMinimal) : C.ChronalNeighbours ↔ C.NonemptyChronalCones :=
  AbsolutelyMinimal.chronalNeighbours_iff h

/-- `absolutely_minimal ∧ nonempty_chronal_cones ⇒ chronal_neighbours`, on a `T1` space. -/
theorem AbsolutelyMinimal.chronalNeighbours_of_nonemptyChronalCones [T1Space M]
    (h : C.AbsolutelyMinimal) (hI : C.NonemptyChronalCones) : C.ChronalNeighbours :=
  (AbsolutelyMinimal.chronalNeighbours_iff h).2 hI

/-- Under absolute minimality on a `T1` space, chronal neighbours in every open set are: every
point strongly tarentin in the future and in the past (`Z^± = M`, `def:strongly_tarentin_point`;
`rem:absolutely_minimal_topological_spacetime`, `AbsolutelyMinimal.mem_Zplus_iff`). -/
theorem AbsolutelyMinimal.chronalNeighbours_iff_Z [T1Space M] (h : C.AbsolutelyMinimal) :
    C.ChronalNeighbours ↔ C.Zplus = univ ∧ C.Zminus = univ := by
  rw [AbsolutelyMinimal.chronalNeighbours_iff h, eq_univ_iff_forall, eq_univ_iff_forall,
    ← forall_and]
  exact forall_congr' fun x => and_congr (AbsolutelyMinimal.mem_Zplus_iff h).symm
    (AbsolutelyMinimal.mem_Zminus_iff h).symm

/-- Under absolute minimality on a `T1` space, a point has a chronal neighbour iff it is strongly
tarentin in the future or in the past: the absolutely minimal counterpart of
`CausallyArcConnected.hasChronalNeighbour_iff` (`Causal.LocateExtension`). -/
theorem AbsolutelyMinimal.hasChronalNeighbour_iff [T1Space M] (h : C.AbsolutelyMinimal) :
    C.HasChronalNeighbour p ↔ p ∈ C.Zplus ∪ C.Zminus := by
  rw [HasChronalNeighbour, mem_union, AbsolutelyMinimal.mem_Zplus_iff h,
    AbsolutelyMinimal.mem_Zminus_iff h]

/-- **Under causal arc-connectedness, with no separation axiom**, chronal past neighbours in every
open set are a non-empty chronological past at every point: a chronal curve from `q ≪ v` has an
initial piece in any open `V ∋ v` (`CausallyArcConnectedOn.Iminus_nonempty_of_le`). -/
theorem CausallyArcConnected.chronalPastNeighbours_iff (hC : C.CausallyArcConnected) :
    C.ChronalPastNeighbours ↔ ∀ x : M, (C.Iminus ⊤ {x}).Nonempty := by
  refine ⟨fun hN x => hN.Iminus_nonempty x, fun hI V v hv => ?_⟩
  obtain ⟨q, hq⟩ := CausallyArcConnectedOn.Iminus_nonempty_of_le hC le_top hv (hI v)
  have hqv : C.lt V q v := Precausality.mem_Iminus_singleton.1 hq
  exact ⟨q, C.lt_mem_left hqv, hqv⟩

/-- **Under causal arc-connectedness, with no separation axiom**, chronal future neighbours in
every open set are a non-empty chronological future at every point
(`CausallyArcConnected.chronalPastNeighbours_iff` for `C.dual`). -/
theorem CausallyArcConnected.chronalFutureNeighbours_iff (hC : C.CausallyArcConnected) :
    C.ChronalFutureNeighbours ↔ ∀ x : M, (C.Iplus ⊤ {x}).Nonempty :=
  CausallyArcConnected.chronalPastNeighbours_iff (C := C.dual) (dual_causallyArcConnectedOn.2 hC)

/-- **Under causal arc-connectedness, with no separation axiom**, `ChronalNeighbours` iff `I⁺(x)`
and `I⁻(x)` are non-empty for every `x`. -/
theorem CausallyArcConnected.chronalNeighbours_iff (hC : C.CausallyArcConnected) :
    C.ChronalNeighbours ↔ ∀ x : M, (C.Iplus ⊤ {x}).Nonempty ∧ (C.Iminus ⊤ {x}).Nonempty := by
  rw [ChronalNeighbours, CausallyArcConnected.chronalPastNeighbours_iff hC,
    CausallyArcConnected.chronalFutureNeighbours_iff hC, ← forall_and]
  exact forall_congr' fun _ => And.comm

/-- `causally_arc_connected ∧ nonempty_chronal_cones ⇒ chronal_neighbours`, no separation. -/
theorem CausallyArcConnected.chronalNeighbours_of_nonemptyChronalCones
    (hC : C.CausallyArcConnected) (hI : C.NonemptyChronalCones) : C.ChronalNeighbours :=
  (CausallyArcConnected.chronalNeighbours_iff hC).2 hI

/-! ## Locating an extension, restated with the named forms -/

/-- **`exists_leaving` with a chronal neighbour at every point** (the named everywhere form of its
hypothesis on `∂O`). -/
theorem exists_leaving_of_hasChronalNeighbourEverywhere [PreconnectedSpace M]
    (hC : C.CausallyArcConnected) (hE : C.HasChronalNeighbourEverywhere) (hO : IsOpen O)
    (hne : O.Nonempty) (hne' : O ≠ univ) :
    ∃ γ : ℝ → M, (C.ChronalCurveOn ⊤ γ 0 1 ∨ C.dual.ChronalCurveOn ⊤ γ 0 1) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O ∧ γ 1 ∈ frontier O :=
  exists_leaving hC hO hne hne' fun p _ => hE p

/-- **Locating an extension with `ChronalNeighbours`**: a proper non-empty open subset `O` of a
connected causally arc-connected spacetime with chronal neighbours; some chronal curve of `M`,
future or past, lies in `O` on `[0, 1)` and ends on `∂O`. Corollary of `exists_leaving`. -/
theorem exists_leaving_of_chronalNeighbours [PreconnectedSpace M] (hC : C.CausallyArcConnected)
    (hN : C.ChronalNeighbours) (hO : IsOpen O) (hne : O.Nonempty) (hne' : O ≠ univ) :
    ∃ γ : ℝ → M, (C.ChronalCurveOn ⊤ γ 0 1 ∨ C.dual.ChronalCurveOn ⊤ γ 0 1) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O ∧ γ 1 ∈ frontier O :=
  exists_leaving hC hO hne hne' fun p _ => hN.hasChronalNeighbour p

/-- `∂⁺O ∪ ∂⁻O ≠ ∅`, with `ChronalNeighbours`. -/
theorem futureBoundary_union_pastBoundary_nonempty_of_chronalNeighbours [PreconnectedSpace M]
    (hC : C.CausallyArcConnected) (hN : C.ChronalNeighbours) (hO : IsOpen O) (hne : O.Nonempty)
    (hne' : O ≠ univ) : (C.futureBoundary O ∪ C.pastBoundary O).Nonempty :=
  futureBoundary_union_pastBoundary_nonempty hC hO hne hne' fun p _ => hN.hasChronalNeighbour p

/-- **Sbierski 1507.00601 Lemma 2.17 in ETT, with `ChronalNeighbours`**: the conclusion of
`exists_leaving_of_isOpenEmbedding`, its boundary hypothesis supplied by chronal neighbours. -/
theorem exists_leaving_of_isOpenEmbedding_of_chronalNeighbours {N : Type v} [TopologicalSpace N]
    [Nonempty N] [PreconnectedSpace M] {ι : N → M} (hι : IsOpenEmbedding ι)
    (hproper : range ι ≠ univ) (hC : C.CausallyArcConnected) (hN : C.ChronalNeighbours) :
    ∃ D : Causality M, (D = C ∨ D = C.dual) ∧ ∃ γ : ℝ → M, D.ChronalCurveOn ⊤ γ 0 1 ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ range ι) ∧ γ 1 ∉ range ι ∧ γ 1 ∈ frontier (range ι) ∧
      ∀ s ∈ Ico (0 : ℝ) 1, D.ChronalCurveOn ⟨range ι, hι.isOpen_range⟩ γ 0 s :=
  exists_leaving_of_isOpenEmbedding hι hproper hC fun p _ => hN.hasChronalNeighbour p

/-- **Density, with `ChronalNeighbours`**: `∂⁺O ∪ ∂⁻O` is dense in `∂O` for every open `O`. -/
theorem frontier_subset_closure_boundary_of_chronalNeighbours (hC : C.CausallyArcConnected)
    (hN : C.ChronalNeighbours) (hO : IsOpen O) :
    frontier O ⊆ closure (C.futureBoundary O ∪ C.pastBoundary O) :=
  frontier_subset_closure_boundary hC hO fun p _ => hN.hasChronalNeighbour p

/-- **Locating an extension from local causal arc-connectedness and chronal past neighbours**:
since the chronology is taken in every open set, a causally arc-connected neighbourhood `W` of a
boundary point contains a chronological past of it, which is what `exists_leaving_of_local` asks.
Neither causal arc-connectedness of `M` nor a future side is used. -/
theorem exists_leaving_of_locallyCausallyArcConnected_of_chronalPastNeighbours
    [PreconnectedSpace M] (hL : C.LocallyCausallyArcConnected) (hP : C.ChronalPastNeighbours)
    (hO : IsOpen O) (hne : O.Nonempty) (hne' : O ≠ univ) :
    ∃ γ : ℝ → M, (C.ChronalCurveOn ⊤ γ 0 1 ∨ C.dual.ChronalCurveOn ⊤ γ 0 1) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O ∧ γ 1 ∈ frontier O := by
  refine exists_leaving_of_local hO hne hne' fun p _ => ?_
  obtain ⟨W, hpW, -, hW⟩ := hL p univ univ_mem
  exact ⟨W, hW, Or.inr (hP.Iminus_nonempty_of_mem hpW)⟩

/-- **Locating an extension from local causal arc-connectedness and `ChronalNeighbours`.** -/
theorem exists_leaving_of_locallyCausallyArcConnected [PreconnectedSpace M]
    (hL : C.LocallyCausallyArcConnected) (hN : C.ChronalNeighbours) (hO : IsOpen O)
    (hne : O.Nonempty) (hne' : O ≠ univ) :
    ∃ γ : ℝ → M, (C.ChronalCurveOn ⊤ γ 0 1 ∨ C.dual.ChronalCurveOn ⊤ γ 0 1) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O ∧ γ 1 ∈ frontier O :=
  exists_leaving_of_locallyCausallyArcConnected_of_chronalPastNeighbours hL hN.1 hO hne hne'

end Causality

/-! ## Witnesses -/

/-! ### The converse fails: the closed half-line -/

/-- Every point of the closed half-line has a chronal neighbour (its future). -/
theorem closedHalfLine_hasChronalNeighbourEverywhere :
    closedHalfLine.HasChronalNeighbourEverywhere :=
  closedHalfLine_hasChronalNeighbour

/-- The endpoint of the closed half-line has an empty chronological past. -/
theorem closedHalfLine_not_nonemptyChronalCones : ¬ closedHalfLine.NonemptyChronalCones :=
  fun h => by
    have h0 := (h ClosedHalfLine.zero).2
    rw [closedHalfLine_Iminus_zero] at h0
    exact not_nonempty_empty h0

theorem closedHalfLine_not_chronalNeighbours : ¬ closedHalfLine.ChronalNeighbours := fun h =>
  closedHalfLine_not_nonemptyChronalCones h.nonemptyChronalCones

/-- **The converse of `ChronalNeighbours.hasChronalNeighbourEverywhere` fails**, on a `T1`,
preconnected, causally arc-connected (hence absolutely minimal) spacetime: the closed half-line, whose
endpoint has a chronological future and no chronological past. So in
`AbsolutelyMinimal.chronalNeighbours_iff` the two-sided cones cannot be one-sided. -/
theorem closedHalfLine_separates_chronalNeighbours :
    T1Space ClosedHalfLine ∧ PreconnectedSpace ClosedHalfLine ∧
      closedHalfLine.CausallyArcConnected ∧ closedHalfLine.AbsolutelyMinimal ∧
      closedHalfLine.HasChronalNeighbourEverywhere ∧ ¬ closedHalfLine.NonemptyChronalCones ∧
      ¬ closedHalfLine.ChronalNeighbours :=
  ⟨inferInstance, Subtype.preconnectedSpace isPreconnected_Ici,
    closedHalfLine_causallyArcConnected, closedHalfLine_causallyArcConnected.absolutelyMinimal,
    closedHalfLine_hasChronalNeighbourEverywhere, closedHalfLine_not_nonemptyChronalCones,
    closedHalfLine_not_chronalNeighbours⟩

/-- **The converse, bare, is false**: a chronal neighbour at every point does not give chronal
neighbours in every open set, even on a `T1` causally arc-connected spacetime. -/
theorem not_chronalNeighbours_of_hasChronalNeighbourEverywhere_bare :
    ¬ ∀ (X : Type) [TopologicalSpace X] [T1Space X] (D : Causality X), D.CausallyArcConnected →
      D.HasChronalNeighbourEverywhere → D.ChronalNeighbours := fun h =>
  closedHalfLine_not_chronalNeighbours (h ClosedHalfLine closedHalfLine
    closedHalfLine_causallyArcConnected closedHalfLine_hasChronalNeighbourEverywhere)

/-! ### Absolute minimality cannot be dropped: chronology in `ℝ` only -/

/-- **The globally chronological line**: on `ℝ`, `x ≪_U y` iff `U = ℝ` and `x < y`; `x ≤_U y` iff
`x = y ∈ U`, or `U = ℝ` and `x < y`. Every point has a chronological future and past in `ℝ`, and
none in a proper open set: the generated causality of the cover by proper opens is the diagonal. -/
def globalLine : Causality ℝ where
  le U x y := (x = y ∧ x ∈ U) ∨ (U = ⊤ ∧ x < y)
  lt U x y := U = ⊤ ∧ x < y
  le_mem_left h := by
    rcases h with ⟨-, h⟩ | ⟨rfl, -⟩
    · exact h
    · trivial
  le_mem_right h := by
    rcases h with ⟨rfl, h⟩ | ⟨rfl, -⟩
    · exact h
    · trivial
  lt_mem_left h := h.1 ▸ trivial
  lt_mem_right h := h.1 ▸ trivial
  le_refl hx := Or.inl ⟨rfl, hx⟩
  le_trans h₁ h₂ := by
    rcases h₁ with ⟨rfl, -⟩ | ⟨hU, h1⟩
    · exact h₂
    rcases h₂ with ⟨rfl, -⟩ | ⟨-, h2⟩
    · exact Or.inr ⟨hU, h1⟩
    · exact Or.inr ⟨hU, h1.trans h2⟩
  lt_trans h₁ h₂ := ⟨h₁.1, h₁.2.trans h₂.2⟩
  le_mono h _ _ h' := by
    rcases h' with ⟨h1, h2⟩ | ⟨rfl, h2⟩
    · exact Or.inl ⟨h1, h h2⟩
    · exact Or.inr ⟨top_le_iff.1 h, h2⟩
  lt_mono h _ _ h' := by
    obtain ⟨rfl, h2⟩ := h'
    exact ⟨top_le_iff.1 h, h2⟩
  le_of_lt h := Or.inr h
  isOpen_lt_right U x := by
    by_cases hU : U = ⊤
    · simp only [hU, true_and]
      exact isOpen_Ioi
    · simp only [hU, false_and, setOf_false]
      exact isOpen_empty
  isOpen_lt_left U y := by
    by_cases hU : U = ⊤
    · simp only [hU, true_and]
      exact isOpen_Iio
    · simp only [hU, false_and, setOf_false]
      exact isOpen_empty

theorem globalLine_nonemptyChronalCones : globalLine.NonemptyChronalCones := fun x =>
  ⟨⟨x + 1, Precausality.mem_Iplus_singleton.2 ⟨rfl, lt_add_one x⟩⟩,
    ⟨x - 1, Precausality.mem_Iminus_singleton.2 ⟨rfl, sub_one_lt x⟩⟩⟩

/-- `0` has no chronological past in the open `(-1, ∞)`. -/
theorem globalLine_not_chronalPastNeighbours : ¬ globalLine.ChronalPastNeighbours := fun h => by
  let V : Opens ℝ := ⟨Ioi (-1), isOpen_Ioi⟩
  obtain ⟨p, -, hp⟩ := h V 0 (show (0 : ℝ) ∈ Ioi (-1) by norm_num)
  have hV : V = ⊤ := hp.1
  have h2 : (-2 : ℝ) ∈ (V : Set ℝ) := by rw [hV]; trivial
  exact absurd (mem_Ioi.1 h2) (by norm_num)

theorem globalLine_not_chronalNeighbours : ¬ globalLine.ChronalNeighbours := fun h =>
  globalLine_not_chronalPastNeighbours h.1

/-- The globally chronological line is not absolutely minimal: by
`AbsolutelyMinimal.chronalNeighbours_of_nonemptyChronalCones` (`ℝ` is `T1`). -/
theorem globalLine_not_absolutelyMinimal : ¬ globalLine.AbsolutelyMinimal := fun h =>
  globalLine_not_chronalNeighbours
    (Causality.AbsolutelyMinimal.chronalNeighbours_of_nonemptyChronalCones h
      globalLine_nonemptyChronalCones)

/-- The globally chronological line has push-up: both relations are those of `<` in `ℝ` itself. -/
theorem globalLine_pushUp : globalLine.PushUp := by
  rw [Causality.pushUp_iff]
  intro U x y z
  refine ⟨fun hxy hyz => ?_, fun hxy hyz => ?_⟩
  · rcases hyz with ⟨rfl, -⟩ | ⟨-, hyz⟩
    · exact hxy
    · exact ⟨hxy.1, hxy.2.trans hyz⟩
  · rcases hxy with ⟨rfl, -⟩ | ⟨-, hxy⟩
    · exact hyz
    · exact ⟨hyz.1, hxy.trans hyz.2⟩

/-- The globally chronological line is causal: `≤_ℝ` is the order of `ℝ`. -/
theorem globalLine_isCausal : globalLine.IsCausal := by
  intro x y hxy hyx
  rcases hxy with ⟨rfl, -⟩ | ⟨-, hxy⟩
  · rfl
  rcases hyx with ⟨rfl, -⟩ | ⟨-, hyx⟩
  · rfl
  · exact absurd (hxy.trans hyx) (lt_irrefl _)

/-- The globally chronological line is causally open: `J^±_U(V)` is `V` when `U ≠ ℝ`, and
`V ∪ I^±(V)` when `U = ℝ`. -/
theorem globalLine_causallyOpen : globalLine.CausallyOpen := by
  refine ⟨fun U V hVU => ?_, fun U V hVU => ?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, hxy⟩
    rcases hxy with ⟨rfl, -⟩ | ⟨hU, hxy⟩
    · exact Filter.mem_of_superset (V.isOpen.mem_nhds hx)
        fun z hz => ⟨z, hz, Or.inl ⟨rfl, hVU hz⟩⟩
    · exact Filter.mem_of_superset (isOpen_Ioi.mem_nhds hxy)
        fun z hz => ⟨x, hx, Or.inr ⟨hU, hz⟩⟩
  · rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, hyx⟩
    rcases hyx with ⟨rfl, -⟩ | ⟨hU, hyx⟩
    · exact Filter.mem_of_superset (V.isOpen.mem_nhds hx)
        fun z hz => ⟨z, hz, Or.inl ⟨rfl, hVU hz⟩⟩
    · exact Filter.mem_of_superset (isOpen_Iio.mem_nhds hyx)
        fun z hz => ⟨x, hx, Or.inr ⟨hU, hz⟩⟩

/-- **Absolute minimality cannot be dropped** from `AbsolutelyMinimal.chronalNeighbours_iff`, nor
from `AbsolutelyMinimal.chronalPastNeighbours_iff`: on `ℝ` (Hausdorff, second countable), a causal,
causally open causality with push-up and non-empty chronological cones, without chronal (past)
neighbours, hence not absolutely minimal. -/
theorem globalLine_separates :
    globalLine.NonemptyChronalCones ∧ globalLine.PushUp ∧ globalLine.CausallyOpen ∧
      globalLine.IsCausal ∧ ¬ globalLine.ChronalPastNeighbours ∧
      ¬ globalLine.ChronalNeighbours ∧ ¬ globalLine.AbsolutelyMinimal :=
  ⟨globalLine_nonemptyChronalCones, globalLine_pushUp, globalLine_causallyOpen,
    globalLine_isCausal, globalLine_not_chronalPastNeighbours, globalLine_not_chronalNeighbours,
    globalLine_not_absolutelyMinimal⟩

/-- The bare form: on a `T1` space, non-empty chronological cones do not give chronal neighbours. -/
theorem not_chronalNeighbours_of_t1_bare :
    ¬ ∀ (X : Type) [TopologicalSpace X] [T1Space X] (D : Causality X),
      D.NonemptyChronalCones → D.ChronalNeighbours := fun h =>
  globalLine_not_chronalNeighbours (h ℝ globalLine globalLine_nonemptyChronalCones)

/-! ### `T1` cannot be dropped: the Sierpiński space -/

/-- **A causality on the Sierpiński space** `Prop` (`{True}` open): `x ≪_U y` iff `U = ⊤`, and
`x ≤_U y` iff `x = y ∈ U` or `U = ⊤`. Every open containing `False` is `⊤`, so every cover
contains `⊤` and the causality is absolutely minimal; the open `{True}` has no chronology. -/
def sierpinskiCausality : Causality Prop where
  le U x y := (x = y ∧ x ∈ U) ∨ U = ⊤
  lt U _ _ := U = ⊤
  le_mem_left h := by
    rcases h with ⟨-, h⟩ | rfl
    · exact h
    · trivial
  le_mem_right h := by
    rcases h with ⟨rfl, h⟩ | rfl
    · exact h
    · trivial
  lt_mem_left h := h ▸ trivial
  lt_mem_right h := h ▸ trivial
  le_refl hx := Or.inl ⟨rfl, hx⟩
  le_trans h₁ h₂ := by
    rcases h₁ with ⟨rfl, -⟩ | hU
    · exact h₂
    · exact Or.inr hU
  lt_trans h₁ _ := h₁
  le_mono h _ _ h' := by
    rcases h' with ⟨h1, h2⟩ | rfl
    · exact Or.inl ⟨h1, h h2⟩
    · exact Or.inr (top_le_iff.1 h)
  lt_mono h _ _ h' := by
    subst h'
    exact top_le_iff.1 h
  le_of_lt h := Or.inr h
  isOpen_lt_right U _ := isOpen_const
  isOpen_lt_left U _ := isOpen_const

/-- Every causality of the Sierpiński space is absolutely minimal; this one in particular: the only
open containing `False` is `⊤` (`nhds_false`), so every cover contains `⊤`. -/
theorem sierpinskiCausality_absolutelyMinimal : sierpinskiCausality.AbsolutelyMinimal := by
  refine Precausality.absolutelyMinimal_iff.2 fun S hS V _ x y => ?_
  obtain ⟨O, hOS, hFO⟩ := hS False trivial
  have hO : O = ⊤ := by
    have hmem : (O : Set Prop) ∈ 𝓝 False := O.isOpen.mem_nhds hFO
    rw [nhds_false, Filter.mem_top] at hmem
    exact SetLike.coe_injective hmem
  subst hO
  refine ⟨fun h => Relation.TransGen.single ⟨⊤, hOS, ?_⟩,
    fun h => Relation.TransGen.single ⟨⊤, hOS, ?_⟩⟩
  · rw [inf_top_eq]; exact h
  · rw [inf_top_eq]; exact h

theorem sierpinskiCausality_nonemptyChronalCones :
    sierpinskiCausality.NonemptyChronalCones := fun x =>
  ⟨⟨x, Precausality.mem_Iplus_singleton.2 rfl⟩, ⟨x, Precausality.mem_Iminus_singleton.2 rfl⟩⟩

/-- `True` has no chronological past in the open `{True}`. -/
theorem sierpinskiCausality_not_chronalPastNeighbours :
    ¬ sierpinskiCausality.ChronalPastNeighbours := fun h => by
  let V : Opens Prop := ⟨{True}, isOpen_singleton_true⟩
  obtain ⟨p, -, hp⟩ := h V True (mem_singleton True)
  have hV : V = ⊤ := hp
  have hF : False ∈ (V : Set Prop) := by rw [hV]; trivial
  exact (mem_singleton_iff.1 hF).mpr trivial

theorem sierpinskiCausality_not_chronalNeighbours :
    ¬ sierpinskiCausality.ChronalNeighbours := fun h =>
  sierpinskiCausality_not_chronalPastNeighbours h.1

/-- **`T1` cannot be dropped** from `AbsolutelyMinimal.chronalNeighbours_iff`, nor from
`AbsolutelyMinimal.chronalPastNeighbours_iff`: an absolutely minimal causality of the Sierpiński
space with non-empty chronological cones and without chronal (past) neighbours. That `Prop` is
not `T1` follows from the theorem. -/
theorem sierpinskiCausality_separates :
    sierpinskiCausality.AbsolutelyMinimal ∧ sierpinskiCausality.NonemptyChronalCones ∧
      ¬ sierpinskiCausality.ChronalPastNeighbours ∧ ¬ sierpinskiCausality.ChronalNeighbours ∧
      ¬ T1Space Prop :=
  ⟨sierpinskiCausality_absolutelyMinimal, sierpinskiCausality_nonemptyChronalCones,
    sierpinskiCausality_not_chronalPastNeighbours, sierpinskiCausality_not_chronalNeighbours,
    fun hT => by
      haveI := hT
      exact sierpinskiCausality_not_chronalNeighbours
        (Causality.AbsolutelyMinimal.chronalNeighbours_of_nonemptyChronalCones
          sierpinskiCausality_absolutelyMinimal sierpinskiCausality_nonemptyChronalCones)⟩

/-- The bare form of the strict lemma without `T1`: absolute minimality and a non-empty
chronological past at every point do not give chronal past neighbours. -/
theorem not_chronalPastNeighbours_of_absolutelyMinimal_bare :
    ¬ ∀ (X : Type) [TopologicalSpace X] (D : Causality X), D.AbsolutelyMinimal →
      (∀ x : X, (D.Iminus ⊤ {x}).Nonempty) → D.ChronalPastNeighbours := fun h =>
  sierpinskiCausality_not_chronalPastNeighbours (h Prop sierpinskiCausality
    sierpinskiCausality_absolutelyMinimal fun x => (sierpinskiCausality_nonemptyChronalCones x).2)

/-- The bare form without `T1`: absolute minimality and non-empty chronological cones do not give
chronal neighbours. -/
theorem not_chronalNeighbours_of_absolutelyMinimal_bare :
    ¬ ∀ (X : Type) [TopologicalSpace X] (D : Causality X), D.AbsolutelyMinimal →
      D.NonemptyChronalCones → D.ChronalNeighbours := fun h =>
  sierpinskiCausality_not_chronalNeighbours (h Prop sierpinskiCausality
    sierpinskiCausality_absolutelyMinimal sierpinskiCausality_nonemptyChronalCones)

/-! ### Ladder witnesses for the two names -/

/-- The timelike line has non-empty chronological cones. -/
theorem timelikeLine_nonemptyChronalCones : timelikeLine.NonemptyChronalCones :=
  timelikeLine_chronalNeighbours.nonemptyChronalCones

/-- **No chronal neighbour anywhere on the lightlike line** (its chronology is empty), though it
has push-up, causal openness, global hyperbolicity, no causal endpoint, causal arc-connectedness and
is tarentin. -/
theorem lightlikeLine_separates_hasChronalNeighbour :
    lightlikeLine.PushUp ∧ lightlikeLine.CausallyOpen ∧ lightlikeLine.GloballyHyperbolic ∧
      lightlikeLine.NoCausalEndpoint ∧ lightlikeLine.CausallyArcConnected ∧
      lightlikeLine.Tarentin ∧ ¬ lightlikeLine.HasChronalNeighbourEverywhere :=
  ⟨lightlikeLine_pushUp, lightlikeLine_causallyOpen, lightlikeLine_globallyHyperbolic,
    lightlikeLine_noCausalEndpoint, lightlikeLine_causallyArcConnected,
    (timelikeLine_tarentin : lightlikeLine.Tarentin), fun h => by
      rcases h 0 with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact Precausality.mem_Iplus_singleton.1 hy
      · exact Precausality.mem_Iminus_singleton.1 hy⟩

/-- **A causally arc-connected, causally open, causally plain line without chronal neighbours**:
the line with a chronologically isolated origin (`isolatedLine`, `Causal.LocateExtension`). -/
theorem isolatedLine_separates_chronalNeighbours :
    isolatedLine.CausallyArcConnected ∧ isolatedLine.CausallyOpen ∧ isolatedLine.CausallyPlain ∧
      ¬ isolatedLine.HasChronalNeighbourEverywhere ∧ ¬ isolatedLine.ChronalNeighbours :=
  ⟨isolatedLine_causallyArcConnected, isolatedLine_causallyOpen, isolatedLine_causallyPlain,
    fun h => isolatedLine_not_hasChronalNeighbour_zero (h 0),
    fun h => isolatedLine_not_hasChronalNeighbour_zero (h.hasChronalNeighbour 0)⟩

end Causal
