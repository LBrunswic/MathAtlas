import Causal.SingularFlat
import Causal.ChronalNeighbourBridge
import Causal.Port.E0SingularFlat
import Causal.Port.SFAManifolds

/-!
# `E₀` and every `E_{≥0}`-manifold have a chronal neighbour at every point, BTZ points included

Programme target `T-loc-e0-has-chronal-neighbour` (`programme/roadmap.toml`; layer 3,
localisation, model `E_0`, provides `has_chronal_neighbour`; DEC-159, OQ-51). No label is marked:
the ladder property is the definition `Causality.HasChronalNeighbourEverywhere`
(`Causal.ChronalNeighbourBridge`, ladder `has_chronal_neighbour`), and every statement here is an
instance of it or says which of its two disjuncts holds. Cited, unmarked: `rem:btz_pas_tarentin`
— `ETT.tex:1358`, the source of the field `SingularFlatAxioms.mem_Zplus`, and `defi:causal_E0` —
`ETT.tex:1344`, whose `I⁻(p) = ∅` (l.1347) makes the property one-sided at BTZ points.

> Every point of a $\mass{\geq 0}$-manifold is strongly tarentin in the future, and the points
> which fail to be strongly tarentin in the past are exactly the BTZ points: this is immediate
> from Definitions \ref{defi:causal_Ealpha} and \ref{defi:causal_E0} read in a chart.
> (`rem:btz_pas_tarentin`, `ETT.tex:1358–1361`)

> $$I^-(p)=\emptyset \qquad\text{and}\qquad J^-(p)=\{\r=0,~\tau\leq \tau(p)\},$$
> (`defi:causal_E0`, `ETT.tex:1347`)

## What is here

* **Every causality with `SingularFlatAxioms`**:
  `Causality.SingularFlatAxioms.hasChronalNeighbourEverywhere`, the left disjunct
  (`I⁺(p) ≠ ∅`, `SingularFlatAxioms.Iplus_nonempty`) at every point, from the field `mem_Zplus`
  with `U = M`. The right disjunct holds exactly off the BTZ points
  (`SingularFlatAxioms.Iminus_nonempty_iff`: `I⁻(p) ≠ ∅ ↔ p ∉ sing₀`), so with a BTZ point
  the past side and the two-sided notions fail: `not_nonemptyChronalCones`,
  `not_chronalPastNeighbours` (the past side), `not_chronalNeighbours`. On a connected one (`SingularFlatSpacetime`) `exists_leaving` applies
  unchanged: `SingularFlatSpacetime.exists_leaving`.
* **The model `E₀`** (`Causal.E0.causality`, from `E0.singularFlatAxioms`):
  `E0.hasChronalNeighbourEverywhere`, `E0.Iminus_nonempty_iff` (`I⁻(p) ≠ ∅ ↔ p ∉ axis`), the
  future side in every open set (`E0.chronalFutureNeighbours`, from `E0LM.e0_locZplus`) and not
  the past side (`E0.not_chronalPastNeighbours`), `E0.not_nonemptyChronalCones`,
  `E0.not_chronalNeighbours`; bundled with E₀'s other ladder properties in
  `E0.separates_chronalNeighbours`; the witness `E0.exists_leaving`, a one-line application of
  `Causality.exists_leaving_of_hasChronalNeighbourEverywhere`.
* **Every `E_{≥0}`-manifold** (DEC-25): `SFALocal.hasChronalNeighbourEverywhere` for every
  causality with an isomorphic chart at each point over the family (`IsoChartsCoverDEC25`), with no
  absolute minimality, separation or countability; the natural causality
  (`…_of_isAtlasCausalityDEC25`); `SFALocal.chronalFutureNeighbours`; with absolute minimality the
  sides (`SFALocal.Iminus_nonempty_iff`, `not_nonemptyChronalCones`, `not_chronalPastNeighbours`,
  `not_chronalNeighbours`) and `SFALocal.exists_leaving`. **`E₀`-manifolds** with their natural
  causality: `SFALocalE0.hasChronalNeighbourEverywhere`, `chronalFutureNeighbours`,
  `Iminus_nonempty_iff`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| target: `E₀` (`E0.singularFlatAxioms`) | ✓ carried, no instance argument |
| target: every `E_{≥0}`-manifold the `SingularFlatAxioms` instances cover (`SFAManifolds.singularFlatAxioms`: T2, second countable, absolutely minimal, `IsoChartsCoverDEC25`; `SFALine.singularFlatAxioms_e0`) | ⚠ weakened: `IsoChartsCoverDEC25` alone (`SFALocal.mem_Zplus` is a chart fact); the instances' route is checked at the end |
| the sides at BTZ points (`I⁻(p) = ∅`) at a manifold | ✓ carried: absolute minimality, `I⁻(p) = ∅` is not a chart fact (kb/0135) |
| `exists_leaving`: preconnected, causally arc-connected | ✓ carried (`E₀` connected; `SingularFlatSpacetime.connected`; `[PreconnectedSpace M]`) |

## SCOPE (disclosed)

* **Which side.** The node is two-sided-or; at every point the **future** disjunct holds. The past
  disjunct fails exactly at the BTZ points (`I⁻(p) = ∅`, `defi:causal_E0`), so `E₀` and every
  `E_{≥0}`-manifold with a BTZ point (its causality absolutely minimal, as the natural one is) have
  neither non-empty chronal cones nor chronal past neighbours nor chronal neighbours:
  `E₀` separates `has_chronal_neighbour` from `chronal_neighbours` in a model with push-up, global
  hyperbolicity, tarentin and causal plainness, beside the model-free closed half-line.
* **Inline step.** `Z⁺(M) = M ⇒` a chronal neighbour everywhere is model-free and one line
  (`Causality.Iplus_nonempty_of_mem_Zplus`); it is written inline in each proof, not as a lemma
  here (kb/0047). Likewise `LocZplus ⇒ ChronalFutureNeighbours` (`N = V` in the definition).
* **No new mathematics**: every input was in Lean (`mem_Zplus`, `Iminus_eq_empty`,
  `mem_Zminus_iff`, `E0LM.e0_locZplus`, `SFALocal.mem_Zplus`, `SFALocal.locZplus`). The readings of
  `E₀` (OQ-34, OQ-35) and of `E_{≥0}`-manifolds (DEC-25, OQ-18) are those of the modules imported.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology

universe u

/-! ### Every causality with `SingularFlatAxioms` -/

namespace Causality

variable {M : Type u} [TopologicalSpace M] {C : Causality M} {sing : ℝ → Set M}

/-- **The future side at every point**: under `SingularFlatAxioms` every point has a non-empty
chronological future in `M` (`rem:btz_pas_tarentin`, the field `mem_Zplus` read with `U = M`). -/
theorem SingularFlatAxioms.Iplus_nonempty (h : C.SingularFlatAxioms sing) (p : M) :
    (C.Iplus ⊤ {p}).Nonempty :=
  Iplus_nonempty_of_mem_Zplus (h.mem_Zplus p)

/-- **The past side exactly off the BTZ points**: under `SingularFlatAxioms`, `I⁻(p) ≠ ∅` iff `p`
is not a BTZ point (`I⁻(p) = ∅` on `sing₀`, `defi:causal_E0`; `Z⁻` off `sing₀`,
`rem:btz_pas_tarentin`). -/
theorem SingularFlatAxioms.Iminus_nonempty_iff (h : C.SingularFlatAxioms sing) (p : M) :
    (C.Iminus ⊤ {p}).Nonempty ↔ p ∉ sing 0 :=
  ⟨fun hI hp => hI.ne_empty (h.Iminus_eq_empty p hp),
    fun hp => Iminus_nonempty_of_mem_Zminus ((h.mem_Zminus_iff p).2 hp)⟩

/-- **`has_chronal_neighbour` for every causality with `SingularFlatAxioms`**, BTZ points
included: every point has a chronal neighbour in `M`, on the future side
(`HasChronalNeighbour`'s left disjunct). -/
theorem SingularFlatAxioms.hasChronalNeighbourEverywhere (h : C.SingularFlatAxioms sing) :
    C.HasChronalNeighbourEverywhere :=
  fun p => Or.inl (h.Iplus_nonempty p)

/-- With a BTZ point, the chronological cones are not all non-empty: the property is one-sided. -/
theorem SingularFlatAxioms.not_nonemptyChronalCones (h : C.SingularFlatAxioms sing)
    (hne : (sing 0).Nonempty) : ¬ C.NonemptyChronalCones := by
  obtain ⟨p, hp⟩ := hne
  exact fun hI => (hI p).2.ne_empty (h.Iminus_eq_empty p hp)

/-- With a BTZ point there are no chronal past neighbours: a BTZ point has no chronological past
in `M`, hence none in any open set. -/
theorem SingularFlatAxioms.not_chronalPastNeighbours (h : C.SingularFlatAxioms sing)
    (hne : (sing 0).Nonempty) : ¬ C.ChronalPastNeighbours := by
  obtain ⟨p, hp⟩ := hne
  exact fun hP => (hP.Iminus_nonempty p).ne_empty (h.Iminus_eq_empty p hp)

/-- With a BTZ point there are no chronal neighbours (ladder `chronal_neighbours`). -/
theorem SingularFlatAxioms.not_chronalNeighbours (h : C.SingularFlatAxioms sing)
    (hne : (sing 0).Nonempty) : ¬ C.ChronalNeighbours :=
  fun hN => h.not_chronalPastNeighbours hne hN.1

/-- **Locating an extension in a singular flat spacetime** (`def:singular_spacetime`'s
abstraction, connected): `exists_leaving_of_hasChronalNeighbourEverywhere` applies as stated. -/
theorem SingularFlatSpacetime.exists_leaving (h : C.SingularFlatSpacetime sing) {O : Set M}
    (hO : IsOpen O) (hne : O.Nonempty) (hne' : O ≠ univ) :
    ∃ γ : ℝ → M, (C.ChronalCurveOn ⊤ γ 0 1 ∨ C.dual.ChronalCurveOn ⊤ γ 0 1) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O ∧ γ 1 ∈ frontier O :=
  haveI := h.connected
  exists_leaving_of_hasChronalNeighbourEverywhere h.causallyArcConnected
    h.hasChronalNeighbourEverywhere hO hne hne'

end Causality

/-! ### The model `E₀` -/

namespace E0

/-- **`E₀` has a chronal neighbour at every point** (ladder `has_chronal_neighbour`), BTZ points
included: the future side, from `E0.singularFlatAxioms`. -/
theorem hasChronalNeighbourEverywhere : causality.HasChronalNeighbourEverywhere :=
  singularFlatAxioms.hasChronalNeighbourEverywhere

/-- In `E₀` a point has a chronological past iff it is off the axis (the BTZ line). -/
theorem Iminus_nonempty_iff (p : E0) : (causality.Iminus ⊤ {p}).Nonempty ↔ p ∉ axis := by
  rw [← singE0_zero]
  exact singularFlatAxioms.Iminus_nonempty_iff p

/-- **The future side in every open set**: every point `v` of every open `V ⊆ E₀` has a point
`p ∈ V` with `v ≪_V p` (`Z⁺` in every open set, `E0LM.e0_locZplus`, read with `N = V`). -/
theorem chronalFutureNeighbours : causality.ChronalFutureNeighbours :=
  fun V v hv => E0LM.e0_locZplus V v hv V (V.isOpen.mem_nhds hv)

/-- `E₀` does not have non-empty chronological cones: `I⁻ = ∅` on the axis. -/
theorem not_nonemptyChronalCones : ¬ causality.NonemptyChronalCones :=
  singularFlatAxioms.not_nonemptyChronalCones singE0_zero_nonempty

/-- `E₀` has no chronal past neighbours. -/
theorem not_chronalPastNeighbours : ¬ causality.ChronalPastNeighbours :=
  singularFlatAxioms.not_chronalPastNeighbours singE0_zero_nonempty

/-- `E₀` has no chronal neighbours (ladder `chronal_neighbours`). -/
theorem not_chronalNeighbours : ¬ causality.ChronalNeighbours :=
  singularFlatAxioms.not_chronalNeighbours singE0_zero_nonempty

/-- **`E₀` separates `has_chronal_neighbour` from `chronal_neighbours`**: a Hausdorff, second
countable, connected model, causally arc-connected, absolutely minimal, causal, push-up, tarentin,
causally plain, globally hyperbolic, strongly causal (both forms), with curves extending, with a
chronal neighbour at every point and chronal future neighbours, and without non-empty chronological
cones, chronal past neighbours or chronal neighbours. -/
theorem separates_chronalNeighbours :
    T2Space E0 ∧ SecondCountableTopology E0 ∧ ConnectedSpace E0 ∧
      causality.CausallyArcConnected ∧ causality.AbsolutelyMinimal ∧ causality.IsCausal ∧
      causality.PushUp ∧ causality.Tarentin ∧ causality.CausallyPlain ∧
      causality.GloballyHyperbolic ∧ causality.StronglyCausal ∧ causality.StronglyCausalOpen ∧
      causality.CurvesExtend ∧ causality.HasChronalNeighbourEverywhere ∧
      causality.ChronalFutureNeighbours ∧ ¬ causality.NonemptyChronalCones ∧
      ¬ causality.ChronalPastNeighbours ∧ ¬ causality.ChronalNeighbours :=
  ⟨inferInstance, inferInstance, inferInstance, causallyArcConnected,
    causallyArcConnected.absolutelyMinimal, isCausal, E0LM.e0_pushUp, tarentin, causallyPlain,
    globallyHyperbolic, stronglyCausal, ModelRowsE0.e0_stronglyCausalOpen, curvesExtend,
    hasChronalNeighbourEverywhere, chronalFutureNeighbours, not_nonemptyChronalCones,
    not_chronalPastNeighbours, not_chronalNeighbours⟩

/-- **Locating an extension in `E₀`** (the layer-3 witness): a proper non-empty open subset of
`E₀` is left by a chronal curve of `E₀`, future or past, ending on its frontier —
`Causality.exists_leaving_of_hasChronalNeighbourEverywhere` applied to `E₀` as stated. -/
theorem exists_leaving {O : Set E0} (hO : IsOpen O) (hne : O.Nonempty) (hne' : O ≠ univ) :
    ∃ γ : ℝ → E0, (causality.ChronalCurveOn ⊤ γ 0 1 ∨ causality.dual.ChronalCurveOn ⊤ γ 0 1) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O ∧ γ 1 ∈ frontier O :=
  Causality.exists_leaving_of_hasChronalNeighbourEverywhere causallyArcConnected
    hasChronalNeighbourEverywhere hO hne hne'

end E0

/-! ### Every `E_{≥0}`-manifold (DEC-25) -/

namespace SFALocal

open SFATransfer MassAModelsInstance

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-- **Every `E_{≥0}`-manifold has a chronal neighbour at every point** (ladder
`has_chronal_neighbour`), BTZ points included, for every causality with an isomorphic chart at
each point over the family: a chart fact (`SFALocal.mem_Zplus`), so no absolute minimality,
separation or countability is asked. -/
theorem hasChronalNeighbourEverywhere
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.HasChronalNeighbourEverywhere :=
  fun p => Or.inl (Causality.Iplus_nonempty_of_mem_Zplus (mem_Zplus hC p))

/-- The same for the natural causality of an `E_{≥0}`-manifold (`IsAtlasCausalityDEC25`). -/
theorem hasChronalNeighbourEverywhere_of_isAtlasCausalityDEC25 (hcov : MassACovered M)
    (hC : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.HasChronalNeighbourEverywhere :=
  hasChronalNeighbourEverywhere (of_isAtlasCausalityDEC25 hcov hC).2

/-- **The future side in every open set** at every `E_{≥0}`-manifold (`SFALocal.locZplus`, read
with `N = V`), for every causality with an isomorphic chart at each point. -/
theorem chronalFutureNeighbours
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.ChronalFutureNeighbours :=
  fun V v hv => locZplus hC V v hv V (V.isOpen.mem_nhds hv)

/-- At an `E_{≥0}`-manifold with an absolutely minimal causality, a point has a chronological past
iff it is not a BTZ point. -/
theorem Iminus_nonempty_iff (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) (p : M) :
    (C.Iminus ⊤ {p}).Nonempty ↔ p ∉ sing M 0 :=
  ⟨fun hI hp => hI.ne_empty (Iminus_eq_empty hmin hC p hp),
    fun hp => Causality.Iminus_nonempty_of_mem_Zminus ((mem_Zminus_iff hmin hC p).2 hp)⟩

/-- With a BTZ point, an `E_{≥0}`-manifold (absolutely minimal causality) does not have non-empty
chronological cones. -/
theorem not_nonemptyChronalCones (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hne : (sing M 0).Nonempty) : ¬ C.NonemptyChronalCones := by
  obtain ⟨p, hp⟩ := hne
  exact fun hI => (hI p).2.ne_empty (Iminus_eq_empty hmin hC p hp)

/-- With a BTZ point, an `E_{≥0}`-manifold (absolutely minimal causality) has no chronal past
neighbours. -/
theorem not_chronalPastNeighbours (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hne : (sing M 0).Nonempty) : ¬ C.ChronalPastNeighbours := by
  obtain ⟨p, hp⟩ := hne
  exact fun hP => (hP.Iminus_nonempty p).ne_empty (Iminus_eq_empty hmin hC p hp)

/-- With a BTZ point, an `E_{≥0}`-manifold (absolutely minimal causality) has no chronal
neighbours (ladder `chronal_neighbours`). -/
theorem not_chronalNeighbours (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality)
    (hne : (sing M 0).Nonempty) : ¬ C.ChronalNeighbours :=
  fun hN => not_chronalPastNeighbours hmin hC hne hN.1

/-- **Locating an extension in a connected `E_{≥0}`-manifold**:
`Causality.exists_leaving_of_hasChronalNeighbourEverywhere` with `SFALocal.causallyArcConnected`
and `hasChronalNeighbourEverywhere`. -/
theorem exists_leaving [PreconnectedSpace M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) {O : Set M}
    (hO : IsOpen O) (hne : O.Nonempty) (hne' : O ≠ univ) :
    ∃ γ : ℝ → M, (C.ChronalCurveOn ⊤ γ 0 1 ∨ C.dual.ChronalCurveOn ⊤ γ 0 1) ∧
      (∀ t ∈ Ico (0 : ℝ) 1, γ t ∈ O) ∧ γ 1 ∉ O ∧ γ 1 ∈ frontier O :=
  Causality.exists_leaving_of_hasChronalNeighbourEverywhere (causallyArcConnected hmin hC)
    (hasChronalNeighbourEverywhere hC) hO hne hne'

end SFALocal

/-! ### Every `E₀`-manifold with its natural causality -/

namespace SFALocalE0

attribute [local instance] E0GX.singularGX

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

/-- **Every `E₀`-manifold with its natural causality has a chronal neighbour at every point**
(`SFALocalE0.mem_Zplus`). -/
theorem hasChronalNeighbourEverywhere (hcov : E0Covered M) (hC : IsE0Natural C) :
    C.HasChronalNeighbourEverywhere :=
  fun p => Or.inl (Causality.Iplus_nonempty_of_mem_Zplus (mem_Zplus hcov hC p))

/-- Chronal future neighbours at every `E₀`-manifold with its natural causality
(`SFALocalE0.locZplus`). -/
theorem chronalFutureNeighbours (hcov : E0Covered M) (hC : IsE0Natural C) :
    C.ChronalFutureNeighbours :=
  fun V v hv => locZplus hcov hC V v hv V (V.isOpen.mem_nhds hv)

/-- At an `E₀`-manifold with its natural causality, a point has a chronological past iff it is not
a BTZ point. -/
theorem Iminus_nonempty_iff (hcov : E0Covered M) (hC : IsE0Natural C) (p : M) :
    (C.Iminus ⊤ {p}).Nonempty ↔ p ∉ sing M 0 :=
  ⟨fun hI hp => hI.ne_empty (Iminus_eq_empty hcov hC p hp),
    fun hp => Causality.Iminus_nonempty_of_mem_Zminus ((mem_Zminus_iff hcov hC p).2 hp)⟩

end SFALocalE0

/-! ### Checks

The general form applies to each `SingularFlatAxioms` instance of the library as stated, and the
manifold forms are not vacuous: `E₀` itself over the family (`SFALocal.nonvacuous_e0`, a BTZ line)
and `E_π` (`SFALocal.nonvacuous_epi`, no BTZ point). The node is invariant under time reversal
(`Causality.dual_hasChronalNeighbourEverywhere`), so `E₀`'s reversal has it too, on the past
side. -/

section Checks

variable {M : Type u} [TopologicalSpace M] [SingularGXStructure (Flat.isom 2) (Minkowski 2) M]
  {C : Causality M}

example [T2Space M] [SecondCountableTopology M] (hmin : C.AbsolutelyMinimal)
    (hC : IsoChartsCoverDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.HasChronalNeighbourEverywhere :=
  (SFAManifolds.singularFlatAxioms hmin hC).hasChronalNeighbourEverywhere

example [T2Space M] [SecondCountableTopology M] (hcov : SFALocal.MassACovered M)
    (hC : IsAtlasCausalityDEC25 (Flat.isom 2) C (minkowski 2) massAModelCausality) :
    C.HasChronalNeighbourEverywhere :=
  (SFAManifolds.singularFlatAxioms_of_isAtlasCausalityDEC25 hcov hC).hasChronalNeighbourEverywhere

example : E0.causality.dual.HasChronalNeighbourEverywhere :=
  Causality.dual_hasChronalNeighbourEverywhere.2 E0.hasChronalNeighbourEverywhere

section E0Instance

attribute [local instance] E0GX.singularGX

example [T2Space M] [SecondCountableTopology M] (hcov : SFALocalE0.E0Covered M)
    (hC : SFALocalE0.IsE0Natural C) : C.HasChronalNeighbourEverywhere :=
  (SFALine.singularFlatAxioms_e0 hcov hC).hasChronalNeighbourEverywhere

example : E0.causality.HasChronalNeighbourEverywhere :=
  SFALocalE0.e0_singularFlatAxioms.hasChronalNeighbourEverywhere

example : E0.causality.HasChronalNeighbourEverywhere ∧ ¬ E0.causality.ChronalNeighbours :=
  ⟨SFALocal.hasChronalNeighbourEverywhere SFALocal.nonvacuous_e0.2.1,
    SFALocal.not_chronalNeighbours SFALocal.nonvacuous_e0.1 SFALocal.nonvacuous_e0.2.1
      SFALocal.nonvacuous_e0.2.2.2⟩

example : E0.causality.HasChronalNeighbourEverywhere ∧ E0.causality.ChronalFutureNeighbours :=
  ⟨SFALocalE0.hasChronalNeighbourEverywhere SFALocalE0.nonvacuous.1 SFALocalE0.nonvacuous.2.1,
    SFALocalE0.chronalFutureNeighbours SFALocalE0.nonvacuous.1 SFALocalE0.nonvacuous.2.1⟩

end E0Instance

section EPiInstance

attribute [local instance] EAlphaGX.singularGX EAlphaGX.fact_pi_pos

example : (massive Real.pi).HasChronalNeighbourEverywhere ∧
    (massive Real.pi).ChronalFutureNeighbours :=
  ⟨SFALocal.hasChronalNeighbourEverywhere SFALocal.nonvacuous_epi.2.1,
    SFALocal.chronalFutureNeighbours SFALocal.nonvacuous_epi.2.1⟩

end EPiInstance

end Checks

end Causal
