import Causal.LemmaKSCLocal
import Causal.LadderLocal

/-!
# Lemma K in ETT's setting — a compact connected locally Cauchy set of a causally open, second countable globally hyperbolic spacetime is a Cauchy surface

No label is marked. Lemma K is DEC-44's abstraction of a sentence Barbot asserts and never proves
(Rem 2.3 `clomax`, `GHFspace.tex:572`; §11, l.3537–3539 of the labelled file
`papers/barbot/legacy/labeled/GHFspace.tex`); it carries no paper label. DEC-93 states it in
ETT's setting — causal openness (`CausallyOpen`, `def:causally_open_spacetime_open`, two-sided per
DEC-8) and second countability (`def:category_topological_spacetimes`, `ETT.tex:255`) are part of
the spacetime — and this module is **the lemma of record**:
`Causality.isCauchySurface_of_isLocallyCauchy_of_causallyOpen`.

> A fundamental observation is that in a GH spacetime, every
> closed spacelike hypersurface is necessarely a Cauchy surface,
> hence, every GH spacetime containing an embedded copy of …
> (`GHFspace.tex`, l.3537–3539)

> Let $M$ be a topological spacetime. The causality of $M$ is open, and $M$ is causally open, if
> for every open subset $\U$ of $M$ and every open subset $\V\subset \U$ the set $J^+_\U(\V)$ is
> open. (`def:causally_open_spacetime_open`, `ETT.tex:694`)

> A topological spacetime is a second countable Hausdorff topological space endowed with a
> causality. (`def:category_topological_spacetimes`, `ETT.tex:255`)

## Hypothesis checklist

| hypothesis (DEC-44, DEC-93) | here |
|---|---|
| `C` a causality on `M`, `M` connected, `C.GloballyHyperbolic` | ✓ carried |
| `Σ` compact, connected, locally Cauchy (`IsLocallyCauchy`) | ✓ carried |
| separation | ✓ carried: `T2Space M`, part of ETT's spacetime (`ETT.tex:255`) |
| causally open | ✓ carried: causally open, part of ETT's spacetime (DEC-93, def:causally_open_spacetime_open) — `C.CausallyOpen`, two-sided per DEC-8 |
| second countable | ✓ carried: second countable, ETT.tex:255 — `SecondCountableTopology M` |
| — | as in the scaffold stub: `C.Tarentin`, `C.CausallyArcConnected`, `J^±(p) ≠ {p}` (the regularity hypotheses of the bare form, copied unchanged) |

## What is proved

* `Causality.isCauchySurface_of_isLocallyCauchy_of_causallyOpen`: the bare form's exact
  hypotheses (`CausalScaffold.CompactCauchy.isCauchySurface_of_isLocallyCauchy`) plus
  `[SecondCountableTopology M]` and `C.CausallyOpen`. Proof: `CurvesExtend` from Levin's theorem
  (`curvesExtend_of_secondCountable`, `Causal.LevinTimeFunction`), then
  `isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus` (`Causal.LemmaKLocal`) with
  `J^±(V)` open for `V` open, read off `CausallyOpen` at `U = ⊤`.
* `Causality.isCauchySurface_of_isLocallyCauchy_of_causallyOpen_of_curvesExtend`: the
  second-countability-free form, `CurvesExtend` assumed in its place.
* `Causality.causallyOpen_of_pushUp`: push-up plus "every point of an open `V` has a
  chronological past and future point in `V`, chronology taken in `V`" gives causal openness;
  with `causallyOpenFuture_of_pushUp`, it cites `Causal.LadderLocal`'s
  `PushUp.causallyOpen_of_chronalNeighbours` (and `…Future_of_chronalPastNeighbours`), whose
  hypotheses are these definitionally (T-abs-merge-stranded-duplicates: one proof, both names).
* Non-vacuity: `timelikeLine_causallyOpen`, and `timelikeLine_isCauchySurface_zero_of_causallyOpen`
  (every hypothesis of the main theorem, causal openness included, holds on the timelike line
  `ℝ` with `Σ = {0}`, and it applies).

## SCOPE (disclosed)

* **Why second countability is used.** Only to obtain `CurvesExtend`: Levin's utility needs
  σ-compactness (`sigmaCompactSpace_of_globallyHyperbolic`, `Causal.LevinTimeFunction`, from SC
  and the local compactness GH gives). Causal openness is not known to imply `CurvesExtend`; the
  library's other routes to it need a time function (`curvesExtend_of_timeFunction`) or
  admissible measures (`GloballyHyperbolic.curvesExtend`). The SC-free form is therefore stated
  with `CurvesExtend` as a hypothesis, not without it.
* The forms without causal openness (`CausalScaffold.CompactCauchy`, bare;
  `CausalScaffold.LemmaKSCOpen`, second countable) stay in the scaffold as open generalisations,
  not owed (DEC-93).
* **ETT layer** (T-abs-hoist-lemma-k, 2026-11-22): this module and its whole import closure
  (`Causal.LemmaKSCLocal`, `Causal.LemmaKLocal`, `Causal.LemmaKSC`, `Causal.LemmaKReduction`,
  `Causal.LemmaKBare`, `Causal.LevinUtility`, `Causal.LevinTimeFunction`, and, since
  T-abs-merge-stranded-duplicates, `Causal.LadderLocal`) import no model, so a layer-1 module may
  import Lemma K and `causallyOpen_of_pushUp`. The model corollaries of the
  family are in `Causal.Model.LemmaKModels`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Filter Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M}

/-- Push-up, and a chronological past point inside every open `V` (chronology in `V`), give
causal openness in the future. `PushUp.causallyOpenFuture_of_chronalPastNeighbours`
(`Causal.LadderLocal`), whose hypothesis `ChronalPastNeighbours` is `hZ` definitionally
(`chronalPastNeighbours_def`); cited, not re-proved (T-abs-merge-stranded-duplicates). -/
theorem causallyOpenFuture_of_pushUp (hpush : C.PushUp)
    (hZ : ∀ (V : Opens M), ∀ v ∈ V, ∃ p ∈ V, C.lt V p v) : C.CausallyOpenFuture :=
  hpush.causallyOpenFuture_of_chronalPastNeighbours hZ

/-- **Causal openness from push-up** and chronological past and future points inside every
open `V`, chronology taken in `V`. `PushUp.causallyOpen_of_chronalNeighbours`
(`Causal.LadderLocal`), whose hypothesis `ChronalNeighbours` is `⟨hZm, hZp⟩` definitionally;
cited, not re-proved (T-abs-merge-stranded-duplicates). -/
theorem causallyOpen_of_pushUp (hpush : C.PushUp)
    (hZm : ∀ (V : Opens M), ∀ v ∈ V, ∃ p ∈ V, C.lt V p v)
    (hZp : ∀ (V : Opens M), ∀ v ∈ V, ∃ p ∈ V, C.lt V v p) : C.CausallyOpen :=
  hpush.causallyOpen_of_chronalNeighbours ⟨hZm, hZp⟩

/-- **Lemma K in ETT's setting (DEC-93), the lemma of record.** In a connected, Hausdorff,
second countable, causally open spacetime with a tarentin globally hyperbolic causally
arc-connected causality and `J^±(p) ≠ {p}`, a compact connected locally Cauchy set is a Cauchy
surface. The hypotheses are those of the bare stub
`CausalScaffold.CompactCauchy.isCauchySurface_of_isLocallyCauchy`, plus
`[SecondCountableTopology M]` (`ETT.tex:255`) and `C.CausallyOpen`
(`def:causally_open_spacetime_open`, DEC-8). -/
theorem isCauchySurface_of_isLocallyCauchy_of_causallyOpen [T2Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hCO : C.CausallyOpen)
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus hT hG hC hJm hJp
    (curvesExtend_of_secondCountable hT hG) (fun V => hCO.1 ⊤ V le_top)
    (fun V => hCO.2 ⊤ V le_top) hSc hSconn hloc

/-- **Lemma K under causal openness without second countability**, `CurvesExtend` assumed in its
place (second countability is used only to produce it, through Levin's theorem). -/
theorem isCauchySurface_of_isLocallyCauchy_of_causallyOpen_of_curvesExtend [T2Space M]
    [ConnectedSpace M]
    (hT : C.Tarentin) (hG : C.GloballyHyperbolic) (hC : C.CausallyArcConnected)
    (hJm : ∀ p : M, C.Jminus ⊤ {p} ≠ {p}) (hJp : ∀ p : M, C.Jplus ⊤ {p} ≠ {p})
    (hCO : C.CausallyOpen) (hext : C.CurvesExtend)
    {S : Set M} (hSc : IsCompact S) (hSconn : IsConnected S) (hloc : C.IsLocallyCauchy S) :
    C.IsCauchySurface S :=
  isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus hT hG hC hJm hJp hext
    (fun V => hCO.1 ⊤ V le_top) (fun V => hCO.2 ⊤ V le_top) hSc hSconn hloc

end Causality

/-! ### Non-vacuity -/

/-- **The timelike line is causally open.** -/
theorem timelikeLine_causallyOpen : timelikeLine.CausallyOpen := by
  refine Causality.causallyOpen_of_pushUp timelikeLine_pushUp (fun V v hv => ?_)
    (fun V v hv => ?_)
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 V.isOpen v hv
    refine ⟨v - ε / 2, hball ?_, show v - ε / 2 < v ∧ _ from ⟨by linarith, fun z hz => hball ?_⟩⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hz.1, hz.2]
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 V.isOpen v hv
    refine ⟨v + ε / 2, hball ?_, show v < v + ε / 2 ∧ _ from ⟨by linarith, fun z hz => hball ?_⟩⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hz.1, hz.2]

/-- On the timelike line every hypothesis of
`Causality.isCauchySurface_of_isLocallyCauchy_of_causallyOpen` holds with `Σ = {0}` — `ℝ` is
connected, Hausdorff and second countable, and the line is causally open — and it applies. -/
theorem timelikeLine_isCauchySurface_zero_of_causallyOpen :
    timelikeLine.IsCauchySurface ({0} : Set ℝ) := by
  obtain ⟨hT, hG, hC, hJm, hJp, -, -, hSc, hSconn, hloc⟩ := timelikeLine_lemmaK_hypotheses
  exact Causality.isCauchySurface_of_isLocallyCauchy_of_causallyOpen hT hG hC hJm hJp
    timelikeLine_causallyOpen hSc hSconn hloc.isLocallyCauchy

end Causal
