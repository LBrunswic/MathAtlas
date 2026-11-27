import Causal.Ers464WithoutArc
import Causal.GluingModels.NonMinimal
import Causal.TimelikeHomotopy
import Causal.Ladder.Rules

/-!
# The density causality's full form: globally hyperbolic and tarentin, not causally arc-connected

No label of `ETT.tex` is certified here. The file is the programme target
`T-abs-dens-separates` (layer 1, `programme/roadmap.toml`).

* **`Causal.densCausality_separates`** decides each of the ladder's 20 causality-sort nodes on
  the density causality.
* `Causal.DensWitness.densCausality` lives in `Causal.CBG.SubExtensionAbstract`. It sets
  `x ≤_U y` iff `x ≤ y`, `x, y ∈ U` and `U` fills at least half of `]x, y]`.
* It is the conjoined Lean witness of `[globally_hyperbolic, tarentin] ⇏ causally_arc_connected`,
  in the no-gluing reading. The ladder's comment names that separation and leaves it unrecorded:

> The separation [globally_hyperbolic, tarentin] ⇏ causally_arc_connected, which no counterexample
> on the ladder gives as a conjunction (each single premise is refuted, by different models), has
> no conjoined Lean witness: Causal.DensWitness.densCausality has the three properties (globally
> hyperbolic by Causal.DensWitness.densCausality_globallyHyperbolic; tarentin, TarentinOn ⊤, by the
> second conjunct of Causal.ErsNoArcWitness.data at D = densCausality; not causally arc-connected by
> the first conjunct of
> Causal.densCausality_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc), but in three
> declarations, none conjoining them, so it is not recorded (a proposal: a conjoined statement; it
> is not absolutely minimal, so it would refute the pair in the no-gluing reading only).
> (`programme/ladder.toml:243–251`, the comment of T-lad-record-ers-cauchy-forms)

* **The positive conjuncts (18).**
  * `GloballyHyperbolic` and `Tarentin`, the entry's `from`.
  * The ladder's closure of them on `ℝ`: `IsCausal`, `CausallyCompact`, `StronglyCausal`,
    `HasTimeFunction`, `CurvesExtend`.
  * Three facts new to the library:
    * `PushUp` (`DensWitness.densCausality_pushUp`, by the additivity of the measure);
    * `ChronalNeighbours` (`DensWitness.chronalNeighbours_of_timelike`);
    * `FutureOneConnected`, and `FutureOneConnectedOn W` for every open `W`
      (`DensWitness.futureOneConnectedOn_of_timelike`: the chronal curves are the timelike
      line's, `DensWitness.chronalCurveOn_iff_timelike`).
  * What the ladder's closure gives from these: `StronglyCausalOpen`, `LocallyPushUp`,
    `CausallyOpen`, `CausallyOpenFuture`, `LocallyCausallyOpenFuture`, `LocallyCausallyOpen`,
    `CausallyPlain`, `HasChronalNeighbourEverywhere`.
* **The negative conjuncts.** `¬ CausallyArcConnected`, the ladder's node, i.e. on `⊤`.
  `¬ AbsolutelyMinimal`, and its hereditary form `¬ ∀ W, AbsolutelyMinimalOn W` (DEC-167).

## Hypothesis checklist

| target's assertion | here |
|---|---|
| `GloballyHyperbolic`, `Tarentin` | ✓ conjuncts 1–2 (`Tarentin` from `TarentinOn ⊤` by `tarentinOn_top`) |
| `IsCausal`, `CausallyCompact`, `StronglyCausal`, `HasTimeFunction`, `CurvesExtend` | ✓ conjuncts 3–7, by `causal_ladder` on `ℝ` (T2, second countable) |
| `¬ CausallyArcConnected` | ✓ the node itself (`CausallyArcConnectedOn ⊤` by definition) |
| `¬ AbsolutelyMinimal` | ✓ with `¬ ∀ W, AbsolutelyMinimalOn W` beside it |
| every further node the library decides | ✓ the 11 others, all positive: 3 new facts, 8 by `causal_ladder` |
| instance arguments | none: every statement is on `ℝ`, and the main theorem is closed |

## SCOPE (disclosed)

* **No-gluing reading only** (kb/0014, OQ-18, DEC-167). The density causality is not absolutely
  minimal: `0 ≤ 1` in `]-1/4, 1/4[ ∪ ]1/2, 5/4[`. So it is not one of ETT's spacetimes when
  `defi:causalite` is read with gluing, and in that reading it refutes nothing. The reading is the
  last two conjuncts.
* **Layer 1.** The direct imports are `Causal.Ers464WithoutArc`, `Causal.GluingModels.NonMinimal`,
  `Causal.TimelikeHomotopy` and `Causal.Ladder.Rules`.
  * `tools/ladder.py`'s `model_path` is `None` for each, checked one at a time in memory
    (kb/0247), and `None` for this module with those imports.
  * The import closure holds 69 Causal modules and no module of the model layer.
  * No statement mentions a metric. The Lebesgue measure is inside the definition of
    `densCausality`.
  * The module is a leaf, and nothing imports it. `Causal.Ers464WithoutArc` and
    `Causal.GluingModels.NonMinimal` reach `Causal.Ladder.Rules` already, so the new import adds
    no cycle (kb/0221).
* **Beyond the target's list.** The target's nine assertions are all here. Eleven positive nodes
  are added, with two forms on every open set: future one-connectedness, and the hereditary form
  of minimality. Simulated in memory (the report), the entry
  `[globally_hyperbolic, tarentin] → causally_arc_connected` moves no pair. An entry with the 18
  positive nodes as `from` and `to = absolutely_minimal` settles, on the ladder of 2026-11-27 20:57
  UTC, three `[[open]]` pairs, each in the no-gluing reading (once future_one_connected's
  separations are recorded, only the first is new; densCausality is the first non-vacuous witness
  of the other two):
  * `chronal_neighbours → absolutely_minimal`;
  * `future_one_connected → absolutely_minimal`;
  * `future_one_connected → causally_arc_connected`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace

namespace DensWitness

/-- The density causality contains the timelike line's chronology. -/
theorem densCausality_lt_of_timelike {U : Opens ℝ} {x y : ℝ} (h : timelikeLine.lt U x y) :
    densCausality.lt U x y := by
  obtain ⟨hxy, hsub⟩ := h
  refine ⟨hxy, hsub (left_mem_Icc.2 hxy.le), hsub (right_mem_Icc.2 hxy.le), ?_⟩
  rw [dens_of_subset hxy.le (Ioc_subset_Icc_self.trans hsub)]
  linarith

/-- **The density causality has push-up**: `≤_U` followed or preceded by `≪_U` is `≪_U`, because
the measure of `U ∩ ]x, z]` adds over `y`. -/
theorem densCausality_pushUp : densCausality.PushUp := by
  rw [Causality.pushUp_iff]
  intro U x y z
  constructor
  · rintro ⟨hxy, hx, -, h1⟩ ⟨hyz, -, hz, h2⟩
    refine ⟨hxy.trans_le hyz, hx, hz, ?_⟩
    rw [dens_add _ hxy.le hyz]
    linarith
  · rintro ⟨hxy, hx, -, h1⟩ ⟨hyz, -, hz, h2⟩
    refine ⟨hxy.trans_lt hyz, hx, hz, ?_⟩
    rw [dens_add _ hxy hyz.le]
    linarith

/-- A causality of `ℝ` containing the timelike line's chronology has chronal neighbours, as the
timelike line does. -/
theorem chronalNeighbours_of_timelike {D : Causality ℝ}
    (hsub : ∀ {U : Opens ℝ} {x y : ℝ}, timelikeLine.lt U x y → D.lt U x y) :
    D.ChronalNeighbours := by
  obtain ⟨hP, hF⟩ := timelikeLine_chronalNeighbours
  refine ⟨Causality.chronalPastNeighbours_def.2 fun V v hv => ?_, fun V v hv => ?_⟩
  · obtain ⟨p, hp, h⟩ := Causality.chronalPastNeighbours_def.1 hP V v hv
    exact ⟨p, hp, hsub h⟩
  · obtain ⟨p, hp, h⟩ := hF V v hv
    exact ⟨p, hp, hsub h⟩

/-- **A causality of `ℝ` whose chronology goes up and contains the timelike line's has the
timelike line's chronal curves**: a chronological relation of a small open interval around a
point of the curve is one of the timelike line. The chronal form of
`causalCurveOn_iff_timelike`. -/
theorem chronalCurveOn_iff_timelike {D : Causality ℝ}
    (hup : ∀ {U : Opens ℝ} {x y : ℝ}, D.lt U x y → x < y)
    (hsub : ∀ {U : Opens ℝ} {x y : ℝ}, timelikeLine.lt U x y → D.lt U x y)
    {W : Opens ℝ} {c : ℝ → ℝ} {a b : ℝ} :
    D.ChronalCurveOn W c a b ↔ timelikeLine.ChronalCurveOn W c a b := by
  constructor
  · intro h
    refine ⟨h.mem, fun t ht N hNW hct => ?_⟩
    obtain ⟨l, u, hlu, hsubN⟩ := mem_nhds_iff_exists_Ioo_subset.1 (N.isOpen.mem_nhds hct)
    let N' : Opens ℝ := ⟨Ioo l u, isOpen_Ioo⟩
    have hN'N : N' ≤ N := fun _ hz => hsubN hz
    obtain ⟨l', u', hl', hu', hrel⟩ := h.rel t ht N' (hN'N.trans hNW) hlu
    refine ⟨l', u', hl', hu', fun s hs s' hs' h1 h2 h3 => ?_⟩
    have hD := hrel s hs s' hs' h1 h2 h3
    have hs1 : c s ∈ Ioo l u := D.lt_mem_left hD
    have hs2 : c s' ∈ Ioo l u := D.lt_mem_right hD
    exact ⟨hup hD, fun z hz => hsubN ⟨hs1.1.trans_le hz.1, hz.2.trans_lt hs2.2⟩⟩
  · intro h
    refine ⟨h.mem, fun t ht N hNW hct => ?_⟩
    obtain ⟨l, u, hl, hu, hrel⟩ := h.rel t ht N hNW hct
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => hsub (hrel s hs s' hs' h1 h2 h3)⟩

/-- **A causality of `ℝ` whose chronology goes up and contains the timelike line's is future
one-connected on every open set**: its chronal curves are the timelike line's, and so are those of
the convex-combination homotopy of `timelikeLine_futureOneConnectedOn`. -/
theorem futureOneConnectedOn_of_timelike {D : Causality ℝ}
    (hup : ∀ {U : Opens ℝ} {x y : ℝ}, D.lt U x y → x < y)
    (hsub : ∀ {U : Opens ℝ} {x y : ℝ}, timelikeLine.lt U x y → D.lt U x y) (W : Opens ℝ) :
    D.FutureOneConnectedOn W := by
  intro p q γ₀ γ₁ h₀ hp₀ hq₀ h₁ hp₁ hq₁
  obtain ⟨Γ, hΓ⟩ := timelikeLine_futureOneConnectedOn W p q γ₀ γ₁
    ((chronalCurveOn_iff_timelike hup hsub).1 h₀) hp₀ hq₀
    ((chronalCurveOn_iff_timelike hup hsub).1 h₁) hp₁ hq₁
  exact ⟨Γ, hΓ.continuousOn, fun t ht => (chronalCurveOn_iff_timelike hup hsub).2
    (hΓ.chronalCurveOn t ht), hΓ.fix_zero, hΓ.fix_one, hΓ.eqOn_zero, hΓ.eqOn_one⟩

end DensWitness

open DensWitness in
/-- **The density causality's full form**: every causality-sort node of the ladder decided on
`densCausality`. Positive conjuncts, in this order:
* globally hyperbolic, tarentin (the entry's `from`);
* causal, causally compact, strongly causal, with a time function, curves extend (their ladder
  closure on `ℝ`);
* strongly causal with open neighbourhoods, push-up (also locally), causally open (also in the
  future, and both locally), causally plain, chronal neighbours (and one at every point), future
  one-connected (also on every open set).

Negative conjuncts: not causally arc-connected, not absolutely minimal, not absolutely minimal on
every open set. The ladder steps (`causal_ladder`):
* globally_hyperbolic ⇒ is_causal, causally_compact;
* globally_hyperbolic ∧ tarentin ⇒ strongly_causal (T2), time_function (T2, second countable);
* time_function ⇒ curves_extend;
* push_up ∧ chronal_neighbours ⇒ causally_open, causally_plain;
* strongly_causal ∧ causally_open ⇒ strongly_causal_open;
* push_up ⇒ locally_push_up;
* causally_open ⇒ causally_open_future, locally_causally_open;
* causally_open_future ⇒ locally_causally_open_future;
* chronal_neighbours ⇒ has_chronal_neighbour. -/
theorem densCausality_separates :
    densCausality.GloballyHyperbolic ∧ densCausality.Tarentin ∧
      densCausality.IsCausal ∧ densCausality.CausallyCompact ∧ densCausality.StronglyCausal ∧
      densCausality.HasTimeFunction ∧ densCausality.CurvesExtend ∧
      densCausality.StronglyCausalOpen ∧ densCausality.PushUp ∧ densCausality.LocallyPushUp ∧
      densCausality.CausallyOpen ∧ densCausality.CausallyOpenFuture ∧
      densCausality.LocallyCausallyOpenFuture ∧ densCausality.LocallyCausallyOpen ∧
      densCausality.CausallyPlain ∧ densCausality.ChronalNeighbours ∧
      densCausality.HasChronalNeighbourEverywhere ∧ densCausality.FutureOneConnected ∧
      (∀ W : Opens ℝ, densCausality.FutureOneConnectedOn W) ∧
      ¬ densCausality.CausallyArcConnected ∧ ¬ densCausality.AbsolutelyMinimal ∧
      ¬ ∀ W : Opens ℝ, densCausality.AbsolutelyMinimalOn W := by
  have hGH : densCausality.GloballyHyperbolic := densCausality_globallyHyperbolic
  have hT : densCausality.Tarentin := Causality.tarentinOn_top.1
    (ErsNoArcWitness.data (D := densCausality) (fun h => (densCausality_le.1 h).1)
      densCausality_le_of_timelike).2.1
  have hPU : densCausality.PushUp := densCausality_pushUp
  have hCN : densCausality.ChronalNeighbours :=
    chronalNeighbours_of_timelike densCausality_lt_of_timelike
  have hFOC : ∀ W : Opens ℝ, densCausality.FutureOneConnectedOn W :=
    futureOneConnectedOn_of_timelike (fun h => (densCausality_lt.1 h).1)
      densCausality_lt_of_timelike
  have hNAC : ¬ densCausality.CausallyArcConnected :=
    densCausality_ers_theorem_4_64_of_isCauchySurfaceOn_secondCountable_noArc.1
  have hNAM : ¬ densCausality.AbsolutelyMinimal := GluingModels.densCausality_not_minimal
  have hCO : densCausality.CausallyOpen := by causal_ladder
  have hCOF : densCausality.CausallyOpenFuture := by causal_ladder
  have hSC : densCausality.StronglyCausal := by causal_ladder
  exact ⟨hGH, hT, by causal_ladder, by causal_ladder, hSC, by causal_ladder, by causal_ladder,
    by causal_ladder, hPU, by causal_ladder, hCO, hCOF, by causal_ladder, by causal_ladder,
    by causal_ladder, hCN, by causal_ladder, hFOC ⊤, hFOC, hNAC, hNAM,
    GluingModels.not_forall_of_not_absolutelyMinimal hNAM⟩

end Causal
