import Causal.TimelikeHomotopy
import Causal.LemmaKObstruction
import Causal.RationalLineExtras
import Causal.ChronalNeighbourBridge
import Causal.PushUpOfMinimalLocal
import Causal.PushUpNotOpen
import Causal.StrongCausalityLifts
import Causal.DeuxPushup
import Causal.GluingModels.Minimal
import Causal.Ladder.Rules

/-!
# Future one-connectedness without chronology, and the five conjoined witnesses of `future_one_connected ⇏ X`

No label of `ETT.tex` is certified here (no `**` mark). The file is the programme target
`T-abs-future-one-connected-vacuous` (layer 1, `programme/roadmap.toml`). The ladder node is
`future_one_connected`, `Causal.Causality.FutureOneConnected` (Sbierski 1507.00601 Def 2.13,
`Causal.TimelikeHomotopy`). Its 18 `[[open]]` pairs `future_one_connected → X` (every causality
node `X` but `curves_extend`) were each "False, argued", and the ladder named the way:

> a causality with no chronology is future one-connected vacuously, a future chronal curve γ of W
> over [0, 1] having γ 0 ≪_W γ 1 (Causal.Causality.ChronalCurveOn.lt_of_lt); so are the
> half-chronological line's, by the timelike line's convex combination
> (Causal.timelikeLine_futureOneConnectedOn's proof, with −1 < p).
> (`programme/ladder.toml`, the comment of the `[[open]]` section `future_one_connected → X`,
> 2026-11-27; anchored by its text, since the file is edited often)

* **Layer-1 lemmas.** `Causality.futureOneConnectedOn_of_forall_not_lt`: no `x ≪_W y` gives
  `C.FutureOneConnectedOn W` (`Causality.not_chronalCurveOn_of_forall_not_lt`: no chronal curve of
  `W` over `[a, b]`, `a < b`). Hence `Causality.withoutChronology_futureOneConnectedOn` and
  `Causality.withoutChronology_futureOneConnected`. Three more facts of an empty chronology:
  `Causality.pushUp_of_forall_not_lt`, `Causality.not_hasChronalNeighbourEverywhere_of_forall_not_lt`
  and `Causality.not_causallyPlain_of_forall_not_lt` (the last two on a non-empty space).
* **The half-chronological line, not vacuous.** Its chronal curves of `W` over `[a, b]`, `a < b`,
  are the timelike line's that start after `−1` (`halfChronoLine_chronalCurveOn_iff`), i.e. the
  continuous strictly increasing maps into `W ∩ (−1, ∞)`
  (`halfChronoLine_chronalCurveOn_iff_strictMonoOn`). So the timelike line's homotopy, the convex
  combination, is one of the half-chronological line: `halfChronoLine_futureOneConnectedOn`, on
  every open set. Also new: `halfChronoLine_not_hasChronalNeighbourEverywhere` (nothing at `−1`).
* **Five full forms** (kb/0296). Each decides all 20 causality nodes for its model. Its positive
  conjuncts are the `has`, and its negated ones the `lacks`, of `ladder.counterexample` (checked
  in memory). Each adds `∀ W, FutureOneConnectedOn W`, and `∀ W, AbsolutelyMinimalOn W` where
  that holds, so the reading is in the statement.
  - `rationalLine_separates_futureOneConnected` covers → causally_arc_connected, causally_compact,
    causally_open, causally_open_future, causally_plain, chronal_neighbours,
    locally_causally_open, locally_causally_open_future, tarentin (and globally_hyperbolic). Either reading.
  - `lightlikeLine_separates_futureOneConnected` covers → has_chronal_neighbour. Either reading.
  - `halfChronoLine_separates_futureOneConnected` covers → push_up, locally_push_up. Either reading.
  - `jumpLine_separates_futureOneConnected` covers → absolutely_minimal. No-gluing reading only:
    the line is not absolutely minimal (DEC-167, kb/0014).
  - `symmRationalLine_separates_futureOneConnected` covers → is_causal, strongly_causal,
    strongly_causal_open, globally_hyperbolic, time_function. Either reading. `0 ≤ 1 ≤ 0`, and
    every other fact of the line not in the library, is proved inside the theorem.

## Hypothesis checklist

| target's assertion | here |
|---|---|
| `(∀ x y, ¬ C.lt W x y) → C.FutureOneConnectedOn W` | ✓ `futureOneConnectedOn_of_forall_not_lt`, any causality, any open, no instance |
| `withoutChronology_futureOneConnected(On)` | ✓ both, every open `W` |
| half-chronological line: chronal curves = continuous strictly increasing into `W ∩ (−1, ∞)`; convex combination | ✓ `halfChronoLine_chronalCurveOn_iff_strictMonoOn`, `halfChronoLine_futureOneConnectedOn` (every `W`) |
| one conjoined theorem per model with what it has and lacks | ✓ five, each deciding all 20 nodes; `∀ W, AbsolutelyMinimalOn W` in the four that are |
| `¬ symmRationalLine.IsCausal` inline, no other global name about the line | ✓ a conjunct; every fact of it not in the library is a `have` |
| instance arguments | none in the five: closed statements on `ℝ` |

## SCOPE (disclosed)

* **Layer 1.** The direct imports are `Causal.TimelikeHomotopy`, `LemmaKObstruction`,
  `RationalLineExtras`, `ChronalNeighbourBridge`, `PushUpOfMinimalLocal`, `PushUpNotOpen`,
  `StrongCausalityLifts`, `DeuxPushup`, `GluingModels.Minimal` and `Ladder.Rules`.
  `tools/ladder.py`'s `model_path` is `None` for each (kb/0247). No statement mentions a metric.
  The module is a leaf. `causal_ladder` runs here, and nothing it is built from imports this file
  (kb/0221).
* **Not the flat time cylinder.** The keeper argued → is_causal and its four companions with
  `(Causal.Flat.timeCylinder d).withoutChronology`, a model (layer 3). The symmetric rational line
  settles them in the ETT layer. The cylinder, now `withoutChronology_futureOneConnected` applied
  to it, is a model follow-up.
* **The node at `M`.** `FutureOneConnectedOn W` is not hereditary in general (argued, not in
  Lean: ℝ^{1,2} minus the time axis). Here it holds on
  every open set, and each witness says so as a separate conjunct beside the node.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C : Causality M} {W : Opens M} {c : ℝ → M} {a b : ℝ}

/-- Without chronology in `W` there is no future chronal curve of `W` over a non-degenerate
segment. -/
theorem not_chronalCurveOn_of_forall_not_lt (h : ∀ x y, ¬ C.lt W x y) (hab : a < b) :
    ¬ C.ChronalCurveOn W c a b :=
  fun hc => h _ _ (hc.lt_of_lt le_rfl hab le_rfl)

/-- **Future one-connectedness without chronology**: if no `x ≪_W y`, the open `W` is future
one-connected as a spacetime, vacuously. A future chronal curve `γ` of `W` over `[0, 1]` would have
`γ 0 ≪_W γ 1` (`ChronalCurveOn.lt_of_lt`), so there is none. -/
theorem futureOneConnectedOn_of_forall_not_lt (h : ∀ x y, ¬ C.lt W x y) :
    C.FutureOneConnectedOn W :=
  fun _ _ _ _ h₀ _ _ _ _ _ => (not_chronalCurveOn_of_forall_not_lt h zero_lt_one h₀).elim

/-- `C` without chronology (`≪ = ∅`, `Causal.LemmaKObstruction`) is future one-connected on every
open set. -/
theorem withoutChronology_futureOneConnectedOn (C : Causality M) (W : Opens M) :
    C.withoutChronology.FutureOneConnectedOn W :=
  futureOneConnectedOn_of_forall_not_lt fun _ _ h => h

/-- `C` without chronology is future one-connected. -/
theorem withoutChronology_futureOneConnected (C : Causality M) :
    C.withoutChronology.FutureOneConnected :=
  C.withoutChronology_futureOneConnectedOn ⊤

/-- With no chronology on any open set, push-up holds vacuously (`pushUp_iff`). -/
theorem pushUp_of_forall_not_lt (h : ∀ (U : Opens M) x y, ¬ C.lt U x y) : C.PushUp :=
  pushUp_iff.2 fun U _ _ _ => ⟨fun hxy _ => (h U _ _ hxy).elim, fun _ hyz => (h U _ _ hyz).elim⟩

/-- With no chronology in `M`, on a non-empty space, some point has no chronal neighbour. -/
theorem not_hasChronalNeighbourEverywhere_of_forall_not_lt [Nonempty M]
    (h : ∀ x y, ¬ C.lt ⊤ x y) : ¬ C.HasChronalNeighbourEverywhere := by
  intro hN
  obtain ⟨p⟩ := ‹Nonempty M›
  rcases hN p with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact h _ _ (Precausality.mem_Iplus_singleton.1 hy)
  · exact h _ _ (Precausality.mem_Iminus_singleton.1 hy)

/-- With no chronology in `M`, on a non-empty space, `C` is not causally plain:
`Int J⁺_M(M) = M` while `I⁺_M(M) = ∅`. -/
theorem not_causallyPlain_of_forall_not_lt [Nonempty M] (h : ∀ x y, ¬ C.lt ⊤ x y) :
    ¬ C.CausallyPlain := by
  intro hP
  obtain ⟨p⟩ := ‹Nonempty M›
  have hJ : C.Jplus ⊤ univ = univ := eq_univ_of_forall fun y => ⟨y, trivial, C.le_refl trivial⟩
  have hI : C.Iplus ⊤ univ = ∅ := eq_empty_of_forall_notMem fun _ ⟨_, _, hl⟩ => h _ _ hl
  have hp := (hP ⊤ univ).1 (show p ∈ interior (C.Jplus ⊤ univ) by rw [hJ, interior_univ]; trivial)
  rw [hI, closure_empty] at hp
  exact hp

end Causality

/-! ## The half-chronological line -/

/-- On the half-chronological line, a future chronal curve of `W` over `[a, b]`, `a < b`, is a
future chronal curve of the timelike line which starts after `−1`. -/
theorem halfChronoLine_chronalCurveOn_iff {W : Opens ℝ} {c : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    halfChronoLine.ChronalCurveOn W c a b ↔ timelikeLine.ChronalCurveOn W c a b ∧ -1 < c a := by
  constructor
  · intro hc
    refine ⟨{ mem := hc.mem, rel := fun t ht N hN htN => ?_ }, ?_⟩
    · obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht N hN htN
      exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 =>
        timelikeLine_lt.2 (halfChronoLine_lt.1 (hrel s hs s' hs' h1 h2 h3)).2⟩
    · exact (halfChronoLine_lt.1 (hc.lt_of_lt le_rfl hab le_rfl)).1
  · rintro ⟨hc, hca⟩
    have hmono := (timelikeLine_chronalCurveOn_iff.1 hc).1
    refine { mem := hc.mem, rel := fun t ht N hN htN => ?_ }
    obtain ⟨l, u, hl, hu, hrel⟩ := hc.rel t ht N hN htN
    refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => halfChronoLine_lt.2 ⟨?_, ?_⟩⟩
    · exact hca.trans_le (hmono.monotoneOn (left_mem_Icc.2 hab.le) hs hs.1)
    · exact timelikeLine_lt.1 (hrel s hs s' hs' h1 h2 h3)

/-- On the half-chronological line, the future chronal curves of `W` over `[a, b]`, `a < b`, are
the continuous strictly increasing maps of `[a, b]` into `W ∩ (−1, ∞)`. -/
theorem halfChronoLine_chronalCurveOn_iff_strictMonoOn {W : Opens ℝ} {c : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) :
    halfChronoLine.ChronalCurveOn W c a b ↔
      StrictMonoOn c (Icc a b) ∧ ContinuousOn c (Icc a b) ∧
        MapsTo c (Icc a b) ((W : Set ℝ) ∩ Ioi (-1)) := by
  rw [halfChronoLine_chronalCurveOn_iff hab, timelikeLine_chronalCurveOn_iff]
  constructor
  · rintro ⟨⟨hm, hc, hW⟩, ha⟩
    exact ⟨hm, hc, fun s hs =>
      ⟨hW hs, ha.trans_le (hm.monotoneOn (left_mem_Icc.2 hab.le) hs hs.1)⟩⟩
  · rintro ⟨hm, hc, hW⟩
    exact ⟨⟨hm, hc, fun s hs => (hW hs).1⟩, (hW (left_mem_Icc.2 hab.le)).2⟩

/-- **The half-chronological line is future one-connected on every open set**, not vacuously:
two future chronal curves of `W` over `[0, 1]` from `p` to `q` are chronal curves of the timelike
line, homotopic through their convex combinations (`timelikeLine_futureOneConnectedOn`). Each
slice starts at `p > −1`, so it is a chronal curve of the half-chronological line. -/
theorem halfChronoLine_futureOneConnectedOn (W : Opens ℝ) :
    halfChronoLine.FutureOneConnectedOn W := by
  intro p q γ₀ γ₁ h₀ hp₀ hq₀ h₁ hp₁ hq₁
  have hab : (0 : ℝ) < 1 := zero_lt_one
  obtain ⟨t₀, hm₀⟩ := (halfChronoLine_chronalCurveOn_iff hab).1 h₀
  obtain ⟨t₁, -⟩ := (halfChronoLine_chronalCurveOn_iff hab).1 h₁
  obtain ⟨Γ, hΓ⟩ := timelikeLine_futureOneConnectedOn W p q γ₀ γ₁ t₀ hp₀ hq₀ t₁ hp₁ hq₁
  refine ⟨Γ, hΓ.continuousOn, fun t ht => (halfChronoLine_chronalCurveOn_iff hab).2
    ⟨hΓ.chronalCurveOn t ht, ?_⟩, hΓ.fix_zero, hΓ.fix_one, hΓ.eqOn_zero, hΓ.eqOn_one⟩
  rw [hΓ.fix_zero t ht]
  exact hm₀

/-- On the half-chronological line, `−1` has no chronal neighbour: `x ≪ y` asks `−1 < x`. -/
theorem halfChronoLine_not_hasChronalNeighbourEverywhere :
    ¬ halfChronoLine.HasChronalNeighbourEverywhere := by
  intro h
  rcases h (-1) with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact lt_irrefl _ (halfChronoLine_lt.1 (Precausality.mem_Iplus_singleton.1 hy)).1
  · have hy' := halfChronoLine_lt.1 (Precausality.mem_Iminus_singleton.1 hy)
    linarith [hy'.1, hy'.2.1]

/-! ## The five conjoined separations -/

/-- **The rational line's full form, with the node** (either reading). It is future one-connected,
vacuously (`≪` is empty), on every open set. It is absolutely minimal, on every open set for every
cover, causal, push-up (also locally), with a time function, curves extend, strongly causal in both
forms. It is not causally arc-connected, not causally open in the future or two-sided, not locally
causally open in either form, not tarentin, not causally plain, without chronal neighbours or a
chronal neighbour at every point, not causally compact, not globally hyperbolic. All but the node
and `¬ HasChronalNeighbourEverywhere` are `rationalLine_separates`'s conjuncts; `∀ W,
AbsolutelyMinimalOn W` is `rationalLine_absolutelyMinimalOn`. -/
theorem rationalLine_separates_futureOneConnected :
    rationalLine.FutureOneConnected ∧ (∀ W : Opens ℝ, rationalLine.FutureOneConnectedOn W) ∧
      rationalLine.AbsolutelyMinimal ∧ (∀ W : Opens ℝ, rationalLine.AbsolutelyMinimalOn W) ∧
      rationalLine.IsCausal ∧ rationalLine.PushUp ∧ rationalLine.LocallyPushUp ∧
      rationalLine.HasTimeFunction ∧ rationalLine.CurvesExtend ∧
      rationalLine.StronglyCausalOpen ∧ rationalLine.StronglyCausal ∧
      ¬ rationalLine.CausallyArcConnected ∧ ¬ rationalLine.CausallyOpenFuture ∧
      ¬ rationalLine.CausallyOpen ∧ ¬ rationalLine.LocallyCausallyOpenFuture ∧
      ¬ rationalLine.LocallyCausallyOpen ∧ ¬ rationalLine.Tarentin ∧
      ¬ rationalLine.CausallyPlain ∧ ¬ rationalLine.ChronalNeighbours ∧
      ¬ rationalLine.HasChronalNeighbourEverywhere ∧
      ¬ rationalLine.CausallyCompact ∧ ¬ rationalLine.GloballyHyperbolic := by
  obtain ⟨hAM, hC, hPU, hLPU, hTF, hCE, hSCO, hSC, hNAC, hNCOF, hNCO, hNLCOF, hNLCO, hNT, hNCP,
    hNCN, hNCC, hNGH⟩ := rationalLine_separates
  exact ⟨Causality.futureOneConnectedOn_of_forall_not_lt fun _ _ h => h,
    fun _ => Causality.futureOneConnectedOn_of_forall_not_lt fun _ _ h => h, hAM,
    rationalLine_absolutelyMinimalOn, hC, hPU, hLPU, hTF, hCE, hSCO, hSC, hNAC, hNCOF, hNCO, hNLCOF,
    hNLCO, hNT, hNCP, hNCN, Causality.not_hasChronalNeighbourEverywhere_of_forall_not_lt
      fun _ _ h => h, hNCC, hNGH⟩

/-- **The lightlike line's full form, with the node** (either reading). It is future
one-connected, vacuously, on every open set, and absolutely minimal on every open set. It has
push-up and causal openness in all forms, global hyperbolicity, causal compactness, causality,
causal arc-connectedness, tarentin, strong causality in both forms, a time function, and curves
extend. Some point has no chronal neighbour (`¬ HasChronalNeighbourEverywhere`; in fact none
has, which is not stated here), it has no chronal neighbours, and is not causally plain. `causal_ladder` gives the closure on `ℝ`, from `lightlikeLine_separates_hasChronalNeighbour`
and absolute minimality: strongly_causal from globally_hyperbolic ∧ tarentin (T2), and
time_function from the same (T2, second countable). -/
theorem lightlikeLine_separates_futureOneConnected :
    lightlikeLine.FutureOneConnected ∧ (∀ W : Opens ℝ, lightlikeLine.FutureOneConnectedOn W) ∧
      lightlikeLine.AbsolutelyMinimal ∧ (∀ W : Opens ℝ, lightlikeLine.AbsolutelyMinimalOn W) ∧
      lightlikeLine.PushUp ∧ lightlikeLine.LocallyPushUp ∧ lightlikeLine.CausallyOpen ∧
      lightlikeLine.CausallyOpenFuture ∧ lightlikeLine.LocallyCausallyOpenFuture ∧
      lightlikeLine.LocallyCausallyOpen ∧ lightlikeLine.GloballyHyperbolic ∧
      lightlikeLine.CausallyCompact ∧ lightlikeLine.IsCausal ∧
      lightlikeLine.CausallyArcConnected ∧ lightlikeLine.Tarentin ∧
      lightlikeLine.StronglyCausal ∧ lightlikeLine.StronglyCausalOpen ∧
      lightlikeLine.HasTimeFunction ∧ lightlikeLine.CurvesExtend ∧
      ¬ lightlikeLine.HasChronalNeighbourEverywhere ∧ ¬ lightlikeLine.ChronalNeighbours ∧
      ¬ lightlikeLine.CausallyPlain := by
  obtain ⟨hPU, hCO, hGH, -, hAC, hT, hNH⟩ := lightlikeLine_separates_hasChronalNeighbour
  have hAM : lightlikeLine.AbsolutelyMinimal := lightlikeLine_absolutelyMinimal
  have hCOF : lightlikeLine.CausallyOpenFuture := by causal_ladder
  have hSC : lightlikeLine.StronglyCausal := by causal_ladder
  exact ⟨Causality.futureOneConnectedOn_of_forall_not_lt fun _ _ h => h,
    fun _ => Causality.futureOneConnectedOn_of_forall_not_lt fun _ _ h => h, hAM,
    lightlikeLine_absolutelyMinimalOn, hPU, by causal_ladder, hCO, hCOF, by causal_ladder,
    by causal_ladder, hGH, by causal_ladder, by causal_ladder, hAC, hT, hSC, by causal_ladder,
    by causal_ladder, by causal_ladder, hNH, lightlikeLine_not_chronalNeighbours,
    lightlikeLine_not_causallyPlain⟩

/-- **The half-chronological line's full form, with the node** (either reading). It is future
one-connected on every open set (`halfChronoLine_futureOneConnectedOn`, not vacuous), absolutely
minimal on every open set, causally arc-connected, globally hyperbolic, causally compact, causal,
strongly causal in both forms, causally open in all forms, tarentin, with a time function, and
curves extend. It is neither locally push-up nor push-up, not causally plain, without chronal
neighbours, and `−1` has no chronal neighbour. -/
theorem halfChronoLine_separates_futureOneConnected :
    halfChronoLine.FutureOneConnected ∧ (∀ W : Opens ℝ, halfChronoLine.FutureOneConnectedOn W) ∧
      halfChronoLine.AbsolutelyMinimal ∧ (∀ W : Opens ℝ, halfChronoLine.AbsolutelyMinimalOn W) ∧
      halfChronoLine.CausallyArcConnected ∧ halfChronoLine.GloballyHyperbolic ∧
      halfChronoLine.CausallyCompact ∧ halfChronoLine.IsCausal ∧
      halfChronoLine.StronglyCausal ∧ halfChronoLine.StronglyCausalOpen ∧
      halfChronoLine.CausallyOpen ∧ halfChronoLine.CausallyOpenFuture ∧
      halfChronoLine.LocallyCausallyOpenFuture ∧ halfChronoLine.LocallyCausallyOpen ∧
      halfChronoLine.Tarentin ∧ halfChronoLine.HasTimeFunction ∧ halfChronoLine.CurvesExtend ∧
      ¬ halfChronoLine.LocallyPushUp ∧ ¬ halfChronoLine.PushUp ∧
      ¬ halfChronoLine.CausallyPlain ∧ ¬ halfChronoLine.ChronalNeighbours ∧
      ¬ halfChronoLine.HasChronalNeighbourEverywhere := by
  obtain ⟨hAC, hAM, hGH, hC, hSC, hSCO, hCO, hT, hTF, hCE, hNLPU, hNPU⟩ :=
    halfChronoLine_separates_pushUp
  have hCOF : halfChronoLine.CausallyOpenFuture := by causal_ladder
  exact ⟨halfChronoLine_futureOneConnectedOn ⊤, halfChronoLine_futureOneConnectedOn, hAM,
    GluingModels.halfChronoLine_hereditary, hAC, hGH, by causal_ladder, hC, hSC, hSCO, hCO, hCOF,
    by causal_ladder, by causal_ladder, hT, hTF, hCE, hNLPU, hNPU, halfChronoLine_not_causallyPlain,
    halfChronoLine_not_chronalNeighbours, halfChronoLine_not_hasChronalNeighbourEverywhere⟩

/-- **The jump line's full form, with the node** (the no-gluing reading only: it is not absolutely
minimal, and every `X ⇒ absolutely_minimal` holds in a gluing reading, DEC-167). It is future
one-connected, vacuously, on every open set. It is push-up (also locally), two-sided locally
causally open, globally hyperbolic, causally compact, causal, strongly causal in both forms, with a
time function, and curves extend. It is not absolutely minimal, not causally open in the future or
two-sided, not causally arc-connected, without chronal neighbours, not tarentin, not causally
plain, and has no chronal neighbour at some point. -/
theorem jumpLine_separates_futureOneConnected :
    jumpLine.FutureOneConnected ∧ (∀ W : Opens ℝ, jumpLine.FutureOneConnectedOn W) ∧
      jumpLine.PushUp ∧ jumpLine.LocallyPushUp ∧ jumpLine.LocallyCausallyOpen ∧
      jumpLine.LocallyCausallyOpenFuture ∧ jumpLine.GloballyHyperbolic ∧
      jumpLine.CausallyCompact ∧ jumpLine.IsCausal ∧ jumpLine.StronglyCausal ∧
      jumpLine.StronglyCausalOpen ∧ jumpLine.HasTimeFunction ∧ jumpLine.CurvesExtend ∧
      ¬ jumpLine.AbsolutelyMinimal ∧ ¬ jumpLine.CausallyOpenFuture ∧ ¬ jumpLine.CausallyOpen ∧
      ¬ jumpLine.CausallyArcConnected ∧ ¬ jumpLine.ChronalNeighbours ∧ ¬ jumpLine.Tarentin ∧
      ¬ jumpLine.CausallyPlain ∧ ¬ jumpLine.HasChronalNeighbourEverywhere := by
  obtain ⟨hPU, hLCO, hGH, hSCO, hTF, hNCOF, hNCO, hNAM, hNAC, hNCN, hNT, hNCP⟩ :=
    jumpLine_separates_causallyOpenFuture
  exact ⟨Causality.futureOneConnectedOn_of_forall_not_lt fun _ _ h => h,
    fun _ => Causality.futureOneConnectedOn_of_forall_not_lt fun _ _ h => h, hPU, by causal_ladder,
    hLCO, by causal_ladder, hGH, by causal_ladder, by causal_ladder, by causal_ladder, hSCO, hTF,
    by causal_ladder, hNAM, hNCOF, hNCO, hNAC, hNCN, hNT, hNCP,
    Causality.not_hasChronalNeighbourEverywhere_of_forall_not_lt fun _ _ h => h⟩

/-- **The symmetric rational line's full form, with the node** (either reading: absolutely minimal
on every open set for every cover, `symmRationalLine_absolutelyMinimalOn`). It is future
one-connected, vacuously (`≪` is empty), on every open set. It is absolutely minimal, push-up
(vacuously, also locally), and curves extend. It is not causal: `0 ≤_M 1 ≤_M 0`. So it is neither
strongly causal (in either form), nor globally hyperbolic, nor with a time function. It is not
causally compact (`J_M(0, 0)` holds every natural number), not causally arc-connected, not causally
open in any form (`J⁺_M((0, 1))` holds `1` and no irrational above `1`), and not tarentin (an
irrational point of `J_M(p, q)` is `p`, so no diamond has interior). It is not causally plain,
without chronal neighbours, and has no chronal neighbour at some point. The facts of the line the
library lacks are `have`s, not global names (the target's coordination). -/
theorem symmRationalLine_separates_futureOneConnected :
    symmRationalLine.FutureOneConnected ∧
      (∀ W : Opens ℝ, symmRationalLine.FutureOneConnectedOn W) ∧
      symmRationalLine.AbsolutelyMinimal ∧
      (∀ W : Opens ℝ, symmRationalLine.AbsolutelyMinimalOn W) ∧
      symmRationalLine.PushUp ∧ symmRationalLine.LocallyPushUp ∧ symmRationalLine.CurvesExtend ∧
      ¬ symmRationalLine.IsCausal ∧ ¬ symmRationalLine.StronglyCausal ∧
      ¬ symmRationalLine.StronglyCausalOpen ∧ ¬ symmRationalLine.GloballyHyperbolic ∧
      ¬ symmRationalLine.HasTimeFunction ∧ ¬ symmRationalLine.CausallyCompact ∧
      ¬ symmRationalLine.CausallyArcConnected ∧ ¬ symmRationalLine.CausallyOpenFuture ∧
      ¬ symmRationalLine.CausallyOpen ∧ ¬ symmRationalLine.LocallyCausallyOpenFuture ∧
      ¬ symmRationalLine.LocallyCausallyOpen ∧ ¬ symmRationalLine.Tarentin ∧
      ¬ symmRationalLine.CausallyPlain ∧ ¬ symmRationalLine.ChronalNeighbours ∧
      ¬ symmRationalLine.HasChronalNeighbourEverywhere := by
  have hlt : ∀ (U : Opens ℝ) (x y : ℝ), ¬ symmRationalLine.lt U x y := fun _ _ _ h => h
  have hq : ∀ r : ℚ, (r : ℝ) ∈ range ((↑) : ℚ → ℝ) := fun r => ⟨r, rfl⟩
  -- any two rationals are related both ways in `M`
  have hle : ∀ r r' : ℚ, symmRationalLine.le ⊤ (r : ℝ) r' := fun r r' =>
    Or.inr ⟨hq r, hq r', fun _ _ => trivial⟩
  -- an irrational point is related to itself only
  have hirr : ∀ {U : Opens ℝ} {x y : ℝ}, symmRationalLine.le U x y → Irrational y → x = y := by
    intro U x y h hy
    rcases h with ⟨h, -⟩ | ⟨-, hy', -⟩
    · exact h
    · exact (hy hy').elim
  have hAM : symmRationalLine.AbsolutelyMinimal :=
    GluingModels.absolutelyMinimal_of_forall symmRationalLine_absolutelyMinimalOn
  have hPU : symmRationalLine.PushUp := Causality.pushUp_of_forall_not_lt hlt
  -- `0 ≤ 1 ≤ 0`
  have hNC : ¬ symmRationalLine.IsCausal := fun h => by
    have := h (by exact_mod_cast hle 0 1) (by exact_mod_cast hle 1 0)
    norm_num at this
  have hNSC := symmRationalLine_not_stronglyCausal
  -- `J_M(0, 0)` holds every natural number
  have hNCC : ¬ symmRationalLine.CausallyCompact := by
    intro h
    obtain ⟨B, hB⟩ := (h ((0 : ℚ) : ℝ) ((0 : ℚ) : ℝ)).bddAbove
    have := hB (Causality.mem_diamond.2 ⟨hle 0 (⌈B⌉₊ + 1 : ℕ), hle (⌈B⌉₊ + 1 : ℕ) 0⟩)
    push_cast at this
    linarith [Nat.le_ceil B]
  -- `J⁺_M((0, 1))` contains `1` and no irrational number above `1`
  have hNCOF : ¬ symmRationalLine.CausallyOpenFuture := by
    intro h
    let V : Opens ℝ := ⟨Ioo 0 1, isOpen_Ioo⟩
    have h1 : (1 : ℝ) ∈ symmRationalLine.Jplus ⊤ V := by
      rw [Precausality.mem_Jplus]
      refine ⟨((1 / 2 : ℚ) : ℝ), show ((1 / 2 : ℚ) : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num, ?_⟩
      exact_mod_cast hle (1 / 2) 1
    obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 ((h ⊤ V le_top).mem_nhds h1)
    obtain ⟨v, hvirr, hv1, hv2⟩ := exists_irrational_btwn hu
    obtain ⟨x, hx, hxv⟩ := Precausality.mem_Jplus.1 (hlu ⟨hl.trans hv1, hv2⟩)
    have hx' : x ∈ Ioo (0 : ℝ) 1 := hx
    have := hirr hxv hvirr
    linarith [hx'.2]
  -- no diamond has interior: an irrational point of `J_M(p, q)` is `p`
  have hNT : ¬ symmRationalLine.Tarentin := by
    intro h
    obtain ⟨p, -, q, -, hx⟩ := h 0 univ Filter.univ_mem
    obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 (mem_interior_iff_mem_nhds.1 hx)
    obtain ⟨v, hv, hlv, hv0⟩ := exists_irrational_btwn hl
    obtain ⟨w, hw, h0w, hwu⟩ := exists_irrational_btwn hu
    have h1 := (Causality.mem_diamond.1 (hlu ⟨hlv, hv0.trans hu⟩)).1
    have h2 := (Causality.mem_diamond.1 (hlu ⟨hl.trans h0w, hwu⟩)).1
    have hvw : v = w := (hirr h1 hv).symm.trans (hirr h2 hw)
    linarith
  have hNH : ¬ symmRationalLine.HasChronalNeighbourEverywhere :=
    Causality.not_hasChronalNeighbourEverywhere_of_forall_not_lt (hlt ⊤)
  exact ⟨Causality.futureOneConnectedOn_of_forall_not_lt (hlt ⊤),
    fun W => Causality.futureOneConnectedOn_of_forall_not_lt (hlt W), hAM,
    symmRationalLine_absolutelyMinimalOn, hPU, by causal_ladder, by causal_ladder, hNC, hNSC,
    fun h => hNSC (by causal_ladder), fun h => hNC h.1, fun h => hNC (by causal_ladder), hNCC,
    symmRationalLine_not_causallyArcConnected, hNCOF, fun h => hNCOF (by causal_ladder),
    fun h => hNCOF (by causal_ladder), fun h => hNCOF (by causal_ladder), hNT,
    Causality.not_causallyPlain_of_forall_not_lt (hlt ⊤),
    fun h => hNH h.hasChronalNeighbourEverywhere, hNH⟩

end Causal
