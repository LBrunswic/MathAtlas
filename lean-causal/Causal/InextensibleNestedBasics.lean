import Causal.NestedCausalities
import Causal.LineDevelopment
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The nesting of inextensible curves: reflexive, transitive, invariant under time reversal, and not monotone in the open set

No label of `ETT.tex` is certified here: the file is the programme target
`T-abs-inextensible-nested-basics` (layer 1, `programme/roadmap.toml`), the keeper's proposal of
T-lad-nested-inextensible (journal 2026-11-22 23:10: "InextensibleNestedOn.refl/trans/dual"). It
gives the ladder's pair node `inextensible_nested` (`Causal.Causality.InextensibleNestedOn C C' W`,
`Causal.NestedCausalities`) its basic lemmas, and settles the question its entry leaves open:

> C is inextensibly nested in C' on an open W: every inextensible causal curve of W for C is an
> inextensible causal curve of W for C' (W = M unless an entry names W; not known to pass to a
> smaller open) (`programme/ladder.toml:854`)

* `Causality.InextensibleNestedOn.refl`, `Causality.InextensibleNestedOn.trans` — **with no
  hypothesis**. The definition asks of a `C`-inextensible curve that it be `C'`-inextensible, which
  includes being a `C'`-causal curve (`Inextensible` is `CausalCurveIn ∧ ¬ Extensible`), so the
  composite needs nothing of the middle causality.
* `Causality.InextensibleNestedOn.dual`, `Causality.dual_inextensibleNestedOn_iff` — time reversal,
  through `Causality.Inextensible.of_dual_reverse` and `Causality.dual_inextensible_iff` (a curve is
  inextensible iff, run backwards, it is inextensible for the reversed causality; one direction is
  the library's `Inextensible.dual_reverse`).
* **Not monotone in the open set**: `Causal.not_inextensibleNestedOn_mono` refutes "nested on `W`,
  `V ≤ W` ⇒ nested on `V`". Witness on the coarse space `Causal.CoarsePoint` (two near points
  forming an open set, a far point for each set of reals, the open sets `∅`, the near points and
  everything): `allRelated` is inextensibly nested in `diag` (a point related only to itself) on
  the whole space (`CoarsePoint.allRelated_inextensibleNestedOn_top`), vacuously, since no causal
  curve of `allRelated` is inextensible there (`CoarsePoint.allRelated_extensible`: its image
  misses a far point, by Cantor, which it reaches after its parameters are squeezed below `π / 2`
  by `arctan`); and not on the near points
  (`CoarsePoint.not_allRelated_inextensibleNestedOn_nearOpens`): the step from one near point to
  the other is inextensible there for `allRelated` (its image is all of them) and is no causal
  curve of `diag`. Bundled: `CoarsePoint.separates_inextensibleNestedOn_mono`, with both
  causalities absolutely minimal on every open set (`CoarsePoint.absolutelyMinimalOn`: every open
  cover of a nonempty open `W` has a member containing `W`), so that it stands in either form of DEC-167's
  gluing, and `diag` causal (`CoarsePoint.diag_isCausal`).
* What does pass: `Causality.InextensibleNestedOn.mono_of_inextensible` (nesting on `W` gives it on
  `V ≤ W` when every `C`-inextensible curve of `V` is `C`-inextensible in `W`), through
  `Causality.Inextensible.restrict` (an inextensible curve of `W` with image in `V` is one of `V`).
* Witnesses (kb/0011): `Causality.curveNestedOn_allRelated` (every causal curve is one of
  `allRelated`), `Causal.timelikeLine_inextensibleNestedOn_allRelated` (the timelike line is
  inextensibly nested in `allRelated` at `M`, through
  `GloballyHyperbolic.inextensibleNestedOn_top`),
  `Causal.timelikeLine_inextensibleNested_basics` (refl, trans and dual on the timelike line).

## Hypothesis checklist

| target's assertion | here |
|---|---|
| `.refl` | ✓ no hypothesis |
| `.trans` | ✓ no hypothesis: the definition asks the middle causality's curves to be its causal curves (`Inextensible` is `CausalCurveIn ∧ ¬ Extensible`) |
| `.dual` (time reversal) | ✓ no hypothesis; an iff |
| monotonicity in the open set "if it holds" | refuted in Lean on a space that is not T1 (see SCOPE); a sufficient condition, `hV` |
| instance arguments | none, for every lemma |

## SCOPE (disclosed)

* **The counterexample's space is not T1** (nor T0: two far points have the same neighbourhoods),
  so it is not one of ETT's topological spacetimes; it is second countable (three open sets: not
  proved in Lean), and `allRelated` is not causal (`diag` is). It is vacuous on `M`: there is no
  inextensible causal curve of `allRelated` at all, so the conclusion of the curves-extend theorem
  fails there (its T1 hypothesis does; kb/0142).
* **On a Hausdorff, second countable space the bare monotonicity is argued false, not in Lean**:
  on the circle `ℝ/3ℤ`, `C'` clockwise motion and `C` clockwise motion that never passes a point
  `p` (`x ≤ y` iff the clockwise arc `(x, y]` misses `p`, and `x ≪ y` asks moreover `x ≠ p`, so
  that `I⁻` stays open; not `cutLine`'s convention carried to the circle, under which `C` is not
  causal; `C` is causal, `C'` is not; the relations are not in Lean), `V` the circle minus a
  point `q ≠ p`. A `C`-curve never passes `p`, so its lift moves less than a turn and has a limit
  at both ends; it extends at an end unless the end is the start at `p` or the approach to `p`, so
  a `C`-inextensible curve of the circle starts at `p` and comes back to it: its image is the
  circle, and it is `C'`-inextensible. In `V`, the arc from `p` clockwise to `q` is
  `C`-inextensible and `C'` extends it at `p` from the other side. With both causalities causal
  the question is open.
* Why it fails: an inextensible curve of `V` need not be one of `W` (it may extend out of `V`),
  and nothing ties the `C'`-extensions inside `V` to the `C`-inextensible curves of `W`.
* `arctan` and `π` enter one proof only (`CoarsePoint.allRelated_extensible`), to reparametrise a
  curve's real parameter into a bounded interval; no metric of a spacetime is used.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Function

universe u

variable {M : Type u} [TopologicalSpace M]

namespace Causality

variable {C C' C'' : Causality M} {V W : Opens M} {I : Set ℝ} {c : ℝ → M}

/-! ## 1. Reflexivity and transitivity -/

/-- **Reflexivity**: every causality is inextensibly nested in itself, on every open set. -/
theorem InextensibleNestedOn.refl (C : Causality M) (W : Opens M) : InextensibleNestedOn C C W :=
  fun _ _ h => h

/-- **Transitivity**, with no hypothesis on the middle causality: its inextensible curves are
its causal curves. -/
theorem InextensibleNestedOn.trans (h : InextensibleNestedOn C C' W)
    (h' : InextensibleNestedOn C' C'' W) : InextensibleNestedOn C C'' W :=
  fun _ _ hc => h' (h hc)

/-! ## 2. Time reversal -/

/-- An inextensible curve of the reversed causality, run backwards, is inextensible. -/
theorem Inextensible.of_dual_reverse (h : C.dual.Inextensible W (-I) (fun t => c (-t))) :
    C.Inextensible W I c := by
  have h' := h.dual_reverse
  simp only [neg_neg] at h'
  exact h'

/-- **Inextensibility under time reversal**: a curve is inextensible iff, run backwards, it is
inextensible for the reversed causality. -/
theorem dual_inextensible_iff :
    C.dual.Inextensible W (-I) (fun t => c (-t)) ↔ C.Inextensible W I c :=
  ⟨Inextensible.of_dual_reverse, Inextensible.dual_reverse⟩

/-- **Time reversal**: the nesting passes to the reversed causalities. -/
theorem InextensibleNestedOn.dual (h : InextensibleNestedOn C C' W) :
    InextensibleNestedOn C.dual C'.dual W := fun _ _ hc =>
  Inextensible.of_dual_reverse (C := C'.dual) (h hc.dual_reverse)

/-- The nesting of the reversed causalities is the nesting. -/
theorem dual_inextensibleNestedOn_iff :
    InextensibleNestedOn C.dual C'.dual W ↔ InextensibleNestedOn C C' W :=
  ⟨fun h => h.dual, fun h => h.dual⟩

/-! ## 3. Change of open set -/

/-- An inextensible curve of `W` with image in an open `V ≤ W` is an inextensible curve of `V`:
an extension in `V` is one in `W`. -/
theorem Inextensible.restrict (h : C.Inextensible W I c) (hVW : V ≤ W) (hV : ∀ t ∈ I, c t ∈ V) :
    C.Inextensible V I c := by
  refine ⟨⟨h.1.nonempty, h.1.ordConnected, fun a ha b hb => CurveOn.restrict (h.1.curve a ha b hb)
    le_rfl le_rfl hVW fun t ht => hV t (h.1.ordConnected.out ha hb ht)⟩, ?_⟩
  rintro ⟨I', c', hs⟩
  exact h.2 ⟨I', c', hs.curve.mono_opens hVW, hs.reparam, hs.grows⟩

/-- **The nesting passes to a smaller open `V`** when every inextensible curve of `V` for the
narrower causality is inextensible in `W`. It does not in general:
`Causal.not_inextensibleNestedOn_mono`. -/
theorem InextensibleNestedOn.mono_of_inextensible (h : InextensibleNestedOn C C' W) (hVW : V ≤ W)
    (hV : ∀ ⦃I : Set ℝ⦄ ⦃c : ℝ → M⦄, C.Inextensible V I c → C.Inextensible W I c) :
    InextensibleNestedOn C C' V := fun _ _ hc =>
  (h (hV hc)).restrict hVW fun _ ht => hc.1.mem ht

/-! ## 4. Witnesses -/

/-- Every causal curve of `W` is a causal curve of `allRelated`: curve nesting into it. -/
theorem curveNestedOn_allRelated (C : Causality M) (W : Opens M) :
    CurveNestedOn C (LineDevelopment.allRelated M) W := fun _ _ _ hc =>
  ⟨hc.mem, fun t ht N hN htN => by
    obtain ⟨l, u, hl, hu, h⟩ := hc.rel t ht N hN htN
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 =>
      ⟨C.le_mem_left (h s hs s' hs' h1 h2 h3), C.le_mem_right (h s hs s' hs' h1 h2 h3)⟩⟩⟩

end Causality

/-- The timelike line is inextensibly nested in `allRelated` at `M`, through
`GloballyHyperbolic.inextensibleNestedOn_top`: a nesting of two different causalities. -/
theorem timelikeLine_inextensibleNestedOn_allRelated :
    Causality.InextensibleNestedOn timelikeLine (LineDevelopment.allRelated ℝ) ⊤ :=
  Causality.GloballyHyperbolic.inextensibleNestedOn_top timelikeLine_tarentin
    timelikeLine_globallyHyperbolic timelikeLine_causallyArcConnected timelikeLine_Jminus_ne
    timelikeLine_Jplus_ne (Causality.curveNestedOn_allRelated _ ⊤)

/-- **Witnesses** (kb/0011): the hypotheses of `trans` and `dual` are satisfiable, on the timelike
line nested in itself and in `allRelated`. -/
theorem timelikeLine_inextensibleNested_basics :
    Causality.InextensibleNestedOn timelikeLine timelikeLine ⊤ ∧
      Causality.InextensibleNestedOn timelikeLine (LineDevelopment.allRelated ℝ) ⊤ ∧
      Causality.InextensibleNestedOn timelikeLine.dual (LineDevelopment.allRelated ℝ).dual ⊤ :=
  ⟨Causality.InextensibleNestedOn.refl _ _,
    timelikeLine_inextensibleNestedOn_top.trans timelikeLine_inextensibleNestedOn_allRelated,
    timelikeLine_inextensibleNestedOn_allRelated.dual⟩

/-! ## 5. Not monotone in the open set -/

/-- The points of the counterexample: two near points and one far point for every set of reals. -/
inductive CoarsePoint
  | near (b : Bool)
  | far (S : Set ℝ)

namespace CoarsePoint

variable {I J : Set ℝ} {c d : ℝ → CoarsePoint}

/-- The near points. -/
def nearSet : Set CoarsePoint := range near

/-- The set of reals a point carries (`∅` for a near point): what Cantor's theorem is applied to. -/
def toSet : CoarsePoint → Set ℝ
  | near _ => ∅
  | far S => S

/-- The coarse topology: the open sets are `∅`, the two near points, and everything. -/
instance : TopologicalSpace CoarsePoint where
  IsOpen s := ((∃ S, far S ∈ s) → s = univ) ∧ (near false ∈ s ↔ near true ∈ s)
  isOpen_univ := ⟨fun _ => rfl, Iff.rfl⟩
  isOpen_inter s t hs ht := by
    refine ⟨fun ⟨S, hS⟩ => ?_, and_congr hs.2 ht.2⟩
    rw [hs.1 ⟨S, hS.1⟩, ht.1 ⟨S, hS.2⟩, univ_inter]
  isOpen_sUnion F hF := by
    refine ⟨fun ⟨S, hS⟩ => ?_, ?_⟩
    · obtain ⟨s, hsF, hSs⟩ := mem_sUnion.1 hS
      exact eq_univ_of_univ_subset ((hF s hsF).1 ⟨S, hSs⟩ ▸ subset_sUnion_of_mem hsF)
    · simp only [mem_sUnion]
      exact ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, (hF s hs).2.1 h⟩, fun ⟨s, hs, h⟩ => ⟨s, hs, (hF s hs).2.2 h⟩⟩

theorem isOpen_iff {s : Set CoarsePoint} :
    IsOpen s ↔ ((∃ S, far S ∈ s) → s = univ) ∧ (near false ∈ s ↔ near true ∈ s) :=
  Iff.rfl

theorem isOpen_nearSet : IsOpen nearSet :=
  isOpen_iff.2 ⟨(fun ⟨S, b, hb⟩ => by cases hb), ⟨fun _ => ⟨true, rfl⟩, fun _ => ⟨false, rfl⟩⟩⟩

/-- The two near points, as an open set. -/
def nearOpens : Opens CoarsePoint := ⟨nearSet, isOpen_nearSet⟩

/-- An open set containing a far point is everything. -/
theorem eq_univ_of_far_mem (U : Opens CoarsePoint) {S : Set ℝ} (h : far S ∈ U) :
    (U : Set CoarsePoint) = univ :=
  (isOpen_iff.1 U.isOpen).1 ⟨S, h⟩

/-- An open set containing a near point contains both. -/
theorem nearSet_subset (U : Opens CoarsePoint) {b : Bool} (h : near b ∈ U) :
    nearSet ⊆ U := by
  have hU := (isOpen_iff.1 U.isOpen).2
  rintro _ ⟨b', rfl⟩
  cases b <;> cases b'
  · exact h
  · exact hU.1 h
  · exact hU.2 h
  · exact h

/-- The causality in which a point is related only to itself: its causal curves are constant. -/
def diag : Causality CoarsePoint where
  le U x y := x ∈ U ∧ x = y
  lt _ _ _ := False
  le_mem_left h := h.1
  le_mem_right h := h.2 ▸ h.1
  lt_mem_left h := h.elim
  lt_mem_right h := h.elim
  le_refl hx := ⟨hx, rfl⟩
  le_trans h₁ h₂ := ⟨h₁.1, h₁.2.trans h₂.2⟩
  lt_trans h₁ _ := h₁.elim
  le_mono h _ _ h' := ⟨h h'.1, h'.2⟩
  lt_mono _ _ _ h' := h'.elim
  le_of_lt h := h.elim
  isOpen_lt_right _ _ := by simp
  isOpen_lt_left _ _ := by simp

/-! ### The near side: a step from one near point to the other -/

/-- The step: the first near point up to time `0`, the second after. -/
noncomputable def step (t : ℝ) : CoarsePoint := if t ≤ 0 then near false else near true

theorem step_mem (t : ℝ) : step t ∈ nearSet := by
  unfold step
  split_ifs
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

theorem causalCurveIn_step :
    (LineDevelopment.allRelated CoarsePoint).CausalCurveIn nearOpens univ step := by
  refine ⟨univ_nonempty, ordConnected_univ, fun a _ b _ => ⟨fun t _ => step_mem t, ?_⟩⟩
  intro t _ N _ htN
  obtain ⟨b', hb'⟩ := step_mem t
  have hsub := nearSet_subset N (b := b') (hb' ▸ htN)
  exact ⟨t - 1, t + 1, by linarith, by linarith, fun s _ s' _ _ _ _ =>
    ⟨hsub (step_mem s), hsub (step_mem s')⟩⟩

/-- **The step is inextensible in the near points** for `allRelated`: its image is all of them. -/
theorem inextensible_step :
    (LineDevelopment.allRelated CoarsePoint).Inextensible nearOpens univ step := by
  refine ⟨causalCurveIn_step, ?_⟩
  rintro ⟨I', c', hs⟩
  obtain ⟨t', ht', hne⟩ := hs.grows
  obtain ⟨b, hb⟩ : c' t' ∈ nearSet := hs.curve.mem ht'
  cases b
  · exact hne (-1) trivial (by rw [← hb]; simp [step])
  · exact hne 1 trivial (by rw [← hb]; simp [step])

/-- **The step is not a causal curve of `diag`**: it jumps at `0`. -/
theorem not_diag_causalCurveIn_step : ¬ diag.CausalCurveIn nearOpens univ step := by
  intro h
  obtain ⟨l, u, hl, hu, hrel⟩ := (h.curve (-1) trivial 1 trivial).rel 0
    ⟨by norm_num, by norm_num⟩ nearOpens le_rfl (step_mem 0)
  have hu' : 0 < min (u / 2) 1 := lt_min (by linarith) one_pos
  have h1 := (hrel 0 ⟨by norm_num, by norm_num⟩ (min (u / 2) 1)
    ⟨by linarith, min_le_right _ _⟩ hl hu' ((min_le_left _ _).trans_lt (by linarith))).2
  have h0 : step 0 = near false := by simp [step]
  have h2 : step (min (u / 2) 1) = near true := by simp [step, not_le.2 hu']
  rw [h0, h2] at h1
  cases h1

/-- On the near points, `allRelated` is not inextensibly nested in `diag`. -/
theorem not_allRelated_inextensibleNestedOn_nearOpens :
    ¬ (LineDevelopment.allRelated CoarsePoint).InextensibleNestedOn diag nearOpens := fun h =>
  not_diag_causalCurveIn_step (h inextensible_step).1

/-! ### The whole space: no causal curve of `allRelated` is inextensible -/

/-- The causal curves of `allRelated` over `J`, read on the topology: a near point of the curve has
a window of parameters of `J` in which the curve stays near. -/
def NearOpenOn (c : ℝ → CoarsePoint) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, c t ∈ nearSet → ∃ l < t, ∃ u, t < u ∧ ∀ s ∈ J, l < s → s < u → c s ∈ nearSet

theorem causalCurveIn_of_nearOpenOn (hJ : J.Nonempty) (hJc : J.OrdConnected)
    (h : NearOpenOn c J) : (LineDevelopment.allRelated CoarsePoint).CausalCurveIn ⊤ J c := by
  refine ⟨hJ, hJc, fun a ha b hb => ⟨fun _ _ => trivial, fun t ht N _ htN => ?_⟩⟩
  have htJ : t ∈ J := hJc.out ha hb ht
  by_cases hfar : ∃ S, far S ∈ N
  · obtain ⟨S, hS⟩ := hfar
    have hN := eq_univ_of_far_mem N hS
    refine ⟨t - 1, t + 1, by linarith, by linarith, fun s _ s' _ _ _ _ => ?_⟩
    show c s ∈ (N : Set CoarsePoint) ∧ c s' ∈ (N : Set CoarsePoint)
    rw [hN]
    exact ⟨trivial, trivial⟩
  · have hnear : c t ∈ nearSet := by
      cases hct : c t with
      | near b => exact ⟨b, rfl⟩
      | far S => exact absurd ⟨S, hct ▸ htN⟩ hfar
    obtain ⟨b', hb'⟩ := hnear
    have hsub := nearSet_subset N (b := b') (hb' ▸ htN)
    obtain ⟨l, hl, u, hu, hw⟩ := h t htJ ⟨b', hb'⟩
    exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 =>
      ⟨hsub (hw s (hJc.out ha hb hs) h1 (h2.trans h3)),
        hsub (hw s' (hJc.out ha hb hs') (h1.trans h2) h3)⟩⟩

theorem nearOpenOn_of_causalCurveIn
    (hc : (LineDevelopment.allRelated CoarsePoint).CausalCurveIn ⊤ J c) : NearOpenOn c J := by
  intro t ht htn
  have hL : ∃ l < t, ∀ s ∈ J, l < s → s ≤ t → c s ∈ nearSet := by
    by_cases h : ∃ a ∈ J, a < t
    · obtain ⟨a, ha, hat⟩ := h
      obtain ⟨l, u, hl, hu, hrel⟩ := (hc.curve a ha t ht).rel t ⟨hat.le, le_rfl⟩ nearOpens
        le_top htn
      refine ⟨max l a, max_lt hl hat, fun s _ hls hst => ?_⟩
      rcases hst.lt_or_eq with hst | rfl
      · exact (hrel s ⟨(le_max_right _ _).trans hls.le, hst.le⟩ t ⟨hat.le, le_rfl⟩
          ((le_max_left _ _).trans_lt hls) hst hu).1
      · exact htn
    · simp only [not_exists, not_and, not_lt] at h
      exact ⟨t - 1, by linarith, fun s hs _ hst => (le_antisymm hst (h s hs)) ▸ htn⟩
  have hR : ∃ u, t < u ∧ ∀ s ∈ J, t ≤ s → s < u → c s ∈ nearSet := by
    by_cases h : ∃ b ∈ J, t < b
    · obtain ⟨b, hb, htb⟩ := h
      obtain ⟨l, u, hl, hu, hrel⟩ := (hc.curve t ht b hb).rel t ⟨le_rfl, htb.le⟩ nearOpens
        le_top htn
      refine ⟨min u b, lt_min hu htb, fun s _ hts hsu => ?_⟩
      rcases hts.lt_or_eq with hts | rfl
      · exact (hrel t ⟨le_rfl, htb.le⟩ s ⟨hts.le, (hsu.trans_le (min_le_right _ _)).le⟩
          hl hts (hsu.trans_le (min_le_left _ _))).2
      · exact htn
    · simp only [not_exists, not_and, not_lt] at h
      exact ⟨t + 1, by linarith, fun s hs hts _ => (le_antisymm (h s hs) hts) ▸ htn⟩
  obtain ⟨l, hl, hwl⟩ := hL
  obtain ⟨u, hu, hwu⟩ := hR
  refine ⟨l, hl, u, hu, fun s hs hls hsu => ?_⟩
  rcases le_total s t with hst | hts
  · exact hwl s hs hls hst
  · exact hwu s hs hts hsu

/-- **A causal curve of `allRelated` over a parameter set below `2` extends** by a new far point
`x` at the parameter `2`, after a pause at its last point if it has one. -/
theorem extensible_of_lt_two (hJ : J.Nonempty) (hJc : J.OrdConnected) (hJ2 : ∀ t ∈ J, t < 2)
    (hd : NearOpenOn d J) {x : CoarsePoint} (hx : x ∉ nearSet) (hxd : ∀ t ∈ J, x ≠ d t) :
    (LineDevelopment.allRelated CoarsePoint).Extensible ⊤ J d := by
  classical
  set I' : Set ℝ := {s | (∃ t ∈ J, t ≤ s) ∧ s ≤ 2} with hI'
  set c' : ℝ → CoarsePoint := fun s =>
    if s ∈ J then d s else if s < 2 ∧ sSup J ∈ J then d (sSup J) else x with hc'
  have hbdd : BddAbove J := ⟨2, fun j hj => (hJ2 j hj).le⟩
  obtain ⟨t₀, ht₀⟩ := hJ
  have hJI' : ∀ t ∈ J, t ∈ I' := fun t ht => ⟨⟨t, ht, le_rfl⟩, (hJ2 t ht).le⟩
  have h2 : (2 : ℝ) ∈ I' := ⟨⟨t₀, ht₀, (hJ2 t₀ ht₀).le⟩, le_rfl⟩
  have h2J : (2 : ℝ) ∉ J := fun h => lt_irrefl _ (hJ2 2 h)
  have hI'c : I'.OrdConnected := ⟨fun s₁ hs₁ s₂ hs₂ s hs => by
    obtain ⟨⟨t, ht, hts₁⟩, -⟩ := hs₁
    exact ⟨⟨t, ht, hts₁.trans hs.1⟩, hs.2.trans hs₂.2⟩⟩
  -- outside `J`, a parameter of `I'` lies after all of `J`
  have hafter : ∀ s ∈ I', s ∉ J → ∀ j ∈ J, j < s := by
    intro s hs hsJ j hj
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨⟨t, ht, hts⟩, -⟩ := hs
    exact hsJ (hJc.out ht hj ⟨hts, hle⟩)
  have hnear : NearOpenOn c' I' := by
    intro t ht htn
    by_cases htJ : t ∈ J
    · have hct : c' t = d t := if_pos htJ
      obtain ⟨l, hl, u, hu, hw⟩ := hd t htJ (hct ▸ htn)
      by_cases hmax : ∃ t₂ ∈ J, t < t₂
      · obtain ⟨t₂, ht₂, htt₂⟩ := hmax
        refine ⟨l, hl, min u t₂, lt_min hu htt₂, fun s hs hls hsu => ?_⟩
        have hsJ : s ∈ J := by
          obtain ⟨⟨t', ht', hts'⟩, -⟩ := hs
          exact hJc.out ht' ht₂ ⟨hts', (hsu.trans_le (min_le_right _ _)).le⟩
        rw [show c' s = d s from if_pos hsJ]
        exact hw s hsJ hls (hsu.trans_le (min_le_left _ _))
      · simp only [not_exists, not_and, not_lt] at hmax
        have hsup : sSup J = t := IsGreatest.csSup_eq ⟨htJ, fun j hj => hmax j hj⟩
        refine ⟨l, hl, min u 2, lt_min hu (hJ2 t htJ), fun s hs hls hsu => ?_⟩
        by_cases hsJ : s ∈ J
        · rw [show c' s = d s from if_pos hsJ]
          exact hw s hsJ hls (hsu.trans_le (min_le_left _ _))
        · have hcs : c' s = d (sSup J) := by
            simp only [hc', if_neg hsJ]
            rw [if_pos ⟨hsu.trans_le (min_le_right _ _), hsup ▸ htJ⟩]
          rw [hcs, hsup, ← hct]
          exact htn
    · have hcond : t < 2 ∧ sSup J ∈ J := by
        by_contra hcon
        have hcx : c' t = x := by simp only [hc', if_neg htJ, if_neg hcon]
        exact hx (hcx ▸ htn)
      have hct : c' t = d (sSup J) := by simp only [hc', if_neg htJ, if_pos hcond]
      refine ⟨sSup J, hafter t ht htJ _ hcond.2, 2, hcond.1, fun s hs hls hsu => ?_⟩
      have hsJ : s ∉ J := fun hsJ => (le_csSup hbdd hsJ).not_gt hls
      have hcs : c' s = d (sSup J) := by
        simp only [hc', if_neg hsJ]
        rw [if_pos (show s < 2 ∧ sSup J ∈ J from ⟨hsu, hcond.2⟩)]
      rw [hcs, ← hct]
      exact htn
  refine ⟨I', c', causalCurveIn_of_nearOpenOn ⟨t₀, hJI' t₀ ht₀⟩ hI'c hnear,
    ⟨id, strictMono_id.strictMonoOn _, fun t ht => hJI' t ht, by rw [image_id]; exact hJc,
      fun t ht => if_pos ht⟩, ⟨2, h2, fun t ht => ?_⟩⟩
  have hc2 : c' 2 = x := by simp only [hc', if_neg h2J, lt_irrefl, false_and, if_false]
  rw [hc2]
  exact hxd t ht

/-- **No causal curve of `allRelated` on the whole space is inextensible**: its image misses a far
point (Cantor), which it reaches after squeezing its parameters below `π / 2` by `arctan`. -/
theorem allRelated_extensible (hc : (LineDevelopment.allRelated CoarsePoint).CausalCurveIn ⊤ I c) :
    (LineDevelopment.allRelated CoarsePoint).Extensible ⊤ I c := by
  obtain ⟨S, hS⟩ : ∃ S, ∀ t, toSet (c t) ≠ S := by
    have := cantor_surjective (fun t => toSet (c t))
    simpa [Surjective] using this
  have hcn := nearOpenOn_of_causalCurveIn hc
  have hdn : NearOpenOn (fun s => c (Real.tan s)) (Real.arctan '' I) := by
    rintro _ ⟨t₀, ht₀, rfl⟩ htn
    have htn' : c t₀ ∈ nearSet := by simpa [Real.tan_arctan] using htn
    obtain ⟨l, hl, u, hu, hw⟩ := hcn t₀ ht₀ htn'
    refine ⟨Real.arctan l, Real.arctan_strictMono hl, Real.arctan u, Real.arctan_strictMono hu, ?_⟩
    rintro _ ⟨s₀, hs₀, rfl⟩ h1 h2
    show c (Real.tan (Real.arctan s₀)) ∈ nearSet
    rw [Real.tan_arctan]
    exact hw s₀ hs₀ (Real.arctan_strictMono.lt_iff_lt.1 h1) (Real.arctan_strictMono.lt_iff_lt.1 h2)
  have hlt : ∀ t ∈ Real.arctan '' I, t < 2 := by
    rintro _ ⟨t₀, -, rfl⟩
    have := Real.arctan_lt_pi_div_two t₀
    linarith [Real.pi_le_four]
  have hext := extensible_of_lt_two (hc.nonempty.image _)
    ((hc.ordConnected.isPreconnected.image _ Real.continuous_arctan.continuousOn).ordConnected)
    hlt hdn (x := far S) (by rintro ⟨b, hb⟩; cases hb)
    (fun t _ h => hS (Real.tan t) (by rw [← h]; rfl))
  exact hext.of_comp (Real.arctan_strictMono.strictMonoOn _) (mapsTo_image _ _) (surjOn_image _ _)
    fun t _ => by simp [Real.tan_arctan]

/-- On the whole space, `allRelated` is inextensibly nested in `diag`, vacuously. -/
theorem allRelated_inextensibleNestedOn_top :
    (LineDevelopment.allRelated CoarsePoint).InextensibleNestedOn diag ⊤ := fun _ _ hc =>
  absurd (allRelated_extensible hc.1) hc.2

/-! ### Gluing: every precausality of the coarse space is absolutely minimal on every open set -/

/-- Every open cover of a nonempty open `W` has a member containing `W`, so **every precausality of the
coarse space is absolutely minimal on every open set** (DEC-167, either form). -/
theorem absolutelyMinimalOn (Q : Precausality CoarsePoint) (W : Opens CoarsePoint) :
    Q.AbsolutelyMinimalOn W := by
  intro S hS V hVW x y
  have hcover : (∃ z, z ∈ V) → ∃ O ∈ S, V ≤ O := by
    rintro ⟨z, hz⟩
    by_cases hfar : ∃ S', far S' ∈ V
    · obtain ⟨S', hS'⟩ := hfar
      obtain ⟨O, hO, hzO⟩ := hS _ (hVW hS')
      refine ⟨O, hO, fun w _ => ?_⟩
      have := eq_univ_of_far_mem O hzO
      show w ∈ (O : Set CoarsePoint)
      rw [this]
      trivial
    · obtain ⟨O, hO, hzO⟩ := hS z (hVW hz)
      refine ⟨O, hO, fun w hw => ?_⟩
      cases w with
      | far S' => exact absurd ⟨S', hw⟩ hfar
      | near b' =>
        cases z with
        | far S' => exact absurd ⟨S', hz⟩ hfar
        | near b => exact nearSet_subset O hzO ⟨b', rfl⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨O, hO, hVO⟩ := hcover ⟨x, Q.le_mem_left h⟩
    exact Relation.TransGen.single ⟨O, hO, by rwa [inf_eq_left.2 hVO]⟩
  · obtain ⟨O, hO, hVO⟩ := hcover ⟨x, Q.lt_mem_left h⟩
    exact Relation.TransGen.single ⟨O, hO, by rwa [inf_eq_left.2 hVO]⟩

/-- `diag` is causal. -/
theorem diag_isCausal : diag.IsCausal := fun _ _ h _ => h.2

/-- **The witness, bundled**: the near points are an open set of the coarse space; `allRelated` is
inextensibly nested in `diag` on the whole space and not on the near points; both causalities
are absolutely minimal on every open set (so the witness stands in either form of DEC-167's
gluing), and `diag` is causal. -/
theorem separates_inextensibleNestedOn_mono :
    nearOpens ≤ ⊤ ∧
      (LineDevelopment.allRelated CoarsePoint).InextensibleNestedOn diag ⊤ ∧
      ¬ (LineDevelopment.allRelated CoarsePoint).InextensibleNestedOn diag nearOpens ∧
      (∀ W, (LineDevelopment.allRelated CoarsePoint).AbsolutelyMinimalOn W) ∧
      (∀ W, diag.AbsolutelyMinimalOn W) ∧ diag.IsCausal :=
  ⟨le_top, allRelated_inextensibleNestedOn_top, not_allRelated_inextensibleNestedOn_nearOpens,
    fun W => absolutelyMinimalOn _ W, fun W => absolutelyMinimalOn _ W, diag_isCausal⟩

end CoarsePoint

/-- **The nesting of inextensible curves does not pass to a smaller open set**: on the coarse
space `CoarsePoint`, `allRelated` is inextensibly nested in `diag` on the whole space and not on
the open set of the two near points. -/
theorem not_inextensibleNestedOn_mono :
    ¬ ∀ (M : Type) [TopologicalSpace M] (C C' : Causality M) (V W : Opens M), V ≤ W →
      C.InextensibleNestedOn C' W → C.InextensibleNestedOn C' V := fun h =>
  CoarsePoint.not_allRelated_inextensibleNestedOn_nearOpens
    (h CoarsePoint _ _ CoarsePoint.nearOpens ⊤ le_top
      CoarsePoint.allRelated_inextensibleNestedOn_top)

end Causal
