import Causal.OneWayMembrane
import Causal.Ladder.Rules

/-!
# The one-way membrane with a chronology: chronal neighbours, absolutely minimal, without push-up

Programme target `T-abs-one-way-membrane-chronal` (`programme/roadmap.toml:925`; layer 1, no label
of `ETT.tex`). Imports: `Causal.OneWayMembrane`, `Causal.Ladder.Rules` (ETT layer: no model, no
CBG, Splitting, LemmaK* or LevinUtility module, transitively). On `ℝ^{1+1}` in null coordinates
`(u, v) = (t + x¹, t − x¹)`, `R = {x¹ > 0} = {v < u}` (`membraneRight`), the membrane `{u = v}`.
`chronalMembrane` has the `≤` of `oneWayMembrane` (`TransGen (membraneStep U)`, the same relation,
`chronalMembrane_le`) and `x ≪_U y` iff a chain of future timelike segments inside `U` runs from `x`
to `y`, each of which, if it starts in `R̄ = {x¹ ≥ 0}`, ends in `R` (`chronalMembraneStep`). At
`U = M` that is the planner's rule (`chronalMembrane_lt_top_iff`). Every claim of the target is
proved; nothing is refuted. The full one-way Minkowski chronology (`x ∈ R → y ∈ R` in place of
`x ∈ R̄ → y ∈ R`) is no causality's `≪_M` (`not_exists_causality_naive_membrane_chronology`).

**`T-abs-one-way-membrane-chronal/1-causality`** — `chronalMembraneStep`, `chronalMembrane` (`I±_U`
open, transitive, inside `≤`, monotone), `chronalMembrane_lt_top_iff`,
`not_exists_causality_naive_membrane_chronology`.
**`T-abs-one-way-membrane-chronal/2-chronal-neighbours`** — `chronalMembrane_chronalNeighbours`.
**`T-abs-one-way-membrane-chronal/3-arc-connected`** — `chronalMembraneStep.chronalCurveOn`,
`chronalMembrane_causallyArcConnected` (both relations), `_causallyArcConnectedOn`,
`_absolutelyMinimal`, `_absolutelyMinimalOn` (every open set, every cover).
**`T-abs-one-way-membrane-chronal/4-tarentin`** — `chronalMembrane_tarentin`.
**`T-abs-one-way-membrane-chronal/5-causally-open-future`** — `chronalMembrane_causallyOpenFuture`,
`_locallyCausallyOpenFuture`, `_not_causallyOpenPast`, `_causallyOpenPastOn_iff`,
`_not_causallyOpen`, `_not_locallyCausallyOpen`.
**`T-abs-one-way-membrane-chronal/6-not-push-up`** — `chronalMembrane_not_pushUpOn` (no open set
meeting the membrane), `_not_pushUp`, `_not_locallyPushUp`; the other half at `M`,
`chronalMembrane_lt_le_top`.
**`T-abs-one-way-membrane-chronal/7-not-plain`** — `chronalMembrane_not_causallyPlain`.
**`T-abs-one-way-membrane-chronal/8-time-reversal`** — `chronalMembrane_dual_separates`,
`chronalMembrane_dual_absolutelyMinimalOn`.
**`T-abs-one-way-membrane-chronal/9-separation`** — `chronalMembrane_separates`,
`chronalMembrane_dual_separates`, `exists_chronalNeighbours_absolutelyMinimal_not_locallyPushUp`,
`not_locallyPushUp_of_chronalNeighbours_bare`, `not_causallyOpen_of_chronalNeighbours_bare`,
`not_causallyPlain_of_chronalNeighbours_bare`.

> The one-way membrane with a chronology: T-abs-one-way-membrane's ≤, and ≪_U by the timelike
> curves in U that respect the membrane, so that only left ≪ left, left ≪ membrane, left ≪ right,
> membrane ≪ right and right ≪ right occur (left = {x¹ < 0}, right = {x¹ > 0}).
> (`programme/roadmap.toml:926`, title)

> with the rule of the title, I⁺(m) = I⁺_Mink(m) ∩ right and I⁻(m) = I⁻_Mink(m) ∩ left at a membrane
> point m, I⁻(p) = I⁻_Mink(p) ∩ left for p left, I⁺(r) = I⁺_Mink(r) ∩ right for r right, and the
> full open cones otherwise (`programme/roadmap.toml:935`, evidence)

## Hypothesis checklist

| target claim | here |
|---|---|
| `I±_U` open, transitive, inside `≤`: a library `Causality` | ✓ proved, every field |
| chronal neighbours | ✓ proved: `v ∓ (r, r/2)` in a ball about `v` |
| causally arc-connected for both relations, absolutely minimal | ✓ proved, on every open set |
| tarentin | ✓ proved (`ChronalNeighbours.tarentin`) |
| causally open in the future, not in the past | ✓ proved (the same `J±` as the membrane) |
| neither push-up nor locally push-up | ✓ proved: `r ≤ v ≪ w`, not `r ≪ w`, at each membrane point |
| not causally plain | ✓ proved (`causal_ladder`: absolute minimality, T1) |
| the time reversal | ✓ proved, conjoined |

## SCOPE (disclosed)

* **Polygonal curves, and a reading of "respect the membrane".** The target says "the timelike
  curves in U that respect the membrane"; the Lean takes finite chains of future timelike segments.
  A timelike curve is read as respecting the membrane when, once it meets `R̄` at a parameter, it
  is in `R` at every later one (exactly the title's five pairs along the curve); along a segment
  `x¹` is affine, so for a chain this is the per-step condition (`pos_affine_of_nonneg`). The two
  give the same `≪_U` (an inscribed polygon of a timelike curve in `U` has timelike edges in `U`
  and the condition at its vertices), argued, not formalised: no model is importable in layer 1.
  The witness is the polygonal causality; its own chronal curves realise every `≪_U`.
* **Either reading.** Absolutely minimal on every open set for every cover (the gluing reading of
  `defi:causalite`, OQ-18), and a library causality: every separation holds in either reading.
* **Push-up.** The half `x ≪ y ≤ z ⇒ x ≪ z` holds at `U = M` (`chronalMembrane_lt_le_top`); in a
  general `U` it is not settled here. The half `x ≤ y ≪ z ⇒ x ≪ z` fails in every open set meeting
  the membrane; whether an open set missing it has push-up is not settled here.
* `ℝ × ℝ` is Hausdorff and second countable (mathlib instances). No metric notion is in a
  statement (coordinate inequalities, segments, the product order, `Opens`, ladder predicates);
  balls, a thickening of a compact segment and `dist` appear inside proofs only.
* Names checked unique against `Causal/`, the scaffold and `lean-gx`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation Filter

/-! ## The construction -/

/-- One chronal step of the membrane in `U`: a future timelike segment (strictly increasing in both
null coordinates) inside `U` which, if it starts in the closed right side `R̄ = {x¹ ≥ 0} = {v ≤ u}`,
ends in `R = {x¹ > 0}`. -/
def chronalMembraneStep (U : Opens (ℝ × ℝ)) (a b : ℝ × ℝ) : Prop :=
  (a.1 < b.1 ∧ a.2 < b.2) ∧ segment ℝ a b ⊆ (U : Set (ℝ × ℝ)) ∧
    (a.2 ≤ a.1 → b ∈ membraneRight)

variable {U V W : Opens (ℝ × ℝ)} {a b x y z : ℝ × ℝ}

/-- A chronal step is a causal step of the one-way membrane: `≪ ⊆ ≤` step by step. -/
theorem chronalMembraneStep.membraneStep (h : chronalMembraneStep U a b) :
    membraneStep U a b :=
  ⟨⟨h.1.1.le, h.1.2.le⟩, h.2.1, fun ha => h.2.2 (show a.2 < a.1 from ha).le⟩

/-- A segment inside an open set stays inside it when its second end moves a little: it lies in a
thickening of the compact segment `[a, b]`, inside the open set
(`IsCompact.exists_thickening_subset_open`), and `[a, b']` is within `dist b' b` of `[a, b]`. -/
theorem eventually_segment_subset_of_isOpen {O : Set (ℝ × ℝ)} (hO : IsOpen O)
    (h : segment ℝ a b ⊆ O) : ∀ᶠ b' in 𝓝 b, segment ℝ a b' ⊆ O := by
  have hK : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image]; exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open hO h
  filter_upwards [Metric.ball_mem_nhds b hδ] with b' hb'
  rintro w ⟨s, t, hs, ht, hst, rfl⟩
  refine hth (Metric.mem_thickening_iff.2 ⟨s • a + t • b, ⟨s, t, hs, ht, hst, rfl⟩, ?_⟩)
  rw [dist_add_left, dist_smul₀, Real.norm_of_nonneg ht]
  have hb'' : dist b' b < δ := hb'
  have ht1 : t ≤ 1 := by linarith
  calc t * dist b' b ≤ 1 * dist b' b := by gcongr
    _ < δ := by rw [one_mul]; exact hb''

/-- **The end of a chronal step can move**: the strict inequalities are open, the segment stays in
`U` (`eventually_segment_subset_of_isOpen`), and if the step starts in `R̄` its end is in `R`, which
is open. This makes `I⁺_U(x)` open. -/
theorem chronalMembraneStep.eventually_right (h : chronalMembraneStep U a b) :
    ∀ᶠ b' in 𝓝 b, chronalMembraneStep U a b' := by
  have h3 : ∀ᶠ b' in 𝓝 b, a.2 ≤ a.1 → b' ∈ membraneRight := by
    by_cases ha : a.2 ≤ a.1
    · filter_upwards [isOpen_membraneRight.mem_nhds (h.2.2 ha)] with b' hb' using fun _ => hb'
    · exact Eventually.of_forall fun _ h' => absurd h' ha
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds h.1.1,
    (isOpen_lt continuous_const continuous_snd).mem_nhds h.1.2, h3,
    eventually_segment_subset_of_isOpen U.isOpen h.2.1] with b' h1 h2 h3 h4
  exact ⟨⟨h1, h2⟩, h4, h3⟩

/-- **The start of a chronal step can move**: if the end is in `R` the side condition holds for
every start; if not, the start is in the open left side `{x¹ < 0}`, which is open. This makes
`I⁻_U(x)` open, and is where the full one-way chronology fails
(`not_exists_causality_naive_membrane_chronology`): with `x ∈ R → y ∈ R` a start on the membrane
has starts in `R` arbitrarily near it. -/
theorem chronalMembraneStep.eventually_left (h : chronalMembraneStep U a b) :
    ∀ᶠ a' in 𝓝 a, chronalMembraneStep U a' b := by
  have h3 : ∀ᶠ a' in 𝓝 a, a'.2 ≤ a'.1 → b ∈ membraneRight := by
    by_cases hb : b ∈ membraneRight
    · exact Eventually.of_forall fun _ _ => hb
    · have ha : a.1 < a.2 := not_le.1 fun h' => hb (h.2.2 h')
      filter_upwards [(isOpen_lt continuous_fst continuous_snd).mem_nhds ha] with a' ha' h'
      exact absurd h' (not_le.2 ha')
  have h4 : ∀ᶠ a' in 𝓝 a, segment ℝ a' b ⊆ (U : Set (ℝ × ℝ)) := by
    have := eventually_segment_subset_of_isOpen U.isOpen
      (show segment ℝ b a ⊆ (U : Set (ℝ × ℝ)) by rw [segment_symm]; exact h.2.1)
    filter_upwards [this] with a' ha'
    rw [segment_symm]; exact ha'
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds h.1.1,
    (isOpen_lt continuous_snd continuous_const).mem_nhds h.1.2, h3, h4] with a' h1 h2 h3 h4
  exact ⟨⟨h1, h2⟩, h4, h3⟩

/-- **The one-way membrane with a chronology**: the causal relation of `oneWayMembrane` (chains of
future causal segments in `U`, never passing from `R` into `L`), and `x ≪_U y` iff a chain of future
timelike segments in `U` runs from `x` to `y`, none starting in `R̄ = {x¹ ≥ 0}` without ending in
`R = {x¹ > 0}`: only left ≪ left, left ≪ membrane, left ≪ right, membrane ≪ right and
right ≪ right. -/
def chronalMembrane : Causality (ℝ × ℝ) where
  le U := TransGen (membraneStep U)
  lt U := TransGen (chronalMembraneStep U)
  le_mem_left := oneWayMembrane.le_mem_left
  le_mem_right := oneWayMembrane.le_mem_right
  lt_mem_left h := by
    obtain ⟨_, h, -⟩ := TransGen.head'_iff.1 h
    exact h.2.1 (left_mem_segment ℝ _ _)
  lt_mem_right h := by
    obtain ⟨_, -, h⟩ := TransGen.tail'_iff.1 h
    exact h.2.1 (right_mem_segment ℝ _ _)
  le_refl := oneWayMembrane.le_refl
  le_trans := oneWayMembrane.le_trans
  lt_trans h₁ h₂ := h₁.trans h₂
  le_mono := oneWayMembrane.le_mono
  lt_mono h _ _ h' := h'.mono fun _ _ hab => ⟨hab.1, hab.2.1.trans h, hab.2.2⟩
  le_of_lt h := h.mono fun _ _ hab => hab.membraneStep
  isOpen_lt_right U x := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨z, hxz, hzy⟩ := TransGen.tail'_iff.1 hy
    filter_upwards [hzy.eventually_right] with y' hy'
    exact TransGen.tail' hxz hy'
  isOpen_lt_left U x := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨z, hyz, hzx⟩ := TransGen.head'_iff.1 hy
    filter_upwards [hyz.eventually_left] with y' hy'
    exact TransGen.head' hy' hzx

/-- The same causal relation as the one-way membrane. -/
theorem chronalMembrane_le : chronalMembrane.le U x y ↔ oneWayMembrane.le U x y := Iff.rfl

/-- The chronology, unfolded. -/
theorem chronalMembrane_lt : chronalMembrane.lt U x y ↔ TransGen (chronalMembraneStep U) x y :=
  Iff.rfl

/-- **`≪_M` in closed form**: the open Minkowski cone, except that from `R̄ = {x¹ ≥ 0}` only points
of `R` are reached. At a membrane point `m`, `I⁺(m) = I⁺_Mink(m) ∩ R` and `I⁻(m) = I⁻_Mink(m) ∩ L°`;
for `p` with `x¹ < 0`, `I⁻(p) = I⁻_Mink(p) ∩ L°`; for `r ∈ R`, `I⁺(r) = I⁺_Mink(r) ∩ R`; the full
open cones otherwise (`L° = {x¹ < 0}`), as the planner's rule has it. -/
theorem chronalMembrane_lt_top_iff :
    chronalMembrane.lt ⊤ x y ↔ (x.1 < y.1 ∧ x.2 < y.2) ∧ (x.2 ≤ x.1 → y ∈ membraneRight) := by
  constructor
  · intro h
    have h' : TransGen (chronalMembraneStep ⊤) x y := h
    clear h
    induction h' with
    | single h => exact ⟨h.1, h.2.2⟩
    | tail _ h ih =>
      exact ⟨⟨ih.1.1.trans h.1.1, ih.1.2.trans h.1.2⟩,
        fun hx => h.2.2 (show _ < _ from ih.2 hx).le⟩
  · intro h
    exact TransGen.single ⟨h.1, fun _ _ => trivial, h.2⟩

/-- Along `≪_U`, the closed form of `≪_M` holds (`lt_mono` to `M`). -/
theorem chronalMembrane_lt_imp (h : chronalMembrane.lt U x y) :
    (x.1 < y.1 ∧ x.2 < y.2) ∧ (x.2 ≤ x.1 → y ∈ membraneRight) :=
  chronalMembrane_lt_top_iff.1 (chronalMembrane.lt_mono le_top h)

/-- The set `{y | y ≪_Mink (0, 1) ∧ (y ∈ R → (0, 1) ∈ R)}` is not open: it contains the membrane
point `(−1/2, −1/2)` and none of the points `(−1/2 + δ, −1/2)` of `R`. -/
theorem not_isOpen_naive_membrane_Iminus :
    ¬ IsOpen {y : ℝ × ℝ | (y.1 < 0 ∧ y.2 < 1) ∧
      (y ∈ membraneRight → ((0, 1) : ℝ × ℝ) ∈ membraneRight)} := by
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 h (-1 / 2, -1 / 2)
    ⟨⟨by norm_num, by norm_num⟩, fun h' => absurd (show (-1 / 2 : ℝ) < -1 / 2 from h')
      (lt_irrefl _)⟩
  have hw : ((-1 / 2 + min (ε / 2) (1 / 4), -1 / 2) : ℝ × ℝ) ∈
      Metric.ball ((-1 / 2, -1 / 2) : ℝ × ℝ) ε := by
    have hm : 0 < min (ε / 2) (1 / 4) := lt_min (by linarith) (by norm_num)
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt]
    refine ⟨⟨by linarith, by linarith [min_le_left (ε / 2) (1 / 4)]⟩, by linarith, by linarith⟩
  have hm : 0 < min (ε / 2) (1 / 4) := lt_min (by linarith) (by norm_num)
  have := (hball hw).2 (show (-1 / 2 : ℝ) < -1 / 2 + min (ε / 2) (1 / 4) by linarith)
  exact absurd (show (1 : ℝ) < 0 from this) (by norm_num)

/-- **The full one-way Minkowski chronology is no causality's `≪_M`**: with `x ≪ y` iff `x`
precedes `y` strictly in both null coordinates and `x ∈ R → y ∈ R`, `I⁻((0, 1))` is not open
(`not_isOpen_naive_membrane_Iminus`), against `Causality.isOpen_lt_left`. Hence the rule
`x ∈ R̄ → y ∈ R` of `chronalMembraneStep` (the planner's correction, confirmed). -/
theorem not_exists_causality_naive_membrane_chronology :
    ¬ ∃ C : Causality (ℝ × ℝ), ∀ x y : ℝ × ℝ, C.lt ⊤ x y ↔
      (x.1 < y.1 ∧ x.2 < y.2) ∧ (x ∈ membraneRight → y ∈ membraneRight) := by
  rintro ⟨C, hC⟩
  apply not_isOpen_naive_membrane_Iminus
  have e : {y : ℝ × ℝ | C.lt ⊤ y (0, 1)} = {y : ℝ × ℝ | (y.1 < 0 ∧ y.2 < 1) ∧
      (y ∈ membraneRight → ((0, 1) : ℝ × ℝ) ∈ membraneRight)} := by
    ext y
    exact hC y (0, 1)
  rw [← e]
  exact C.isOpen_lt_left ⊤ (0, 1)

/-! ## Chronal neighbours -/

/-- **The membrane with a chronology has chronal neighbours** (ladder `chronal_neighbours`): in a
ball of radius `ρ` about `v` inside `V`, `v − (ρ/2, ρ/4) ≪_V v ≪_V v + (ρ/2, ρ/4)` by one segment
each. The tilt to the right keeps the side condition at the membrane: `v − (ρ/2, ρ/4)` is in `R̄`
only if `v` is in `R`, and `v + (ρ/2, ρ/4)` is in `R` whenever `v` is in `R̄`. -/
theorem chronalMembrane_chronalNeighbours : chronalMembrane.ChronalNeighbours := by
  -- in a ball of radius `ρ` about `v`, the points `v ∓ (ρ/2, ρ/4)`
  have key : ∀ (V : Opens (ℝ × ℝ)) (v : ℝ × ℝ), v ∈ V → ∃ r > 0,
      chronalMembraneStep V (v.1 - r, v.2 - r / 2) v ∧
        chronalMembraneStep V v (v.1 + r, v.2 + r / 2) := by
    intro V v hv
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 V.isOpen v hv
    have hp : ((v.1 - ρ / 2, v.2 - ρ / 2 / 2) : ℝ × ℝ) ∈ Metric.ball v ρ := by
      simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    have hq : ((v.1 + ρ / 2, v.2 + ρ / 2 / 2) : ℝ × ℝ) ∈ Metric.ball v ρ := by
      simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt]
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    refine ⟨ρ / 2, by linarith, ⟨⟨by simp only; linarith, by simp only; linarith⟩,
      ((convex_ball v ρ).segment_subset hp (Metric.mem_ball_self hρ)).trans hball,
      fun h => ?_⟩, ⟨⟨by simp only; linarith, by simp only; linarith⟩,
      ((convex_ball v ρ).segment_subset (Metric.mem_ball_self hρ) hq).trans hball,
      fun h => ?_⟩⟩
    · have h' : v.2 - ρ / 2 / 2 ≤ v.1 - ρ / 2 := h
      show v.2 < v.1
      linarith
    · show v.2 + ρ / 2 / 2 < v.1 + ρ / 2
      linarith
  refine ⟨fun V v hv => ?_, fun V v hv => ?_⟩
  · obtain ⟨r, -, h1, -⟩ := key V v hv
    exact ⟨_, h1.2.1 (left_mem_segment ℝ _ _), TransGen.single h1⟩
  · obtain ⟨r, -, -, h2⟩ := key V v hv
    exact ⟨_, h2.2.1 (right_mem_segment ℝ _ _), TransGen.single h2⟩

/-! ## Causal arc-connectedness -/

/-- Along a segment the coordinate `x¹` is affine: if `0 ≤ d_a → 0 < d_b`, then on `[0, 1]` the
affine function `d_a + r (d_b − d_a)`, once non-negative, is positive at every later parameter. -/
theorem pos_affine_of_nonneg {da db s s' : ℝ} (hab : 0 ≤ da → 0 < db) (hs : 0 ≤ s)
    (hss' : s < s') (hs' : s' ≤ 1) (h : 0 ≤ da + s * (db - da)) : 0 < da + s' * (db - da) := by
  by_cases hdb : 0 < db
  · -- `(1 - s) d(s') = (1 - s') d(s) + (s' - s) d_b`
    have h1s : 0 < 1 - s := by linarith
    have e : (1 - s) * (da + s' * (db - da)) =
        (1 - s') * (da + s * (db - da)) + (s' - s) * db := by ring
    have hpos : 0 < (1 - s') * (da + s * (db - da)) + (s' - s) * db :=
      add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) h) (mul_pos (by linarith) hdb)
    rw [← e] at hpos
    exact pos_of_mul_pos_right hpos h1s.le
  · push Not at hdb
    have hda : da < 0 := not_le.1 fun h' => absurd (hab h') (not_lt.2 hdb)
    -- `d(s) = (1 - s) d_a + s d_b < 0` for `s < 1`
    have : da + s * (db - da) < 0 := by
      have e : da + s * (db - da) = (1 - s) * da + s * db := by ring
      rw [e]
      have : (1 - s) * da < 0 := mul_neg_of_pos_of_neg (by linarith) hda
      nlinarith [mul_nonneg hs (neg_nonneg.2 hdb)]
    linarith

/-- A chronal step is realised by its affine parametrisation, a chronal curve of the membrane: near
each parameter the curve stays in a small ball inside the given open set, convex, and a sub-segment
of a chronal step is a chronal step (`pos_affine_of_nonneg` for the side condition). -/
theorem chronalMembraneStep.chronalCurveOn (h : chronalMembraneStep U a b) :
    chronalMembrane.ChronalCurveOn U (fun r => a + r • (b - a)) 0 1 := by
  have hseg : ∀ r ∈ Icc (0 : ℝ) 1, a + r • (b - a) ∈ segment ℝ a b := fun r hr =>
    ⟨1 - r, r, by linarith [hr.2], hr.1, by ring, by ext <;> simp <;> ring⟩
  have hcont : Continuous fun r : ℝ => a + r • (b - a) := by fun_prop
  refine ⟨fun t ht => h.2.1 (hseg t ht), fun t _ N _ htN => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 N.isOpen _ htN
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1
    (hcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ))
  refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => TransGen.single ⟨?_, ?_, ?_⟩⟩
  · have e1 := mul_lt_mul_of_pos_right h2 (sub_pos.2 h.1.1)
    have e2 := mul_lt_mul_of_pos_right h2 (sub_pos.2 h.1.2)
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  · exact ((convex_ball _ _).segment_subset (hlu ⟨h1, h2.trans h3⟩)
      (hlu ⟨h1.trans h2, h3⟩)).trans hball
  · intro hR
    have hab : 0 ≤ a.1 - a.2 → 0 < b.1 - b.2 := fun ha =>
      sub_pos.2 (h.2.2 (sub_nonneg.1 ha))
    have e : ∀ r : ℝ, (a + r • (b - a)).1 - (a + r • (b - a)).2 =
        (a.1 - a.2) + r * ((b.1 - b.2) - (a.1 - a.2)) := fun r => by simp; ring
    have hR' : 0 ≤ (a.1 - a.2) + s * ((b.1 - b.2) - (a.1 - a.2)) := by
      rw [← e]; exact sub_nonneg.2 hR
    have := pos_affine_of_nonneg hab hs.1 h2 hs'.2 hR'
    rw [← e] at this
    exact sub_pos.1 this

/-- **The membrane with a chronology is causally arc-connected** (`def:causal_arc_connectedness`),
for both relations: `≤` by the one-way membrane's causal curves (the same `≤`), `≪` by the
concatenation of the affine curves of a chain of chronal steps (`CurveOn.exists_concat`). -/
theorem chronalMembrane_causallyArcConnected : chronalMembrane.CausallyArcConnected := by
  rw [Causality.CausallyArcConnected, Causality.causallyArcConnectedOn_iff]
  intro U _ p q
  refine ⟨fun hpq => ?_, fun hpq => ?_⟩
  · exact (Causality.causallyArcConnectedOn_iff.1 oneWayMembrane_causallyArcConnected
      U le_top p q).1 hpq
  · have hpq' : TransGen (chronalMembraneStep U) p q := hpq
    clear hpq
    induction hpq' with
    | single h => exact ⟨_, h.chronalCurveOn, by simp, by simp⟩
    | tail _ h ih =>
      obtain ⟨c₁, hc₁, h0, h1⟩ := ih
      obtain ⟨c, hc, hc0, hc1⟩ := CurveOn.exists_concat chronalMembrane.isRelFamily_lt hc₁
        h.chronalCurveOn (by simp [h1])
      exact ⟨c, hc, hc0.trans h0, by simpa using hc1⟩

/-- Causally arc-connected on every open set (`rem:cac_local`). -/
theorem chronalMembrane_causallyArcConnectedOn (W : Opens (ℝ × ℝ)) :
    chronalMembrane.CausallyArcConnectedOn W :=
  Causality.CausallyArcConnectedOn.mono chronalMembrane_causallyArcConnected le_top

/-- **Absolutely minimal** (`cor:causalement_connexe_minimal`). -/
theorem chronalMembrane_absolutelyMinimal : chronalMembrane.AbsolutelyMinimal :=
  chronalMembrane_causallyArcConnected.absolutelyMinimal

/-- Absolutely minimal on every open set, for every cover of it (the gluing reading of
`defi:causalite`, OQ-18). -/
theorem chronalMembrane_absolutelyMinimalOn (W : Opens (ℝ × ℝ)) :
    chronalMembrane.AbsolutelyMinimalOn W :=
  (chronalMembrane_causallyArcConnectedOn W).absolutelyMinimalOn

/-! ## Tarentin; causal openness in the future, not in the past -/

/-- **Tarentin** (`def:tarentin_spacetime`), from chronal neighbours
(`ChronalNeighbours.tarentin`). -/
theorem chronalMembrane_tarentin : chronalMembrane.Tarentin :=
  chronalMembrane_chronalNeighbours.tarentin

/-- **Causally open in the future** (`def:causally_open_spacetime_open` as printed): `J⁺` reads `≤`
only, which is the one-way membrane's (`oneWayMembrane_causallyOpenFuture`). -/
theorem chronalMembrane_causallyOpenFuture : chronalMembrane.CausallyOpenFuture :=
  oneWayMembrane_causallyOpenFuture

/-- Locally causally open in the future. -/
theorem chronalMembrane_locallyCausallyOpenFuture :
    chronalMembrane.LocallyCausallyOpenFuture :=
  chronalMembrane_causallyOpenFuture.locallyCausallyOpenFuture

/-- **Not causally open in the past** (`oneWayMembrane_not_causallyOpenPast`, the same `J⁻`). -/
theorem chronalMembrane_not_causallyOpenPast : ¬ chronalMembrane.dual.CausallyOpenFuture :=
  oneWayMembrane_not_causallyOpenPast

/-- An open set is causally open in the past iff it misses the membrane. -/
theorem chronalMembrane_causallyOpenPastOn_iff :
    chronalMembrane.dual.CausallyOpenFutureOn W ↔ ∀ z ∈ W, z.1 ≠ z.2 :=
  oneWayMembrane_causallyOpenPastOn_iff

/-- **Not causally open** (DEC-8's two-sided reading). -/
theorem chronalMembrane_not_causallyOpen : ¬ chronalMembrane.CausallyOpen :=
  fun h => chronalMembrane_not_causallyOpenPast h.2

/-- Not locally causally open (two-sided): no open set about `(0, 0)` is causally open in the
past. -/
theorem chronalMembrane_not_locallyCausallyOpen : ¬ chronalMembrane.LocallyCausallyOpen :=
  oneWayMembrane_not_locallyCausallyOpen

/-! ## Push-up fails, at the membrane -/

/-- **The first half of push-up holds at `M`**: `x ≪_M y ≤_M z ⇒ x ≪_M z` (from `R̄` the chronology
lands in `R`, and `≤` never leaves `R`). It is the other half that fails. -/
theorem chronalMembrane_lt_le_top (h₁ : chronalMembrane.lt ⊤ x y)
    (h₂ : chronalMembrane.le ⊤ y z) : chronalMembrane.lt ⊤ x z := by
  obtain ⟨⟨h1, h2⟩, hR⟩ := chronalMembrane_lt_top_iff.1 h₁
  obtain ⟨⟨h3, h4⟩, hR'⟩ := oneWayMembrane_le_top_iff.1 h₂
  exact chronalMembrane_lt_top_iff.2 ⟨⟨h1.trans_le h3, h2.trans_le h4⟩, fun hx => hR' (hR hx)⟩

/-- **No open set meeting the membrane has push-up** (its half `x ≤ y ≪ z ⇒ x ≪ z`): at a membrane
point `m` with a ball of radius `r` in `W`, `m ≤_W (m.1, m.2 + r/2) ≪_W (m.1 + r/4, m.2 + 3r/4)`
(a null segment into the open left side, then a timelike one inside it), while `m ∈ R̄` is
chronologically followed only by points of `R`. -/
theorem chronalMembrane_not_pushUpOn {m : ℝ × ℝ} (hm : m ∈ W) (hm' : m.1 = m.2) :
    ¬ chronalMembrane.PushUpOn W := by
  intro h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 W.isOpen m hm
  have hy : ((m.1, m.2 + r / 2) : ℝ × ℝ) ∈ Metric.ball m r := by
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hz : ((m.1 + r / 4, m.2 + 3 * r / 4) : ℝ × ℝ) ∈ Metric.ball m r := by
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  -- `m ≤_W y`: a null segment from the membrane into the open left side
  have hmy : chronalMembrane.le W m (m.1, m.2 + r / 2) :=
    TransGen.single ⟨⟨le_rfl, by linarith⟩,
      ((convex_ball m r).segment_subset (Metric.mem_ball_self hr) hy).trans hball,
      fun h => absurd (show m.2 < m.1 from h) (by rw [hm']; exact lt_irrefl _)⟩
  -- `y ≪_W z`: a timelike segment inside the open left side
  have hyz : chronalMembrane.lt W (m.1, m.2 + r / 2) (m.1 + r / 4, m.2 + 3 * r / 4) :=
    TransGen.single ⟨⟨by simp only; linarith, by simp only; linarith⟩,
      ((convex_ball m r).segment_subset hy hz).trans hball, fun h => by
        exfalso
        have h' : m.2 + r / 2 ≤ m.1 := h
        linarith⟩
  -- `m ≪_W z` would put `z` on the right
  have hmz := (h W le_rfl).2 hmy hyz
  have hzR : m.2 + 3 * r / 4 < m.1 + r / 4 := (chronalMembrane_lt_imp hmz).2 (by rw [hm'])
  linarith

/-- **No push-up**, by the ladder read backwards: push-up and chronal neighbours would give causal
openness (`PushUp.causallyOpen_of_chronalNeighbours`), which fails. -/
theorem chronalMembrane_not_pushUp : ¬ chronalMembrane.PushUp := by
  intro h
  have hN := chronalMembrane_chronalNeighbours
  exact chronalMembrane_not_causallyOpen (by causal_ladder)

/-- **Not locally push-up**: no open neighbourhood of `(0, 0)` has push-up. -/
theorem chronalMembrane_not_locallyPushUp : ¬ chronalMembrane.LocallyPushUp := fun h =>
  let ⟨_, hW, hW'⟩ := h (0, 0)
  chronalMembrane_not_pushUpOn hW rfl hW'

/-- **Not causally plain**, by the ladder read backwards: on a T1 space absolute minimality and
plainness give push-up (`pushUp_of_causallyPlain_of_absolutelyMinimal`), which fails. -/
theorem chronalMembrane_not_causallyPlain : ¬ chronalMembrane.CausallyPlain := by
  intro h
  have hmin := chronalMembrane_absolutelyMinimal
  exact chronalMembrane_not_pushUp (by causal_ladder)

/-! ## The other ladder properties, read off `≤` -/

/-- Causal (the one-way membrane's `≤`). -/
theorem chronalMembrane_isCausal : chronalMembrane.IsCausal :=
  oneWayMembrane_isCausal

/-- Strongly causal with open causally convex neighbourhoods (the one-way membrane's `≤`). -/
theorem chronalMembrane_stronglyCausalOpen : chronalMembrane.StronglyCausalOpen :=
  oneWayMembrane_stronglyCausalOpen

/-- A time function, `u + v = 2t` (the one-way membrane's `≤`). -/
theorem chronalMembrane_hasTimeFunction : chronalMembrane.HasTimeFunction :=
  oneWayMembrane_hasTimeFunction

/-- Not causally compact (the one-way membrane's diamonds). -/
theorem chronalMembrane_not_causallyCompact : ¬ chronalMembrane.CausallyCompact :=
  oneWayMembrane_not_causallyCompact

/-! ## The separations -/

/-- **The membrane with a chronology, conjoined for the ladder**: chronal neighbours, absolutely
minimal, causally arc-connected, tarentin, causally open in the future (hence locally), causal,
strongly causal (both forms), a time function (hence curves extend); neither causally open nor
locally so, neither push-up nor locally push-up, not causally plain, not causally compact (so not
globally hyperbolic). -/
theorem chronalMembrane_separates :
    chronalMembrane.ChronalNeighbours ∧ chronalMembrane.AbsolutelyMinimal ∧
      chronalMembrane.CausallyArcConnected ∧ chronalMembrane.Tarentin ∧
      chronalMembrane.CausallyOpenFuture ∧ chronalMembrane.LocallyCausallyOpenFuture ∧
      chronalMembrane.IsCausal ∧ chronalMembrane.StronglyCausalOpen ∧
      chronalMembrane.StronglyCausal ∧ chronalMembrane.HasTimeFunction ∧
      chronalMembrane.CurvesExtend ∧
      ¬ chronalMembrane.CausallyOpen ∧ ¬ chronalMembrane.LocallyCausallyOpen ∧
      ¬ chronalMembrane.PushUp ∧ ¬ chronalMembrane.LocallyPushUp ∧
      ¬ chronalMembrane.CausallyPlain ∧ ¬ chronalMembrane.CausallyCompact ∧
      ¬ chronalMembrane.GloballyHyperbolic :=
  ⟨chronalMembrane_chronalNeighbours, chronalMembrane_absolutelyMinimal,
    chronalMembrane_causallyArcConnected, chronalMembrane_tarentin,
    chronalMembrane_causallyOpenFuture, chronalMembrane_locallyCausallyOpenFuture,
    chronalMembrane_isCausal, chronalMembrane_stronglyCausalOpen,
    chronalMembrane_stronglyCausalOpen.stronglyCausal, chronalMembrane_hasTimeFunction,
    chronalMembrane_hasTimeFunction.curvesExtend,
    chronalMembrane_not_causallyOpen, chronalMembrane_not_locallyCausallyOpen,
    chronalMembrane_not_pushUp, chronalMembrane_not_locallyPushUp,
    chronalMembrane_not_causallyPlain, chronalMembrane_not_causallyCompact,
    fun h => chronalMembrane_not_causallyCompact h.causallyCompact⟩

/-- **Its time reversal, conjoined for the ladder**: chronal neighbours, absolutely minimal,
causally arc-connected, tarentin, causal, strongly causal (both forms), a time function (hence
curves extend); not causally open in the future, nor locally, nor two-sided, nor locally two-sided,
neither push-up nor locally push-up, not causally plain, not causally compact (so not globally
hyperbolic). The negations by `causal_ladder` on `C.dual` from `¬ C.dual.CausallyOpenFuture`
(kb/0091). -/
theorem chronalMembrane_dual_separates :
    chronalMembrane.dual.ChronalNeighbours ∧ chronalMembrane.dual.AbsolutelyMinimal ∧
      chronalMembrane.dual.CausallyArcConnected ∧ chronalMembrane.dual.Tarentin ∧
      chronalMembrane.dual.IsCausal ∧ chronalMembrane.dual.StronglyCausalOpen ∧
      chronalMembrane.dual.StronglyCausal ∧ chronalMembrane.dual.HasTimeFunction ∧
      chronalMembrane.dual.CurvesExtend ∧
      ¬ chronalMembrane.dual.CausallyOpenFuture ∧
      ¬ chronalMembrane.dual.LocallyCausallyOpenFuture ∧
      ¬ chronalMembrane.dual.CausallyOpen ∧ ¬ chronalMembrane.dual.LocallyCausallyOpen ∧
      ¬ chronalMembrane.dual.PushUp ∧ ¬ chronalMembrane.dual.LocallyPushUp ∧
      ¬ chronalMembrane.dual.CausallyPlain ∧ ¬ chronalMembrane.dual.CausallyCompact ∧
      ¬ chronalMembrane.dual.GloballyHyperbolic := by
  have hN : chronalMembrane.dual.ChronalNeighbours :=
    Causality.dual_chronalNeighbours.2 chronalMembrane_chronalNeighbours
  have hcac : chronalMembrane.dual.CausallyArcConnected :=
    Causality.dual_causallyArcConnectedOn.2 chronalMembrane_causallyArcConnected
  have hmin : chronalMembrane.dual.AbsolutelyMinimal := hcac.absolutelyMinimal
  have hT : chronalMembrane.dual.Tarentin := hN.tarentin
  have hcausal : chronalMembrane.dual.IsCausal :=
    Causality.dual_isCausal.2 chronalMembrane_isCausal
  have hsco : chronalMembrane.dual.StronglyCausalOpen :=
    Causality.dual_stronglyCausalOpen.2 chronalMembrane_stronglyCausalOpen
  have htf : chronalMembrane.dual.HasTimeFunction := oneWayMembrane_dual_hasTimeFunction
  have hnof : ¬ chronalMembrane.dual.CausallyOpenFuture := chronalMembrane_not_causallyOpenPast
  -- the rest by the ladder, read backwards on `C.dual` (kb/0080, kb/0091)
  have hnolf : ¬ chronalMembrane.dual.LocallyCausallyOpenFuture := fun h => hnof (by causal_ladder)
  have hnoc : ¬ chronalMembrane.dual.CausallyOpen := fun h => hnof (by causal_ladder)
  have hnolc : ¬ chronalMembrane.dual.LocallyCausallyOpen := fun h => hnolf (by causal_ladder)
  have hnpu : ¬ chronalMembrane.dual.PushUp := fun h => hnoc (by causal_ladder)
  have hnlpu : ¬ chronalMembrane.dual.LocallyPushUp := fun h => hnpu (by causal_ladder)
  have hnpl : ¬ chronalMembrane.dual.CausallyPlain := fun h => hnpu (by causal_ladder)
  have hncc : ¬ chronalMembrane.dual.CausallyCompact := fun h =>
    chronalMembrane_not_causallyCompact (Causality.dual_causallyCompact.1 h)
  have hngh : ¬ chronalMembrane.dual.GloballyHyperbolic := fun h => hncc (by causal_ladder)
  exact ⟨hN, hmin, hcac, hT, hcausal, hsco, hsco.stronglyCausal, htf, htf.curvesExtend, hnof,
    hnolf, hnoc, hnolc, hnpu, hnlpu, hnpl, hncc, hngh⟩

/-- The time reversal is absolutely minimal on every open set, for every cover of it. -/
theorem chronalMembrane_dual_absolutelyMinimalOn (W : Opens (ℝ × ℝ)) :
    chronalMembrane.dual.AbsolutelyMinimalOn W :=
  (Causality.CausallyArcConnectedOn.mono
    (Causality.dual_causallyArcConnectedOn.2 chronalMembrane_causallyArcConnected)
    le_top).absolutelyMinimalOn

/-- **Chronal neighbours and absolute minimality, in either reading, give neither local push-up nor
causal plainness nor local causal openness**: a causality absolutely minimal on every open set for
every cover (the gluing reading of `defi:causalite`, OQ-18, as well as the library's), causally
arc-connected, with chronal neighbours, causally open in the future, and neither locally push-up,
nor causally plain, nor locally causally open, nor causally open in the past. -/
theorem exists_chronalNeighbours_absolutelyMinimal_not_locallyPushUp :
    ∃ C : Causality (ℝ × ℝ), (∀ W : Opens (ℝ × ℝ), C.AbsolutelyMinimalOn W) ∧
      C.CausallyArcConnected ∧ C.ChronalNeighbours ∧ C.CausallyOpenFuture ∧
      ¬ C.LocallyPushUp ∧ ¬ C.CausallyPlain ∧ ¬ C.LocallyCausallyOpen ∧
      ¬ C.dual.CausallyOpenFuture :=
  ⟨chronalMembrane, chronalMembrane_absolutelyMinimalOn, chronalMembrane_causallyArcConnected,
    chronalMembrane_chronalNeighbours, chronalMembrane_causallyOpenFuture,
    chronalMembrane_not_locallyPushUp, chronalMembrane_not_causallyPlain,
    chronalMembrane_not_locallyCausallyOpen, chronalMembrane_not_causallyOpenPast⟩

/-- **Chronal neighbours and causal arc-connectedness do not give local push-up.** -/
theorem not_locallyPushUp_of_chronalNeighbours_bare :
    ¬ ∀ C : Causality (ℝ × ℝ), C.CausallyArcConnected → C.ChronalNeighbours →
      C.LocallyPushUp := fun h =>
  chronalMembrane_not_locallyPushUp
    (h _ chronalMembrane_causallyArcConnected chronalMembrane_chronalNeighbours)

/-- **Chronal neighbours and causal arc-connectedness do not give causal openness, not even
locally** (two-sided); with the time reversal, not even in the future
(`chronalMembrane_dual_separates`). -/
theorem not_causallyOpen_of_chronalNeighbours_bare :
    ¬ ∀ C : Causality (ℝ × ℝ), C.CausallyArcConnected → C.ChronalNeighbours →
      C.LocallyCausallyOpen := fun h =>
  chronalMembrane_not_locallyCausallyOpen
    (h _ chronalMembrane_causallyArcConnected chronalMembrane_chronalNeighbours)

/-- **Chronal neighbours and causal arc-connectedness do not give causal plainness.** -/
theorem not_causallyPlain_of_chronalNeighbours_bare :
    ¬ ∀ C : Causality (ℝ × ℝ), C.CausallyArcConnected → C.ChronalNeighbours →
      C.CausallyPlain := fun h =>
  chronalMembrane_not_causallyPlain
    (h _ chronalMembrane_causallyArcConnected chronalMembrane_chronalNeighbours)

end Causal
