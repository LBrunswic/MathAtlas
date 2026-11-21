import Causal.OneWayMembraneChronal
import Causal.Ladder.Rules
import Mathlib.NumberTheory.Real.Irrational

/-!
# The rational-jump plane: an absolutely minimal causality with chronal neighbours that is not causally arc-connected

Programme target `T-abs-chronal-not-arc-connected` (`programme/roadmap.toml:1045`; layer 1, no
label of `ETT.tex`). Imports: `Causal.OneWayMembraneChronal` (for
`eventually_segment_subset_of_isOpen`), `Causal.Ladder.Rules` (the `causal_ladder` tactic),
`Mathlib.NumberTheory.Real.Irrational`; ETT layer: no model, no CBG, Splitting, LemmaK* or
LevinUtility module, transitively. On `ℝ^{1+1}` in the coordinates `(t, x)` (`p.1 = t`,
`p.2 = x`), the **rational-jump plane** `rationalJumpPlane` has `x ≪_U y` iff a chain of future
timelike segments (`|Δx| < Δt`) inside `U` runs from `x` to `y` (Minkowski's chronology), and
`x ≤_U y` iff a chain runs from `x` to `y` whose steps are future causal segments (`|Δx| ≤ Δt`)
inside `U` or rational jumps `(t, q) → (t, q')`, `q < q'` rational, `{t} × [q, q'] ⊆ U`. The
planner's sketch is confirmed in every part; nothing is refuted and the model is unchanged.

**`T-abs-chronal-not-arc-connected/1-causality`** — `rationalJumpPlane`; `rationalJumpPlane_lt_imp`
(`≪` inside Minkowski's chronology), `rationalJumpPlane_le_imp` (`t` and `t + x` do not decrease
along `≤`; at equal `t`, equal points or a rational jump).
**`T-abs-chronal-not-arc-connected/2-absolutely-minimal`** — `transGen_of_segment_subdivision`
(equal subdivision at the rational parameters `k/n`, below a Lebesgue number),
`rationalJumpPlane_absolutelyMinimalOn` (every open set, every cover),
`rationalJumpPlane_absolutelyMinimal`.
**`T-abs-chronal-not-arc-connected/3-chronal-neighbours`** — `rationalJumpPlane_chronalNeighbours`,
`rationalJumpPlane_tarentin`.
**`T-abs-chronal-not-arc-connected/4-time-function`** — `rationalJumpPlane_hasTimeFunction`
(`2t + x`), `rationalJumpPlane_isCausal`.
**`T-abs-chronal-not-arc-connected/5-not-arc-connected`** — `rationalJumpPlane_le_zero_one`,
`rationalJumpPlane_causalCurveOn_eq` (a causal curve with equal `t` at its ends is constant),
`rationalJumpPlane_not_exists_causalCurveOn`, `rationalJumpPlane_zero_one_separates`,
`rationalJumpPlane_not_causallyArcConnected`; on no non-empty open set
(`rationalJumpPlane_not_causallyArcConnectedOn`), not locally
(`rationalJumpPlane_not_locallyCausallyArcConnected`).
**`T-abs-chronal-not-arc-connected/6-not-push-up`** — `rationalJumpPlane_not_pushUpOn` (no non-empty
open set), `rationalJumpPlane_not_pushUp`, `_not_locallyPushUp`, `_not_causallyPlain`.
**`T-abs-chronal-not-arc-connected/7-ladder`** — beyond the target: causally open in the future
and in the past (`rationalJumpPlane_causallyOpen`, chains moved along the time axis,
`rationalJumpPlane_le_eventually_shift`), strongly causal with open causally convex boxes
(`rationalJumpPlane_stronglyCausalOpen`), not causally compact
(`rationalJumpPlane_not_causallyCompact`).
**`T-abs-chronal-not-arc-connected/8-separation`** — `rationalJumpPlane_separates` (the keeper's
conjoined witness), `exists_chronalNeighbours_absolutelyMinimal_not_causallyArcConnected`, and the
bare forms `not_causallyArcConnected_of_chronalNeighbours_bare`,
`not_locallyPushUp_of_chronalNeighbours_causallyOpen_bare`,
`not_causallyPlain_of_chronalNeighbours_causallyOpen_bare`.

> An absolutely minimal causality with chronal neighbours that is not causally arc-connected, in
> either reading: the rational-jump plane. On ℝ^{1+1}, Minkowski's chronology (chains of timelike
> segments in U); as causal steps, the causal segments in U and the horizontal jumps
> (t, q) → (t, q'), q < q' rational, {t} × [q, q'] ⊆ U. It is absolutely minimal on every open
> set, has chronal neighbours (hence is tarentin), is causal and has a time function; (0, 0) ≤
> (0, 1) is joined by no causal curve; it is not push-up (`programme/roadmap.toml:1046`)

> (v) It is not causally arc-connected. t is non-decreasing along ≤, so a causal curve from (0, 0)
> to (0, 1) stays on t = 0. There the only non-trivial steps are jumps, which start at rational x
> (`programme/roadmap.toml:1055`, evidence)

> $M$ is causally arc-connected if for every open subset $\U$ and all $p,q\in \U$ the following are
> equivalent: (i) $p\leq_\U q$ (resp. $p\ll_\U q$); (ii) there exists a future causal (resp. future
> chronal) curve $c:[0,1]\rightarrow \U$ with $c(0)=p$ and $c(1)=q$.
> (`def:causal_arc_connectedness`, `ETT.tex:403–409`)

## Hypothesis checklist

| target claim | here |
|---|---|
| a causality (`I^±_U` Minkowski's, open; `≪ ⊆ ≤`; concatenation) | ✓ proved, every field of `Causality` |
| absolutely minimal on every open set (Lebesgue number, rational nodes) | ✓ proved, for every cover of every open set |
| chronal neighbours `(t ∓ ε, x)`, hence tarentin | ✓ proved |
| `T = t + x/2` a time function, hence causal | ✓ proved, with `2t + x` |
| `(0, 0) ≤ (0, 1)` and no causal curve joins them | ✓ proved, in every open set and over every segment `[s₀, s₁]` |
| not push-up: `(0, 0) ≤ (0, 1) ≪ (1, 3/2)` | ✓ proved, with a triple in every non-empty open set |

## SCOPE (disclosed)

* The target defines both relations by chains of segments, and the Lean takes them so (polygonal
  chains). For `≪` this is Minkowski's chronology of `U`, argued, not formalised: no Minkowski
  model may be imported in layer 1. The witness is the causality as the target defines it.
* **Either reading.** Absolutely minimal on every open set for every cover of it
  (`rationalJumpPlane_absolutelyMinimalOn`, the gluing reading of `defi:causalite`, OQ-18) and a
  library causality: every separation here holds in either reading.
* (v) is proved by the rational line's argument (`rationalLine_causalCurveOn_eq`,
  `Causal/NestedConverse.lean:279`: an irrational value between two values of `x` is taken by the
  intermediate value theorem), not by the evidence's last-parameter argument. Both work.
* Its time reversal is, argued, the image of the plane under the point reflection
  `(t, x) ↦ (−t, −x)` (a reversed step, reflected, keeps its displacement; a reflected jump runs
  from `−q'` to `−q`), so it has the same ladder properties; it is not stated in Lean.
* `ℝ × ℝ` is Hausdorff and second countable (mathlib instances). No metric notion is in a
  statement (coordinate inequalities, segments, `ℚ`, the ladder predicates); a Lebesgue number,
  balls, `dist` and a thickening of a compact segment appear inside proofs only.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation Filter

/-! ## The construction -/

/-- A future causal displacement of the Minkowski cone of `ℝ^{1+1}` in the coordinates `(t, x)`:
`|x_b − x_a| ≤ t_b − t_a`, written as two coordinate inequalities. -/
def RationalJumpCausal (a b : ℝ × ℝ) : Prop :=
  a.2 - b.2 ≤ b.1 - a.1 ∧ b.2 - a.2 ≤ b.1 - a.1

/-- A future timelike displacement: `|x_b − x_a| < t_b − t_a`. -/
def RationalJumpChronal (a b : ℝ × ℝ) : Prop :=
  a.2 - b.2 < b.1 - a.1 ∧ b.2 - a.2 < b.1 - a.1

/-- A rational jump `(t, q) → (t, q')`, `q < q'` both rational. -/
def IsRationalJump (a b : ℝ × ℝ) : Prop :=
  a.1 = b.1 ∧ a.2 < b.2 ∧ a.2 ∈ range ((↑) : ℚ → ℝ) ∧ b.2 ∈ range ((↑) : ℚ → ℝ)

/-- One causal step of the rational-jump plane in `U`: a future causal segment or a rational
jump, the segment `[a, b]` inside `U`. -/
def rationalJumpStep (U : Opens (ℝ × ℝ)) (a b : ℝ × ℝ) : Prop :=
  (RationalJumpCausal a b ∨ IsRationalJump a b) ∧ segment ℝ a b ⊆ (U : Set (ℝ × ℝ))

/-- One chronal step in `U`: a future timelike segment inside `U`. -/
def rationalJumpChronalStep (U : Opens (ℝ × ℝ)) (a b : ℝ × ℝ) : Prop :=
  RationalJumpChronal a b ∧ segment ℝ a b ⊆ (U : Set (ℝ × ℝ))

variable {U V W : Opens (ℝ × ℝ)} {a b c x y z : ℝ × ℝ}

/-- A timelike displacement is causal: `≪ ⊆ ≤` step by step. -/
theorem RationalJumpChronal.causal (h : RationalJumpChronal a b) : RationalJumpCausal a b :=
  ⟨h.1.le, h.2.le⟩

/-- Timelike displacements add up: the open Minkowski cone is convex. -/
theorem RationalJumpChronal.trans (h₁ : RationalJumpChronal a b) (h₂ : RationalJumpChronal b c) :
    RationalJumpChronal a c :=
  ⟨by linarith [h₁.1, h₂.1], by linarith [h₁.2, h₂.2]⟩

/-- Two rational jumps at one time make a rational jump. -/
theorem IsRationalJump.trans (h₁ : IsRationalJump a b) (h₂ : IsRationalJump b c) :
    IsRationalJump a c :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1, h₂.2.2.2⟩

/-- **The end of a chronal step can move**: the strict inequalities are open, and the segment stays
in `U` (`eventually_segment_subset_of_isOpen`). This makes `I⁺_U(x)` open. -/
theorem rationalJumpChronalStep.eventually_right (h : rationalJumpChronalStep U a b) :
    ∀ᶠ b' in 𝓝 b, rationalJumpChronalStep U a b' := by
  have h1 : ∀ᶠ b' in 𝓝 b, a.2 - b'.2 < b'.1 - a.1 :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds h.1.1
  have h2 : ∀ᶠ b' in 𝓝 b, b'.2 - a.2 < b'.1 - a.1 :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds h.1.2
  filter_upwards [h1, h2, eventually_segment_subset_of_isOpen U.isOpen h.2] with b' h1 h2 h3
  exact ⟨⟨h1, h2⟩, h3⟩

/-- **The start of a chronal step can move**, likewise: `I⁻_U(x)` is open. -/
theorem rationalJumpChronalStep.eventually_left (h : rationalJumpChronalStep U a b) :
    ∀ᶠ a' in 𝓝 a, rationalJumpChronalStep U a' b := by
  have h1 : ∀ᶠ a' in 𝓝 a, a'.2 - b.2 < b.1 - a'.1 :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds h.1.1
  have h2 : ∀ᶠ a' in 𝓝 a, b.2 - a'.2 < b.1 - a'.1 :=
    (isOpen_lt (by fun_prop) (by fun_prop)).mem_nhds h.1.2
  have h3 : ∀ᶠ a' in 𝓝 a, segment ℝ a' b ⊆ (U : Set (ℝ × ℝ)) := by
    have := eventually_segment_subset_of_isOpen U.isOpen
      (show segment ℝ b a ⊆ (U : Set (ℝ × ℝ)) by rw [segment_symm]; exact h.2)
    filter_upwards [this] with a' ha'
    rw [segment_symm]; exact ha'
  filter_upwards [h1, h2, h3] with a' h1 h2 h3
  exact ⟨⟨h1, h2⟩, h3⟩

/-- **The rational-jump plane** on `ℝ^{1+1}`, coordinates `(t, x)`: `x ≪_U y` iff a chain of
future timelike segments inside `U` runs from `x` to `y` (Minkowski's chronology), and `x ≤_U y`
iff a chain runs from `x` to `y` whose steps are future causal segments inside `U` or rational jumps
`(t, q) → (t, q')`, `q < q'` rational, with `{t} × [q, q'] ⊆ U`. -/
def rationalJumpPlane : Causality (ℝ × ℝ) where
  le U := TransGen (rationalJumpStep U)
  lt U := TransGen (rationalJumpChronalStep U)
  le_mem_left h := by
    obtain ⟨_, h, -⟩ := TransGen.head'_iff.1 h
    exact h.2 (left_mem_segment ℝ _ _)
  le_mem_right h := by
    obtain ⟨_, -, h⟩ := TransGen.tail'_iff.1 h
    exact h.2 (right_mem_segment ℝ _ _)
  lt_mem_left h := by
    obtain ⟨_, h, -⟩ := TransGen.head'_iff.1 h
    exact h.2 (left_mem_segment ℝ _ _)
  lt_mem_right h := by
    obtain ⟨_, -, h⟩ := TransGen.tail'_iff.1 h
    exact h.2 (right_mem_segment ℝ _ _)
  le_refl {_ x} hx := TransGen.single ⟨Or.inl ⟨by simp, by simp⟩, by
    rw [segment_same]; simpa using hx⟩
  le_trans h₁ h₂ := h₁.trans h₂
  lt_trans h₁ h₂ := h₁.trans h₂
  le_mono h _ _ h' := h'.mono fun _ _ hab => ⟨hab.1, hab.2.trans h⟩
  lt_mono h _ _ h' := h'.mono fun _ _ hab => ⟨hab.1, hab.2.trans h⟩
  le_of_lt h := h.mono fun _ _ hab => ⟨Or.inl hab.1.causal, hab.2⟩
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

/-- The causal relation, unfolded. -/
theorem rationalJumpPlane_le : rationalJumpPlane.le U x y ↔ TransGen (rationalJumpStep U) x y :=
  Iff.rfl

/-- The chronology, unfolded. -/
theorem rationalJumpPlane_lt :
    rationalJumpPlane.lt U x y ↔ TransGen (rationalJumpChronalStep U) x y :=
  Iff.rfl

/-- Along `≪_U` the displacement is future timelike: `≪` lies in Minkowski's chronology. -/
theorem rationalJumpPlane_lt_imp (h : rationalJumpPlane.lt U x y) : RationalJumpChronal x y := by
  have h' : TransGen (rationalJumpChronalStep U) x y := h
  clear h
  induction h' with
  | single h => exact h.1
  | tail _ h ih => exact ih.trans h.1

/-- Along a causal step, `t` and `t + x` do not decrease, and a step at constant `t` is trivial or
a rational jump. -/
theorem rationalJumpStep.imp (h : rationalJumpStep U a b) :
    a.1 ≤ b.1 ∧ a.1 + a.2 ≤ b.1 + b.2 ∧ (a.1 = b.1 → a = b ∨ IsRationalJump a b) := by
  rcases h.1 with ⟨h1, h2⟩ | h
  · exact ⟨by linarith, by linarith, fun ht => Or.inl (Prod.ext ht (by linarith))⟩
  · exact ⟨h.1.le, by linarith [h.1, h.2.1], fun _ => Or.inr h⟩

/-- **`≤` in coordinates**: along `≤_U`, `t` and `t + x` do not decrease, and between two points
at the same time `≤_U` is the rational line's relation: equal points, or a rational jump
`q < q'`. -/
theorem rationalJumpPlane_le_imp (h : rationalJumpPlane.le U x y) :
    x.1 ≤ y.1 ∧ x.1 + x.2 ≤ y.1 + y.2 ∧ (x.1 = y.1 → x = y ∨ IsRationalJump x y) := by
  have h' : TransGen (rationalJumpStep U) x y := h
  clear h
  induction h' with
  | single h => exact h.imp
  | @tail b c _ hbc ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    obtain ⟨s1, s2, s3⟩ := hbc.imp
    refine ⟨i1.trans s1, i2.trans s2, fun ht => ?_⟩
    have hxb : x.1 = b.1 := le_antisymm i1 (s1.trans ht.ge)
    have hbc' : b.1 = c.1 := le_antisymm s1 (ht.symm.le.trans i1)
    rcases i3 hxb with rfl | hj1 <;> rcases s3 hbc' with rfl | hj2
    · exact Or.inl rfl
    · exact Or.inr hj2
    · exact Or.inr hj1
    · exact Or.inr (hj1.trans hj2)

/-! ## Absolute minimality -/

/-- A sub-segment of a causal segment is causal. -/
theorem RationalJumpCausal.sub (h : RationalJumpCausal a b) {c₁ c₂ : ℝ} (hc : c₁ ≤ c₂) :
    RationalJumpCausal (a + c₁ • (b - a)) (a + c₂ • (b - a)) := by
  obtain ⟨h1, h2⟩ := h
  have hc' : 0 ≤ c₂ - c₁ := sub_nonneg.2 hc
  simp only [RationalJumpCausal, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1 hc']
  · nlinarith [mul_le_mul_of_nonneg_left h2 hc']

/-- A non-trivial sub-segment of a timelike segment is timelike. -/
theorem RationalJumpChronal.sub (h : RationalJumpChronal a b) {c₁ c₂ : ℝ} (hc : c₁ < c₂) :
    RationalJumpChronal (a + c₁ • (b - a)) (a + c₂ • (b - a)) := by
  obtain ⟨h1, h2⟩ := h
  have hc' : 0 < c₂ - c₁ := sub_pos.2 hc
  simp only [RationalJumpChronal, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  constructor
  · nlinarith [mul_lt_mul_of_pos_left h1 hc']
  · nlinarith [mul_lt_mul_of_pos_left h2 hc']

/-- A sub-segment of a rational jump at rational parameters is a rational jump. -/
theorem IsRationalJump.sub (h : IsRationalJump a b) {c₁ c₂ : ℚ} (hc : c₁ < c₂) :
    IsRationalJump (a + (c₁ : ℝ) • (b - a)) (a + (c₂ : ℝ) • (b - a)) := by
  obtain ⟨h1, h2, ⟨q, hq⟩, ⟨q', hq'⟩⟩ := h
  have hc' : (c₁ : ℝ) < c₂ := by exact_mod_cast hc
  simp only [IsRationalJump, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  refine ⟨by rw [h1]; ring, ?_, ⟨q + c₁ * (q' - q), ?_⟩, ⟨q + c₂ * (q' - q), ?_⟩⟩
  · nlinarith [mul_lt_mul_of_pos_right hc' (sub_pos.2 h2)]
  · push_cast; rw [hq, hq']
  · push_cast; rw [hq, hq']

/-- **A segment subdivides along a cover**: if a relation `R` holds between the points of `[a, b]`
at any two rational parameters `0 ≤ c₁ < c₂ ≤ 1`, and `[a, b] ⊆ V` with `V` covered by `S`, then `a`
and `b` are joined by a chain of `R`-related points whose segments each lie in some `V ⊓ O`,
`O ∈ S`: the equal subdivision at the parameters `k/n`, with `‖b − a‖/n` below a Lebesgue number
of the cover. The rational nodes are what keeps a rational jump's pieces rational. -/
theorem transGen_of_segment_subdivision {R : ℝ × ℝ → ℝ × ℝ → Prop}
    (hR : ∀ c₁ c₂ : ℚ, 0 ≤ c₁ → c₁ < c₂ → c₂ ≤ 1 →
      R (a + (c₁ : ℝ) • (b - a)) (a + (c₂ : ℝ) • (b - a)))
    {S : Set (Opens (ℝ × ℝ))} (hS : ∀ z ∈ V, ∃ O ∈ S, z ∈ O)
    (hseg : segment ℝ a b ⊆ (V : Set (ℝ × ℝ))) :
    TransGen (fun x y => ∃ O ∈ S, R x y ∧
      segment ℝ x y ⊆ ((V ⊓ O : Opens (ℝ × ℝ)) : Set (ℝ × ℝ))) a b := by
  have hK : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image]; exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hK
    (c := fun O : S => ((V ⊓ (O : Opens (ℝ × ℝ)) : Opens (ℝ × ℝ)) : Set (ℝ × ℝ)))
    (fun _ => Opens.isOpen _)
    (fun z hz => by
      obtain ⟨O, hO, hzO⟩ := hS z (hseg hz)
      exact mem_iUnion.2 ⟨⟨O, hO⟩, hseg hz, hzO⟩)
  obtain ⟨n, hn⟩ := exists_nat_gt (‖b - a‖ / δ)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (norm_nonneg _) hδ.le) hn
  have hn0' : (0 : ℚ) < n := by exact_mod_cast hn0
  have hnδ : ‖b - a‖ < n * δ := (div_lt_iff₀ hδ).1 hn
  let p : ℕ → ℝ × ℝ := fun j => a + (((j : ℚ) / n : ℚ) : ℝ) • (b - a)
  have hstep : ∀ k : ℕ, k < n → ∃ O ∈ S, R (p k) (p (k + 1)) ∧
      segment ℝ (p k) (p (k + 1)) ⊆ ((V ⊓ O : Opens (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
    intro k hk
    have hk' : (k : ℚ) + 1 ≤ n := by exact_mod_cast hk
    have hpk : p k ∈ segment ℝ a b := by
      rw [segment_eq_image']
      refine ⟨(((k : ℚ) / n : ℚ) : ℝ), ⟨?_, ?_⟩, rfl⟩
      · exact_mod_cast div_nonneg k.cast_nonneg hn0'.le
      · exact_mod_cast (div_le_one hn0').2 (by linarith)
    obtain ⟨⟨O, hO⟩, hOb⟩ := hball (p k) hpk
    have hR' : R (p k) (p (k + 1)) := by
      refine hR _ _ (div_nonneg k.cast_nonneg hn0'.le) ?_ ?_
      · exact div_lt_div_of_pos_right (by push_cast; linarith) hn0'
      · exact (div_le_one hn0').2 (by push_cast; linarith)
    refine ⟨O, hO, hR',
      ((convex_ball (p k) δ).segment_subset (Metric.mem_ball_self hδ) ?_).trans hOb⟩
    have e : p (k + 1) - p k = ((n : ℝ)⁻¹) • (b - a) := by
      simp only [p]
      rw [add_sub_add_left_eq_sub, ← sub_smul]
      congr 1
      push_cast
      field_simp
      ring
    rw [Metric.mem_ball, dist_eq_norm, e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hn0.le)]
    calc (n : ℝ)⁻¹ * ‖b - a‖ < (n : ℝ)⁻¹ * (n * δ) := mul_lt_mul_of_pos_left hnδ (inv_pos.2 hn0)
      _ = δ := by field_simp
  have hchain : ∀ k : ℕ, k < n → TransGen (fun x y => ∃ O ∈ S, R x y ∧
      segment ℝ x y ⊆ ((V ⊓ O : Opens (ℝ × ℝ)) : Set (ℝ × ℝ))) (p 0) (p (k + 1)) := by
    intro k
    induction k with
    | zero => intro h0; exact TransGen.single (hstep 0 h0)
    | succ k ih => intro hk; exact (ih (Nat.lt_of_succ_lt hk)).tail (hstep (k + 1) hk)
  have h0 : p 0 = a := by simp [p]
  have hN : p n = b := by
    simp only [p]
    rw [div_self hn0'.ne', Rat.cast_one, one_smul, add_sub_cancel]
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by exact_mod_cast hn0.ne')
  have := hchain m (by omega)
  rw [← hm, hN, h0] at this
  exact this

/-- **The rational-jump plane is absolutely minimal on every open set, for every cover of it** (the
gluing reading of `defi:causalite`, OQ-18): each step of a chain, causal segment, rational jump or
timelike segment, subdivides into steps of the same kind inside the members of the cover
(`transGen_of_segment_subdivision`), as for the rational line. No arc-connectedness is used. -/
theorem rationalJumpPlane_absolutelyMinimalOn (W : Opens (ℝ × ℝ)) :
    rationalJumpPlane.AbsolutelyMinimalOn W := by
  intro S hS V hV x y
  have hS' : ∀ z ∈ V, ∃ O ∈ S, z ∈ O := fun z hz => hS z (hV hz)
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · have hstep : ∀ a b, rationalJumpStep V a b →
        TransGen (fun a b => ∃ O ∈ S, rationalJumpPlane.le (V ⊓ O) a b) a b := by
      intro a b hab
      refine (transGen_of_segment_subdivision
        (R := fun a b => RationalJumpCausal a b ∨ IsRationalJump a b) ?_ hS' hab.2).mono ?_
      · intro c₁ c₂ _ h12 _
        rcases hab.1 with h | h
        · exact Or.inl (h.sub (by exact_mod_cast h12.le))
        · exact Or.inr (h.sub h12)
      · rintro u w ⟨O, hO, hR, hseg⟩
        exact ⟨O, hO, TransGen.single ⟨hR, hseg⟩⟩
    have h' : TransGen (rationalJumpStep V) x y := hxy
    clear hxy
    induction h' with
    | single h => exact hstep _ _ h
    | tail _ h ih => exact ih.trans (hstep _ _ h)
  · have hstep : ∀ a b, rationalJumpChronalStep V a b →
        TransGen (fun a b => ∃ O ∈ S, rationalJumpPlane.lt (V ⊓ O) a b) a b := by
      intro a b hab
      refine (transGen_of_segment_subdivision (R := RationalJumpChronal) ?_ hS' hab.2).mono ?_
      · intro c₁ c₂ _ h12 _
        exact hab.1.sub (by exact_mod_cast h12)
      · rintro u w ⟨O, hO, hR, hseg⟩
        exact ⟨O, hO, TransGen.single ⟨hR, hseg⟩⟩
    have h' : TransGen (rationalJumpChronalStep V) x y := hxy
    clear hxy
    induction h' with
    | single h => exact hstep _ _ h
    | tail _ h ih => exact ih.trans (hstep _ _ h)

/-- **The rational-jump plane is absolutely minimal**
(`def:topological_space_causality_absolutely`). -/
theorem rationalJumpPlane_absolutelyMinimal : rationalJumpPlane.AbsolutelyMinimal :=
  Precausality.absolutelyMinimal_iff.2 (rationalJumpPlane_absolutelyMinimalOn ⊤)

/-! ## Chronal neighbours, a time function -/

/-- **Chronal neighbours** (ladder `chronal_neighbours`): in a ball of radius `ρ` about `v` inside
`V`, `(t − ρ/2, x) ≪_V v ≪_V (t + ρ/2, x)` by one vertical segment each. -/
theorem rationalJumpPlane_chronalNeighbours : rationalJumpPlane.ChronalNeighbours := by
  have key : ∀ (V : Opens (ℝ × ℝ)) (v : ℝ × ℝ), v ∈ V → ∃ r > 0,
      rationalJumpChronalStep V (v.1 - r, v.2) v ∧ rationalJumpChronalStep V v (v.1 + r, v.2) := by
    intro V v hv
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 V.isOpen v hv
    have hp : ((v.1 - ρ / 2, v.2) : ℝ × ℝ) ∈ Metric.ball v ρ := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      simp only [Real.dist_eq, sub_self, abs_zero]
      refine ⟨?_, hρ⟩
      rw [show v.1 - ρ / 2 - v.1 = -(ρ / 2) by ring, abs_neg, abs_of_pos (by linarith)]
      linarith
    have hq : ((v.1 + ρ / 2, v.2) : ℝ × ℝ) ∈ Metric.ball v ρ := by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
      simp only [Real.dist_eq, sub_self, abs_zero]
      refine ⟨?_, hρ⟩
      rw [show v.1 + ρ / 2 - v.1 = ρ / 2 by ring, abs_of_pos (by linarith)]
      linarith
    refine ⟨ρ / 2, by linarith, ⟨⟨by simp only; linarith, by simp only; linarith⟩,
      ((convex_ball v ρ).segment_subset hp (Metric.mem_ball_self hρ)).trans hball⟩,
      ⟨⟨by simp only; linarith, by simp only; linarith⟩,
      ((convex_ball v ρ).segment_subset (Metric.mem_ball_self hρ) hq).trans hball⟩⟩
  refine ⟨fun V v hv => ?_, fun V v hv => ?_⟩
  · obtain ⟨r, -, h1, -⟩ := key V v hv
    exact ⟨_, h1.2 (left_mem_segment ℝ _ _), TransGen.single h1⟩
  · obtain ⟨r, -, -, h2⟩ := key V v hv
    exact ⟨_, h2.2 (right_mem_segment ℝ _ _), TransGen.single h2⟩

/-- Tarentin, from chronal neighbours (`ChronalNeighbours.tarentin`). -/
theorem rationalJumpPlane_tarentin : rationalJumpPlane.Tarentin :=
  rationalJumpPlane_chronalNeighbours.tarentin

/-- Along a causal step `2t + x` increases strictly unless the step is trivial: by `Δt` at least
on a causal segment with `Δt > 0` (a causal segment with `Δt = 0` is trivial), by `Δx > 0` on a
jump. -/
theorem rationalJumpStep.eq_or_lt (h : rationalJumpStep U a b) :
    a = b ∨ 2 * a.1 + a.2 < 2 * b.1 + b.2 := by
  rcases h.1 with ⟨h1, h2⟩ | ⟨h1, h2, -, -⟩
  · rcases eq_or_lt_of_le (show a.1 ≤ b.1 by linarith) with ht | ht
    · exact Or.inl (Prod.ext ht (by linarith))
    · exact Or.inr (by linarith)
  · exact Or.inr (by linarith)

/-- Along `≤_U`, `2t + x` increases strictly between distinct points. -/
theorem rationalJumpPlane_le_eq_or_lt (h : rationalJumpPlane.le U x y) :
    x = y ∨ 2 * x.1 + x.2 < 2 * y.1 + y.2 := by
  have h' : TransGen (rationalJumpStep U) x y := h
  clear h
  induction h' with
  | single h => exact h.eq_or_lt
  | tail _ h ih =>
    rcases ih with rfl | ih
    · exact h.eq_or_lt
    · rcases h.eq_or_lt with rfl | h'
      · exact Or.inr ih
      · exact Or.inr (ih.trans h')

/-- **A time function** (ladder `time_function`): `2t + x`, the evidence's `t + x/2` doubled. -/
theorem rationalJumpPlane_hasTimeFunction : rationalJumpPlane.HasTimeFunction :=
  ⟨fun z => 2 * z.1 + z.2, by fun_prop, fun _ _ hxy hne =>
    (rationalJumpPlane_le_eq_or_lt hxy).resolve_left hne⟩

/-- **Causal** (`time_function ⇒ is_causal`). -/
theorem rationalJumpPlane_isCausal : rationalJumpPlane.IsCausal :=
  rationalJumpPlane_hasTimeFunction.isCausal

/-! ## Not causally arc-connected -/

/-- `(0, 0) ≤_M (0, 1)`, by one rational jump. -/
theorem rationalJumpPlane_le_zero_one : rationalJumpPlane.le ⊤ (0, 0) (0, 1) := by
  exact TransGen.single ⟨Or.inr ⟨rfl, zero_lt_one, ⟨0, Rat.cast_zero⟩, ⟨1, Rat.cast_one⟩⟩,
    fun _ _ => trivial⟩

/-- **A causal curve with the same time at its ends is constant**: `t` is constant along it, so
between two of its points `≤` is a rational jump or equality (`rationalJumpPlane_le_imp`); were the
curve's `x` not constant, an irrational value between two of its values would be taken
(intermediate value theorem) at a point no rational jump reaches. -/
theorem rationalJumpPlane_causalCurveOn_eq {γ : ℝ → ℝ × ℝ} {s₀ s₁ : ℝ}
    (hγ : rationalJumpPlane.CausalCurveOn W γ s₀ s₁) (ht : (γ s₀).1 = (γ s₁).1) {s s' : ℝ}
    (hs : s ∈ Icc s₀ s₁) (hs' : s' ∈ Icc s₀ s₁) : γ s = γ s' := by
  wlog hss : s ≤ s' generalizing s s'
  · exact (this hs' hs (le_of_not_ge hss)).symm
  have hcont : ContinuousOn γ (Icc s s') :=
    (CurveOn.continuousOn rationalJumpPlane.isRelFamily_le hγ).mono (Icc_subset_Icc hs.1 hs'.2)
  -- `t` is constant along the curve
  have hconst : ∀ r ∈ Icc s₀ s₁, (γ r).1 = (γ s₀).1 := by
    intro r hr
    have h1 := (rationalJumpPlane_le_imp (hγ.le_of_le le_rfl hr.1 hr.2)).1
    have h2 := (rationalJumpPlane_le_imp (hγ.le_of_le hr.1 hr.2 le_rfl)).1
    linarith
  rcases (rationalJumpPlane_le_imp (hγ.le_of_le hs.1 hss hs'.2)).2.2
      (by rw [hconst s hs, hconst s' hs']) with h | ⟨-, hlt, -, -⟩
  · exact h
  · exfalso
    -- an irrational value between `x(γ s) < x(γ s')` is taken at some `r`
    obtain ⟨v, hvirr, hv1, hv2⟩ := exists_irrational_btwn hlt
    obtain ⟨r, hr, hγr⟩ := intermediate_value_Icc hss (continuous_snd.comp_continuousOn hcont)
      ⟨hv1.le, hv2.le⟩
    have hγr' : (γ r).2 = v := hγr
    have hr' : r ∈ Icc s₀ s₁ := ⟨hs.1.trans hr.1, hr.2.trans hs'.2⟩
    rcases (rationalJumpPlane_le_imp (hγ.le_of_le hs.1 hr.1 hr'.2)).2.2
        (by rw [hconst s hs, hconst r hr']) with h | ⟨-, -, -, hrat⟩
    · rw [← h] at hγr'
      linarith
    · exact hvirr (hγr' ▸ hrat)

/-- **No causal curve joins `(0, 0)` to `(0, 1)`**, in any open set, over any segment. -/
theorem rationalJumpPlane_not_exists_causalCurveOn (W : Opens (ℝ × ℝ)) {s₀ s₁ : ℝ}
    (h : s₀ ≤ s₁) :
    ¬ ∃ γ : ℝ → ℝ × ℝ, rationalJumpPlane.CausalCurveOn W γ s₀ s₁ ∧ γ s₀ = (0, 0) ∧
      γ s₁ = (0, 1) := by
  rintro ⟨γ, hγ, h0, h1⟩
  have := rationalJumpPlane_causalCurveOn_eq hγ (by rw [h0, h1]) (left_mem_Icc.2 h)
    (right_mem_Icc.2 h)
  rw [h0, h1] at this
  exact absurd (congrArg Prod.snd this) (by norm_num)

/-- **The rational-jump plane is not causally arc-connected** (`def:causal_arc_connectedness`):
`(0, 0) ≤_M (0, 1)` and no causal curve of `M` joins them. -/
theorem rationalJumpPlane_not_causallyArcConnected :
    ¬ rationalJumpPlane.CausallyArcConnected := by
  intro h
  exact rationalJumpPlane_not_exists_causalCurveOn ⊤ zero_le_one
    ((h ⊤ le_rfl (0, 0) (0, 1)).1.1 rationalJumpPlane_le_zero_one)

/-- In every open set about `m`, a rational jump `(m.1, q) → (m.1, q')` followed by a timelike
segment to `(m.1 + (q' − q)/2, q')`, both inside the open set. -/
theorem exists_rationalJump_chronal {m : ℝ × ℝ} (hm : m ∈ W) :
    ∃ q q' : ℚ, (q : ℝ) < q' ∧ rationalJumpStep W (m.1, q) (m.1, q') ∧
      rationalJumpChronalStep W (m.1, q') (m.1 + ((q' : ℝ) - q) / 2, q') := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 W.isOpen m hm
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show m.2 < m.2 + ρ / 8 by linarith)
  obtain ⟨q', hq1', hq2'⟩ := exists_rat_btwn (show (q : ℝ) < m.2 + ρ / 4 by linarith)
  have hmem : ∀ z : ℝ × ℝ, |z.1 - m.1| < ρ → |z.2 - m.2| < ρ → z ∈ Metric.ball m ρ :=
    fun z h1 h2 => by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      exact ⟨h1, h2⟩
  have ha : ((m.1, (q : ℝ)) : ℝ × ℝ) ∈ Metric.ball m ρ := hmem _
    (by simp only [sub_self, abs_zero]; exact hρ)
    (by simp only; rw [abs_lt]; constructor <;> linarith)
  have hb : ((m.1, (q' : ℝ)) : ℝ × ℝ) ∈ Metric.ball m ρ := hmem _
    (by simp only [sub_self, abs_zero]; exact hρ)
    (by simp only; rw [abs_lt]; constructor <;> linarith)
  have hc : ((m.1 + ((q' : ℝ) - q) / 2, (q' : ℝ)) : ℝ × ℝ) ∈ Metric.ball m ρ := hmem _
    (by simp only; rw [abs_lt]; constructor <;> linarith)
    (by simp only; rw [abs_lt]; constructor <;> linarith)
  refine ⟨q, q', hq1', ⟨Or.inr ⟨rfl, hq1', ⟨q, rfl⟩, ⟨q', rfl⟩⟩,
    ((convex_ball m ρ).segment_subset ha hb).trans hball⟩,
    ⟨⟨by simp only; linarith, by simp only; linarith⟩,
    ((convex_ball m ρ).segment_subset hb hc).trans hball⟩⟩

/-- No non-empty open set is causally arc-connected: it contains a rational jump. -/
theorem rationalJumpPlane_not_causallyArcConnectedOn {m : ℝ × ℝ} (hm : m ∈ W) :
    ¬ rationalJumpPlane.CausallyArcConnectedOn W := by
  intro h
  obtain ⟨q, q', hqq', hjump, -⟩ := exists_rationalJump_chronal hm
  obtain ⟨γ, hγ, h0, h1⟩ := (h W le_rfl _ _).1.1 (TransGen.single hjump)
  have := rationalJumpPlane_causalCurveOn_eq hγ (by rw [h0, h1]) (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one)
  rw [h0, h1] at this
  exact absurd (congrArg Prod.snd this) hqq'.ne

/-- Not locally causally arc-connected (`def:local_causal_arc_connectedness`). -/
theorem rationalJumpPlane_not_locallyCausallyArcConnected :
    ¬ rationalJumpPlane.LocallyCausallyArcConnected := by
  intro h
  obtain ⟨V, hV, -, hV'⟩ := h 0 univ univ_mem
  exact rationalJumpPlane_not_causallyArcConnectedOn hV hV'

/-! ## Not push-up -/

/-- **No non-empty open set has push-up**: in it, `(m.1, q) ≤ (m.1, q') ≪ (m.1 + (q' − q)/2, q')`,
and `(m.1, q) ≪ (m.1 + (q' − q)/2, q')` would need `q' − q < (q' − q)/2`. -/
theorem rationalJumpPlane_not_pushUpOn {m : ℝ × ℝ} (hm : m ∈ W) :
    ¬ rationalJumpPlane.PushUpOn W := by
  intro h
  obtain ⟨q, q', hqq', hjump, hchr⟩ := exists_rationalJump_chronal hm
  have hac := (h W le_rfl).2 (TransGen.single hjump) (TransGen.single hchr)
  have := (rationalJumpPlane_lt_imp hac).2
  simp only at this
  linarith

/-- **Not push-up** (`defi:pushup`). -/
theorem rationalJumpPlane_not_pushUp : ¬ rationalJumpPlane.PushUp := fun h =>
  rationalJumpPlane_not_pushUpOn (W := ⊤) (m := 0) trivial (Causality.pushUpOn_top.2 h)

/-- Not locally push-up: no open neighbourhood of `(0, 0)` has push-up. -/
theorem rationalJumpPlane_not_locallyPushUp : ¬ rationalJumpPlane.LocallyPushUp := fun h =>
  let ⟨_, hW, hW'⟩ := h 0
  rationalJumpPlane_not_pushUpOn hW hW'

/-- **Not causally plain**, by the ladder read backwards: on a T1 space absolute minimality and
plainness give push-up (`pushUp_of_causallyPlain_of_absolutelyMinimal`), which fails. -/
theorem rationalJumpPlane_not_causallyPlain : ¬ rationalJumpPlane.CausallyPlain := by
  intro h
  have hmin := rationalJumpPlane_absolutelyMinimal
  exact rationalJumpPlane_not_pushUp (by causal_ladder)

/-! ## Causal openness and strong causality -/

/-- **A step moved along the time axis is a step**: the kinds of step are invariant under
`(t, x) ↦ (t + s, x)` (a jump keeps its rational ends), and for small `s` the moved segment stays in
`U` (a thickening of the compact segment, `IsCompact.exists_thickening_subset_open`). -/
theorem rationalJumpStep.eventually_shift (h : rationalJumpStep U a b) :
    ∀ᶠ s in 𝓝 (0 : ℝ), rationalJumpStep U (a + (s, 0)) (b + (s, 0)) := by
  have hK : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image]; exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open U.isOpen h.2
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with s hs
  refine ⟨?_, ?_⟩
  · rcases h.1 with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · left
      simp only [RationalJumpCausal, Prod.fst_add, Prod.snd_add, add_zero]
      constructor <;> linarith
    · right
      simp only [IsRationalJump, Prod.fst_add, Prod.snd_add, add_zero]
      exact ⟨by rw [h1], h2, h3, h4⟩
  · have e : segment ℝ (a + (s, 0)) (b + (s, 0)) =
        (fun z => ((s, 0) : ℝ × ℝ) + z) '' segment ℝ a b := by
      rw [segment_translate_image, add_comm a, add_comm b]
    rw [e]
    rintro _ ⟨z, hz, rfl⟩
    refine hth (Metric.mem_thickening_iff.2 ⟨z, hz, ?_⟩)
    have hs' : |s| < δ := by simpa [Real.dist_eq] using hs
    rw [dist_eq_norm, add_sub_cancel_right, Prod.norm_mk, Real.norm_eq_abs, norm_zero]
    exact max_lt hs' hδ

/-- A chain moved along the time axis by a small `s` is a chain. -/
theorem rationalJumpPlane_le_eventually_shift (h : rationalJumpPlane.le U x y) :
    ∀ᶠ s in 𝓝 (0 : ℝ), rationalJumpPlane.le U (x + (s, 0)) (y + (s, 0)) := by
  have h' : TransGen (rationalJumpStep U) x y := h
  clear h
  induction h' with
  | single h => exact h.eventually_shift.mono fun s hs => TransGen.single hs
  | tail _ h ih => exact (ih.and h.eventually_shift).mono fun s hs => TransGen.tail hs.1 hs.2

/-- **The rational-jump plane is causally open, in the future and in the past** (DEC-8's reading of
`def:causally_open_spacetime_open`). For `y ∈ J⁺_U(V)` from `x ∈ V`, move the chain down the time
axis by a small `s > 0`: `x − (s, 0) ∈ V` and `x − (s, 0) ≤_U y − (s, 0) ≪_U y`, and `I⁺_U` of
`y − (s, 0)` is an open neighbourhood of `y` inside `J⁺_U(V)`. The past likewise, moving up. -/
theorem rationalJumpPlane_causallyOpen : rationalJumpPlane.CausallyOpen := by
  have htend : ∀ z : ℝ × ℝ, Tendsto (fun s : ℝ => z + ((s, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 z) :=
    fun z => by
      have : Continuous fun s : ℝ => z + ((s, 0) : ℝ × ℝ) := by fun_prop
      simpa [Prod.mk_zero_zero] using this.tendsto 0
  -- along the time axis, the segment from `y` stays in `U` for small shifts
  have hseg : ∀ (U : Opens (ℝ × ℝ)), ∀ y ∈ U, ∀ᶠ s in 𝓝 (0 : ℝ),
      segment ℝ y (y + ((s, 0) : ℝ × ℝ)) ⊆ (U : Set (ℝ × ℝ)) :=
    fun U y hy => (htend y).eventually
      (eventually_segment_subset_of_isOpen U.isOpen (by rw [segment_same]; simpa using hy))
  refine ⟨fun U V hVU => ?_, fun U V hVU => ?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hxV, hxy⟩
    have h1 := rationalJumpPlane_le_eventually_shift hxy
    have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), x + ((s, 0) : ℝ × ℝ) ∈ V :=
      (htend x).eventually (V.isOpen.mem_nhds hxV)
    have h3 := hseg U y (rationalJumpPlane.le_mem_right hxy)
    obtain ⟨s, ⟨⟨h1, h2⟩, h3⟩, hs⟩ :=
      ((((h1.and h2).and h3).filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin (s := Iio (0 : ℝ)))).exists
    have hs' : s < 0 := hs
    -- `y − (|s|, 0) ≪_U y`
    have hlt : rationalJumpPlane.lt U (y + ((s, 0) : ℝ × ℝ)) y := by
      refine TransGen.single ⟨⟨?_, ?_⟩, by rw [segment_symm]; exact h3⟩ <;>
        simp only [Prod.fst_add, Prod.snd_add, add_zero] <;> linarith
    filter_upwards [(rationalJumpPlane.isOpen_lt_right U _).mem_nhds hlt] with y' hy'
    exact ⟨_, h2, rationalJumpPlane.le_trans h1 (rationalJumpPlane.le_of_lt hy')⟩
  · rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hxV, hyx⟩
    have h1 := rationalJumpPlane_le_eventually_shift hyx
    have h2 : ∀ᶠ s in 𝓝 (0 : ℝ), x + ((s, 0) : ℝ × ℝ) ∈ V :=
      (htend x).eventually (V.isOpen.mem_nhds hxV)
    have h3 := hseg U y (rationalJumpPlane.le_mem_left hyx)
    obtain ⟨s, ⟨⟨h1, h2⟩, h3⟩, hs⟩ :=
      ((((h1.and h2).and h3).filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
    have hs' : 0 < s := hs
    -- `y ≪_U y + (s, 0)`
    have hlt : rationalJumpPlane.lt U y (y + ((s, 0) : ℝ × ℝ)) := by
      refine TransGen.single ⟨⟨?_, ?_⟩, h3⟩ <;>
        simp only [Prod.fst_add, Prod.snd_add, add_zero] <;> linarith
    filter_upwards [(rationalJumpPlane.isOpen_lt_left U _).mem_nhds hlt] with y' hy'
    exact ⟨_, h2, rationalJumpPlane.le_trans (rationalJumpPlane.le_of_lt hy') h1⟩

/-- **Strongly causal, with open causally convex neighbourhoods**: a small open box in the
coordinates `t` and `t + x`, both non-decreasing along `≤`, contains the diamonds of its points. -/
theorem rationalJumpPlane_stronglyCausalOpen : rationalJumpPlane.StronglyCausalOpen := by
  intro p N hN
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hN
  -- a box in the coordinates `t` and `t + x`, both non-decreasing along `≤`
  let B : Set (ℝ × ℝ) := {z | p.1 - ρ / 2 < z.1} ∩ {z | z.1 < p.1 + ρ / 2} ∩
    {z | p.1 + p.2 - ρ / 2 < z.1 + z.2} ∩ {z | z.1 + z.2 < p.1 + p.2 + ρ / 2}
  have hB : IsOpen B :=
    (((isOpen_lt (by fun_prop) (by fun_prop)).inter (isOpen_lt (by fun_prop) (by fun_prop))).inter
      (isOpen_lt (by fun_prop) (by fun_prop))).inter (isOpen_lt (by fun_prop) (by fun_prop))
  refine ⟨⟨B, hB⟩, ?_, ?_, fun _ _ => trivial, ?_⟩
  · show p ∈ B
    simp only [B, mem_inter_iff, mem_setOf_eq]
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩, by linarith⟩
  · rintro z ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
    simp only [mem_setOf_eq] at h1 h2 h3 h4
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro a ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ b ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ z hz
    obtain ⟨haz, hzb⟩ := Causality.mem_diamond.1 hz
    obtain ⟨h1, h2, -⟩ := rationalJumpPlane_le_imp haz
    obtain ⟨h3, h4, -⟩ := rationalJumpPlane_le_imp hzb
    simp only [mem_setOf_eq] at a1 a2 a3 a4 b1 b2 b3 b4
    show z ∈ B
    simp only [B, mem_inter_iff, mem_setOf_eq]
    exact ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩, by linarith⟩

/-- **Not causally compact**: on `t = 0` the diamond `J_M((0, 0), (0, 1))` contains `(0, q)` for
the rationals `q ∈ (0, 1)` and no `(0, v)` with `v` irrational, so it is not closed. -/
theorem rationalJumpPlane_not_causallyCompact : ¬ rationalJumpPlane.CausallyCompact := by
  intro h
  set D := rationalJumpPlane.diamond ⊤ ((0 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) with hD
  have hcl : IsClosed ((fun r : ℝ => ((0 : ℝ), r)) ⁻¹' D) :=
    (h _ _).isClosed.preimage (by fun_prop)
  -- the rationals of `(0, 1)` lie on the slice of the diamond
  have hmem : ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < 1 → (q : ℝ) ∈ (fun r : ℝ => ((0 : ℝ), r)) ⁻¹' D := by
    intro q h0 h1
    rw [mem_preimage, hD, Causality.mem_diamond]
    exact ⟨TransGen.single ⟨Or.inr ⟨rfl, h0, ⟨0, Rat.cast_zero⟩, ⟨q, rfl⟩⟩, fun _ _ => trivial⟩,
      TransGen.single ⟨Or.inr ⟨rfl, h1, ⟨q, rfl⟩, ⟨1, Rat.cast_one⟩⟩, fun _ _ => trivial⟩⟩
  obtain ⟨v, hv, hv0, hv1⟩ := exists_irrational_btwn (show (0 : ℝ) < 1 by norm_num)
  have hvcl : v ∈ closure ((fun r : ℝ => ((0 : ℝ), r)) ⁻¹' D) := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1 ht
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (max_lt hl hv0)
    exact ⟨r, hlu ⟨(le_max_left _ _).trans_lt hr1, hr2.trans hu⟩,
      hmem r ((le_max_right _ _).trans_lt hr1) (hr2.trans hv1)⟩
  rw [hcl.closure_eq, mem_preimage, hD, Causality.mem_diamond] at hvcl
  -- `(0, 0) ≤ (0, v)` with equal times: equal, or a rational jump
  rcases (rationalJumpPlane_le_imp hvcl.1).2.2 rfl with h0 | ⟨-, -, -, hrat⟩
  · have := congrArg Prod.snd h0
    simp only at this
    linarith
  · exact hv hrat

/-! ## The separation -/

/-- **The rational-jump plane, conjoined for the ladder**: chronal neighbours, absolutely minimal,
tarentin, causally open (in the future, and locally, both sides), causal, strongly causal (both
forms), a time function (hence curves extend); not causally arc-connected, neither push-up nor
locally push-up, not causally plain, not causally compact (so not globally hyperbolic). Valid in
either reading of `defi:causalite` (`rationalJumpPlane_absolutelyMinimalOn`). -/
theorem rationalJumpPlane_separates :
    rationalJumpPlane.ChronalNeighbours ∧ rationalJumpPlane.AbsolutelyMinimal ∧
      rationalJumpPlane.Tarentin ∧ rationalJumpPlane.CausallyOpen ∧
      rationalJumpPlane.CausallyOpenFuture ∧ rationalJumpPlane.LocallyCausallyOpen ∧
      rationalJumpPlane.LocallyCausallyOpenFuture ∧ rationalJumpPlane.IsCausal ∧
      rationalJumpPlane.StronglyCausalOpen ∧ rationalJumpPlane.StronglyCausal ∧
      rationalJumpPlane.HasTimeFunction ∧ rationalJumpPlane.CurvesExtend ∧
      ¬ rationalJumpPlane.CausallyArcConnected ∧ ¬ rationalJumpPlane.PushUp ∧
      ¬ rationalJumpPlane.LocallyPushUp ∧ ¬ rationalJumpPlane.CausallyPlain ∧
      ¬ rationalJumpPlane.CausallyCompact ∧ ¬ rationalJumpPlane.GloballyHyperbolic :=
  ⟨rationalJumpPlane_chronalNeighbours, rationalJumpPlane_absolutelyMinimal,
    rationalJumpPlane_tarentin, rationalJumpPlane_causallyOpen,
    rationalJumpPlane_causallyOpen.future, rationalJumpPlane_causallyOpen.locallyCausallyOpen,
    rationalJumpPlane_causallyOpen.future.locallyCausallyOpenFuture, rationalJumpPlane_isCausal,
    rationalJumpPlane_stronglyCausalOpen, rationalJumpPlane_stronglyCausalOpen.stronglyCausal,
    rationalJumpPlane_hasTimeFunction, rationalJumpPlane_hasTimeFunction.curvesExtend,
    rationalJumpPlane_not_causallyArcConnected, rationalJumpPlane_not_pushUp,
    rationalJumpPlane_not_locallyPushUp, rationalJumpPlane_not_causallyPlain,
    rationalJumpPlane_not_causallyCompact,
    fun h => rationalJumpPlane_not_causallyCompact h.causallyCompact⟩

/-- **The target's statement on `(0, 0)` and `(0, 1)`**: `(0, 0) ≤_M (0, 1)`, and in no open set,
over no segment of parameters, does a causal curve join them. -/
theorem rationalJumpPlane_zero_one_separates :
    rationalJumpPlane.le ⊤ (0, 0) (0, 1) ∧ ∀ (W : Opens (ℝ × ℝ)) (s₀ s₁ : ℝ), s₀ ≤ s₁ →
      ¬ ∃ γ : ℝ → ℝ × ℝ, rationalJumpPlane.CausalCurveOn W γ s₀ s₁ ∧ γ s₀ = (0, 0) ∧
        γ s₁ = (0, 1) :=
  ⟨rationalJumpPlane_le_zero_one, fun W _ _ h => rationalJumpPlane_not_exists_causalCurveOn W h⟩

/-- **Chronal neighbours and absolute minimality, in either reading, do not give causal
arc-connectedness, not even locally, nor push-up, even with causal openness and a time function**:
a causality absolutely minimal on every open set for every cover (the gluing reading of
`defi:causalite`, OQ-18, as well as the library's), with chronal neighbours, causally open and with
a time function, that is neither locally causally arc-connected nor locally push-up nor causally
plain. -/
theorem exists_chronalNeighbours_absolutelyMinimal_not_causallyArcConnected :
    ∃ C : Causality (ℝ × ℝ), (∀ W : Opens (ℝ × ℝ), C.AbsolutelyMinimalOn W) ∧
      C.ChronalNeighbours ∧ C.CausallyOpen ∧ C.HasTimeFunction ∧
      ¬ C.LocallyCausallyArcConnected ∧ ¬ C.CausallyArcConnected ∧ ¬ C.LocallyPushUp ∧
      ¬ C.CausallyPlain :=
  ⟨rationalJumpPlane, rationalJumpPlane_absolutelyMinimalOn, rationalJumpPlane_chronalNeighbours,
    rationalJumpPlane_causallyOpen, rationalJumpPlane_hasTimeFunction,
    rationalJumpPlane_not_locallyCausallyArcConnected, rationalJumpPlane_not_causallyArcConnected,
    rationalJumpPlane_not_locallyPushUp, rationalJumpPlane_not_causallyPlain⟩

/-- **Chronal neighbours and absolute minimality on every open set do not give causal
arc-connectedness**, even with causal openness: the ladder pair `chronal_neighbours →
causally_arc_connected`, refuted in either reading. -/
theorem not_causallyArcConnected_of_chronalNeighbours_bare :
    ¬ ∀ C : Causality (ℝ × ℝ), (∀ W : Opens (ℝ × ℝ), C.AbsolutelyMinimalOn W) →
      C.ChronalNeighbours → C.CausallyOpen → C.CausallyArcConnected := fun h =>
  rationalJumpPlane_not_causallyArcConnected (h _ rationalJumpPlane_absolutelyMinimalOn
    rationalJumpPlane_chronalNeighbours rationalJumpPlane_causallyOpen)

/-- **Lemma K's edge `push_up ∧ chronal_neighbours ⇒ causally_open` does not reverse**: chronal
neighbours, causal openness and absolute minimality on every open set do not give local push-up. -/
theorem not_locallyPushUp_of_chronalNeighbours_causallyOpen_bare :
    ¬ ∀ C : Causality (ℝ × ℝ), (∀ W : Opens (ℝ × ℝ), C.AbsolutelyMinimalOn W) →
      C.ChronalNeighbours → C.CausallyOpen → C.LocallyPushUp := fun h =>
  rationalJumpPlane_not_locallyPushUp (h _ rationalJumpPlane_absolutelyMinimalOn
    rationalJumpPlane_chronalNeighbours rationalJumpPlane_causallyOpen)

/-- Chronal neighbours, causal openness and absolute minimality on every open set do not give
causal plainness. -/
theorem not_causallyPlain_of_chronalNeighbours_causallyOpen_bare :
    ¬ ∀ C : Causality (ℝ × ℝ), (∀ W : Opens (ℝ × ℝ), C.AbsolutelyMinimalOn W) →
      C.ChronalNeighbours → C.CausallyOpen → C.CausallyPlain := fun h =>
  rationalJumpPlane_not_causallyPlain (h _ rationalJumpPlane_absolutelyMinimalOn
    rationalJumpPlane_chronalNeighbours rationalJumpPlane_causallyOpen)

end Causal
