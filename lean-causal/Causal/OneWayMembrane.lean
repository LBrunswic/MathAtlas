import Causal.LadderLocal
import Causal.CurvesExtend

/-!
# The one-way membrane: an absolutely minimal tarentin causality, causally open in the future and not in the past

Programme target `T-abs-one-way-membrane` (`programme/roadmap.toml:906`; layer 1, no label of
`ETT.tex`), OQ-69 (`registers/DECISIONS.md:225`). Imports: `Causal.LadderLocal`,
`Causal.CurvesExtend` (ETT layer: no model, no CBG, Splitting, LemmaK* or LevinUtility module,
transitively). On `ℝ^{1+1}` in null coordinates `(u, v) = (t + x¹, t − x¹)`, the Minkowski cone is
the product order of `ℝ × ℝ`; `R = {x¹ > 0} = {v < u}` (`membraneRight`), `L` its complement. The
**one-way membrane** `oneWayMembrane` has `≪` empty and `x ≤_U y` iff a chain of future causal
segments inside `U` runs from `x` to `y`, none passing from `R` into `L` (`membraneStep`). The
planner's sketch is confirmed in every part; nothing is refuted. **OQ-69's question: yes.**

**`T-abs-one-way-membrane/1-causality`** — `oneWayMembrane`; `oneWayMembrane_le_prod`,
`oneWayMembrane_mem_right` (one-way), `oneWayMembrane_le_top_iff` (`≤_M` in closed form).
**`T-abs-one-way-membrane/2-arc-connected`** — `membraneStep.causalCurveOn`,
`oneWayMembrane_causallyArcConnected`, `oneWayMembrane_causallyArcConnectedOn`.
**`T-abs-one-way-membrane/3-absolutely-minimal`** — `oneWayMembrane_absolutelyMinimal`, and on every
open set for every cover, `oneWayMembrane_absolutelyMinimalOn`.
**`T-abs-one-way-membrane/4-tarentin`** — `oneWayMembrane_tarentin`.
**`T-abs-one-way-membrane/5-causally-open-future`** — `membraneStep.shift`,
`oneWayMembrane_causallyOpenFuture`, `oneWayMembrane_locallyCausallyOpenFuture`.
**`T-abs-one-way-membrane/6-not-causally-open-past`** — `oneWayMembrane_Jminus_box`
(`J⁻_M((−1, 1) × (1, 3)) = {u ≤ v, u < 1, v < 3}`), `oneWayMembrane_not_isOpen_Jminus_box`,
`oneWayMembrane_not_causallyOpenPast`, `oneWayMembrane_not_causallyOpen`.
**`T-abs-one-way-membrane/7-local`** — `oneWayMembrane_not_locallyCausallyOpen`; an open set is
causally open in the past iff it misses the membrane (`oneWayMembrane_causallyOpenPastOn_iff`).
**`T-abs-one-way-membrane/8-time-reversal`** — `oneWayMembrane_dual_causallyArcConnected`,
`_dual_absolutelyMinimal(On)`, `_dual_tarentin`, `_dual_not_locallyCausallyOpenFuture`,
`_dual_hasTimeFunction`.
**`T-abs-one-way-membrane/9-ladder`** — push-up, causal, strongly causal with open convex
neighbourhoods, a time function (`u + v`); not causally compact, not GH
(`oneWayMembrane_diamond_of_mem_right`), not plain, no chronal neighbours; Alexandrov topology =
topology.
**`T-abs-one-way-membrane/10-separation`** — `oneWayMembrane_separates`,
`oneWayMembrane_dual_separates` (the keeper's conjoined witnesses);
`exists_tarentin_absolutelyMinimal_causallyOpenFuture_not_past` (OQ-69);
`not_causallyOpen_of_tarentin_of_causallyOpenFuture_bare`, its gluing form, and
`not_locallyCausallyOpenFuture_of_tarentin_of_causallyArcConnected_bare`.

Beyond the target, for `prop:tarentin_topological_spacetime_causality` (not marked: nothing of it is
certified here): its proof's step `J⁻(˚J⁻(b)) = ˚J⁻(b)` (`ETT.tex:746`) fails
(`oneWayMembrane_not_Jminus_interior_Jminus_subset`), and an open diamond need not be causally
convex (`oneWayMembrane_not_causallyConvexIn_openDiamond`); the membrane satisfies (i) and (ii).

> Question left open by the closer: can an absolutely minimal tarentin causality be causally open
> in the future and not in the past? (That decides whether DEC-8's ± is needed for that proposition
> as printed.) (OQ-69, `registers/DECISIONS.md:225`)

> x ≤_U y iff some causal curve in U goes from x to y and, once in R, stays in R; ≪ empty.
> (`programme/roadmap.toml:916`, evidence)

> The causality of $M$ is open, and $M$ is causally open, if for every open subset $\U$ of $M$
> and every open subset $\V\subset \U$ the set $J^+_\U(\V)$ is open.
> (`def:causally_open_spacetime_open`, `ETT.tex:694–697`; read with `J^±` by DEC-8)

> A topological spacetime $M$ is tarentin if for every $x\in M$ and every neighbourhood $\U$ of $x$
> there exist $p,q\in \U$ such that $x\in \mathrm{Int}\left(J_M(p,q)\right)$.
> (`def:tarentin_spacetime`, `ETT.tex:677–680`)

## Hypothesis checklist

| target claim | here |
|---|---|
| a causality: `le_trans` by concatenation, `le_mono` by inclusion | ✓ proved, every field |
| causally arc-connected, hence absolutely minimal, on every open set | ✓ proved (`cor:causalement_connexe_minimal`) |
| tarentin: at a membrane point `p ∈ L`, `q ∈ R` with the full diamond; off it, one side | ✓ proved |
| causally open in the future | ✓ proved, for every open `U` |
| `J⁻` of a small ball left of the membrane not open | ✓ proved, a box (`U = ⊤`) |
| neither causally open nor locally so | ✓ proved; past openness fails exactly on the open sets meeting the membrane |
| the time reversal | ✓ proved: arc-connected, minimal, tarentin, not locally causally open in the future |
| not globally hyperbolic (diamond between points of `R` cut to `R`) | ✓ proved |

## SCOPE (disclosed)

* **Polygonal curves.** The target asks for "a causal curve of the Minkowski cone inside `U`"; the
  Lean takes finite chains of future causal segments (polygonal curves). The two give the same
  `≤_U` (a Lipschitz causal curve in `U` is approximated by an inscribed polygon in `U`, vertex to
  vertex; the membrane condition passes to the vertices), argued, not formalised: the Minkowski
  model is not importable in layer 1. The witness is the polygonal causality; its own causal curves
  realise every `≤_U` (`oneWayMembrane_causallyArcConnected`).
* **Either reading.** Absolutely minimal on every open set for every cover of it
  (`oneWayMembrane_absolutelyMinimalOn`, the gluing reading of `defi:causalite`, OQ-18) and a
  library causality: every separation here holds in either reading.
* **Not a counterexample to `prop:tarentin_topological_spacetime_causality`**: the membrane is
  strongly causal and its Alexandrov topology is the topology. What it shows is that the printed
  hypothesis (`J⁺` only) does not carry the proof's `J⁻` step, among absolutely minimal, tarentin,
  strongly causal causalities. Whether the proposition holds with `J⁺` only is not settled here.
* `ℝ × ℝ` is Hausdorff and second countable (mathlib instances). No metric notion is in a
  statement (coordinate inequalities, segments, the product order); balls, a thickening of a
  compact segment and `dist` appear inside proofs only.
* Names checked unique against `Causal/`, the scaffold and `lean-gx`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set TopologicalSpace Topology Relation

/-! ## The construction -/

/-- The right side `R = {x¹ > 0}` of the membrane, in the null coordinates
`(u, v) = (t + x¹, t − x¹)` of `ℝ^{1+1}`: `v < u`. Its complement `L = {x¹ ≤ 0}` contains the
membrane `{u = v}`. -/
def membraneRight : Set (ℝ × ℝ) := {p | p.2 < p.1}

/-- One step of the one-way membrane in the open set `U`: a future causal segment of the Minkowski
cone of `ℝ^{1+1}` (in null coordinates, `a ≤ b` in the product order) lying in `U`, which does not
pass from `R` into `L` (`a ∈ R → b ∈ R`: along a segment the sign of `x¹` changes at most once). -/
def membraneStep (U : Opens (ℝ × ℝ)) (a b : ℝ × ℝ) : Prop :=
  a ≤ b ∧ segment ℝ a b ⊆ (U : Set (ℝ × ℝ)) ∧ (a ∈ membraneRight → b ∈ membraneRight)

theorem membraneStep.mem_left {U : Opens (ℝ × ℝ)} {a b : ℝ × ℝ} (h : membraneStep U a b) :
    a ∈ U :=
  h.2.1 (left_mem_segment ℝ a b)

theorem membraneStep.mem_right {U : Opens (ℝ × ℝ)} {a b : ℝ × ℝ} (h : membraneStep U a b) :
    b ∈ U :=
  h.2.1 (right_mem_segment ℝ a b)

/-- **The one-way membrane** on `ℝ^{1+1}`: `x ≤_U y` iff a future causal polygonal curve of the
Minkowski cone inside `U` runs from `x` to `y` and, once in `R = {x¹ > 0}`, stays in `R`; `≪`
empty. -/
def oneWayMembrane : Causality (ℝ × ℝ) where
  le U := TransGen (membraneStep U)
  lt _ _ _ := False
  le_mem_left h := by
    obtain ⟨_, h, -⟩ := TransGen.head'_iff.1 h
    exact h.mem_left
  le_mem_right h := by
    obtain ⟨_, -, h⟩ := TransGen.tail'_iff.1 h
    exact h.mem_right
  lt_mem_left h := h.elim
  lt_mem_right h := h.elim
  le_refl {_ x} hx := TransGen.single ⟨le_rfl, by rw [segment_same]; simpa using hx, id⟩
  le_trans h₁ h₂ := h₁.trans h₂
  lt_trans h _ := h
  le_mono h _ _ h' := h'.mono fun _ _ hab => ⟨hab.1, hab.2.1.trans h, hab.2.2⟩
  lt_mono _ _ _ h' := h'
  le_of_lt h := h.elim
  isOpen_lt_right _ _ := by simp
  isOpen_lt_left _ _ := by simp

variable {U V : Opens (ℝ × ℝ)} {x y : ℝ × ℝ}

theorem oneWayMembrane_le : oneWayMembrane.le U x y ↔ TransGen (membraneStep U) x y := Iff.rfl

/-- Along `≤` the product order of the null coordinates increases: `≤` lies in the Minkowski
cone. -/
theorem oneWayMembrane_le_prod (h : oneWayMembrane.le U x y) : x ≤ y := by
  have h' : TransGen (membraneStep U) x y := h
  clear h
  induction h' with
  | single h => exact h.1
  | tail _ h ih => exact ih.trans h.1

/-- **The membrane is one-way**: along `≤`, a point of `R` is followed by points of `R` only. -/
theorem oneWayMembrane_mem_right (h : oneWayMembrane.le U x y) (hx : x ∈ membraneRight) :
    y ∈ membraneRight := by
  have h' : TransGen (membraneStep U) x y := h
  clear h
  induction h' with
  | single h => exact h.2.2 hx
  | tail _ h ih => exact h.2.2 ih

/-- `≤_M` in closed form: the Minkowski order, except that nothing in `R` precedes a point of
`L`. -/
theorem oneWayMembrane_le_top_iff :
    oneWayMembrane.le ⊤ x y ↔ x ≤ y ∧ (x ∈ membraneRight → y ∈ membraneRight) :=
  ⟨fun h => ⟨oneWayMembrane_le_prod h, oneWayMembrane_mem_right h⟩,
    fun h => TransGen.single ⟨h.1, fun _ _ => trivial, h.2⟩⟩

/-! ## Causal arc-connectedness and absolute minimality -/

/-- Along a segment the coordinate `x¹` is affine: if `0 < d_a → 0 < d_b`, then on `[0, 1]` the
affine function `d_a + r (d_b − d_a)`, once positive, stays positive. -/
theorem pos_affine_of_pos {da db s s' : ℝ} (hab : 0 < da → 0 < db) (hs : 0 ≤ s) (hss' : s ≤ s')
    (hs' : s' ≤ 1) (h : 0 < da + s * (db - da)) : 0 < da + s' * (db - da) := by
  by_cases hdb : 0 < db
  · by_cases hda : 0 < da
    · rcases hs'.lt_or_eq with h1 | h1
      · nlinarith [mul_pos (sub_pos.2 h1) hda, mul_nonneg (hs.trans hss') hdb.le]
      · rw [h1]; linarith
    · push Not at hda
      nlinarith [mul_nonneg (sub_nonneg.2 hss') (sub_nonneg.2 (hda.trans hdb.le))]
  · push Not at hdb
    have hda : da ≤ 0 := not_lt.1 fun h' => absurd (hab h') (not_lt.2 hdb)
    nlinarith [mul_nonneg hs (neg_nonneg.2 hdb),
      mul_nonneg (sub_nonneg.2 (hss'.trans hs')) (neg_nonneg.2 hda)]

/-- A step is realised by its affine parametrisation, a future causal curve of the membrane: near
each parameter the curve stays in a small ball inside the given open set, convex, and a sub-segment
of a step is a step. -/
theorem membraneStep.causalCurveOn {a b : ℝ × ℝ} (h : membraneStep U a b) :
    oneWayMembrane.CausalCurveOn U (fun r => a + r • (b - a)) 0 1 := by
  have hseg : ∀ r ∈ Icc (0 : ℝ) 1, a + r • (b - a) ∈ segment ℝ a b := fun r hr =>
    ⟨1 - r, r, by linarith [hr.2], hr.1, by ring, by ext <;> simp <;> ring⟩
  have hcont : Continuous fun r : ℝ => a + r • (b - a) := by fun_prop
  refine ⟨fun t ht => h.2.1 (hseg t ht), fun t _ N _ htN => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 N.isOpen _ htN
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1
    (hcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ))
  refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => TransGen.single ⟨?_, ?_, ?_⟩⟩
  · have hab := h.1
    refine ⟨?_, ?_⟩ <;> simp <;> nlinarith [hab.1, hab.2]
  · exact ((convex_ball _ _).segment_subset (hlu ⟨h1, h2.trans h3⟩)
      (hlu ⟨h1.trans h2, h3⟩)).trans hball
  · intro hR
    have hab : 0 < a.1 - a.2 → 0 < b.1 - b.2 := fun ha => sub_pos.2 (h.2.2 (sub_pos.1 ha))
    have e : ∀ r : ℝ, (a + r • (b - a)).1 - (a + r • (b - a)).2 =
        (a.1 - a.2) + r * ((b.1 - b.2) - (a.1 - a.2)) := fun r => by simp; ring
    have hR' : 0 < (a.1 - a.2) + s * ((b.1 - b.2) - (a.1 - a.2)) := by
      rw [← e]; exact sub_pos.2 hR
    have := pos_affine_of_pos hab hs.1 h2.le hs'.2 hR'
    rw [← e] at this
    exact sub_pos.1 this

/-- **The one-way membrane is causally arc-connected** (`def:causal_arc_connectedness`): a chain of
steps is realised by the concatenation of their affine curves (`CurveOn.exists_concat`). -/
theorem oneWayMembrane_causallyArcConnected : oneWayMembrane.CausallyArcConnected := by
  rw [Causality.CausallyArcConnected, Causality.causallyArcConnectedOn_iff]
  intro U _ p q
  refine ⟨fun hpq => ?_, fun h => False.elim h⟩
  have hpq' : TransGen (membraneStep U) p q := hpq
  clear hpq
  induction hpq' with
  | single h => exact ⟨_, h.causalCurveOn, by simp, by simp⟩
  | tail _ h ih =>
    obtain ⟨c₁, hc₁, h0, h1⟩ := ih
    obtain ⟨c, hc, hc0, hc1⟩ := CurveOn.exists_concat oneWayMembrane.isRelFamily_le hc₁
      h.causalCurveOn (by simp [h1])
    exact ⟨c, hc, hc0.trans h0, by simpa using hc1⟩

theorem oneWayMembrane_causallyArcConnectedOn (W : Opens (ℝ × ℝ)) :
    oneWayMembrane.CausallyArcConnectedOn W :=
  Causality.CausallyArcConnectedOn.mono oneWayMembrane_causallyArcConnected le_top

/-- **The one-way membrane is absolutely minimal** (`cor:causalement_connexe_minimal`). -/
theorem oneWayMembrane_absolutelyMinimal : oneWayMembrane.AbsolutelyMinimal :=
  oneWayMembrane_causallyArcConnected.absolutelyMinimal

/-- Absolutely minimal on every open set, for every cover of it (the gluing reading of
`defi:causalite`, OQ-18). -/
theorem oneWayMembrane_absolutelyMinimalOn (W : Opens (ℝ × ℝ)) :
    oneWayMembrane.AbsolutelyMinimalOn W :=
  (oneWayMembrane_causallyArcConnectedOn W).absolutelyMinimalOn

/-! ## Tarentin -/

theorem isOpen_membraneRight : IsOpen membraneRight := isOpen_lt continuous_snd continuous_fst

/-- A point between `p` and `q` in the Minkowski order, with the membrane crossed the right way at
each end, lies in the diamond `J_M(p, q)`. -/
theorem oneWayMembrane_mem_diamond {p q z : ℝ × ℝ} (hpz : p ≤ z) (hzq : z ≤ q)
    (hp : p ∈ membraneRight → z ∈ membraneRight) (hq : z ∈ membraneRight → q ∈ membraneRight) :
    z ∈ oneWayMembrane.diamond ⊤ p q :=
  Causality.mem_diamond.2
    ⟨oneWayMembrane_le_top_iff.2 ⟨hpz, hp⟩, oneWayMembrane_le_top_iff.2 ⟨hzq, hq⟩⟩

/-- **The one-way membrane is tarentin** (`def:tarentin_spacetime`). At a point of `R` (resp. of
the interior of `L`) the vertices `x ∓ (ε, ε)` stay on its side, and the open box between them
intersected with that side lies in `J_M(p, q)`; at a point `m` of the membrane, `p = m − (2ε, ε)`
lies in `L` and `q = m + (2ε, ε)` in `R` (the planner's `m ∓ (δ, 2δ)` in `(x¹, t)`), and the whole
open box between them lies in `J_M(p, q)`: a segment from `L` crosses the membrane at most once,
into `R`. -/
theorem oneWayMembrane_tarentin : oneWayMembrane.Tarentin := by
  intro x N hN
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hN
  have hmem : ∀ a b : ℝ, |a| < r → |b| < r → (x.1 + a, x.2 + b) ∈ N := fun a b ha hb =>
    hball (by simp [Metric.mem_ball, Prod.dist_eq, ha, hb])
  have habs : ∀ c : ℝ, 0 < c → c < r → |c| < r ∧ |-c| < r := fun c hc hcr =>
    ⟨by rw [abs_of_pos hc]; exact hcr, by rw [abs_neg, abs_of_pos hc]; exact hcr⟩
  -- an open set around `x` inside the diamond gives `x` in the open diamond
  have key : ∀ p q : ℝ × ℝ, ∀ O : Set (ℝ × ℝ), IsOpen O → x ∈ O →
      (∀ z ∈ O, p ≤ z ∧ z ≤ q ∧ (p ∈ membraneRight → z ∈ membraneRight) ∧
        (z ∈ membraneRight → q ∈ membraneRight)) → x ∈ oneWayMembrane.openDiamond ⊤ p q :=
    fun p q O hO hx hz => interior_maximal
      (fun z hzO => let ⟨h1, h2, h3, h4⟩ := hz z hzO; oneWayMembrane_mem_diamond h1 h2 h3 h4) hO hx
  have hbox : ∀ a b c d : ℝ, IsOpen {z : ℝ × ℝ | a < z.1 ∧ z.1 < b ∧ c < z.2 ∧ z.2 < d} :=
    fun a b c d => (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt continuous_snd continuous_const)))
  have hr2 : 0 < r / 2 := by linarith
  have hr4 : 0 < r / 4 := by linarith
  rcases lt_trichotomy x.2 x.1 with h | h | h
  · -- `x ∈ R`: the box between `x ∓ (r/2, r/2)`, inside `R`
    refine ⟨(x.1 + -(r / 2), x.2 + -(r / 2)), hmem _ _ (habs _ hr2 (by linarith)).2
      (habs _ hr2 (by linarith)).2, (x.1 + r / 2, x.2 + r / 2), hmem _ _
      (habs _ hr2 (by linarith)).1 (habs _ hr2 (by linarith)).1, ?_⟩
    refine key _ _ ({z | x.1 + -(r / 2) < z.1 ∧ z.1 < x.1 + r / 2 ∧ x.2 + -(r / 2) < z.2 ∧
      z.2 < x.2 + r / 2} ∩ membraneRight) ((hbox _ _ _ _).inter isOpen_membraneRight)
      ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, h⟩ ?_
    rintro z ⟨⟨h1, h2, h3, h4⟩, hz⟩
    exact ⟨⟨h1.le, h3.le⟩, ⟨h2.le, h4.le⟩, fun _ => hz, fun _ =>
      show x.2 + r / 2 < x.1 + r / 2 by linarith⟩
  · -- `x` on the membrane: the box between `x ∓ (r/2, r/4)`
    refine ⟨(x.1 + -(r / 2), x.2 + -(r / 4)), hmem _ _ (habs _ hr2 (by linarith)).2
      (habs _ hr4 (by linarith)).2, (x.1 + r / 2, x.2 + r / 4), hmem _ _
      (habs _ hr2 (by linarith)).1 (habs _ hr4 (by linarith)).1, ?_⟩
    refine key _ _ {z | x.1 + -(r / 2) < z.1 ∧ z.1 < x.1 + r / 2 ∧ x.2 + -(r / 4) < z.2 ∧
      z.2 < x.2 + r / 4} (hbox _ _ _ _) ⟨by linarith, by linarith, by linarith, by linarith⟩ ?_
    rintro z ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1.le, h3.le⟩, ⟨h2.le, h4.le⟩, fun hp => ?_, fun _ =>
      show x.2 + r / 4 < x.1 + r / 2 by linarith⟩
    have hp' : x.2 + -(r / 4) < x.1 + -(r / 2) := hp
    linarith
  · -- `x` in the interior of `L`: the box between `x ∓ (r/2, r/2)`, inside `{u < v}`
    refine ⟨(x.1 + -(r / 2), x.2 + -(r / 2)), hmem _ _ (habs _ hr2 (by linarith)).2
      (habs _ hr2 (by linarith)).2, (x.1 + r / 2, x.2 + r / 2), hmem _ _
      (habs _ hr2 (by linarith)).1 (habs _ hr2 (by linarith)).1, ?_⟩
    refine key _ _ ({z | x.1 + -(r / 2) < z.1 ∧ z.1 < x.1 + r / 2 ∧ x.2 + -(r / 2) < z.2 ∧
      z.2 < x.2 + r / 2} ∩ {z | z.1 < z.2}) ((hbox _ _ _ _).inter
        (isOpen_lt continuous_fst continuous_snd))
      ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, h⟩ ?_
    rintro z ⟨⟨h1, h2, h3, h4⟩, hz⟩
    refine ⟨⟨h1.le, h3.le⟩, ⟨h2.le, h4.le⟩, fun hp => ?_, fun hz' => ?_⟩
    · have hp' : x.2 + -(r / 2) < x.1 + -(r / 2) := hp
      linarith
    · have hz'' : z.2 < z.1 := hz'
      exact absurd hz (not_lt.2 hz''.le)

/-! ## Causal openness: in the future, not in the past -/

/-- Shifting along the diagonal `(η, η)` (the time direction `∂_t`, in null coordinates) does not
change `x¹`, hence the side of the membrane. -/
theorem sub_diag_mem_membraneRight_iff (y : ℝ × ℝ) (η : ℝ) :
    y - (η, η) ∈ membraneRight ↔ y ∈ membraneRight := by
  show y.2 - η < y.1 - η ↔ y.2 < y.1
  exact sub_lt_sub_iff_right η

/-- The same, shifting to the future. -/
theorem add_diag_mem_membraneRight_iff (y : ℝ × ℝ) (η : ℝ) :
    y + (η, η) ∈ membraneRight ↔ y ∈ membraneRight := by
  show y.2 + η < y.1 + η ↔ y.2 < y.1
  exact add_lt_add_iff_right η

/-- **A step shifted a little along the time direction is a step**: `a + (η, η) → b + (η, η)` for
every small `η`, of either sign. The shifted segment lies in a thickening of the compact segment
`[a, b]`, inside `U` (`IsCompact.exists_thickening_subset_open`); the shift keeps both ends on their
sides. -/
theorem membraneStep.shift {a b : ℝ × ℝ} (h : membraneStep U a b) :
    ∃ δ > 0, ∀ η : ℝ, |η| < δ → membraneStep U (a + (η, η)) (b + (η, η)) := by
  have hK : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image]; exact isCompact_Icc.image (by fun_prop)
  obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open U.isOpen h.2.1
  refine ⟨δ, hδ, fun η hηδ => ⟨add_le_add_left h.1 _, fun w hw => hth ?_, fun ha => ?_⟩⟩
  · refine Metric.mem_thickening_iff.2 ⟨w + (-η, -η), ?_, ?_⟩
    · have := (mem_segment_translate ℝ ((-η, -η) : ℝ × ℝ)).2 hw
      have e : ∀ c : ℝ × ℝ, (-η, -η) + (c + (η, η)) = c := fun c => by
        ext <;> simp
      rw [e, e, add_comm] at this
      exact this
    · simp [hηδ]
  · exact (add_diag_mem_membraneRight_iff b η).2
      (h.2.2 ((add_diag_mem_membraneRight_iff a η).1 ha))

/-- The shift of `membraneStep.shift`, to the past. -/
theorem membraneStep.shift_sub {a b : ℝ × ℝ} (h : membraneStep U a b) :
    ∃ δ > 0, ∀ η : ℝ, 0 ≤ η → η < δ → membraneStep U (a - (η, η)) (b - (η, η)) := by
  obtain ⟨δ, hδ, hst⟩ := h.shift
  refine ⟨δ, hδ, fun η hη hηδ => ?_⟩
  have := hst (-η) (by rw [abs_neg, abs_of_nonneg hη]; exact hηδ)
  simpa [sub_eq_add_neg] using this

/-- **The one-way membrane is causally open in the future** (`def:causally_open_spacetime_open`
as printed). A point `y ∈ J⁺_U(V)` can be pushed a little to the past along the diagonal and stay
in `J⁺_U(V)` (induction along the chain of steps from `V`, each shifted by `membraneStep.shift`;
`V` is open at the start). From `a = y − (η, η)` every point `w` of a small ball about `y` is
reached by one step, `w` on the side of `y` when `y ∈ R` (`R` is open), on either side when
`y ∈ L`: the null boundary of a cone is in the interior of the cone of a point slightly earlier,
which keeps that point's side. -/
theorem oneWayMembrane_causallyOpenFuture : oneWayMembrane.CausallyOpenFuture := by
  intro U V hVU
  -- the invariant: a point of `J⁺_U(V)` stays there when pushed a little to the past
  have step : ∀ z y : ℝ × ℝ, (∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ →
      z - (η, η) ∈ oneWayMembrane.Jplus U V) → membraneStep U z y →
      ∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ → y - (η, η) ∈ oneWayMembrane.Jplus U V := by
    rintro z y ⟨η₀, hη₀, hz⟩ hzy
    obtain ⟨δ, hδ, hst⟩ := hzy.shift_sub
    refine ⟨min η₀ δ, lt_min hη₀ hδ, fun η hη hηm => ?_⟩
    obtain ⟨x, hx, hxz⟩ := hz η hη (hηm.trans_le (min_le_left _ _))
    exact ⟨x, hx, TransGen.tail hxz (hst η hη.le (hηm.trans_le (min_le_right _ _)))⟩
  have hshift : ∀ y ∈ oneWayMembrane.Jplus U V, ∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ →
      y - (η, η) ∈ oneWayMembrane.Jplus U V := by
    rintro y ⟨x, hx, hxy⟩
    have hbase : ∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ →
        x - (η, η) ∈ oneWayMembrane.Jplus U V := by
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 V.isOpen x hx
      refine ⟨r, hr, fun η hη hηr => Precausality.subset_Jplus (fun _ hz => hVU hz)
        (hball ?_)⟩
      simp [Metric.mem_ball, abs_of_pos hη, hηr]
    have hxy' : TransGen (membraneStep U) x y := hxy
    clear hxy
    induction hxy' with
    | single h => exact step _ _ hbase h
    | tail _ h ih => exact step _ _ ih h
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨η₀, hη₀, hη⟩ := hshift y hy
  have hyU : y ∈ U := Precausality.Jplus_subset_carrier hy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 U.isOpen y hyU
  obtain ⟨m, hm0, hmη, hmr⟩ : ∃ m : ℝ, 0 < m ∧ m < η₀ ∧ m < r :=
    ⟨min (η₀ / 2) (r / 2), lt_min (by linarith) (by linarith),
      (min_le_left _ _).trans_lt (by linarith), (min_le_right _ _).trans_lt (by linarith)⟩
  obtain ⟨x, hx, hxa⟩ := hη m hm0 hmη
  have hO : {w | w ∈ Metric.ball y m ∧ (y ∈ membraneRight → w ∈ membraneRight)} ∈ 𝓝 y := by
    by_cases hyR : y ∈ membraneRight
    · filter_upwards [Metric.ball_mem_nhds y hm0, isOpen_membraneRight.mem_nhds hyR]
        with w hw hwR
      exact ⟨hw, fun _ => hwR⟩
    · filter_upwards [Metric.ball_mem_nhds y hm0] with w hw
      exact ⟨hw, fun h => absurd h hyR⟩
  refine Filter.mem_of_superset hO fun w ⟨hw, hwR⟩ => ⟨x, hx, TransGen.tail hxa ⟨?_, ?_, ?_⟩⟩
  · simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt] at hw
    exact ⟨by simp only [Prod.fst_sub]; linarith, by simp only [Prod.snd_sub]; linarith⟩
  · refine ((convex_ball y r).segment_subset ?_ (Metric.ball_subset_ball hmr.le hw)).trans hball
    rw [Metric.mem_ball, show dist (y - (m, m)) y = m by simp [abs_of_pos hm0]]
    exact hmr
  · exact fun ha => hwR ((sub_diag_mem_membraneRight_iff y _).1 ha)

theorem oneWayMembrane_locallyCausallyOpenFuture : oneWayMembrane.LocallyCausallyOpenFuture :=
  oneWayMembrane_causallyOpenFuture.locallyCausallyOpenFuture

/-- **`J⁻` of a box left of the membrane**: `J⁻_M((−1, 1) × (1, 3)) = {u ≤ v, u < 1, v < 3}`. -/
theorem oneWayMembrane_Jminus_box :
    oneWayMembrane.Jminus ⊤ (Ioo (-1) 1 ×ˢ Ioo 1 3) = {y | y.1 ≤ y.2 ∧ y.1 < 1 ∧ y.2 < 3} := by
  ext y
  constructor
  · rintro ⟨v, ⟨hv1, hv2⟩, hyv⟩
    obtain ⟨hle, hR⟩ := oneWayMembrane_le_top_iff.1 hyv
    refine ⟨not_lt.1 fun h => ?_, hle.1.trans_lt hv1.2, hle.2.trans_lt hv2.2⟩
    have hv : v.2 < v.1 := hR h
    linarith [hv1.2, hv2.1]
  · rintro ⟨h12, h1, h2⟩
    refine ⟨((max y.1 (-1) + 1) / 2, (max y.2 1 + 3) / 2), ⟨⟨?_, ?_⟩, ?_, ?_⟩,
      oneWayMembrane_le_top_iff.2 ⟨⟨?_, ?_⟩, fun h => absurd h (not_lt.2 h12)⟩⟩
    · linarith [le_max_right y.1 (-1)]
    · linarith [max_lt h1 (show (-1 : ℝ) < 1 by norm_num)]
    · linarith [le_max_right y.2 1]
    · linarith [max_lt h2 (show (1 : ℝ) < 3 by norm_num)]
    · linarith [le_max_left y.1 (-1), max_lt h1 (show (-1 : ℝ) < 1 by norm_num)]
    · linarith [le_max_left y.2 1, max_lt h2 (show (1 : ℝ) < 3 by norm_num)]

theorem oneWayMembrane_not_isOpen_Jminus_box :
    ¬ IsOpen (oneWayMembrane.Jminus ⊤ (Ioo (-1) 1 ×ˢ Ioo 1 3)) := by
  rw [oneWayMembrane_Jminus_box]
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 h (0, 0)
    ⟨le_rfl, by norm_num, by norm_num⟩
  have hmem : ((ε / 2, 0) : ℝ × ℝ) ∈ Metric.ball ((0, 0) : ℝ × ℝ) ε := by
    simp [Metric.mem_ball, Prod.dist_eq, abs_of_pos hε]
    linarith
  have := (hball hmem).1
  simp only at this
  linarith

/-- **The one-way membrane is not causally open in the past**. -/
theorem oneWayMembrane_not_causallyOpenPast : ¬ oneWayMembrane.dual.CausallyOpenFuture := fun h =>
  oneWayMembrane_not_isOpen_Jminus_box
    (h ⊤ ⟨Ioo (-1) 1 ×ˢ Ioo 1 3, isOpen_Ioo.prod isOpen_Ioo⟩ le_top)

/-- **The one-way membrane is not causally open** (DEC-8's two-sided reading). -/
theorem oneWayMembrane_not_causallyOpen : ¬ oneWayMembrane.CausallyOpen := fun h =>
  oneWayMembrane_not_causallyOpenPast h.2

/-- **No open set meeting the membrane is causally open in the past**. -/
theorem oneWayMembrane_not_causallyOpenPastOn {W : Opens (ℝ × ℝ)} {m : ℝ × ℝ} (hm : m ∈ W)
    (hm' : m.1 = m.2) : ¬ oneWayMembrane.dual.CausallyOpenFutureOn W := by
  intro h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 W.isOpen m hm
  -- a box of `L` above `m`, inside the ball
  let V : Opens (ℝ × ℝ) := ⟨Ioo (m.1 - r / 4) (m.1 + r / 4) ×ˢ Ioo (m.2 + r / 4) (m.2 + 3 * r / 4),
    isOpen_Ioo.prod isOpen_Ioo⟩
  have hVW : V ≤ W := by
    rintro z ⟨⟨h1, h2⟩, h3, h4⟩
    refine hball ?_
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hopen := h W V le_rfl hVW
  -- `m ≤_W (m.1, m.2 + r/2) ∈ V` along a null segment inside the ball
  have hq : ((m.1, m.2 + r / 2) : ℝ × ℝ) ∈ Metric.ball m r := by
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hmJ : m ∈ oneWayMembrane.dual.Jplus W V :=
    ⟨(m.1, m.2 + r / 2), ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩,
      TransGen.single ⟨⟨le_rfl, by linarith⟩,
        ((convex_ball m r).segment_subset (Metric.mem_ball_self hr) hq).trans hball,
        fun h => absurd (show m.2 < m.1 from h) (by rw [hm']; exact lt_irrefl _)⟩⟩
  obtain ⟨ρ, hρ, hρball⟩ := Metric.isOpen_iff.1 hopen m hmJ
  -- the point `m + (ρ/2, 0)` of `R` would precede a point of `V ⊆ L`
  have hw : ((m.1 + ρ / 2, m.2) : ℝ × ℝ) ∈ Metric.ball m ρ := by
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  obtain ⟨v, hv, hwv⟩ := hρball hw
  have hvR : v.2 < v.1 := oneWayMembrane_mem_right (U := W) hwv
    (show m.2 < m.1 + ρ / 2 by linarith)
  obtain ⟨⟨_, hv2⟩, hv3, _⟩ := hv
  linarith

/-- **`J⁻_U(V)` is a neighbourhood of each of its points off the membrane.** Pushed a little to the
future, a point of `J⁻_U(V)` stays there (head induction along the chain of steps to `V`, each
shifted by `membraneStep.shift`), and from `y + (η, η)` the points of a small ball about `y` on
`y`'s side are reached by one step; off the membrane the side of `y` is open. -/
theorem oneWayMembrane_Jminus_mem_nhds (hVU : V ≤ U) (hy : y ∈ oneWayMembrane.Jminus U V)
    (hy' : y.1 ≠ y.2) : oneWayMembrane.Jminus U V ∈ 𝓝 y := by
  have step : ∀ y z : ℝ × ℝ, membraneStep U y z → (∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ →
      z + (η, η) ∈ oneWayMembrane.Jminus U V) →
      ∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ → y + (η, η) ∈ oneWayMembrane.Jminus U V := by
    rintro y z hyz ⟨η₀, hη₀, hz⟩
    obtain ⟨δ, hδ, hst⟩ := hyz.shift
    refine ⟨min η₀ δ, lt_min hη₀ hδ, fun η hη hηm => ?_⟩
    obtain ⟨x, hx, hzx⟩ := hz η hη (hηm.trans_le (min_le_left _ _))
    exact ⟨x, hx, TransGen.head (hst η (by
      rw [abs_of_pos hη]; exact hηm.trans_le (min_le_right _ _))) hzx⟩
  obtain ⟨x, hx, hyx⟩ := hy
  have hbase : ∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ → x + (η, η) ∈ oneWayMembrane.Jminus U V := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 V.isOpen x hx
    refine ⟨r, hr, fun η hη hηr => Precausality.subset_Jminus (fun _ hz => hVU hz)
      (hball ?_)⟩
    simp [Metric.mem_ball, abs_of_pos hη, hηr]
  have hyx' : TransGen (membraneStep U) y x := hyx
  have hP : ∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ → y + (η, η) ∈ oneWayMembrane.Jminus U V :=
    TransGen.head_induction_on (motive := fun y _ => ∃ η₀ > 0, ∀ η : ℝ, 0 < η → η < η₀ →
      y + (η, η) ∈ oneWayMembrane.Jminus U V) hyx'
      (fun h => step _ _ h hbase) fun h _ ih => step _ _ h ih
  obtain ⟨η₀, hη₀, hη⟩ := hP
  have hyU : y ∈ U := oneWayMembrane.le_mem_left hyx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 U.isOpen y hyU
  obtain ⟨m, hm0, hmη, hmr⟩ : ∃ m : ℝ, 0 < m ∧ m < η₀ ∧ m < r :=
    ⟨min (η₀ / 2) (r / 2), lt_min (by linarith) (by linarith),
      (min_le_left _ _).trans_lt (by linarith), (min_le_right _ _).trans_lt (by linarith)⟩
  obtain ⟨x', hx', hax⟩ := hη m hm0 hmη
  have hO : {w | w ∈ Metric.ball y m ∧ (w ∈ membraneRight → y ∈ membraneRight)} ∈ 𝓝 y := by
    rcases lt_or_gt_of_ne hy' with h | h
    · filter_upwards [Metric.ball_mem_nhds y hm0,
        (isOpen_lt continuous_fst continuous_snd).mem_nhds h] with w hw hw'
      exact ⟨hw, fun hwR => absurd (show w.2 < w.1 from hwR) (not_lt.2 (le_of_lt hw'))⟩
    · filter_upwards [Metric.ball_mem_nhds y hm0] with w hw
      exact ⟨hw, fun _ => h⟩
  refine Filter.mem_of_superset hO fun w ⟨hw, hwR⟩ => ⟨x', hx', TransGen.head ⟨?_, ?_, ?_⟩ hax⟩
  · simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt] at hw
    exact ⟨by simp only [Prod.fst_add]; linarith, by simp only [Prod.snd_add]; linarith⟩
  · refine ((convex_ball y r).segment_subset (Metric.ball_subset_ball hmr.le hw) ?_).trans hball
    rw [Metric.mem_ball, show dist (y + (m, m)) y = m by simp [abs_of_pos hm0]]
    exact hmr
  · exact fun h => (add_diag_mem_membraneRight_iff y m).2 (hwR h)

/-- **An open set is causally open in the past iff it misses the membrane**: the failure of past
causal openness sits exactly on `{x¹ = 0}` (`oneWayMembrane_not_causallyOpenPastOn` one way,
`oneWayMembrane_Jminus_mem_nhds` the other). -/
theorem oneWayMembrane_causallyOpenPastOn_iff {W : Opens (ℝ × ℝ)} :
    oneWayMembrane.dual.CausallyOpenFutureOn W ↔ ∀ z ∈ W, z.1 ≠ z.2 := by
  constructor
  · intro h z hz hz'
    exact oneWayMembrane_not_causallyOpenPastOn hz hz' h
  · intro hW U V hUW hVU
    rw [isOpen_iff_mem_nhds]
    intro y hy
    exact oneWayMembrane_Jminus_mem_nhds hVU hy
      (hW y (hUW (Precausality.Jminus_subset_carrier (P := oneWayMembrane.toPrecausality) hy)))

/-- **The one-way membrane is not locally causally open** (two-sided). -/
theorem oneWayMembrane_not_locallyCausallyOpen : ¬ oneWayMembrane.LocallyCausallyOpen := fun h =>
  let ⟨_, hW, hW'⟩ := h.2 (0, 0)
  oneWayMembrane_not_causallyOpenPastOn hW rfl hW'

/-! ## The other ladder properties -/

/-- The one-way membrane has the push-up property, vacuously (`≪` is empty). -/
theorem oneWayMembrane_pushUp : oneWayMembrane.PushUp := by
  rw [Causality.pushUp_iff]
  intro U x y z
  exact ⟨fun h _ => h.elim, fun _ h => h.elim⟩

/-- **The one-way membrane is causal**: `≤` lies in the Minkowski order. -/
theorem oneWayMembrane_isCausal : oneWayMembrane.IsCausal := fun _ _ hxy hyx =>
  le_antisymm (oneWayMembrane_le_prod hxy) (oneWayMembrane_le_prod hyx)

/-- Every diamond lies in the Minkowski diamond (the order interval) of its vertices. -/
theorem oneWayMembrane_diamond_subset_Icc (U : Opens (ℝ × ℝ)) (p q : ℝ × ℝ) :
    oneWayMembrane.diamond U p q ⊆ Icc p q := fun _ hz =>
  ⟨oneWayMembrane_le_prod (Causality.mem_diamond.1 hz).1,
    oneWayMembrane_le_prod (Causality.mem_diamond.1 hz).2⟩

/-- **The one-way membrane is strongly causal, with open causally convex neighbourhoods**: an open
box contains the Minkowski diamonds of its points. -/
theorem oneWayMembrane_stronglyCausalOpen : oneWayMembrane.StronglyCausalOpen := by
  intro p N hN
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨⟨Metric.ball p r, Metric.isOpen_ball⟩, Metric.mem_ball_self hr, hball,
    fun _ _ => trivial, fun a ha b hb z hz => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := oneWayMembrane_diamond_subset_Icc ⊤ a b hz
  have ha' : a ∈ Metric.ball p r := ha
  have hb' : b ∈ Metric.ball p r := hb
  show z ∈ Metric.ball p r
  simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff, abs_lt] at ha' hb' ⊢
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- **The one-way membrane has a time function** (the ladder node `time_function`): `u + v = 2t`. -/
theorem oneWayMembrane_hasTimeFunction : oneWayMembrane.HasTimeFunction := by
  refine ⟨fun z => z.1 + z.2, by fun_prop, fun x y hxy hne => ?_⟩
  obtain ⟨h1, h2⟩ := oneWayMembrane_le_prod hxy
  by_contra hlt
  exact hne (Prod.ext (by linarith) (by linarith))

/-- The one-way membrane has no chronal neighbours: `≪` is empty. -/
theorem oneWayMembrane_not_chronalNeighbours : ¬ oneWayMembrane.ChronalNeighbours := fun h =>
  let ⟨_, _, hp⟩ := h.1 ⊤ 0 trivial
  hp

/-- **The one-way membrane is not causally plain**: `Int J⁺(M) = M` while `I⁺(M) = ∅`. -/
theorem oneWayMembrane_not_causallyPlain : ¬ oneWayMembrane.CausallyPlain := by
  intro h
  have hJ : oneWayMembrane.Jplus ⊤ univ = univ :=
    eq_univ_of_forall fun y => ⟨y, trivial, oneWayMembrane.le_refl trivial⟩
  have hI : oneWayMembrane.Iplus ⊤ univ = ∅ := eq_empty_of_forall_notMem fun _ ⟨_, _, h⟩ => h
  have h0 := (h ⊤ univ).1 (show (0 : ℝ × ℝ) ∈ interior (oneWayMembrane.Jplus ⊤ univ) by
    rw [hJ, interior_univ]; trivial)
  rw [hI, closure_empty] at h0
  exact h0

/-- **A diamond between two points of `R` is the Minkowski diamond cut to `R`**: a point of `R` is
followed by points of `R` only. -/
theorem oneWayMembrane_diamond_of_mem_right {p q : ℝ × ℝ} (hp : p ∈ membraneRight)
    (hq : q ∈ membraneRight) : oneWayMembrane.diamond ⊤ p q = Icc p q ∩ membraneRight := by
  ext z
  constructor
  · intro hz
    exact ⟨oneWayMembrane_diamond_subset_Icc ⊤ p q hz,
      oneWayMembrane_mem_right (Causality.mem_diamond.1 hz).1 hp⟩
  · rintro ⟨⟨hpz, hzq⟩, hz⟩
    exact oneWayMembrane_mem_diamond hpz hzq (fun _ => hz) fun _ => hq

/-- **The one-way membrane is not causally compact**: `J_M((0, −1), (2, 1))` is the square
`[0, 2] × [−1, 1]` cut to `R`, which misses the membrane point `(0, 0)` of its closure. -/
theorem oneWayMembrane_not_causallyCompact : ¬ oneWayMembrane.CausallyCompact := by
  intro h
  have hK := h (0, -1) (2, 1)
  rw [oneWayMembrane_diamond_of_mem_right (show (-1 : ℝ) < 0 by norm_num)
    (show (1 : ℝ) < 2 by norm_num)] at hK
  have h0 : ((0, 0) : ℝ × ℝ) ∈ closure (Icc ((0, -1) : ℝ × ℝ) (2, 1) ∩ membraneRight) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hm : 0 < min (ε / 2) 1 := lt_min (by linarith) one_pos
    refine ⟨(min (ε / 2) 1, 0), ⟨⟨⟨hm.le, by norm_num⟩, ⟨min_le_right _ _ |>.trans
      (by norm_num), by norm_num⟩⟩, show (0 : ℝ) < min (ε / 2) 1 from hm⟩, ?_⟩
    have hd : dist ((0, 0) : ℝ × ℝ) (min (ε / 2) 1, 0) = min (ε / 2) 1 := by
      rw [Prod.dist_eq]; simp [abs_of_pos hm]; linarith
    rw [hd]; linarith [min_le_left (ε / 2) 1]
  have := (hK.isClosed.closure_eq ▸ h0).2
  exact lt_irrefl (0 : ℝ) this

/-- **The one-way membrane is not globally hyperbolic**: it is causal and not causally compact. -/
theorem oneWayMembrane_not_globallyHyperbolic : ¬ oneWayMembrane.GloballyHyperbolic := fun h =>
  oneWayMembrane_not_causallyCompact h.causallyCompact

/-- Its Alexandrov topology is the topology of the plane (`prop:tarentin_topological_spacetime_causality`,
(i) ⇒ (ii), which uses no causal openness): tarentin and strongly causal. -/
theorem oneWayMembrane_alexandrovTopology_eq :
    oneWayMembrane.alexandrovTopology = (inferInstance : TopologicalSpace (ℝ × ℝ)) :=
  Causality.StronglyCausal.alexandrovTopology_eq oneWayMembrane_tarentin
    oneWayMembrane_stronglyCausalOpen.stronglyCausal

/-! ## What the proof of `prop:tarentin_topological_spacetime_causality` uses -/

/-- **The step `J⁻(˚J⁻(b)) = ˚J⁻(b)` of the proof of `prop:tarentin_topological_spacetime_causality`
(`ETT.tex:745–746`) fails** for the one-way membrane, at `b = (1, 3)`: the membrane point `(0, 0)`
precedes the interior point `(0, 1)` of `J⁻((1, 3))` and is not interior (`J⁻((1, 3))` misses `R`).
Library form: `Causality.CausallyOpen.Jminus_interior_Jminus_subset`, which needs `J⁻`-openness. -/
theorem oneWayMembrane_not_Jminus_interior_Jminus_subset :
    ¬ oneWayMembrane.Jminus ⊤ (interior (oneWayMembrane.Jminus ⊤ {(1, 3)})) ⊆
      interior (oneWayMembrane.Jminus ⊤ {(1, 3)}) := by
  intro h
  have hJ : ∀ z : ℝ × ℝ, z ∈ oneWayMembrane.Jminus ⊤ {(1, 3)} ↔
      z ≤ (1, 3) ∧ (z ∈ membraneRight → ((1, 3) : ℝ × ℝ) ∈ membraneRight) := fun z => by
    rw [Precausality.mem_Jminus_singleton, oneWayMembrane_le_top_iff]
  -- `(0, 1)` is an interior point
  have hint : ((0, 1) : ℝ × ℝ) ∈ interior (oneWayMembrane.Jminus ⊤ {(1, 3)}) := by
    refine interior_maximal (t := {z : ℝ × ℝ | z.1 < 1 ∧ z.2 < 3 ∧ z.1 < z.2}) ?_ ?_ ?_
    · rintro z ⟨h1, h2, h3⟩
      exact (hJ z).2 ⟨⟨h1.le, h2.le⟩, fun hz => absurd (show z.2 < z.1 from hz) (not_lt.2 h3.le)⟩
    · exact (isOpen_lt continuous_fst continuous_const).inter
        ((isOpen_lt continuous_snd continuous_const).inter (isOpen_lt continuous_fst continuous_snd))
    · exact ⟨by norm_num, by norm_num, by norm_num⟩
  -- `(0, 0) ≤ (0, 1)`, so `(0, 0)` would be interior
  have h0 : ((0, 0) : ℝ × ℝ) ∈ interior (oneWayMembrane.Jminus ⊤ {(1, 3)}) :=
    h ⟨(0, 1), hint, oneWayMembrane_le_top_iff.2 ⟨⟨le_rfl, zero_le_one⟩,
      fun h => absurd (show (0 : ℝ) < 0 from h) (lt_irrefl 0)⟩⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior _ h0
  have hw : ((ε / 2, 0) : ℝ × ℝ) ∈ Metric.ball ((0, 0) : ℝ × ℝ) ε := by
    simp [Metric.mem_ball, Prod.dist_eq, abs_of_pos hε]
    linarith
  have := ((hJ _).1 (interior_subset (hball hw))).2 (show (0 : ℝ) < ε / 2 by linarith)
  exact absurd (show (3 : ℝ) < 1 from this) (by norm_num)

/-- **An open diamond of the one-way membrane need not be causally convex**: `˚J((−1, 0), (3, 4))`
contains `(0, 1)` and `(2, 3)`, whose diamond contains the membrane point `(1, 1)`, not interior to
`J((−1, 0), (3, 4))`. So the displayed chain of the proof of
`prop:tarentin_topological_spacetime_causality`, (ii) ⇒ (i) (`ETT.tex:742–750`), fails for a
causality open in the printed sense; library form: `Causality.CausallyOpen.causallyConvexIn_openDiamond`.
The membrane is strongly causal all the same (`oneWayMembrane_stronglyCausalOpen`): the proposition
itself is not refuted. -/
theorem oneWayMembrane_not_causallyConvexIn_openDiamond :
    ¬ oneWayMembrane.CausallyConvexIn (oneWayMembrane.openDiamond ⊤ (-1, 0) (3, 4)) ⊤ := by
  rintro ⟨-, h⟩
  have hsub : {z : ℝ × ℝ | -1 < z.1 ∧ z.1 < 3 ∧ 0 < z.2 ∧ z.2 < 4 ∧ z.1 < z.2} ⊆
      oneWayMembrane.openDiamond ⊤ (-1, 0) (3, 4) := by
    refine interior_maximal (fun z ⟨h1, h2, h3, h4, h5⟩ => oneWayMembrane_mem_diamond
      ⟨h1.le, h3.le⟩ ⟨h2.le, h4.le⟩ (fun hp => absurd (show (0 : ℝ) < -1 from hp) (by norm_num))
      fun hz => absurd (show z.2 < z.1 from hz) (not_lt.2 h5.le)) ?_
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          ((isOpen_lt continuous_snd continuous_const).inter
            (isOpen_lt continuous_fst continuous_snd))))
  have h11 := h (0, 1) (hsub ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (2, 3) (hsub ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩)
    (oneWayMembrane_mem_diamond (show ((0, 1) : ℝ × ℝ) ≤ (1, 1) from ⟨by norm_num, le_rfl⟩)
      (show ((1, 1) : ℝ × ℝ) ≤ (2, 3) from ⟨by norm_num, by norm_num⟩)
      (fun hp => absurd (show (1 : ℝ) < 0 from hp) (by norm_num))
      fun hz => absurd (show (1 : ℝ) < 1 from hz) (lt_irrefl 1))
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior _ h11
  have hw : ((1 + ε / 2, 1) : ℝ × ℝ) ∈ Metric.ball ((1, 1) : ℝ × ℝ) ε := by
    simp [Metric.mem_ball, Prod.dist_eq, abs_of_pos hε]
    linarith
  have hq := oneWayMembrane_mem_right (Causality.mem_diamond.1 (interior_subset (hball hw))).2
    (show (1 : ℝ) < 1 + ε / 2 by linarith)
  exact absurd (show (4 : ℝ) < 3 from hq) (by norm_num)

/-! ## The time reversal -/

/-- The time-reversed membrane is causally arc-connected (`Causality.dual_causallyArcConnectedOn`). -/
theorem oneWayMembrane_dual_causallyArcConnected : oneWayMembrane.dual.CausallyArcConnected :=
  Causality.dual_causallyArcConnectedOn.2 oneWayMembrane_causallyArcConnected

theorem oneWayMembrane_dual_absolutelyMinimal : oneWayMembrane.dual.AbsolutelyMinimal :=
  oneWayMembrane_dual_causallyArcConnected.absolutelyMinimal

/-- Absolutely minimal on every open set, for every cover of it. -/
theorem oneWayMembrane_dual_absolutelyMinimalOn (W : Opens (ℝ × ℝ)) :
    oneWayMembrane.dual.AbsolutelyMinimalOn W :=
  (Causality.CausallyArcConnectedOn.mono oneWayMembrane_dual_causallyArcConnected
    le_top).absolutelyMinimalOn

theorem oneWayMembrane_dual_tarentin : oneWayMembrane.dual.Tarentin :=
  Causality.dual_tarentin.2 oneWayMembrane_tarentin

/-- **The time-reversed membrane is not locally causally open in the future**: no open set
containing `(0, 0)` is causally open in the past for the membrane. -/
theorem oneWayMembrane_dual_not_locallyCausallyOpenFuture :
    ¬ oneWayMembrane.dual.LocallyCausallyOpenFuture := fun h =>
  let ⟨_, hW, hW'⟩ := h (0, 0)
  oneWayMembrane_not_causallyOpenPastOn hW rfl hW'

/-- The time-reversed membrane has a time function: `−(u + v)`. -/
theorem oneWayMembrane_dual_hasTimeFunction : oneWayMembrane.dual.HasTimeFunction := by
  refine ⟨fun z => -(z.1 + z.2), by fun_prop, fun x y hxy hne => ?_⟩
  obtain ⟨h1, h2⟩ := oneWayMembrane_le_prod (show oneWayMembrane.le ⊤ y x from hxy)
  by_contra hlt
  exact hne (Prod.ext (by linarith) (by linarith))

/-! ## The separations -/

/-- **The one-way membrane, conjoined for the ladder**: absolutely minimal, causally
arc-connected, tarentin, causally open in the future (hence locally), push-up (hence locally),
causal, strongly causal (both forms), with a time function (hence curves extend); neither causally
open nor locally causally open, not causally compact (so not globally hyperbolic), not causally
plain, no chronal neighbours. -/
theorem oneWayMembrane_separates :
    oneWayMembrane.AbsolutelyMinimal ∧ oneWayMembrane.CausallyArcConnected ∧
      oneWayMembrane.Tarentin ∧ oneWayMembrane.CausallyOpenFuture ∧
      oneWayMembrane.LocallyCausallyOpenFuture ∧ oneWayMembrane.PushUp ∧
      oneWayMembrane.LocallyPushUp ∧ oneWayMembrane.IsCausal ∧
      oneWayMembrane.StronglyCausalOpen ∧ oneWayMembrane.StronglyCausal ∧
      oneWayMembrane.HasTimeFunction ∧ oneWayMembrane.CurvesExtend ∧
      ¬ oneWayMembrane.CausallyOpen ∧ ¬ oneWayMembrane.LocallyCausallyOpen ∧
      ¬ oneWayMembrane.CausallyCompact ∧ ¬ oneWayMembrane.GloballyHyperbolic ∧
      ¬ oneWayMembrane.CausallyPlain ∧ ¬ oneWayMembrane.ChronalNeighbours :=
  ⟨oneWayMembrane_absolutelyMinimal, oneWayMembrane_causallyArcConnected,
    oneWayMembrane_tarentin, oneWayMembrane_causallyOpenFuture,
    oneWayMembrane_locallyCausallyOpenFuture, oneWayMembrane_pushUp,
    oneWayMembrane_pushUp.locallyPushUp, oneWayMembrane_isCausal,
    oneWayMembrane_stronglyCausalOpen, oneWayMembrane_stronglyCausalOpen.stronglyCausal,
    oneWayMembrane_hasTimeFunction, oneWayMembrane_hasTimeFunction.curvesExtend,
    oneWayMembrane_not_causallyOpen, oneWayMembrane_not_locallyCausallyOpen,
    oneWayMembrane_not_causallyCompact, oneWayMembrane_not_globallyHyperbolic,
    oneWayMembrane_not_causallyPlain, oneWayMembrane_not_chronalNeighbours⟩

/-- **The time-reversed membrane, conjoined for the ladder**: absolutely minimal, causally
arc-connected, tarentin, push-up (hence locally), causal, strongly causal (both forms), with a time
function (hence curves extend); not causally open in the future, nor locally, nor two-sided, nor
locally two-sided, not causally compact (so not globally hyperbolic), not causally plain, no
chronal neighbours. -/
theorem oneWayMembrane_dual_separates :
    oneWayMembrane.dual.AbsolutelyMinimal ∧ oneWayMembrane.dual.CausallyArcConnected ∧
      oneWayMembrane.dual.Tarentin ∧ oneWayMembrane.dual.PushUp ∧
      oneWayMembrane.dual.LocallyPushUp ∧ oneWayMembrane.dual.IsCausal ∧
      oneWayMembrane.dual.StronglyCausalOpen ∧ oneWayMembrane.dual.StronglyCausal ∧
      oneWayMembrane.dual.HasTimeFunction ∧ oneWayMembrane.dual.CurvesExtend ∧
      ¬ oneWayMembrane.dual.CausallyOpenFuture ∧ ¬ oneWayMembrane.dual.LocallyCausallyOpenFuture ∧
      ¬ oneWayMembrane.dual.CausallyOpen ∧ ¬ oneWayMembrane.dual.LocallyCausallyOpen ∧
      ¬ oneWayMembrane.dual.CausallyCompact ∧ ¬ oneWayMembrane.dual.GloballyHyperbolic ∧
      ¬ oneWayMembrane.dual.CausallyPlain ∧ ¬ oneWayMembrane.dual.ChronalNeighbours :=
  ⟨oneWayMembrane_dual_absolutelyMinimal, oneWayMembrane_dual_causallyArcConnected,
    oneWayMembrane_dual_tarentin, Causality.dual_pushUp.2 oneWayMembrane_pushUp,
    (Causality.dual_pushUp.2 oneWayMembrane_pushUp).locallyPushUp,
    Causality.dual_isCausal.2 oneWayMembrane_isCausal,
    Causality.dual_stronglyCausalOpen.2 oneWayMembrane_stronglyCausalOpen,
    Causality.dual_stronglyCausal.2 oneWayMembrane_stronglyCausalOpen.stronglyCausal,
    oneWayMembrane_dual_hasTimeFunction, oneWayMembrane_dual_hasTimeFunction.curvesExtend,
    oneWayMembrane_not_causallyOpenPast, oneWayMembrane_dual_not_locallyCausallyOpenFuture,
    fun h => oneWayMembrane_not_causallyOpen (Causality.dual_causallyOpen.1 h),
    fun h => oneWayMembrane_not_locallyCausallyOpen (Causality.dual_locallyCausallyOpen.1 h),
    fun h => oneWayMembrane_not_causallyCompact (Causality.dual_causallyCompact.1 h),
    fun h => oneWayMembrane_not_globallyHyperbolic (Causality.dual_globallyHyperbolic.1 h),
    fun h => oneWayMembrane_not_causallyPlain (Causality.dual_causallyPlain.1 h),
    fun h => oneWayMembrane_not_chronalNeighbours (Causality.dual_chronalNeighbours.1 h)⟩

/-- **OQ-69's question, answered yes**: there is a causality absolutely minimal on every open set
for every cover (the gluing reading of `defi:causalite`, OQ-18, as well as the library's), causally
arc-connected and tarentin, causally open in the future (`def:causally_open_spacetime_open` as
printed) and not causally open in the past. -/
theorem exists_tarentin_absolutelyMinimal_causallyOpenFuture_not_past :
    ∃ C : Causality (ℝ × ℝ), (∀ W : Opens (ℝ × ℝ), C.AbsolutelyMinimalOn W) ∧
      C.CausallyArcConnected ∧ C.Tarentin ∧ C.CausallyOpenFuture ∧ ¬ C.dual.CausallyOpenFuture :=
  ⟨oneWayMembrane, oneWayMembrane_absolutelyMinimalOn, oneWayMembrane_causallyArcConnected,
    oneWayMembrane_tarentin, oneWayMembrane_causallyOpenFuture,
    oneWayMembrane_not_causallyOpenPast⟩

/-- **Among absolutely minimal tarentin causalities, causal openness in the future does not give
causal openness** (DEC-8's `±` is a strict strengthening there too). -/
theorem not_causallyOpen_of_tarentin_of_causallyOpenFuture_bare :
    ¬ ∀ C : Causality (ℝ × ℝ), C.AbsolutelyMinimal → C.Tarentin → C.CausallyOpenFuture →
      C.CausallyOpen := fun h =>
  oneWayMembrane_not_causallyOpen
    (h _ oneWayMembrane_absolutelyMinimal oneWayMembrane_tarentin
      oneWayMembrane_causallyOpenFuture)

/-- The same with absolute minimality on every open set for every cover of it (the gluing
reading of `defi:causalite`, OQ-18). -/
theorem not_causallyOpen_of_tarentin_of_causallyOpenFuture_of_absolutelyMinimalOn_bare :
    ¬ ∀ C : Causality (ℝ × ℝ), (∀ W : Opens (ℝ × ℝ), C.AbsolutelyMinimalOn W) → C.Tarentin →
      C.CausallyOpenFuture → C.CausallyOpen := fun h =>
  oneWayMembrane_not_causallyOpen
    (h _ oneWayMembrane_absolutelyMinimalOn oneWayMembrane_tarentin
      oneWayMembrane_causallyOpenFuture)

/-- **Causal arc-connectedness and tarentin do not give causal openness in the future, not even
locally** (the time-reversed membrane). -/
theorem not_locallyCausallyOpenFuture_of_tarentin_of_causallyArcConnected_bare :
    ¬ ∀ C : Causality (ℝ × ℝ), C.CausallyArcConnected → C.Tarentin →
      C.LocallyCausallyOpenFuture := fun h =>
  oneWayMembrane_dual_not_locallyCausallyOpenFuture
    (h _ oneWayMembrane_dual_causallyArcConnected oneWayMembrane_dual_tarentin)

end Causal
