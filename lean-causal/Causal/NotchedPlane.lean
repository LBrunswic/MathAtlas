import Causal.OneWayMembraneChronal

/-!
# The notched plane: causally plain, absolutely minimal, globally hyperbolic, and not causally open

Programme target `T-abs-plain-not-open` (its block in `programme/roadmap.toml`; layer 1, no label
of `ETT.tex`). Imports: `Causal.OneWayMembraneChronal` only (`eventually_segment_subset_of_isOpen`;
through it `Causal.Ladder.Rules`, the `causal_ladder` tactic; ETT layer: no model, no CBG,
Splitting, LemmaK* or LevinUtility module, transitively). In the null coordinates
`(u, v) = (t + x¹, t − x¹)` of `ℝ^{1+1}` the Minkowski cone is the product order of `ℝ × ℝ`;
`Q = {u > 0 ∧ v > 0} = I⁺(0)` is an open up-set and the **notched plane**
`notchedPlane = ℝ² ∖ Q = {u ≤ 0 ∨ v ≤ 0}` a closed down-set. On it `notchedCausality`: `x ≤_U y`
(`x ≪_U y`) iff a chain of future causal (timelike) segments inside `U` runs from `x` to `y`
(`notchedStep`, `notchedChronalStep`). The planner's sketch is confirmed in every part; nothing is
refuted, nothing corrected.

**`T-abs-plain-not-open/1-causality`** — `notchedCausality`; `notchedCausality_le_top_iff` (`≤_M`
is the product order on `M`), `notchedCausality_lt_top_iff`.
**`T-abs-plain-not-open/2-arc-connected`** — `notchedCausality_causallyArcConnected`,
`notchedCausality_absolutelyMinimal`, and on every open set for every cover,
`notchedCausality_absolutelyMinimalOn`.
**`T-abs-plain-not-open/3-push-up`** — `notchedCausality_pushUp`.
**`T-abs-plain-not-open/4-plain`** — `notchedCausality_causallyPlain`.
**`T-abs-plain-not-open/5-causally-open-future`** — `notchedCausality_chronalPastNeighbours`,
`notchedCausality_causallyOpenFuture`.
**`T-abs-plain-not-open/6-not-causally-open`** — `notchedCausality_not_isOpen_Jminus_box`
(`J⁻_M` of the box `(−1/2, 1/2) × (1/2, 3/2)` about `(0, 1)` is not open),
`notchedCausality_not_causallyOpenPast`, `notchedCausality_not_causallyOpen`.
**`T-abs-plain-not-open/7-corner`** — `notchedCausality_not_causallyOpenPastOn` (no open set about
the corner is causally open in the past), `notchedCausality_not_locallyCausallyOpen`,
`notchedCausality_not_lt_of_mem_edge`, `notchedCausality_not_chronalNeighbours`,
`notchedCorner_notMem_openDiamond`, `notchedCausality_not_tarentin`.
**`T-abs-plain-not-open/8-ladder`** — causal, causally compact (`notchedCausality_diamond_eq`),
globally hyperbolic, strongly causal with open convex neighbourhoods, a time function (`u + v`).
**`T-abs-plain-not-open/9-time-reversal`** — `notchedCausality_dual_*`.
**`T-abs-plain-not-open/10-separation`** — `notchedCausality_separates`,
`notchedCausality_dual_separates` (the keeper's conjoined witnesses),
`not_locallyCausallyOpen_of_causallyPlain_bare`,
`not_locallyCausallyOpenFuture_of_causallyPlain_bare`.

> A causally plain, absolutely minimal causality that is not causally open, in either reading: the
> notched plane, ℝ^{1+1} minus the open future cone of a point (M = {p : ℝ × ℝ | p.1 ≤ 0 ∨ p.2 ≤ 0}
> in null coordinates), with Minkowski's polygonal causality inside M. […] With its time reversal
> (the target's title, `programme/roadmap.toml`)

> A topological spacetime $M$ is \emph{causally plain} if for every open subset $\U$ of $M$ and
> every $A\subset \U$, $\mathrm{Int}\left(J^\pm_\U(A)\right)\subset \overline{I^\pm_\U(A)}$, […]
> (`defi:causalement_plat`, `ETT.tex:283–286`) The causality of $M$ is open, and $M$ is causally
> open, if for every open subset $\U$ of $M$ and every open subset $\V\subset \U$ the set
> $J^+_\U(\V)$ is open. (`def:causally_open_spacetime_open`, `ETT.tex:694–697`; read with `J^±`
> by DEC-8)

## Hypothesis checklist

| target claim (evidence (i)–(ix)) | here |
|---|---|
| (i) a causal segment between points of `M` lies in `M`; `≤_M` is the product order | ✓ proved |
| (ii) a causality: `I^±_U(x)` open, transitive by concatenation, `≪ ⊆ ≤` | ✓ proved, every field |
| (iii) causally arc-connected, absolutely minimal on every open set for every cover | ✓ proved |
| (iv) push-up in every open set | ✓ proved |
| (v) causally plain; causally open in the future | ✓ proved |
| (vi) `J⁻_M` of a small ball on the upper edge not open | ✓ proved, a box about `(0, 1)` |
| (vi) not locally causally open at the corner | ✓ proved, every open set about it |
| (vii) no chronal neighbours; not tarentin at the corner | ✓ proved |
| (viii) causal, GH, strongly causal (open form), the time function `u + v` | ✓ proved |
| (ix) the time reversal | ✓ proved |

## SCOPE (disclosed)

* **Polygonal curves**, as for `Causal.OneWayMembrane`: "Minkowski's polygonal causality inside
  M" taken literally; the witness's own causal and chronal curves realise every relation.
* **Either reading of `defi:causalite`** (OQ-18): absolutely minimal on every open set for every
  cover of it, and a library causality.
* **Plainness** through `Causality.causallyPlain_of_locZ` applied to the time reversal: push-up,
  `Z⁺` of the reversal in every open set (the chronal past neighbours `v − (ε, ε)`), and its `Z⁻`
  off the edge `notchedEdge` (the chronal future neighbours `v + (ε, ε)`, which stay in `M` off the
  edge), whose interior is empty (`interior_notchedEdge`); the planner's (v) argument.
* **The ladder is consistent with it.** The two edges that force such a model, `absolutely_minimal
  ∧ causally_plain ⇒ push_up` (T1) and `push_up ∧ chronal_neighbours ⇒ causally_open`, find push-up
  and no chronal neighbours, each proved directly; the conjoined witnesses re-derive the negations
  by `causal_ladder` read backwards.
* The carrier is the subspace `notchedPlane` of `ℝ × ℝ`, Hausdorff and second countable (mathlib
  instances, conjoined in the witnesses). No metric notion is in a statement (coordinates, open
  intervals, segments, the product order); balls and `dist` appear inside proofs only.
* Names checked unique against `Causal/`, the scaffold, `lean-gx/` and `lean-benzecri/`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/
namespace Causal

open Set TopologicalSpace Topology Relation Filter

/-! ## The notched plane -/

/-- **The notched plane** `ℝ² ∖ I⁺(0)`, in the null coordinates `(u, v) = (t + x¹, t − x¹)` of
`ℝ^{1+1}`: the points with `u ≤ 0` or `v ≤ 0`. -/
def notchedPlane : Set (ℝ × ℝ) := {p | p.1 ≤ 0 ∨ p.2 ≤ 0}

theorem isClosed_notchedPlane : IsClosed notchedPlane :=
  show IsClosed ({p : ℝ × ℝ | p.1 ≤ 0} ∪ {p | p.2 ≤ 0}) from
    (isClosed_le continuous_fst continuous_const).union
      (isClosed_le continuous_snd continuous_const)

/-- The notched plane is a down-set of the product order (the past of a point of `M` lies in
`M`). -/
theorem notchedPlane_of_le {p q : ℝ × ℝ} (hq : q ∈ notchedPlane) (h : p ≤ q) :
    p ∈ notchedPlane := by
  rcases hq with hq | hq
  · exact Or.inl (h.1.trans hq)
  · exact Or.inr (h.2.trans hq)

/-- **A future causal segment ending in `M` lies in `M`**: its points precede its end. -/
theorem segment_subset_notchedPlane {a b : ℝ × ℝ} (hab : a ≤ b) (hb : b ∈ notchedPlane) :
    segment ℝ a b ⊆ notchedPlane := fun _ hw =>
  notchedPlane_of_le hb (segment_subset_Icc hab hw).2

/-- The corner `(0, 0)` of the notch. -/
def notchedCorner : notchedPlane := ⟨(0, 0), Or.inl le_rfl⟩

/-- The edge of the notch: the points of `M` with both null coordinates non-negative, i.e. the two
null half-lines `{0} × [0, ∞)` and `[0, ∞) × {0}` bounding `I⁺(0)`. -/
def notchedEdge : Set notchedPlane := {p | 0 ≤ (p : ℝ × ℝ).1 ∧ 0 ≤ (p : ℝ × ℝ).2}

/-! ## The causality -/

/-- One causal step in the open set `U` of `M`: a future causal segment of the Minkowski cone (in
null coordinates, `a ≤ b` in the product order) lying in `U`. -/
def notchedStep (U : Opens notchedPlane) (a b : notchedPlane) : Prop :=
  (a : ℝ × ℝ) ≤ b ∧ segment ℝ (a : ℝ × ℝ) b ⊆ Subtype.val '' (U : Set notchedPlane)

/-- One chronal step in the open set `U` of `M`: a future timelike segment (strictly increasing in
both null coordinates) lying in `U`. -/
def notchedChronalStep (U : Opens notchedPlane) (a b : notchedPlane) : Prop :=
  ((a : ℝ × ℝ).1 < (b : ℝ × ℝ).1 ∧ (a : ℝ × ℝ).2 < (b : ℝ × ℝ).2) ∧
    segment ℝ (a : ℝ × ℝ) b ⊆ Subtype.val '' (U : Set notchedPlane)

variable {U V W : Opens notchedPlane} {a b x y z : notchedPlane}

theorem notchedStep.mem_left (h : notchedStep U a b) : a ∈ U :=
  Subtype.val_injective.mem_set_image.1 (h.2 (left_mem_segment ℝ _ _))

theorem notchedStep.mem_right (h : notchedStep U a b) : b ∈ U :=
  Subtype.val_injective.mem_set_image.1 (h.2 (right_mem_segment ℝ _ _))

theorem notchedStep.mono (hVU : V ≤ U) (h : notchedStep V a b) : notchedStep U a b :=
  ⟨h.1, h.2.trans (image_mono (show (V : Set notchedPlane) ⊆ U from hVU))⟩

theorem notchedStep_refl (ha : a ∈ U) : notchedStep U a a :=
  ⟨le_rfl, by rw [segment_same]; exact singleton_subset_iff.2 ⟨a, ha, rfl⟩⟩

theorem notchedChronalStep.notchedStep (h : notchedChronalStep U a b) : notchedStep U a b :=
  ⟨⟨h.1.1.le, h.1.2.le⟩, h.2⟩

theorem notchedChronalStep.mono (hVU : V ≤ U) (h : notchedChronalStep V a b) :
    notchedChronalStep U a b :=
  ⟨h.1, h.2.trans (image_mono (show (V : Set notchedPlane) ⊆ U from hVU))⟩

/-- An open set of `M` is the trace of an open set `O` of `ℝ²`; a future causal segment in `O`
ending in `M` lies in the image of the open set. -/
theorem notchedPlane_segment_subset_image {O : Set (ℝ × ℝ)}
    (hO : Subtype.val ⁻¹' O = (U : Set notchedPlane)) {p q : ℝ × ℝ} (hpq : p ≤ q)
    (hq : q ∈ notchedPlane) (h : segment ℝ p q ⊆ O) :
    segment ℝ p q ⊆ Subtype.val '' (U : Set notchedPlane) := fun w hw =>
  ⟨⟨w, segment_subset_notchedPlane hpq hq hw⟩, by rw [← hO]; exact h hw, rfl⟩

theorem notchedPlane_image_subset {O : Set (ℝ × ℝ)}
    (hO : Subtype.val ⁻¹' O = (U : Set notchedPlane)) :
    Subtype.val '' (U : Set notchedPlane) ⊆ O := by
  rintro _ ⟨w, hw, rfl⟩
  rw [← hO] at hw
  exact hw

/-- **The end of a chronal step can move**: the strict inequalities are open, the segment stays in
`U` (a thickening of the compact segment, `eventually_segment_subset_of_isOpen`) and in `M`
(`segment_subset_notchedPlane`). This makes `I⁺_U(x)` open. -/
theorem notchedChronalStep.eventually_right (h : notchedChronalStep U a b) :
    ∀ᶠ b' in 𝓝 b, notchedChronalStep U a b' := by
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 U.isOpen
  have e1 : ∀ᶠ w in 𝓝 (b : ℝ × ℝ), (a : ℝ × ℝ).1 < w.1 :=
    (isOpen_lt continuous_const continuous_fst).mem_nhds h.1.1
  have e2 : ∀ᶠ w in 𝓝 (b : ℝ × ℝ), (a : ℝ × ℝ).2 < w.2 :=
    (isOpen_lt continuous_const continuous_snd).mem_nhds h.1.2
  have h1 : ∀ᶠ w in 𝓝 (b : ℝ × ℝ), ((a : ℝ × ℝ).1 < w.1 ∧ (a : ℝ × ℝ).2 < w.2) ∧
      segment ℝ (a : ℝ × ℝ) w ⊆ O :=
    (e1.and e2).and
      (eventually_segment_subset_of_isOpen hO (h.2.trans (notchedPlane_image_subset hOU)))
  filter_upwards [(continuous_subtype_val.tendsto b).eventually h1] with b' hb'
  exact ⟨hb'.1, notchedPlane_segment_subset_image hOU ⟨hb'.1.1.le, hb'.1.2.le⟩ b'.property hb'.2⟩

/-- **The start of a chronal step can move**. This makes `I⁻_U(x)` open. -/
theorem notchedChronalStep.eventually_left (h : notchedChronalStep U a b) :
    ∀ᶠ a' in 𝓝 a, notchedChronalStep U a' b := by
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 U.isOpen
  have hseg : ∀ᶠ w in 𝓝 (a : ℝ × ℝ), segment ℝ w (b : ℝ × ℝ) ⊆ O := by
    have := eventually_segment_subset_of_isOpen hO (show segment ℝ (b : ℝ × ℝ) a ⊆ O by
      rw [segment_symm]; exact h.2.trans (notchedPlane_image_subset hOU))
    filter_upwards [this] with w hw
    rwa [segment_symm]
  have e1 : ∀ᶠ w in 𝓝 (a : ℝ × ℝ), w.1 < (b : ℝ × ℝ).1 :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds h.1.1
  have e2 : ∀ᶠ w in 𝓝 (a : ℝ × ℝ), w.2 < (b : ℝ × ℝ).2 :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds h.1.2
  have h1 : ∀ᶠ w in 𝓝 (a : ℝ × ℝ), (w.1 < (b : ℝ × ℝ).1 ∧ w.2 < (b : ℝ × ℝ).2) ∧
      segment ℝ w (b : ℝ × ℝ) ⊆ O :=
    (e1.and e2).and hseg
  filter_upwards [(continuous_subtype_val.tendsto a).eventually h1] with a' ha'
  exact ⟨ha'.1, notchedPlane_segment_subset_image hOU ⟨ha'.1.1.le, ha'.1.2.le⟩ b.property ha'.2⟩

/-- **Minkowski's polygonal causality on the notched plane**: `x ≤_U y` (resp. `x ≪_U y`) iff a
chain of future causal (resp. timelike) segments inside `U` runs from `x` to `y`. -/
def notchedCausality : Causality notchedPlane where
  le U := TransGen (notchedStep U)
  lt U := TransGen (notchedChronalStep U)
  le_mem_left h := by
    obtain ⟨_, h, -⟩ := TransGen.head'_iff.1 h
    exact h.mem_left
  le_mem_right h := by
    obtain ⟨_, -, h⟩ := TransGen.tail'_iff.1 h
    exact h.mem_right
  lt_mem_left h := by
    obtain ⟨_, h, -⟩ := TransGen.head'_iff.1 h
    exact h.notchedStep.mem_left
  lt_mem_right h := by
    obtain ⟨_, -, h⟩ := TransGen.tail'_iff.1 h
    exact h.notchedStep.mem_right
  le_refl hx := TransGen.single (notchedStep_refl hx)
  le_trans h₁ h₂ := h₁.trans h₂
  lt_trans h₁ h₂ := h₁.trans h₂
  le_mono h _ _ h' := h'.mono fun _ _ hab => hab.mono h
  lt_mono h _ _ h' := h'.mono fun _ _ hab => hab.mono h
  le_of_lt h := h.mono fun _ _ hab => hab.notchedStep
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

theorem notchedCausality_le : notchedCausality.le U x y ↔ TransGen (notchedStep U) x y := Iff.rfl

theorem notchedCausality_lt :
    notchedCausality.lt U x y ↔ TransGen (notchedChronalStep U) x y := Iff.rfl

/-- Along `≤` the product order of the null coordinates increases. -/
theorem notchedCausality_le_prod (h : notchedCausality.le U x y) : (x : ℝ × ℝ) ≤ y := by
  have h' : TransGen (notchedStep U) x y := h
  clear h
  induction h' with
  | single h => exact h.1
  | tail _ h ih => exact ih.trans h.1

/-- Along `≪` both null coordinates increase strictly. -/
theorem notchedCausality_lt_prod (h : notchedCausality.lt U x y) :
    (x : ℝ × ℝ).1 < (y : ℝ × ℝ).1 ∧ (x : ℝ × ℝ).2 < (y : ℝ × ℝ).2 := by
  have h' : TransGen (notchedChronalStep U) x y := h
  clear h
  induction h' with
  | single h => exact h.1
  | tail _ h ih => exact ⟨ih.1.trans h.1.1, ih.2.trans h.1.2⟩

/-- **`≤_M` is the product order on `M`**: a future causal segment between points of `M` stays in
`M`. -/
theorem notchedCausality_le_top_iff : notchedCausality.le ⊤ x y ↔ (x : ℝ × ℝ) ≤ y :=
  ⟨notchedCausality_le_prod, fun h => TransGen.single
    ⟨h, fun w hw => ⟨⟨w, segment_subset_notchedPlane h y.property hw⟩, trivial, rfl⟩⟩⟩

/-- **`≪_M` is the open Minkowski cone on `M`.** -/
theorem notchedCausality_lt_top_iff :
    notchedCausality.lt ⊤ x y ↔ (x : ℝ × ℝ).1 < (y : ℝ × ℝ).1 ∧ (x : ℝ × ℝ).2 < (y : ℝ × ℝ).2 :=
  ⟨notchedCausality_lt_prod, fun h => TransGen.single
    ⟨h, fun w hw => ⟨⟨w, segment_subset_notchedPlane ⟨h.1.le, h.2.le⟩ y.property hw⟩, trivial,
      rfl⟩⟩⟩

/-! ## Causal arc-connectedness and absolute minimality -/

/-- The affine parametrisation of `[a, b]`, the parameter clamped to `[0, 1]`, lies on `[a, b]`. -/
theorem notchedPath_clamp_mem_segment (p q : ℝ × ℝ) (r : ℝ) :
    p + max 0 (min r 1) • (q - p) ∈ segment ℝ p q := by
  rw [segment_eq_image']
  exact ⟨max 0 (min r 1), ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩, rfl⟩

/-- **The path of a future causal segment ending in `M`**, as a map into `M`: the affine
parametrisation, clamped to `[0, 1]`. -/
noncomputable def notchedPath (a b : notchedPlane) (hab : (a : ℝ × ℝ) ≤ b) (r : ℝ) :
    notchedPlane :=
  ⟨(a : ℝ × ℝ) + max 0 (min r 1) • ((b : ℝ × ℝ) - a),
    segment_subset_notchedPlane hab b.property (notchedPath_clamp_mem_segment _ _ r)⟩

theorem notchedPath_val_of_mem {hab : (a : ℝ × ℝ) ≤ b} {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    (notchedPath a b hab r : ℝ × ℝ) = (a : ℝ × ℝ) + r • ((b : ℝ × ℝ) - a) := by
  simp only [notchedPath, min_eq_left hr.2, max_eq_right hr.1]

theorem notchedPath_zero {hab : (a : ℝ × ℝ) ≤ b} : notchedPath a b hab 0 = a := by
  apply Subtype.ext
  rw [notchedPath_val_of_mem ⟨le_rfl, zero_le_one⟩]
  simp

theorem notchedPath_one {hab : (a : ℝ × ℝ) ≤ b} : notchedPath a b hab 1 = b := by
  apply Subtype.ext
  rw [notchedPath_val_of_mem ⟨zero_le_one, le_rfl⟩]
  simp

theorem continuous_notchedPath {hab : (a : ℝ × ℝ) ≤ b} :
    Continuous fun r => (notchedPath a b hab r : ℝ × ℝ) := by
  unfold notchedPath
  fun_prop

/-- Along the path, both null coordinates increase (strictly, when the segment is timelike). -/
theorem notchedPath_coord {hab : (a : ℝ × ℝ) ≤ b} {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hs' : s' ∈ Icc (0 : ℝ) 1) :
    (notchedPath a b hab s' : ℝ × ℝ).1 - (notchedPath a b hab s : ℝ × ℝ).1 =
        (s' - s) * ((b : ℝ × ℝ).1 - (a : ℝ × ℝ).1) ∧
      (notchedPath a b hab s' : ℝ × ℝ).2 - (notchedPath a b hab s : ℝ × ℝ).2 =
        (s' - s) * ((b : ℝ × ℝ).2 - (a : ℝ × ℝ).2) := by
  rw [notchedPath_val_of_mem hs, notchedPath_val_of_mem hs']
  constructor <;> simp <;> ring

theorem notchedPath_mono {hab : (a : ℝ × ℝ) ≤ b} {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hs' : s' ∈ Icc (0 : ℝ) 1) (hss' : s ≤ s') :
    (notchedPath a b hab s : ℝ × ℝ) ≤ notchedPath a b hab s' := by
  obtain ⟨e1, e2⟩ := notchedPath_coord (hab := hab) hs hs'
  have h1 := mul_nonneg (sub_nonneg.2 hss') (sub_nonneg.2 hab.1)
  have h2 := mul_nonneg (sub_nonneg.2 hss') (sub_nonneg.2 hab.2)
  exact ⟨by linarith, by linarith⟩

/-- **Near each parameter, the path makes causal steps in any open set about its point**: a small
ball about the point, convex, contains the segment between two nearby points of the path, which
lies in `M`. -/
theorem notchedPath_local {hab : (a : ℝ × ℝ) ≤ b} (t : ℝ) (N : Opens notchedPlane)
    (htN : notchedPath a b hab t ∈ N) :
    ∃ l u, l < t ∧ t < u ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ s' ∈ Icc (0 : ℝ) 1, l < s → s < s' → s' < u →
      notchedStep N (notchedPath a b hab s) (notchedPath a b hab s') := by
  obtain ⟨O, hO, hON⟩ := isOpen_induced_iff.1 N.isOpen
  have hO' : (notchedPath a b hab t : ℝ × ℝ) ∈ O := by
    have : notchedPath a b hab t ∈ (N : Set notchedPlane) := htN
    rw [← hON] at this; exact this
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hO _ hO'
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.1
    (continuous_notchedPath.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hρ))
  refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => ⟨notchedPath_mono hs hs' h2.le, ?_⟩⟩
  exact notchedPlane_segment_subset_image hON (notchedPath_mono hs hs' h2.le)
    (notchedPath a b hab s').property (((convex_ball _ _).segment_subset
      (hlu ⟨h1, h2.trans h3⟩) (hlu ⟨h1.trans h2, h3⟩)).trans hball)

/-- A causal step is realised by its affine parametrisation (clamped to `[0, 1]`), a causal curve
of `U`. -/
theorem notchedStep.exists_causalCurveOn (h : notchedStep U a b) :
    ∃ c : ℝ → notchedPlane, notchedCausality.CausalCurveOn U c 0 1 ∧ c 0 = a ∧ c 1 = b := by
  refine ⟨notchedPath a b h.1, ⟨fun t _ => Subtype.val_injective.mem_set_image.1
    (h.2 (notchedPath_clamp_mem_segment _ _ t)), fun t _ N _ htN => ?_⟩, notchedPath_zero,
    notchedPath_one⟩
  obtain ⟨l, u, hl, hu, hrel⟩ := notchedPath_local t N htN
  exact ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 => TransGen.single (hrel s hs s' hs' h1 h2 h3)⟩

/-- A chronal step is realised by its affine parametrisation, a chronal curve of `U`. -/
theorem notchedChronalStep.exists_chronalCurveOn (h : notchedChronalStep U a b) :
    ∃ c : ℝ → notchedPlane, notchedCausality.ChronalCurveOn U c 0 1 ∧ c 0 = a ∧ c 1 = b := by
  have hab : (a : ℝ × ℝ) ≤ b := h.notchedStep.1
  refine ⟨notchedPath a b hab, ⟨fun t _ => Subtype.val_injective.mem_set_image.1
    (h.2 (notchedPath_clamp_mem_segment _ _ t)), fun t _ N _ htN => ?_⟩, notchedPath_zero,
    notchedPath_one⟩
  obtain ⟨l, u, hl, hu, hrel⟩ := notchedPath_local t N htN
  refine ⟨l, u, hl, hu, fun s hs s' hs' h1 h2 h3 =>
    TransGen.single ⟨?_, (hrel s hs s' hs' h1 h2 h3).2⟩⟩
  obtain ⟨e1, e2⟩ := notchedPath_coord (hab := hab) hs hs'
  have k1 := mul_pos (sub_pos.2 h2) (sub_pos.2 h.1.1)
  have k2 := mul_pos (sub_pos.2 h2) (sub_pos.2 h.1.2)
  exact ⟨by linarith, by linarith⟩

/-- **The notched plane is causally arc-connected** (`def:causal_arc_connectedness`). -/
theorem notchedCausality_causallyArcConnected : notchedCausality.CausallyArcConnected := by
  rw [Causality.CausallyArcConnected, Causality.causallyArcConnectedOn_iff]
  intro U _ p q
  refine ⟨fun hpq => ?_, fun hpq => ?_⟩
  · have hpq' : TransGen (notchedStep U) p q := hpq
    clear hpq
    induction hpq' with
    | single h => exact h.exists_causalCurveOn
    | tail _ h ih =>
      obtain ⟨c₁, hc₁, h0, h1⟩ := ih
      obtain ⟨c₂, hc₂, h2, h3⟩ := h.exists_causalCurveOn
      obtain ⟨c, hc, hc0, hc1⟩ := CurveOn.exists_concat notchedCausality.isRelFamily_le hc₁ hc₂
        (h1.trans h2.symm)
      exact ⟨c, hc, hc0.trans h0, hc1.trans h3⟩
  · have hpq' : TransGen (notchedChronalStep U) p q := hpq
    clear hpq
    induction hpq' with
    | single h => exact h.exists_chronalCurveOn
    | tail _ h ih =>
      obtain ⟨c₁, hc₁, h0, h1⟩ := ih
      obtain ⟨c₂, hc₂, h2, h3⟩ := h.exists_chronalCurveOn
      obtain ⟨c, hc, hc0, hc1⟩ := CurveOn.exists_concat notchedCausality.isRelFamily_lt hc₁ hc₂
        (h1.trans h2.symm)
      exact ⟨c, hc, hc0.trans h0, hc1.trans h3⟩

theorem notchedCausality_causallyArcConnectedOn (W : Opens notchedPlane) :
    notchedCausality.CausallyArcConnectedOn W :=
  Causality.CausallyArcConnectedOn.mono notchedCausality_causallyArcConnected le_top

/-- **Absolutely minimal** (`cor:causalement_connexe_minimal`). -/
theorem notchedCausality_absolutelyMinimal : notchedCausality.AbsolutelyMinimal :=
  notchedCausality_causallyArcConnected.absolutelyMinimal

/-- Absolutely minimal on every open set, for every cover of it (the gluing reading of
`defi:causalite`, OQ-18). -/
theorem notchedCausality_absolutelyMinimalOn (W : Opens notchedPlane) :
    notchedCausality.AbsolutelyMinimalOn W :=
  (notchedCausality_causallyArcConnectedOn W).absolutelyMinimalOn

/-! ## Push-up -/

/-- **A causal step pushed to the past along the diagonal is chronal**: for every neighbourhood
`N` of its start, `a − (ε, ε) ∈ N` is the start of a chronal step to `b`, for a small `ε > 0`
(`M` is a down-set). -/
theorem notchedStep.exists_chronalStep_left (h : notchedStep U a b) {N : Set notchedPlane}
    (hN : N ∈ 𝓝 a) : ∃ a' ∈ N, notchedChronalStep U a' b := by
  obtain ⟨s, hs, hsN⟩ := (mem_nhds_subtype _ _ _).1 hN
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 U.isOpen
  have hseg : ∀ᶠ w in 𝓝 (a : ℝ × ℝ), segment ℝ w (b : ℝ × ℝ) ⊆ O := by
    have := eventually_segment_subset_of_isOpen hO (show segment ℝ (b : ℝ × ℝ) a ⊆ O by
      rw [segment_symm]; exact h.2.trans (notchedPlane_image_subset hOU))
    filter_upwards [this] with w hw
    rwa [segment_symm]
  have hT : Tendsto (fun ε : ℝ => (a : ℝ × ℝ) - (ε, ε)) (𝓝 0) (𝓝 (a : ℝ × ℝ)) :=
    (by fun_prop : Continuous fun ε : ℝ => (a : ℝ × ℝ) - (ε, ε)).tendsto' 0 _ (by simp)
  have hs' : ∀ᶠ w in 𝓝 (a : ℝ × ℝ), w ∈ s := hs
  obtain ⟨ε, ⟨h1, h2⟩, hε⟩ := (((hT.eventually (hs'.and hseg)).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hε' : (0 : ℝ) < ε := hε
  have hle : (a : ℝ × ℝ) - (ε, ε) ≤ b :=
    ⟨by simp only [Prod.fst_sub]; linarith [h.1.1], by simp only [Prod.snd_sub]; linarith [h.1.2]⟩
  refine ⟨⟨(a : ℝ × ℝ) - (ε, ε), notchedPlane_of_le b.property hle⟩, hsN h1,
    ⟨⟨?_, ?_⟩, notchedPlane_segment_subset_image hOU hle b.property h2⟩⟩
  · show (a : ℝ × ℝ).1 - ε < (b : ℝ × ℝ).1
    linarith [h.1.1]
  · show (a : ℝ × ℝ).2 - ε < (b : ℝ × ℝ).2
    linarith [h.1.2]

/-- **A causal step pushed to the future along the diagonal is chronal**, when there is room in
`M` above its end (`b + (ε₀, ε₀) ∈ M`): for every neighbourhood `N` of `b`, some `b + (ε, ε) ∈ N`
ends a chronal step from `a`. -/
theorem notchedStep.exists_chronalStep_right (h : notchedStep U a b) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hb : (b : ℝ × ℝ) + (ε₀, ε₀) ∈ notchedPlane) {N : Set notchedPlane} (hN : N ∈ 𝓝 b) :
    ∃ b' ∈ N, notchedChronalStep U a b' := by
  obtain ⟨s, hs, hsN⟩ := (mem_nhds_subtype _ _ _).1 hN
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.1 U.isOpen
  have hseg : ∀ᶠ w in 𝓝 (b : ℝ × ℝ), segment ℝ (a : ℝ × ℝ) w ⊆ O :=
    eventually_segment_subset_of_isOpen hO (h.2.trans (notchedPlane_image_subset hOU))
  have hT : Tendsto (fun ε : ℝ => (b : ℝ × ℝ) + (ε, ε)) (𝓝 0) (𝓝 (b : ℝ × ℝ)) :=
    (by fun_prop : Continuous fun ε : ℝ => (b : ℝ × ℝ) + (ε, ε)).tendsto' 0 _ (by simp)
  have hs' : ∀ᶠ w in 𝓝 (b : ℝ × ℝ), w ∈ s := hs
  have hlt : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < ε₀ := gt_mem_nhds hε₀
  obtain ⟨ε, ⟨⟨h1, h2⟩, h3⟩, hε⟩ := ((((hT.eventually (hs'.and hseg)).and hlt).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hε' : (0 : ℝ) < ε := hε
  have hmem : (b : ℝ × ℝ) + (ε, ε) ∈ notchedPlane :=
    notchedPlane_of_le hb ⟨by simp only [Prod.fst_add]; linarith,
      by simp only [Prod.snd_add]; linarith⟩
  have hle : (a : ℝ × ℝ) ≤ (b : ℝ × ℝ) + (ε, ε) :=
    ⟨by simp only [Prod.fst_add]; linarith [h.1.1], by simp only [Prod.snd_add]; linarith [h.1.2]⟩
  refine ⟨⟨(b : ℝ × ℝ) + (ε, ε), hmem⟩, hsN h1,
    ⟨⟨?_, ?_⟩, notchedPlane_segment_subset_image hOU hle hmem h2⟩⟩
  · show (a : ℝ × ℝ).1 < (b : ℝ × ℝ).1 + ε
    linarith [h.1.1]
  · show (a : ℝ × ℝ).2 < (b : ℝ × ℝ).2 + ε
    linarith [h.1.2]

/-- **The notched plane has the push-up property** (`defi:pushup`), in every open set. For
`x ≪ y ≤ z`, step by step along the chain from `y`: `I⁺_U(x)` is open, so it contains a point
`y − (ε, ε)`, from which the causal step `y → z` becomes chronal. For `x ≤ y ≪ z`, step by step
back along the chain to `y`: `I⁻_U(z)` is open and `y` has a chronal successor in `M`, so it
contains a point `y + (ε, ε)` of `M`, at which the causal step `x → y` becomes chronal. -/
theorem notchedCausality_pushUp : notchedCausality.PushUp := by
  rw [Causality.pushUp_iff]
  intro U x y z
  refine ⟨fun hxy hyz => ?_, fun hxy hyz => ?_⟩
  · -- `x ≪ y ≤ z`: along the chain from `y`
    have key : ∀ y z : notchedPlane, notchedCausality.lt U x y → notchedStep U y z →
        notchedCausality.lt U x z := by
      intro y z hxy hyz
      obtain ⟨y', hy', hst⟩ :=
        hyz.exists_chronalStep_left ((notchedCausality.isOpen_lt_right U x).mem_nhds hxy)
      have hy'' : TransGen (notchedChronalStep U) x y' := hy'
      exact TransGen.tail hy'' hst
    have hyz' : TransGen (notchedStep U) y z := hyz
    clear hyz
    induction hyz' with
    | single h => exact key _ _ hxy h
    | tail _ h ih => exact key _ _ ih h
  · -- `x ≤ y ≪ z`: back along the chain to `y`
    have key : ∀ x y : notchedPlane, notchedStep U x y → notchedCausality.lt U y z →
        notchedCausality.lt U x z := by
      intro x y hxy hyz
      obtain ⟨d, hyd, -⟩ := TransGen.head'_iff.1 hyz
      obtain ⟨m, hm, hm1, hm2⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ (d : ℝ × ℝ).1 - (y : ℝ × ℝ).1 ∧
          m ≤ (d : ℝ × ℝ).2 - (y : ℝ × ℝ).2 :=
        ⟨_, lt_min (sub_pos.2 hyd.1.1) (sub_pos.2 hyd.1.2), min_le_left _ _, min_le_right _ _⟩
      have hroom : (y : ℝ × ℝ) + (m, m) ∈ notchedPlane :=
        notchedPlane_of_le d.property ⟨by simp only [Prod.fst_add]; linarith,
          by simp only [Prod.snd_add]; linarith⟩
      obtain ⟨y', hy', hst⟩ := hxy.exists_chronalStep_right hm hroom
        ((notchedCausality.isOpen_lt_left U z).mem_nhds hyz)
      have hy'' : TransGen (notchedChronalStep U) y' z := hy'
      exact TransGen.head hst hy''
    have hxy' : TransGen (notchedStep U) x y := hxy
    exact TransGen.head_induction_on (motive := fun x _ => notchedCausality.lt U x z) hxy'
      (fun h => key _ _ h hyz) fun h _ ih => key _ _ h ih

/-! ## Chronal past neighbours, causal openness in the future, causal plainness -/

/-- **Every point has chronal past neighbours in every open set**: `v − (ε, ε) ≪_V v`. -/
theorem notchedCausality_chronalPastNeighbours : notchedCausality.ChronalPastNeighbours := by
  intro V v hv
  obtain ⟨p, hp, hst⟩ := (notchedStep_refl hv).exists_chronalStep_left (V.isOpen.mem_nhds hv)
  exact ⟨p, hp, TransGen.single hst⟩

/-- **The notched plane is causally open in the future** (`def:causally_open_spacetime_open` as
printed): push-up and chronal past neighbours
(`PushUp.causallyOpenFuture_of_chronalPastNeighbours`). -/
theorem notchedCausality_causallyOpenFuture : notchedCausality.CausallyOpenFuture :=
  notchedCausality_pushUp.causallyOpenFuture_of_chronalPastNeighbours
    notchedCausality_chronalPastNeighbours

/-- The edge has empty interior in `M`: beside each of its points lie points with a negative null
coordinate. -/
theorem interior_notchedEdge : interior notchedEdge = ∅ := by
  refine eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨s, hs, hsE⟩ := (mem_nhds_subtype _ _ _).1 (mem_interior_iff_mem_nhds.1 hp)
  have hs' : ∀ᶠ w in 𝓝 (p : ℝ × ℝ), w ∈ s := hs
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  rcases p.property with h | h
  · -- `p` on `{u = 0}`: the points `p − (δ, 0)` of `M` have `u < 0`
    have hT : Tendsto (fun δ : ℝ => (p : ℝ × ℝ) - (δ, 0)) (𝓝 0) (𝓝 (p : ℝ × ℝ)) :=
      (by fun_prop : Continuous fun δ : ℝ => (p : ℝ × ℝ) - (δ, 0)).tendsto' 0 _ (by simp)
    obtain ⟨δ, hδs, hδ⟩ := (((hT.eventually hs').filter_mono nhdsWithin_le_nhds).and hpos).exists
    have hmem : (p : ℝ × ℝ) - (δ, 0) ∈ notchedPlane :=
      Or.inl (by simp only [Prod.fst_sub]; linarith)
    have := (hsE (show ((⟨_, hmem⟩ : notchedPlane) : ℝ × ℝ) ∈ s from hδs)).1
    have e : ((⟨_, hmem⟩ : notchedPlane) : ℝ × ℝ).1 = (p : ℝ × ℝ).1 - δ := by simp
    linarith [(interior_subset hp : p ∈ notchedEdge).1]
  · -- `p` on `{v = 0}`: the points `p − (0, δ)`
    have hT : Tendsto (fun δ : ℝ => (p : ℝ × ℝ) - (0, δ)) (𝓝 0) (𝓝 (p : ℝ × ℝ)) :=
      (by fun_prop : Continuous fun δ : ℝ => (p : ℝ × ℝ) - (0, δ)).tendsto' 0 _ (by simp)
    obtain ⟨δ, hδs, hδ⟩ := (((hT.eventually hs').filter_mono nhdsWithin_le_nhds).and hpos).exists
    have hmem : (p : ℝ × ℝ) - (0, δ) ∈ notchedPlane :=
      Or.inr (by simp only [Prod.snd_sub]; linarith)
    have := (hsE (show ((⟨_, hmem⟩ : notchedPlane) : ℝ × ℝ) ∈ s from hδs)).2
    have e : ((⟨_, hmem⟩ : notchedPlane) : ℝ × ℝ).2 = (p : ℝ × ℝ).2 - δ := by simp
    linarith [(interior_subset hp : p ∈ notchedEdge).2]

/-- **Off the edge, every point has chronal future neighbours in every open set**:
`v + (ε, ε)` stays in `M` when a null coordinate of `v` is negative. -/
theorem notchedCausality_exists_lt_right_of_notMem_edge (hy : y ∈ W) (hy' : y ∉ notchedEdge)
    {N : Set notchedPlane} (hN : N ∈ 𝓝 y) : ∃ z ∈ N, notchedCausality.lt W y z := by
  have hroom : ∃ m : ℝ, 0 < m ∧ (y : ℝ × ℝ) + (m, m) ∈ notchedPlane := by
    by_cases h1 : 0 ≤ (y : ℝ × ℝ).1
    · have h2 : (y : ℝ × ℝ).2 < 0 := not_le.1 fun h2 => hy' ⟨h1, h2⟩
      exact ⟨-(y : ℝ × ℝ).2, by linarith, Or.inr (by simp only [Prod.snd_add]; linarith)⟩
    · exact ⟨-(y : ℝ × ℝ).1, by linarith, Or.inl (by simp only [Prod.fst_add]; linarith)⟩
  obtain ⟨m, hm, hmM⟩ := hroom
  obtain ⟨z, hz, hst⟩ := (notchedStep_refl hy).exists_chronalStep_right hm hmM hN
  exact ⟨z, hz, TransGen.single hst⟩

/-- **The notched plane is causally plain** (`defi:causalement_plat`). The time reversal has
push-up, `Z⁺` in every open set (the chronal past neighbours) and `Z⁻` off the edge, which has
empty interior: `Causality.causallyPlain_of_locZ` concludes. -/
theorem notchedCausality_causallyPlain : notchedCausality.CausallyPlain := by
  have hP : notchedCausality.dual.PushUp := Causality.dual_pushUp.2 notchedCausality_pushUp
  have hZp : E0LM.LocZplus notchedCausality.dual := fun W y hy N hN => by
    obtain ⟨z, hz, hst⟩ := (notchedStep_refl hy).exists_chronalStep_left hN
    exact ⟨z, hz, TransGen.single hst⟩
  have hZm : E0LM.LocZminus notchedCausality.dual notchedEdge := fun W y hy hyE N hN =>
    notchedCausality_exists_lt_right_of_notMem_edge hy hyE hN
  exact Causality.dual_causallyPlain.1
    (Causality.causallyPlain_of_locZ hP hZp hZm interior_notchedEdge)

/-! ## Not causally open in the past, at the corner -/

/-- `J⁻_U(V)` of a set above the axis `{v = 0}` lies in `{u ≤ 0}`: a point of `V` has `u ≤ 0`, as
`M` misses `Q`. -/
theorem notchedCausality_Jminus_subset {V : Set notchedPlane}
    (hV : ∀ y ∈ V, 0 < (y : ℝ × ℝ).2) :
    notchedCausality.Jminus U V ⊆ {x | (x : ℝ × ℝ).1 ≤ 0} := by
  rintro x ⟨y, hy, hxy⟩
  have hle := notchedCausality_le_prod hxy
  rcases y.property with h | h
  · exact hle.1.trans h
  · exact absurd h (not_le.2 (hV y hy))

/-- A set of `M` containing the corner and contained in `{u ≤ 0}` is not open: the points
`(ε, 0)` of `M` approach the corner. -/
theorem not_isOpen_of_notchedCorner_mem {S : Set notchedPlane} (h0 : notchedCorner ∈ S)
    (hS : S ⊆ {x | (x : ℝ × ℝ).1 ≤ 0}) : ¬ IsOpen S := by
  intro hO
  obtain ⟨s, hs, hsS⟩ := (mem_nhds_subtype _ _ _).1 (hO.mem_nhds h0)
  have hs' : ∀ᶠ w in 𝓝 (notchedCorner : ℝ × ℝ), w ∈ s := hs
  have hT : Tendsto (fun ε : ℝ => ((ε, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 (notchedCorner : ℝ × ℝ)) :=
    (by fun_prop : Continuous fun ε : ℝ => ((ε, 0) : ℝ × ℝ)).tendsto' 0 _ rfl
  obtain ⟨ε, hεs, hε⟩ := (((hT.eventually hs').filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have := hS (hsS (show ((⟨(ε, 0), Or.inr le_rfl⟩ : notchedPlane) : ℝ × ℝ) ∈ s from hεs))
  exact absurd (show ε ≤ 0 from this) (not_le.2 hε)

/-- **`J⁻_M` of a box about `(0, 1)` on the notch's upper edge is not open**: it contains the
corner (by the null segment `{0} × [0, 1]`) and lies in `{u ≤ 0}`. -/
theorem notchedCausality_not_isOpen_Jminus_box :
    ¬ IsOpen (notchedCausality.Jminus ⊤
      {y | (y : ℝ × ℝ).1 ∈ Ioo (-1 / 2 : ℝ) (1 / 2) ∧ (y : ℝ × ℝ).2 ∈ Ioo (1 / 2 : ℝ) (3 / 2)}) :=
  not_isOpen_of_notchedCorner_mem
    ⟨⟨(0, 1), Or.inl le_rfl⟩, ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩,
      notchedCausality_le_top_iff.2 ⟨le_rfl, zero_le_one⟩⟩
    (notchedCausality_Jminus_subset fun y hy => by linarith [hy.2.1])

/-- **No open set about the corner is causally open in the past**: with `V = W ∩ {v > 0}`,
`J⁻_W(V)` contains the corner and lies in `{u ≤ 0}`. -/
theorem notchedCausality_not_causallyOpenPastOn (hW : notchedCorner ∈ W) :
    ¬ notchedCausality.dual.CausallyOpenFutureOn W := by
  intro h
  let H : Opens notchedPlane := ⟨{y | 0 < (y : ℝ × ℝ).2},
    isOpen_lt continuous_const (continuous_snd.comp continuous_subtype_val)⟩
  have hopen := h W (W ⊓ H) le_rfl inf_le_left
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 W.isOpen _ hW
  -- the null segment from the corner to `(0, δ/2)`, inside the ball
  have hq : ((0, δ / 2) : ℝ × ℝ) ∈ Metric.ball (notchedCorner : ℝ × ℝ) δ := by
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [notchedCorner, Real.dist_eq, sub_zero, abs_zero, abs_of_pos (half_pos hδ)]
    rw [max_lt_iff]
    exact ⟨hδ, half_lt_self hδ⟩
  have hseg : segment ℝ (notchedCorner : ℝ × ℝ) (0, δ / 2) ⊆
      Subtype.val '' (W : Set notchedPlane) := by
    intro w hw
    have hle : (notchedCorner : ℝ × ℝ) ≤ (0, δ / 2) :=
      ⟨show (0 : ℝ) ≤ 0 from le_rfl, show (0 : ℝ) ≤ δ / 2 from (half_pos hδ).le⟩
    have hwM : w ∈ notchedPlane :=
      segment_subset_notchedPlane hle (Or.inl (show (0 : ℝ) ≤ 0 from le_rfl)) hw
    refine ⟨⟨w, hwM⟩, hball ?_, rfl⟩
    rw [Metric.mem_ball, Subtype.dist_eq]
    exact (convex_ball _ _).segment_subset (Metric.mem_ball_self hδ) hq hw
  have h0 : notchedCorner ∈ notchedCausality.Jminus W (W ⊓ H : Opens notchedPlane) :=
    ⟨⟨(0, δ / 2), Or.inl le_rfl⟩, ⟨hball (by rw [Metric.mem_ball, Subtype.dist_eq]; exact hq),
      show (0 : ℝ) < δ / 2 from half_pos hδ⟩,
      TransGen.single ⟨⟨show (0 : ℝ) ≤ 0 from le_rfl, show (0 : ℝ) ≤ δ / 2 from (half_pos hδ).le⟩,
        hseg⟩⟩
  exact not_isOpen_of_notchedCorner_mem h0 (notchedCausality_Jminus_subset fun y hy => hy.2)
    hopen

/-- **The notched plane is not causally open in the past.** -/
theorem notchedCausality_not_causallyOpenPast : ¬ notchedCausality.dual.CausallyOpenFuture :=
  fun h => notchedCausality_not_causallyOpenPastOn (W := ⊤) trivial
    (Causality.causallyOpenFutureOn_top.2 h)

/-- **The notched plane is not causally open** (DEC-8's two-sided reading). -/
theorem notchedCausality_not_causallyOpen : ¬ notchedCausality.CausallyOpen := fun h =>
  notchedCausality_not_causallyOpenPast h.2

/-- **Not locally causally open** (two-sided): not at the corner. -/
theorem notchedCausality_not_locallyCausallyOpen : ¬ notchedCausality.LocallyCausallyOpen :=
  fun h =>
    let ⟨_, hW, hW'⟩ := h.2 notchedCorner
    notchedCausality_not_causallyOpenPastOn hW hW'

/-! ## No chronal neighbours; not tarentin at the corner -/

/-- **Nothing is chronologically after a point of the edge**: `I⁺` in `ℝ²` of such a point lies in
`Q`, which `M` misses. -/
theorem notchedCausality_not_lt_of_mem_edge (hx : x ∈ notchedEdge) : ¬ notchedCausality.lt U x y :=
  fun h => by
    obtain ⟨h1, h2⟩ := notchedCausality_lt_prod h
    rcases y.property with hy | hy
    · linarith [hx.1]
    · linarith [hx.2]

/-- **No chronal neighbours** (the corner has no chronal future). -/
theorem notchedCausality_not_chronalNeighbours : ¬ notchedCausality.ChronalNeighbours :=
  fun h =>
    let ⟨p, _, hp⟩ := h.2 ⊤ notchedCorner trivial
    notchedCausality_not_lt_of_mem_edge (U := ⊤) (y := p) ⟨le_rfl, le_rfl⟩ hp

/-- **The corner lies in no open diamond**: the points `(ε, 0)` and `(0, ε)` of `M` near it would
precede the top vertex, which would lie in `Q`. -/
theorem notchedCorner_notMem_openDiamond (p q : notchedPlane) :
    notchedCorner ∉ notchedCausality.openDiamond ⊤ p q := by
  intro h
  obtain ⟨s, hs, hsD⟩ := (mem_nhds_subtype _ _ _).1 (Causality.isOpen_openDiamond.mem_nhds h)
  have hs' : ∀ᶠ w in 𝓝 (notchedCorner : ℝ × ℝ), w ∈ s := hs
  have hT1 : Tendsto (fun ε : ℝ => ((ε, 0) : ℝ × ℝ)) (𝓝 0) (𝓝 (notchedCorner : ℝ × ℝ)) :=
    (by fun_prop : Continuous fun ε : ℝ => ((ε, 0) : ℝ × ℝ)).tendsto' 0 _ rfl
  have hT2 : Tendsto (fun ε : ℝ => ((0, ε) : ℝ × ℝ)) (𝓝 0) (𝓝 (notchedCorner : ℝ × ℝ)) :=
    (by fun_prop : Continuous fun ε : ℝ => ((0, ε) : ℝ × ℝ)).tendsto' 0 _ rfl
  obtain ⟨ε, ⟨h1, h2⟩, hε⟩ := ((((hT1.eventually hs').and (hT2.eventually hs')).filter_mono
    nhdsWithin_le_nhds).and (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] 0)).exists
  have hε' : (0 : ℝ) < ε := hε
  have hd1 := Causality.openDiamond_subset_diamond
    (hsD (show ((⟨(ε, 0), Or.inr le_rfl⟩ : notchedPlane) : ℝ × ℝ) ∈ s from h1))
  have hd2 := Causality.openDiamond_subset_diamond
    (hsD (show ((⟨(0, ε), Or.inl le_rfl⟩ : notchedPlane) : ℝ × ℝ) ∈ s from h2))
  have hq1 : ε ≤ (q : ℝ × ℝ).1 := (notchedCausality_le_prod (Causality.mem_diamond.1 hd1).2).1
  have hq2 : ε ≤ (q : ℝ × ℝ).2 := (notchedCausality_le_prod (Causality.mem_diamond.1 hd2).2).2
  rcases q.property with hq | hq
  · linarith
  · linarith

/-- **The notched plane is not tarentin** (`def:tarentin_spacetime`), at the corner. -/
theorem notchedCausality_not_tarentin : ¬ notchedCausality.Tarentin := fun h =>
  let ⟨p, _, q, _, hpq⟩ := h notchedCorner univ univ_mem
  notchedCorner_notMem_openDiamond p q hpq

/-! ## The other ladder properties -/

/-- **Causal**: `≤` lies in the product order. -/
theorem notchedCausality_isCausal : notchedCausality.IsCausal := fun _ _ hxy hyx =>
  Subtype.ext (le_antisymm (notchedCausality_le_prod hxy) (notchedCausality_le_prod hyx))

/-- **The diamonds are the order intervals of the product order**, traced on `M`. -/
theorem notchedCausality_diamond_eq (p q : notchedPlane) :
    notchedCausality.diamond ⊤ p q = Subtype.val ⁻¹' Icc (p : ℝ × ℝ) q := by
  ext z
  rw [Causality.mem_diamond, notchedCausality_le_top_iff, notchedCausality_le_top_iff]
  rfl

/-- **Causally compact**: `M` is closed in `ℝ²`, so the trace of a compact order interval is
compact. -/
theorem notchedCausality_causallyCompact : notchedCausality.CausallyCompact := fun p q => by
  rw [notchedCausality_diamond_eq]
  exact isClosed_notchedPlane.isClosedEmbedding_subtypeVal.isCompact_preimage isCompact_Icc

/-- **Globally hyperbolic** (`def:globally_hyperbolic`). -/
theorem notchedCausality_globallyHyperbolic : notchedCausality.GloballyHyperbolic :=
  ⟨notchedCausality_isCausal, notchedCausality_causallyCompact⟩

/-- **Strongly causal, with open causally convex neighbourhoods**: small open boxes. -/
theorem notchedCausality_stronglyCausalOpen : notchedCausality.StronglyCausalOpen := by
  intro p N hN
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hN
  let B : Set notchedPlane := {z | (z : ℝ × ℝ).1 ∈ Ioo ((p : ℝ × ℝ).1 - δ) ((p : ℝ × ℝ).1 + δ) ∧
    (z : ℝ × ℝ).2 ∈ Ioo ((p : ℝ × ℝ).2 - δ) ((p : ℝ × ℝ).2 + δ)}
  have hB : IsOpen B := (isOpen_Ioo.preimage (continuous_fst.comp continuous_subtype_val)).inter
    (isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val))
  refine ⟨⟨B, hB⟩, ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩, fun z hz => hball ?_,
    fun _ _ => trivial, fun a ha b hb w hw => ?_⟩
  · obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
    rw [Metric.mem_ball, Subtype.dist_eq, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq,
      abs_sub_lt_iff, abs_sub_lt_iff]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rw [notchedCausality_diamond_eq] at hw
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hw
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := ha
    obtain ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ := hb
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- **A time function** (the ladder node `time_function`): `u + v = 2t`. -/
theorem notchedCausality_hasTimeFunction : notchedCausality.HasTimeFunction := by
  refine ⟨fun z => (z : ℝ × ℝ).1 + (z : ℝ × ℝ).2, by fun_prop, fun x y hxy hne => ?_⟩
  obtain ⟨h1, h2⟩ := notchedCausality_le_prod hxy
  by_contra hlt
  exact hne (Subtype.ext (Prod.ext (by linarith) (by linarith)))

/-! ## The time reversal -/

theorem notchedCausality_dual_causallyArcConnected : notchedCausality.dual.CausallyArcConnected :=
  Causality.dual_causallyArcConnectedOn.2 notchedCausality_causallyArcConnected

theorem notchedCausality_dual_absolutelyMinimal : notchedCausality.dual.AbsolutelyMinimal :=
  notchedCausality_dual_causallyArcConnected.absolutelyMinimal

/-- Absolutely minimal on every open set, for every cover of it. -/
theorem notchedCausality_dual_absolutelyMinimalOn (W : Opens notchedPlane) :
    notchedCausality.dual.AbsolutelyMinimalOn W :=
  (Causality.CausallyArcConnectedOn.mono notchedCausality_dual_causallyArcConnected
    le_top).absolutelyMinimalOn

/-- The time reversal has a time function: `−(u + v)`. -/
theorem notchedCausality_dual_hasTimeFunction : notchedCausality.dual.HasTimeFunction := by
  refine ⟨fun z => -((z : ℝ × ℝ).1 + (z : ℝ × ℝ).2), by fun_prop, fun x y hxy hne => ?_⟩
  obtain ⟨h1, h2⟩ := notchedCausality_le_prod (show notchedCausality.le ⊤ y x from hxy)
  by_contra hlt
  exact hne (Subtype.ext (Prod.ext (by linarith) (by linarith)))

/-- **The time reversal is not locally causally open in the future**: not at the corner. -/
theorem notchedCausality_dual_not_locallyCausallyOpenFuture :
    ¬ notchedCausality.dual.LocallyCausallyOpenFuture := fun h =>
  let ⟨_, hW, hW'⟩ := h notchedCorner
  notchedCausality_not_causallyOpenPastOn hW hW'

/-! ## The separations -/

/-- **The notched plane, conjoined for the ladder**: Hausdorff and second countable; absolutely
minimal, causally arc-connected, causally plain, push-up (hence locally), causally open in the
future (hence locally), causal, causally compact, globally hyperbolic, strongly causal (both
forms), with a time function (hence curves extend); neither causally open nor locally causally
open, no chronal neighbours, not tarentin. -/
theorem notchedCausality_separates :
    T2Space notchedPlane ∧ SecondCountableTopology notchedPlane ∧
      notchedCausality.AbsolutelyMinimal ∧ notchedCausality.CausallyArcConnected ∧
      notchedCausality.CausallyPlain ∧ notchedCausality.PushUp ∧
      notchedCausality.LocallyPushUp ∧ notchedCausality.CausallyOpenFuture ∧
      notchedCausality.LocallyCausallyOpenFuture ∧ notchedCausality.IsCausal ∧
      notchedCausality.CausallyCompact ∧ notchedCausality.GloballyHyperbolic ∧
      notchedCausality.StronglyCausalOpen ∧ notchedCausality.StronglyCausal ∧
      notchedCausality.HasTimeFunction ∧ notchedCausality.CurvesExtend ∧
      ¬ notchedCausality.CausallyOpen ∧ ¬ notchedCausality.LocallyCausallyOpen ∧
      ¬ notchedCausality.ChronalNeighbours ∧ ¬ notchedCausality.Tarentin := by
  have hAC : notchedCausality.CausallyArcConnected := notchedCausality_causallyArcConnected
  have hAM : notchedCausality.AbsolutelyMinimal := notchedCausality_absolutelyMinimal
  have hPU : notchedCausality.PushUp := notchedCausality_pushUp
  have hCOF : notchedCausality.CausallyOpenFuture := notchedCausality_causallyOpenFuture
  have hGH : notchedCausality.GloballyHyperbolic := notchedCausality_globallyHyperbolic
  have hSCO : notchedCausality.StronglyCausalOpen := notchedCausality_stronglyCausalOpen
  have hTF : notchedCausality.HasTimeFunction := notchedCausality_hasTimeFunction
  have hNCO : ¬ notchedCausality.CausallyOpen := notchedCausality_not_causallyOpen
  -- the ladder steps (`causal_ladder`): push_up ⇒ locally_push_up, causally_open_future ⇒
  -- locally_causally_open_future, globally_hyperbolic ⇒ is_causal, causally_compact,
  -- strongly_causal_open ⇒ strongly_causal, time_function ⇒ curves_extend; and, read backwards,
  -- absolutely_minimal ∧ locally_causally_open ⇒ causally_open and push_up ∧ chronal_neighbours ⇒
  -- causally_open
  exact ⟨inferInstance, inferInstance, hAM, hAC, notchedCausality_causallyPlain, hPU,
    by causal_ladder, hCOF, by causal_ladder, by causal_ladder, by causal_ladder, hGH, hSCO,
    by causal_ladder, hTF, by causal_ladder, hNCO, fun _ => hNCO (by causal_ladder),
    fun _ => hNCO (by causal_ladder), notchedCausality_not_tarentin⟩

/-- **The time-reversed notched plane, conjoined for the ladder**: Hausdorff and second
countable; absolutely minimal, causally arc-connected, causally plain, push-up (hence locally),
causal, causally compact, globally hyperbolic, strongly causal (both forms), with a time function
(hence curves extend); not causally open in the future, nor locally, nor two-sided, nor locally
two-sided, no chronal neighbours, not tarentin. -/
theorem notchedCausality_dual_separates :
    T2Space notchedPlane ∧ SecondCountableTopology notchedPlane ∧
      notchedCausality.dual.AbsolutelyMinimal ∧ notchedCausality.dual.CausallyArcConnected ∧
      notchedCausality.dual.CausallyPlain ∧ notchedCausality.dual.PushUp ∧
      notchedCausality.dual.LocallyPushUp ∧ notchedCausality.dual.IsCausal ∧
      notchedCausality.dual.CausallyCompact ∧ notchedCausality.dual.GloballyHyperbolic ∧
      notchedCausality.dual.StronglyCausalOpen ∧ notchedCausality.dual.StronglyCausal ∧
      notchedCausality.dual.HasTimeFunction ∧ notchedCausality.dual.CurvesExtend ∧
      ¬ notchedCausality.dual.CausallyOpenFuture ∧
      ¬ notchedCausality.dual.LocallyCausallyOpenFuture ∧
      ¬ notchedCausality.dual.CausallyOpen ∧ ¬ notchedCausality.dual.LocallyCausallyOpen ∧
      ¬ notchedCausality.dual.ChronalNeighbours ∧ ¬ notchedCausality.dual.Tarentin := by
  have hAC : notchedCausality.dual.CausallyArcConnected :=
    notchedCausality_dual_causallyArcConnected
  have hAM : notchedCausality.dual.AbsolutelyMinimal := notchedCausality_dual_absolutelyMinimal
  have hCP : notchedCausality.dual.CausallyPlain :=
    Causality.dual_causallyPlain.2 notchedCausality_causallyPlain
  have hPU : notchedCausality.dual.PushUp := Causality.dual_pushUp.2 notchedCausality_pushUp
  have hGH : notchedCausality.dual.GloballyHyperbolic :=
    Causality.dual_globallyHyperbolic.2 notchedCausality_globallyHyperbolic
  have hSCO : notchedCausality.dual.StronglyCausalOpen :=
    Causality.dual_stronglyCausalOpen.2 notchedCausality_stronglyCausalOpen
  have hTF : notchedCausality.dual.HasTimeFunction := notchedCausality_dual_hasTimeFunction
  have hNCOF : ¬ notchedCausality.dual.CausallyOpenFuture := notchedCausality_not_causallyOpenPast
  have hNT : ¬ notchedCausality.dual.Tarentin := fun h =>
    notchedCausality_not_tarentin (Causality.dual_tarentin.1 h)
  -- the ladder steps (`causal_ladder` on the term `notchedCausality.dual`, kb/0091), forwards as
  -- for the notched plane, and backwards from ¬ causally_open_future: causally_open ⇒
  -- causally_open_future, absolutely_minimal ∧ locally_causally_open_future ⇒
  -- causally_open_future, locally_causally_open ⇒ locally_causally_open_future, and
  -- push_up ∧ chronal_neighbours ⇒ causally_open
  exact ⟨inferInstance, inferInstance, hAM, hAC, hCP, hPU, by causal_ladder, by causal_ladder,
    by causal_ladder, hGH, hSCO, by causal_ladder, hTF, by causal_ladder, hNCOF,
    fun _ => hNCOF (by causal_ladder), fun _ => hNCOF (by causal_ladder),
    fun _ => hNCOF (by causal_ladder), fun _ => hNCOF (by causal_ladder), hNT⟩

/-- **Causal plainness does not give causal openness**, among Hausdorff, second countable
spacetimes absolutely minimal on every open set for every cover (either reading of
`defi:causalite`), push-up, globally hyperbolic and causally open in the future (the notched
plane). -/
theorem not_locallyCausallyOpen_of_causallyPlain_bare :
    ¬ ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      (C : Causality M), (∀ W : Opens M, C.AbsolutelyMinimalOn W) → C.CausallyPlain →
        C.PushUp → C.GloballyHyperbolic → C.CausallyOpenFuture → C.LocallyCausallyOpen :=
  fun h => notchedCausality_not_locallyCausallyOpen
    (h notchedPlane notchedCausality notchedCausality_absolutelyMinimalOn
      notchedCausality_causallyPlain notchedCausality_pushUp notchedCausality_globallyHyperbolic
      notchedCausality_causallyOpenFuture)

/-- **Causal plainness does not give causal openness in the future, not even locally**, in the
same class (the time-reversed notched plane). -/
theorem not_locallyCausallyOpenFuture_of_causallyPlain_bare :
    ¬ ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      (C : Causality M), (∀ W : Opens M, C.AbsolutelyMinimalOn W) → C.CausallyPlain →
        C.PushUp → C.GloballyHyperbolic → C.LocallyCausallyOpenFuture :=
  fun h => notchedCausality_dual_not_locallyCausallyOpenFuture
    (h notchedPlane notchedCausality.dual notchedCausality_dual_absolutelyMinimalOn
      (Causality.dual_causallyPlain.2 notchedCausality_causallyPlain)
      (Causality.dual_pushUp.2 notchedCausality_pushUp)
      (Causality.dual_globallyHyperbolic.2 notchedCausality_globallyHyperbolic))

end Causal
