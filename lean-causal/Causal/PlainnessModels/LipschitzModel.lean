import Causal.PlainnessModels.LorentzForm
import Causal.CausallyPlainLocZ
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The causality of a locally Lipschitz Lorentzian metric on `ℝ^{1+n}`

Target `T-ett-plainness-models` (DEC-168: « prove plainness for … Lipschitz metrics », layer 3).
No label is marked here: this is the coordinate model of « Lorentzian manifold » used by
`Causal.PlainnessModels.Lorentzian` for `cor:K_lorentzien`.

> Such a manifold comes naturally with a ``causality'': a distinguished class $\CC$ of connected
> curves, stable under concatenation and under passing to connected subsets. An element of this
> class is called a causal curve, and one says that a point $p$ lies in the past of a point $q$
> when there is such a curve starting at $p$ and ending at $q$. (`ETT.tex:167–171`)

## What is here (no `sorry`)

* `LipschitzMetric n`: a field `g` of Lorentzian forms on `Minkowski n = ℝ × ℝⁿ`
  (`Lorentz.IsLorentzian`, at every point), **locally Lipschitz** (`LocallyLipschitz g`, operator
  norm), with a continuous time orientation `T` (`g x (T x) (T x) < 0`).
* Its causal paths (`IsCausalPath`, Chruściel–Grant's causal curves: Lipschitz, the derivative
  future causal almost everywhere) and timelike paths (`IsTimelikePath`: `C¹` on `[a, b]`, the
  derivative future timelike at every point); `≤_U` is the reflexive-transitive closure of causal
  paths in `U`, `≪_U` the transitive closure of timelike paths in `U` (concatenation, as
  `ETT.tex:168` asks).
* `LipschitzMetric.causality`: a library `Causality` (`≪_U` open in both variables, by
  perturbing the last or first timelike path, `IsTimelikePath.perturb`); local strong tarentinity
  in both directions (`locZplus`, `locZminus`), by segments along `T`.

## SCOPE (disclosed)

* **Coordinates.** The metric is given on all of `ℝ^{1+n}`. A chart of a Lipschitz Lorentzian
  manifold sends a ball onto a ball `B ⊂ ℝ^{1+n}`; composing `g` with the `1`-Lipschitz nearest-point
  retraction onto `B̄` gives a metric of this kind which agrees with the given one on `B`, and the
  relations of the open subsets of `B` only see paths in them. So nothing is lost (argued, not
  formalized).
* **Paths.** A causal path is asked to be Lipschitz on all of `ℝ` (any Lipschitz path on `[a, b]`
  is the restriction of one, `γ ∘ projIcc`), with `0` allowed as a derivative (a reparametrization
  removes it); a timelike path is asked to have a two-sided derivative at the ends (a `C¹` path on
  `[a, b]` extends to one). Timelike paths are `C¹` (piecewise `C¹` after the closure), as in
  Chruściel–Grant; that Lipschitz paths with almost-everywhere timelike derivative give the same
  `≪` at a Lipschitz metric is not used and not proved.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Set Filter Topology TopologicalSpace Metric Relation MeasureTheory

open scoped NNReal

/-- **A locally Lipschitz, time-oriented Lorentzian metric on `ℝ^{1+n}`.** -/
structure LipschitzMetric (n : ℕ) where
  /-- The metric. -/
  g : Minkowski n → (Minkowski n →L[ℝ] Minkowski n →L[ℝ] ℝ)
  /-- The time orientation. -/
  T : Minkowski n → Minkowski n
  lorentzian : ∀ x, Lorentz.IsLorentzian (g x)
  locallyLipschitz : LocallyLipschitz g
  continuous_T : Continuous T
  timelike : ∀ x, g x (T x) (T x) < 0

namespace LipschitzMetric

variable {n : ℕ} (L : LipschitzMetric n)

/-- Future causal at `x`. -/
def FC (x v : Minkowski n) : Prop := Lorentz.FC (L.g x) (L.T x) v

/-- Future timelike at `x`. -/
def FT (x v : Minkowski n) : Prop := Lorentz.FT (L.g x) (L.T x) v

/-- **A causal path** in `O` on `[a, b]`: Lipschitz, in `O`, its derivative future causal
almost everywhere. -/
def IsCausalPath (O : Set (Minkowski n)) (γ : ℝ → Minkowski n) (a b : ℝ) : Prop :=
  a ≤ b ∧ (∃ K, LipschitzWith K γ) ∧ MapsTo γ (Icc a b) O ∧
    ∀ᵐ s, s ∈ Ioo a b → ∃ v, HasDerivAt γ v s ∧ L.FC (γ s) v

/-- **A timelike path** in `O` on `[a, b]`, `a < b`: `C¹`, in `O`, its derivative future
timelike everywhere. -/
def IsTimelikePath (O : Set (Minkowski n)) (γ : ℝ → Minkowski n) (a b : ℝ) : Prop :=
  a < b ∧ ∃ γ' : ℝ → Minkowski n, ContinuousOn γ' (Icc a b) ∧
    (∀ s ∈ Icc a b, HasDerivAt γ (γ' s) s) ∧ MapsTo γ (Icc a b) O ∧
    ∀ s ∈ Icc a b, L.FT (γ s) (γ' s)

/-- One causal path in `O` from `x` to `y`. -/
def CausalStep (O : Set (Minkowski n)) (x y : Minkowski n) : Prop :=
  ∃ γ a b, L.IsCausalPath O γ a b ∧ γ a = x ∧ γ b = y

/-- One timelike path in `O` from `x` to `y`. -/
def TimeStep (O : Set (Minkowski n)) (x y : Minkowski n) : Prop :=
  ∃ γ a b, L.IsTimelikePath O γ a b ∧ γ a = x ∧ γ b = y

variable {L}

theorem continuous_g : Continuous L.g := L.locallyLipschitz.continuous

theorem continuous_pair : Continuous fun p : Minkowski n × Minkowski n => L.g p.1 p.2 p.2 :=
  ((continuous_g.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd

theorem continuous_pairT :
    Continuous fun p : Minkowski n × Minkowski n => L.g p.1 p.2 (L.T p.1) :=
  ((continuous_g.comp continuous_fst).clm_apply continuous_snd).clm_apply
    (L.continuous_T.comp continuous_fst)

theorem isOpen_FT {O : Set (Minkowski n)} (hO : IsOpen O) :
    IsOpen {p : Minkowski n × Minkowski n | p.1 ∈ O ∧ L.FT p.1 p.2} :=
  (hO.preimage continuous_fst).inter
    ((isOpen_lt continuous_pair continuous_const).inter (isOpen_lt continuous_pairT continuous_const))

theorem IsCausalPath.mono {O O' : Set (Minkowski n)} (h : O ⊆ O') {γ a b}
    (hγ : L.IsCausalPath O γ a b) : L.IsCausalPath O' γ a b :=
  ⟨hγ.1, hγ.2.1, hγ.2.2.1.mono_right h, hγ.2.2.2⟩

theorem IsTimelikePath.mono {O O' : Set (Minkowski n)} (h : O ⊆ O') {γ a b}
    (hγ : L.IsTimelikePath O γ a b) : L.IsTimelikePath O' γ a b := by
  obtain ⟨hab, γ', h1, h2, h3, h4⟩ := hγ
  exact ⟨hab, γ', h1, h2, h3.mono_right h, h4⟩

theorem IsTimelikePath.mapsTo {O : Set (Minkowski n)} {γ a b}
    (hγ : L.IsTimelikePath O γ a b) : MapsTo γ (Icc a b) O := by
  obtain ⟨-, γ', -, -, h3, -⟩ := hγ
  exact h3

theorem IsTimelikePath.continuousOn {O : Set (Minkowski n)} {γ a b}
    (hγ : L.IsTimelikePath O γ a b) : ContinuousOn γ (Icc a b) := by
  obtain ⟨-, γ', -, h2, -, -⟩ := hγ
  exact fun s hs => (h2 s hs).continuousAt.continuousWithinAt

/-- A timelike path gives a causal path (extended by `projIcc`). -/
theorem IsTimelikePath.causalStep {O : Set (Minkowski n)} {γ a b}
    (hγ : L.IsTimelikePath O γ a b) : L.CausalStep O (γ a) (γ b) := by
  obtain ⟨hab, γ', h1, h2, h3, h4⟩ := hγ
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn h1
  have hlip : LipschitzOnWith (Real.toNNReal B) γ (Icc a b) := by
    refine (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun s hs => (h2 s hs).hasDerivWithinAt) fun s hs => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact (hB s hs).trans (le_max_left _ _)
  set γ₁ : ℝ → Minkowski n := fun s => γ (projIcc a b hab.le s) with hγ₁
  have heq : EqOn γ₁ γ (Icc a b) := fun s hs => by simp [γ₁, projIcc_of_mem hab.le hs]
  refine ⟨γ₁, a, b, ⟨hab.le, ⟨Real.toNNReal B, ?_⟩, ?_, ?_⟩, heq ⟨le_rfl, hab.le⟩,
    heq ⟨hab.le, le_rfl⟩⟩
  · refine LipschitzWith.of_dist_le_mul fun s t => ?_
    have := hlip (projIcc a b hab.le s).2 (projIcc a b hab.le t).2
    rw [edist_dist, edist_dist] at this
    have h' := ENNReal.toReal_mono (by finiteness) this
    rw [ENNReal.toReal_ofReal dist_nonneg, ENNReal.toReal_mul, ENNReal.toReal_ofReal dist_nonneg]
      at h'
    simp only [ENNReal.coe_toReal] at h'
    refine h'.trans (mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _))
    have h := (LipschitzWith.projIcc hab.le).dist_le_mul s t
    simp only [NNReal.coe_one, one_mul] at h
    exact h
  · exact fun s hs => heq hs ▸ h3 hs
  · refine Eventually.of_forall fun s hs => ⟨γ' s, ?_, ?_⟩
    · refine (h2 s (Ioo_subset_Icc_self hs)).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht using heq (Ioo_subset_Icc_self ht)
    · rw [heq (Ioo_subset_Icc_self hs)]
      exact (h4 s (Ioo_subset_Icc_self hs)).fc

/-- **Perturbing a timelike path** by `φ(s) • w`, `φ` affine with `|φ| ≤ 1` on `[a, b]` and slope
at most `1 / (b − a)`, keeps it timelike in the open set `O` for `w` small. -/
theorem IsTimelikePath.perturb {O : Set (Minkowski n)} (hO : IsOpen O) {γ a b}
    (hγ : L.IsTimelikePath O γ a b) :
    ∃ δ > 0, ∀ w : Minkowski n, ‖w‖ < δ → ∀ c₀ c₁ : ℝ, |c₁| ≤ 1 / (b - a) →
      (∀ s ∈ Icc a b, |c₀ + c₁ * s| ≤ 1) →
      L.IsTimelikePath O (fun s => γ s + (c₀ + c₁ * s) • w) a b := by
  obtain ⟨hab, γ', h1, h2, h3, h4⟩ := hγ
  have hcont : ContinuousOn (fun s => (γ s, γ' s)) (Icc a b) :=
    (IsTimelikePath.continuousOn ⟨hab, γ', h1, h2, h3, h4⟩).prodMk h1
  have hK : IsCompact ((fun s => (γ s, γ' s)) '' Icc a b) := isCompact_Icc.image_of_continuousOn hcont
  have hsub : (fun s => (γ s, γ' s)) '' Icc a b ⊆
      {p : Minkowski n × Minkowski n | p.1 ∈ O ∧ L.FT p.1 p.2} := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨h3 hs, h4 s hs⟩
  obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open (isOpen_FT hO) hsub
  have hba : 0 < b - a := sub_pos.2 hab
  refine ⟨δ * min 1 (b - a), mul_pos hδ (lt_min one_pos hba), fun w hw c₀ c₁ hc₁ hφ => ?_⟩
  have hw1 : ‖w‖ < δ := hw.trans_le (mul_le_of_le_one_right hδ.le (min_le_left _ _))
  have hw2 : ‖w‖ / (b - a) < δ := by
    rw [div_lt_iff₀ hba]
    exact hw.trans_le (mul_le_mul_of_nonneg_left (min_le_right _ _) hδ.le)
  refine ⟨hab, fun s => γ' s + c₁ • w, h1.add continuousOn_const, fun s hs => ?_, ?_, ?_⟩
  · have : HasDerivAt (fun s : ℝ => c₀ + c₁ * s) c₁ s := by
      simpa using ((hasDerivAt_id s).const_mul c₁).const_add c₀
    exact (h2 s hs).add (this.smul_const w)
  all_goals
    have key : ∀ s ∈ Icc a b, (γ s + (c₀ + c₁ * s) • w, γ' s + c₁ • w) ∈
        {p : Minkowski n × Minkowski n | p.1 ∈ O ∧ L.FT p.1 p.2} := by
      intro s hs
      refine hth (mem_thickening_iff.2 ⟨(γ s, γ' s), ⟨s, hs, rfl⟩, ?_⟩)
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      refine ⟨(mul_le_of_le_one_left (norm_nonneg _) (hφ s hs)).trans_lt hw1, ?_⟩
      calc |c₁| * ‖w‖ ≤ 1 / (b - a) * ‖w‖ := mul_le_mul_of_nonneg_right hc₁ (norm_nonneg _)
        _ = ‖w‖ / (b - a) := by ring
        _ < δ := hw2
  · exact fun s hs => (key s hs).1
  · exact fun s hs => (key s hs).2

/-! ### The causality -/

variable (L)

/-- **The causality of `L`**: `≤_U` by chains of causal paths in `U`, `≪_U` by chains of
timelike paths in `U`. -/
def causality : Causality (Minkowski n) where
  le U x y := x ∈ U ∧ ReflTransGen (L.CausalStep U) x y
  lt U x y := TransGen (L.TimeStep U) x y
  le_mem_left h := h.1
  le_mem_right {U x y} h := by
    obtain ⟨hx, h⟩ := h
    rcases h.cases_tail with rfl | ⟨c, -, γ, a, b, hγ, -, rfl⟩
    · exact hx
    · exact hγ.2.2.1 ⟨hγ.1, le_rfl⟩
  lt_mem_left {U x y} h := by
    obtain ⟨c, ⟨γ, a, b, hγ, rfl, -⟩, -⟩ := TransGen.head'_iff.1 h
    exact hγ.mapsTo ⟨le_rfl, hγ.1.le⟩
  lt_mem_right {U x y} h := by
    obtain ⟨c, -, γ, a, b, hγ, -, rfl⟩ := TransGen.tail'_iff.1 h
    exact hγ.mapsTo ⟨hγ.1.le, le_rfl⟩
  le_refl hx := ⟨hx, ReflTransGen.refl⟩
  le_trans h₁ h₂ := ⟨h₁.1, h₁.2.trans h₂.2⟩
  lt_trans h₁ h₂ := h₁.trans h₂
  le_mono {U V} hVU x y h := by
    refine ⟨hVU h.1, h.2.mono fun a b hab => ?_⟩
    obtain ⟨γ, s, t, hγ, h1, h2⟩ := hab
    exact ⟨γ, s, t, hγ.mono hVU, h1, h2⟩
  lt_mono {U V} hVU x y h := by
    refine h.mono fun a b hab => ?_
    obtain ⟨γ, s, t, hγ, h1, h2⟩ := hab
    exact ⟨γ, s, t, hγ.mono hVU, h1, h2⟩
  le_of_lt {U x y} h := by
    refine ⟨?_, ?_⟩
    · obtain ⟨c, ⟨γ, a, b, hγ, rfl, -⟩, -⟩ := TransGen.head'_iff.1 h
      exact hγ.mapsTo ⟨le_rfl, hγ.1.le⟩
    · refine (h.mono fun a b hab => ?_).to_reflTransGen
      obtain ⟨γ, s, t, hγ, rfl, rfl⟩ := hab
      exact hγ.causalStep
  isOpen_lt_right U x := by
    refine Metric.isOpen_iff.2 fun y hy => ?_
    obtain ⟨c, hxc, γ, a, b, hγ, rfl, rfl⟩ := TransGen.tail'_iff.1 hy
    obtain ⟨δ, hδ, hpert⟩ := hγ.perturb U.isOpen
    have hba : 0 < b - a := sub_pos.2 hγ.1
    refine ⟨δ, hδ, fun z hz => ?_⟩
    have hz' : ‖z - γ b‖ < δ := by rwa [← dist_eq_norm]
    have hp := hpert (z - γ b) hz' (-a / (b - a)) (1 / (b - a)) (by
      rw [abs_of_pos (by positivity)]) fun s hs => by
        have : -a / (b - a) + 1 / (b - a) * s = (s - a) / (b - a) := by field_simp; ring
        rw [this, abs_le]
        constructor
        · have : 0 ≤ (s - a) / (b - a) := div_nonneg (by linarith [hs.1]) hba.le
          linarith
        · rw [div_le_one hba]; linarith [hs.2]
    refine TransGen.tail' hxc ⟨_, a, b, hp, ?_, ?_⟩
    · show γ a + (-a / (b - a) + 1 / (b - a) * a) • (z - γ b) = γ a
      have : -a / (b - a) + 1 / (b - a) * a = 0 := by field_simp; ring
      rw [this, zero_smul, add_zero]
    · show γ b + (-a / (b - a) + 1 / (b - a) * b) • (z - γ b) = z
      have : -a / (b - a) + 1 / (b - a) * b = 1 := by field_simp; ring
      rw [this, one_smul, add_sub_cancel]
  isOpen_lt_left U x := by
    refine Metric.isOpen_iff.2 fun y hy => ?_
    obtain ⟨c, ⟨γ, a, b, hγ, rfl, rfl⟩, hcx⟩ := TransGen.head'_iff.1 hy
    obtain ⟨δ, hδ, hpert⟩ := hγ.perturb U.isOpen
    have hba : 0 < b - a := sub_pos.2 hγ.1
    refine ⟨δ, hδ, fun z hz => ?_⟩
    have hz' : ‖z - γ a‖ < δ := by rwa [← dist_eq_norm]
    have hp := hpert (z - γ a) hz' (b / (b - a)) (-1 / (b - a)) (by
      rw [abs_div, abs_neg, abs_one, abs_of_pos hba]) fun s hs => by
        have : b / (b - a) + -1 / (b - a) * s = (b - s) / (b - a) := by field_simp; ring
        rw [this, abs_le]
        constructor
        · have : 0 ≤ (b - s) / (b - a) := div_nonneg (by linarith [hs.2]) hba.le
          linarith
        · rw [div_le_one hba]; linarith [hs.1]
    refine TransGen.head' ⟨_, a, b, hp, ?_, ?_⟩ hcx
    · show γ a + (b / (b - a) + -1 / (b - a) * a) • (z - γ a) = z
      have : b / (b - a) + -1 / (b - a) * a = 1 := by field_simp; ring
      rw [this, one_smul, add_sub_cancel]
    · show γ b + (b / (b - a) + -1 / (b - a) * b) • (z - γ a) = γ b
      have : b / (b - a) + -1 / (b - a) * b = 0 := by field_simp; ring
      rw [this, zero_smul, add_zero]

variable {L}

theorem causality_le_iff {U : Opens (Minkowski n)} {x y : Minkowski n} :
    L.causality.le U x y ↔ x ∈ U ∧ ReflTransGen (L.CausalStep U) x y := Iff.rfl

theorem causality_lt_iff {U : Opens (Minkowski n)} {x y : Minkowski n} :
    L.causality.lt U x y ↔ TransGen (L.TimeStep U) x y := Iff.rfl

/-! ### Segments along `T`: local strong tarentinity -/

/-- **A straight segment** `s ↦ x + s • v`, `s ∈ [a, b]`, whose points all see `v` future
timelike, is a timelike path. -/
theorem isTimelikePath_segment {O : Set (Minkowski n)} {x v : Minkowski n} {a b : ℝ} (hab : a < b)
    (hO : ∀ s ∈ Icc a b, x + s • v ∈ O) (hT : ∀ s ∈ Icc a b, L.FT (x + s • v) v) :
    L.IsTimelikePath O (fun s => x + s • v) a b := by
  refine ⟨hab, fun _ => v, continuousOn_const, fun s _ => ?_, fun s hs => hO s hs, hT⟩
  simpa using ((hasDerivAt_id s).smul_const v).const_add x

/-- Near `x`, the segments along `T x` are timelike in every open set containing `x`. -/
theorem exists_segment_T {W : Set (Minkowski n)} (hW : W ∈ 𝓝 x) :
    ∃ ε > 0, ∀ s : ℝ, |s| ≤ ε → x + s • L.T x ∈ W ∧ L.FT (x + s • L.T x) (L.T x) := by
  have hFT : {y | L.FT y (L.T x)} ∈ 𝓝 x := by
    refine IsOpen.mem_nhds ?_ ⟨L.timelike x, L.timelike x⟩
    exact (isOpen_lt ((continuous_g.clm_apply continuous_const).clm_apply continuous_const)
      continuous_const).inter (isOpen_lt ((continuous_g.clm_apply continuous_const).clm_apply
        L.continuous_T) continuous_const)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hW hFT)
  refine ⟨ρ / (‖L.T x‖ + 1), div_pos hρ (by positivity), fun s hs => hball ?_⟩
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  calc |s| * ‖L.T x‖ ≤ ρ / (‖L.T x‖ + 1) * ‖L.T x‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ < ρ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg (L.T x)]

/-- **Strong tarentinity in the future, in every open set.** -/
theorem locZplus : E0LM.LocZplus L.causality := by
  intro W y hy N hN
  obtain ⟨ε, hε, h⟩ := exists_segment_T (L := L) (inter_mem (W.isOpen.mem_nhds hy) hN)
  refine ⟨y + ε • L.T y, (h ε (by rw [abs_of_pos hε])).1.2, TransGen.single ⟨_, 0, ε,
    isTimelikePath_segment hε (fun s hs => (h s (by rw [abs_of_nonneg hs.1]; exact hs.2)).1.1)
      (fun s hs => (h s (by rw [abs_of_nonneg hs.1]; exact hs.2)).2), by simp, rfl⟩⟩

/-- **Strong tarentinity in the past, in every open set.** -/
theorem locZminus : E0LM.LocZminus L.causality ∅ := by
  intro W y hy _ N hN
  obtain ⟨ε, hε, h⟩ := exists_segment_T (L := L) (inter_mem (W.isOpen.mem_nhds hy) hN)
  have hs' : ∀ s ∈ Icc (-ε) 0, |s| ≤ ε := fun s hs => by
    rw [abs_le]; exact ⟨hs.1, hs.2.trans hε.le⟩
  refine ⟨y + (-ε) • L.T y, (h (-ε) (by rw [abs_neg, abs_of_pos hε])).1.2, TransGen.single ⟨_, -ε,
    0, isTimelikePath_segment (by linarith) (fun s hs => (h s (hs' s hs)).1.1)
      (fun s hs => (h s (hs' s hs)).2), rfl, by simp⟩⟩

end LipschitzMetric

end Causal
