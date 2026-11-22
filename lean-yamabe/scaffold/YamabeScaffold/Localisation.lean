import YamabeScaffold.HalfSpace

/-!
# Chart localisation on a compact manifold with boundary: the metric and the volume read in charts

Labels (NOT marked: infrastructure for the manifold theorems of `YamabeScaffold.ManifoldTheorems` and `YamabeScaffold.Compactness`):

* `lem:kobayashi` — `Yamabegap.tex:613` (statement l.613–625, proof l.626–638): the Sobolev
  embedding its proof cites (l.637) is localised here to charts.
* `lem:positivity` — `Yamabegap.tex:715` (statement l.715–718, proof l.719–721): the finite energy
  of a `C¹` function, and the localisation of the trace theorem it cites (l.720). The Rellich
  theorem is not localised here (no file does yet).

> by the Sobolev embedding $W^{1,2}(\Sigma)\hookrightarrow L^{\pstar}(\Sigma)$ on compact manifolds
> with boundary \cite{Hebey1996}. (l.637)

## What is proved

* **The metric in a chart.** `Mfd.chart_comparison`: near every point `x₀`, uniformly in `u`, the
  Riemannian gradient norm `|∇u|_g(y)` and the norm of the derivative of `u` read in the chart at
  `x₀` (within the half-space, `Mfd.dChart`) are comparable, by constants independent of `u`
  (Mathlib's comparison of a continuous Riemannian metric with the trivialization of the bundle,
  `eventually_norm_trivializationAt_lt`, `eventually_norm_symmL_trivializationAt_lt`, and the chain
  rule `Mfd.hasFDerivWithinAt_inChart`). From it `Mfd.gradNorm_bdd`: a `C¹` function on a compact
  manifold has bounded `|∇u|_g`.
* **Measures in a chart.** `Mfd.map_restrict_comparable`, `Mfd.eLpNorm_chart_comparable`: a
  locally-Lebesgue `μ` pushed by the chart is comparable to Lebesgue measure on the image, and
  `L^p` norms transfer both ways; `Mfd.map_restrict_le_of` for a boundary measure.
* **Functions in a chart.** `Mfd.chartFun` (cut off outside the chart's target): `C¹` on the
  closed half-space and compactly supported for a `C¹` function supported in the chart's source
  (`Mfd.contDiffOn_chartFun`, `Mfd.hasCompactSupport_chartFun`), its half-space derivative is the
  chart derivative (`Mfd.fderivWithin_chartFun`) and vanishes off the image of the support;
  the product rule `Mfd.dChart_mul`.
* **Good chart neighbourhoods** (`Mfd.GoodChart`, `Mfd.exists_goodChart`) and, on them,
  `Mfd.eLpNorm_dChart_mul_le`, **`Mfd.local_sobolev`** and **`Mfd.local_trace`** (a boundary point
  goes to `{z₀ = 0}`: `Mfd.chart_boundary`).
* **`Mfd.assemble`**: a finite smooth partition of unity (Mathlib's
  `SmoothPartitionOfUnity.exists_isSubordinate`) subordinate to good neighbourhoods turns the
  local estimates into the global ones.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ` compact Riemannian with boundary | ✓ carried as in `YamabeScaffold.Sobolev`: `CompactSpace`, `T2Space`, smooth `g`; only the continuity of `g` is used |
| `u ∈ W^{1,2}(Σ)` | ⚠ read as `C¹(M)`, as in round 1 (OQ-93 (b)) |

## SCOPE (disclosed)

* Infrastructure only: no label of the paper is certified here. The theorems it serves are in
  `YamabeScaffold.ManifoldTheorems`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set Bundle
open scoped ENNReal NNReal Manifold ContDiff Bundle

noncomputable section

namespace Yamabe

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M]

/-! ## 1. The gradient norm read in a chart -/

variable (N) in
/-- `u` read in the chart at `x₀`: `u ∘ (extChartAt x₀)⁻¹`, a function on `ℝ^N` (junk off the
chart's target). -/
def inChart (x₀ : M) (u : M → ℝ) : EuclideanSpace ℝ (Fin N) → ℝ :=
  u ∘ (extChartAt (𝓡∂ N) x₀).symm

variable (N) in
/-- The derivative of `u` read in the chart at `x₀`, within the half-space, at the image of `y`. -/
def dChart (x₀ : M) (u : M → ℝ) (y : M) : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ :=
  fderivWithin ℝ (inChart N x₀ u) (range (𝓡∂ N)) (extChartAt (𝓡∂ N) x₀ y)

lemma gradNorm_nonneg (g : RiemannianMetric N M) (u : M → ℝ) (x : M) : 0 ≤ gradNorm g u x :=
  Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ abs_nonneg _

/-- `|∇u|_g(x)` is the operator norm of `du_x` for the inner product `g_x`. -/
lemma gradNorm_eq_norm_dcov (g : RiemannianMetric N M) (u : M → ℝ) (x : M) :
    letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ N) x) := ⟨g.toRiemannianMetric⟩
    gradNorm g u x = ‖dcov (N := N) u x‖ := by
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ N) x) := ⟨g.toRiemannianMetric⟩
  have hnorm : ∀ v : TangentSpace (𝓡∂ N) x, ‖v‖ ^ 2 = g.inner x v v := by
    intro v
    rw [@norm_sq_eq_re_inner ℝ]
    rfl
  have hset : {v : TangentSpace (𝓡∂ N) x | g.inner x v v ≤ 1} = Metric.closedBall 0 1 := by
    ext v
    simp only [Set.mem_setOf_eq, mem_closedBall_zero_iff]
    rw [← hnorm]
    constructor
    · intro h; nlinarith [norm_nonneg v]
    · intro h; nlinarith [norm_nonneg v]
  unfold gradNorm
  rw [hset, ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
  rfl

/-- The chain rule in a chart: `u` read in the chart at `x₀` has derivative `du_y` composed with
the derivative of the inverse chart. -/
lemma hasFDerivWithinAt_inChart (x₀ y : M) (hy : y ∈ (chartAt (EuclideanHalfSpace N) x₀).source)
    (u : M → ℝ) (hu : MDifferentiableAt (𝓡∂ N) 𝓘(ℝ, ℝ) u y) :
    HasFDerivWithinAt (inChart N x₀ u) ((dcov (N := N) u y).comp (mfderivWithin
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (𝓡∂ N) (extChartAt (𝓡∂ N) x₀).symm (range (𝓡∂ N))
      (extChartAt (𝓡∂ N) x₀ y))) (range (𝓡∂ N)) (extChartAt (𝓡∂ N) x₀ y) := by
  have hyext : y ∈ (extChartAt (𝓡∂ N) x₀).source := by rwa [extChartAt_source]
  have hmem : extChartAt (𝓡∂ N) x₀ y ∈ (extChartAt (𝓡∂ N) x₀).target :=
    (extChartAt (𝓡∂ N) x₀).map_source hyext
  have hS := (mdifferentiableWithinAt_extChartAt_symm hmem).hasMFDerivWithinAt
  have hleft : (extChartAt (𝓡∂ N) x₀).symm (extChartAt (𝓡∂ N) x₀ y) = y :=
    (extChartAt (𝓡∂ N) x₀).left_inv hyext
  have hU : HasMFDerivAt (𝓡∂ N) 𝓘(ℝ, ℝ) u
      ((extChartAt (𝓡∂ N) x₀).symm (extChartAt (𝓡∂ N) x₀ y)) (dcov (N := N) u y) := by
    rw [hleft]; exact hu.hasMFDerivAt
  have hc := hU.comp_hasMFDerivWithinAt (extChartAt (𝓡∂ N) x₀ y) hS
  rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt] at hc
  exact hc

omit [IsManifold (𝓡∂ N) ∞ M] in
lemma uniqueDiffWithinAt_chart (x₀ y : M)
    (hy : y ∈ (chartAt (EuclideanHalfSpace N) x₀).source) :
    UniqueDiffWithinAt ℝ (range (𝓡∂ N)) (extChartAt (𝓡∂ N) x₀ y) := by
  have hyext : y ∈ (extChartAt (𝓡∂ N) x₀).source := by rwa [extChartAt_source]
  exact (𝓡∂ N).uniqueDiffOn.uniqueDiffWithinAt
    (extChartAt_target_subset_range x₀ ((extChartAt (𝓡∂ N) x₀).map_source hyext))

/-- **The metric read in a chart.** Near every point `x₀`, with constants independent of `u`:
`|∇u|_g(y) ≤ C ‖D(u ∘ φ⁻¹)(φ y)‖` and `‖D(u ∘ φ⁻¹)(φ y)‖ ≤ C |∇u|_g(y)`, `φ` the chart at `x₀`
and `D` the derivative within the half-space. -/
theorem chart_comparison (g : RiemannianMetric N M) (x₀ : M) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x₀, y ∈ (chartAt (EuclideanHalfSpace N) x₀).source ∧
      ∀ u : M → ℝ, MDifferentiableAt (𝓡∂ N) 𝓘(ℝ, ℝ) u y →
        gradNorm g u y ≤ C * ‖dChart N x₀ u y‖ ∧ ‖dChart N x₀ u y‖ ≤ C * gradNorm g u y := by
  have hsrc : (chartAt (EuclideanHalfSpace N) x₀).source ∈ 𝓝 x₀ :=
    (chartAt (EuclideanHalfSpace N) x₀).open_source.mem_nhds (mem_chart_source _ x₀)
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ N) x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin N))
      (fun x : M => TangentSpace (𝓡∂ N) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  obtain ⟨C₁, hC₁, h₁⟩ := eventually_norm_trivializationAt_lt (EuclideanSpace ℝ (Fin N))
    (fun x : M => TangentSpace (𝓡∂ N) x) x₀
  obtain ⟨C₂, hC₂, h₂⟩ := eventually_norm_symmL_trivializationAt_lt (EuclideanSpace ℝ (Fin N))
    (fun x : M => TangentSpace (𝓡∂ N) x) x₀
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  filter_upwards [h₁, h₂, hsrc] with y hy₁ hy₂ hy
  refine ⟨hy, fun u hu => ?_⟩
  set T := trivializationAt (EuclideanSpace ℝ (Fin N)) (TangentSpace (𝓡∂ N) : M → Type) x₀
    with hT
  have hyb : y ∈ T.baseSet := by rwa [hT, TangentBundle.trivializationAt_baseSet]
  have hsymm : T.symmL ℝ y = mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (𝓡∂ N)
      (extChartAt (𝓡∂ N) x₀).symm (range (𝓡∂ N)) (extChartAt (𝓡∂ N) x₀ y) :=
    TangentBundle.symmL_trivializationAt hy
  have hD : dChart N x₀ u y = (dcov (N := N) u y).comp (T.symmL ℝ y) := by
    have hc : HasFDerivWithinAt (inChart N x₀ u) ((dcov (N := N) u y).comp (T.symmL ℝ y))
        (range (𝓡∂ N)) (extChartAt (𝓡∂ N) x₀ y) := by
      rw [hsymm]; exact hasFDerivWithinAt_inChart x₀ y hy u hu
    exact hc.fderivWithin (uniqueDiffWithinAt_chart x₀ y hy)
  have hinv : ∀ v : TangentSpace (𝓡∂ N) y, T.symmL ℝ y (T.continuousLinearMapAt ℝ y v) = v :=
    fun v => T.symmL_continuousLinearMapAt hyb v
  have hdcov : dcov (N := N) u y = (dChart N x₀ u y).comp (T.continuousLinearMapAt ℝ y) := by
    ext v
    rw [hD]
    simp only [ContinuousLinearMap.comp_apply, hinv]
  have hG := gradNorm_eq_norm_dcov g u y
  have hA : ‖dcov (N := N) u y‖ ≤ ‖dChart N x₀ u y‖ * ‖T.continuousLinearMapAt ℝ y‖ := by
    conv_lhs => rw [hdcov]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have hB : ‖dChart N x₀ u y‖ ≤ ‖dcov (N := N) u y‖ * ‖T.symmL ℝ y‖ := by
    conv_lhs => rw [hD]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  rw [← hG] at hA hB
  have h0 := gradNorm_nonneg g u y
  have h0' : 0 ≤ ‖dChart N x₀ u y‖ := norm_nonneg _
  have e1 : ‖T.continuousLinearMapAt ℝ y‖ ≤ max C₁ C₂ := hy₁.le.trans (le_max_left _ _)
  have e2 : ‖T.symmL ℝ y‖ ≤ max C₁ C₂ := hy₂.le.trans (le_max_right _ _)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left e1 h0']
  · nlinarith [mul_le_mul_of_nonneg_left e2 h0]

/-! ## 2. `C¹` functions read in charts; the gradient norm is bounded on a compact manifold -/

omit [IsManifold (𝓡∂ N) ∞ M] in
/-- On the chart's target, the derivative within the target is the derivative within the
half-space (the target is the half-space cut by an open set). -/
lemma fderivWithin_target_eq (x₀ : M) (f : EuclideanSpace ℝ (Fin N) → ℝ)
    {z : EuclideanSpace ℝ (Fin N)} (hz : z ∈ (extChartAt (𝓡∂ N) x₀).target) :
    fderivWithin ℝ f (extChartAt (𝓡∂ N) x₀).target z = fderivWithin ℝ f (range (𝓡∂ N)) z := by
  have hz' := hz
  rw [extChartAt_target] at hz'
  rw [extChartAt_target, inter_comm]
  exact fderivWithin_inter
    (((chartAt (EuclideanHalfSpace N) x₀).open_target.preimage (𝓡∂ N).continuous_symm).mem_nhds
      hz'.1)

/-- A `C¹` function read in a chart is `C¹` on the chart's target. -/
lemma contDiffOn_inChart {u : M → ℝ} (hu : IsC1 N u) (x₀ : M) :
    ContDiffOn ℝ 1 (inChart N x₀ u) (extChartAt (𝓡∂ N) x₀).target := by
  have h := (contMDiff_iff.mp hu).2 x₀ (u x₀)
  simpa [inChart, extChartAt_model_space_eq_id] using h

/-- The chart derivative of a `C¹` function is continuous on the chart's source. -/
lemma continuousOn_dChart {u : M → ℝ} (hu : IsC1 N u) (x₀ : M) :
    ContinuousOn (dChart N x₀ u) (chartAt (EuclideanHalfSpace N) x₀).source := by
  have h1 : ContinuousOn (fderivWithin ℝ (inChart N x₀ u) (extChartAt (𝓡∂ N) x₀).target)
      (extChartAt (𝓡∂ N) x₀).target :=
    (contDiffOn_inChart hu x₀).continuousOn_fderivWithin (uniqueDiffOn_extChartAt_target x₀)
      le_rfl
  have h2 : ContinuousOn (fun y => fderivWithin ℝ (inChart N x₀ u) (extChartAt (𝓡∂ N) x₀).target
      (extChartAt (𝓡∂ N) x₀ y)) (chartAt (EuclideanHalfSpace N) x₀).source := by
    have hce : ContinuousOn (extChartAt (𝓡∂ N) x₀) (chartAt (EuclideanHalfSpace N) x₀).source := by
      rw [← extChartAt_source (I := 𝓡∂ N)]; exact continuousOn_extChartAt x₀
    refine h1.comp hce fun y hy => ?_
    exact (extChartAt (𝓡∂ N) x₀).map_source (by rwa [extChartAt_source])
  refine h2.congr fun y hy => ?_
  exact (fderivWithin_target_eq x₀ _
    ((extChartAt (𝓡∂ N) x₀).map_source (by rwa [extChartAt_source]))).symm

/-- **A `C¹` function on a compact manifold has bounded gradient norm**: `|∇u|_g ≤ K`. -/
theorem gradNorm_bdd [CompactSpace M] (g : RiemannianMetric N M) {u : M → ℝ} (hu : IsC1 N u) :
    ∃ K : ℝ, ∀ x, gradNorm g u x ≤ K := by
  have hloc : ∀ x₀ : M, ∃ K : ℝ, ∀ᶠ y in 𝓝 x₀, gradNorm g u y ≤ K := by
    intro x₀
    obtain ⟨C, hC, hev⟩ := chart_comparison g x₀
    have hsrc : (chartAt (EuclideanHalfSpace N) x₀).source ∈ 𝓝 x₀ :=
      (chartAt (EuclideanHalfSpace N) x₀).open_source.mem_nhds (mem_chart_source _ x₀)
    have hc : ContinuousAt (dChart N x₀ u) x₀ := (continuousOn_dChart hu x₀).continuousAt hsrc
    have hev2 : ∀ᶠ y in 𝓝 x₀, ‖dChart N x₀ u y‖ < ‖dChart N x₀ u x₀‖ + 1 :=
      hc.norm.eventually (gt_mem_nhds (lt_add_one _))
    refine ⟨C * (‖dChart N x₀ u x₀‖ + 1), ?_⟩
    filter_upwards [hev, hev2] with y hy hy2
    have h3 := (hy.2 u (hu.mdifferentiableAt one_ne_zero)).1
    calc gradNorm g u y ≤ C * ‖dChart N x₀ u y‖ := h3
      _ ≤ C * (‖dChart N x₀ u x₀‖ + 1) := mul_le_mul_of_nonneg_left hy2.le hC.le
  choose K hK using hloc
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => {y | gradNorm g u y ≤ K x})
    (fun x _ => hK x)
  refine ⟨∑ x ∈ t, |K x|, fun y => ?_⟩
  obtain ⟨x, hx, hy⟩ := mem_iUnion₂.mp (ht (mem_univ y))
  calc gradNorm g u y ≤ K x := hy
    _ ≤ |K x| := le_abs_self _
    _ ≤ ∑ x ∈ t, |K x| :=
        Finset.single_le_sum (f := fun x => |K x|) (fun _ _ => abs_nonneg _) hx

/-! ## 3. Measurability in charts -/

omit [NeZero N] [IsManifold (𝓡∂ N) ∞ M] in
/-- The preimage of a measurable set under a map continuous on a measurable set. -/
lemma measurableSet_inter_preimage_of_continuousOn {α β : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] {f : α → β} {s : Set α} (hf : ContinuousOn f s) (hs : MeasurableSet s)
    {t : Set β} (ht : MeasurableSet t) : MeasurableSet (s ∩ f ⁻¹' t) := by
  have hm : MeasurableSet (s.restrict f ⁻¹' t) := hf.restrict.measurable ht
  have h := hs.subtype_image hm
  convert h using 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists, Set.restrict_apply,
    exists_and_right, exists_eq_right]
  tauto

variable [MeasurableSpace M] [BorelSpace M]

omit [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M] in
lemma measurableSet_target (x₀ : M) : MeasurableSet (extChartAt (𝓡∂ N) x₀).target := by
  rw [extChartAt_target]
  exact ((chartAt (EuclideanHalfSpace N) x₀).open_target.preimage
    (𝓡∂ N).continuous_symm).measurableSet.inter (𝓡∂ N).isClosed_range.measurableSet

omit [IsManifold (𝓡∂ N) ∞ M] in
/-- The chart image of a measurable subset of the chart's source is measurable. -/
lemma measurableSet_image_chart (x₀ : M) {A : Set M} (hA : MeasurableSet A)
    (hAs : A ⊆ (chartAt (EuclideanHalfSpace N) x₀).source) :
    MeasurableSet (extChartAt (𝓡∂ N) x₀ '' A) := by
  rw [(extChartAt (𝓡∂ N) x₀).image_eq_target_inter_inv_preimage (by rwa [extChartAt_source])]
  exact measurableSet_inter_preimage_of_continuousOn (continuousOn_extChartAt_symm x₀)
    (measurableSet_target x₀) hA

omit [IsManifold (𝓡∂ N) ∞ M] in
lemma measurableSet_inter_preimage_chart (x₀ : M) {A : Set M} (hA : MeasurableSet A)
    (hAs : A ⊆ (chartAt (EuclideanHalfSpace N) x₀).source) {B : Set (EuclideanSpace ℝ (Fin N))}
    (hB : MeasurableSet B) : MeasurableSet (A ∩ extChartAt (𝓡∂ N) x₀ ⁻¹' B) := by
  have hc : ContinuousOn (extChartAt (𝓡∂ N) x₀) A :=
    (continuousOn_extChartAt x₀).mono (by rwa [extChartAt_source])
  exact measurableSet_inter_preimage_of_continuousOn hc hA hB

omit [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M] in
lemma image_chart_subset_target (x₀ : M) {A : Set M}
    (hAs : A ⊆ (chartAt (EuclideanHalfSpace N) x₀).source) :
    extChartAt (𝓡∂ N) x₀ '' A ⊆ (extChartAt (𝓡∂ N) x₀).target :=
  image_subset_iff.mpr fun y hy => (extChartAt (𝓡∂ N) x₀).map_source (by
    rw [extChartAt_source]; exact hAs hy)

/-! ## 4. Measures read in a chart -/

omit [IsManifold (𝓡∂ N) ∞ M] in
/-- **A measure chartwise comparable to Lebesgue measure, read in the chart.** If on every
measurable `A' ⊆ A` (`A` in the chart's source) `μ A' ≤ C vol(φ A')` and `vol(φ A') ≤ C μ A'`,
then `φ_*(μ|_A) ≤ C vol|_{φ A}` and `vol|_{φ A} ≤ C φ_*(μ|_A)`. -/
theorem map_restrict_comparable (μ : Measure M) (x₀ : M) {A : Set M} (hA : MeasurableSet A)
    (hAs : A ⊆ (chartAt (EuclideanHalfSpace N) x₀).source) {C : ℝ≥0}
    (hC : ∀ A' ⊆ A, MeasurableSet A' → μ A' ≤ C * volume (extChartAt (𝓡∂ N) x₀ '' A') ∧
      volume (extChartAt (𝓡∂ N) x₀ '' A') ≤ C * μ A') :
    Measure.map (extChartAt (𝓡∂ N) x₀) (μ.restrict A) ≤
        (C : ℝ≥0∞) • volume.restrict (extChartAt (𝓡∂ N) x₀ '' A) ∧
      volume.restrict (extChartAt (𝓡∂ N) x₀ '' A) ≤
        (C : ℝ≥0∞) • Measure.map (extChartAt (𝓡∂ N) x₀) (μ.restrict A) := by
  set φ := extChartAt (𝓡∂ N) x₀ with hφ
  have hφA : AEMeasurable φ (μ.restrict A) :=
    ((continuousOn_extChartAt x₀).mono (by rwa [extChartAt_source])).aemeasurable hA
  have himg : ∀ B : Set (EuclideanSpace ℝ (Fin N)), φ '' (A ∩ φ ⁻¹' B) = B ∩ φ '' A := by
    intro B
    ext z
    constructor
    · rintro ⟨y, ⟨hyA, hyB⟩, rfl⟩
      exact ⟨hyB, y, hyA, rfl⟩
    · rintro ⟨hzB, y, hyA, rfl⟩
      exact ⟨y, ⟨hyA, hzB⟩, rfl⟩
  constructor
  · rw [Measure.le_iff]
    intro B hB
    rw [Measure.map_apply_of_aemeasurable hφA hB, Measure.restrict_apply' hA, Measure.smul_apply,
      Measure.restrict_apply hB, smul_eq_mul, inter_comm, ← himg]
    exact (hC _ inter_subset_left (measurableSet_inter_preimage_chart x₀ hA hAs hB)).1
  · rw [Measure.le_iff]
    intro B hB
    rw [Measure.restrict_apply hB, Measure.smul_apply, Measure.map_apply_of_aemeasurable hφA hB,
      Measure.restrict_apply' hA, smul_eq_mul, inter_comm (φ ⁻¹' B), ← himg]
    exact (hC _ inter_subset_left (measurableSet_inter_preimage_chart x₀ hA hAs hB)).2

omit [IsManifold (𝓡∂ N) ∞ M] in
/-- **`L^p` norms read in a chart**, both directions, for a function on `ℝ^N` measurable on the
chart's target. -/
theorem eLpNorm_chart_comparable (μ : Measure M) (x₀ : M) {A : Set M} (hA : MeasurableSet A)
    (hAs : A ⊆ (chartAt (EuclideanHalfSpace N) x₀).source) {C : ℝ≥0} (hC0 : C ≠ 0)
    (hC : ∀ A' ⊆ A, MeasurableSet A' → μ A' ≤ C * volume (extChartAt (𝓡∂ N) x₀ '' A') ∧
      volume (extChartAt (𝓡∂ N) x₀ '' A') ≤ C * μ A')
    {G : Type*} [NormedAddCommGroup G] {F : EuclideanSpace ℝ (Fin N) → G}
    (hF : AEStronglyMeasurable F (volume.restrict (extChartAt (𝓡∂ N) x₀).target)) (p : ℝ≥0∞) :
    eLpNorm (F ∘ extChartAt (𝓡∂ N) x₀) p (μ.restrict A) ≤
        (C : ℝ≥0∞) ^ (1 / p).toReal * eLpNorm F p (volume.restrict (extChartAt (𝓡∂ N) x₀ '' A)) ∧
      eLpNorm F p (volume.restrict (extChartAt (𝓡∂ N) x₀ '' A)) ≤
        (C : ℝ≥0∞) ^ (1 / p).toReal * eLpNorm (F ∘ extChartAt (𝓡∂ N) x₀) p (μ.restrict A) := by
  obtain ⟨h1, h2⟩ := map_restrict_comparable μ x₀ hA hAs hC
  have hφA : AEMeasurable (extChartAt (𝓡∂ N) x₀) (μ.restrict A) :=
    ((continuousOn_extChartAt x₀).mono (by rwa [extChartAt_source])).aemeasurable hA
  have hF' : AEStronglyMeasurable F (volume.restrict (extChartAt (𝓡∂ N) x₀ '' A)) :=
    hF.mono_measure (Measure.restrict_mono (image_chart_subset_target x₀ hAs) le_rfl)
  have hFm : AEStronglyMeasurable F (Measure.map (extChartAt (𝓡∂ N) x₀) (μ.restrict A)) :=
    (hF'.smul_measure (C : ℝ≥0∞)).mono_measure h1
  have hC0' : (C : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hC0
  rw [← eLpNorm_map_measure hFm hφA]
  constructor
  · calc eLpNorm F p (Measure.map (extChartAt (𝓡∂ N) x₀) (μ.restrict A))
        ≤ eLpNorm F p ((C : ℝ≥0∞) • volume.restrict (extChartAt (𝓡∂ N) x₀ '' A)) :=
          eLpNorm_mono_measure _ h1
      _ = _ := by rw [eLpNorm_smul_measure_of_ne_zero hC0', smul_eq_mul]
  · calc eLpNorm F p (volume.restrict (extChartAt (𝓡∂ N) x₀ '' A))
        ≤ eLpNorm F p ((C : ℝ≥0∞) • Measure.map (extChartAt (𝓡∂ N) x₀) (μ.restrict A)) :=
          eLpNorm_mono_measure _ h2
      _ = _ := by rw [eLpNorm_smul_measure_of_ne_zero hC0', smul_eq_mul]

omit [NeZero N] [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M] in
/-- A function vanishing on `T ∖ S` has `‖F‖_{L^p(T)} ≤ ‖F‖_{L^p(S)}`. -/
lemma eLpNorm_restrict_le_of_vanish {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {G : Type*} [NormedAddCommGroup G] {F : α → G} {S T : Set α} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (h0 : ∀ z ∈ T, z ∉ S → F z = 0) (p : ℝ≥0∞) :
    eLpNorm F p (ν.restrict T) ≤ eLpNorm F p (ν.restrict S) := by
  have he : F =ᵐ[ν.restrict T] S.indicator F :=
    (ae_restrict_mem hT).mono fun z hz => by
      by_cases hzS : z ∈ S
      · rw [indicator_of_mem hzS]
      · rw [indicator_of_notMem hzS, h0 z hz hzS]
  rw [eLpNorm_congr_ae he, ← eLpNorm_indicator_eq_eLpNorm_restrict hS]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-! ## 5. Functions read in a chart, cut off outside the target -/

open scoped Classical in
variable (N) in
/-- `f` read in the chart at `x₀`, extended by `0` off the chart's target. -/
def chartFun (x₀ : M) (f : M → ℝ) : EuclideanSpace ℝ (Fin N) → ℝ := fun z =>
  if z ∈ (extChartAt (𝓡∂ N) x₀).target then f ((extChartAt (𝓡∂ N) x₀).symm z) else 0

omit [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M] in
lemma chartFun_chart {x₀ y : M} (hy : y ∈ (chartAt (EuclideanHalfSpace N) x₀).source)
    (f : M → ℝ) : chartFun N x₀ f (extChartAt (𝓡∂ N) x₀ y) = f y := by
  have hy' : y ∈ (extChartAt (𝓡∂ N) x₀).source := by rwa [extChartAt_source]
  rw [chartFun, if_pos ((extChartAt (𝓡∂ N) x₀).map_source hy'),
    (extChartAt (𝓡∂ N) x₀).left_inv hy']

omit [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M] in
lemma chartFun_eq_inChart (x₀ : M) (f : M → ℝ) :
    EqOn (chartFun N x₀ f) (inChart N x₀ f) (extChartAt (𝓡∂ N) x₀).target :=
  fun _ hz => if_pos hz

omit [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M] in
lemma chartFun_eq_zero (x₀ : M) {f : M → ℝ} {z : EuclideanSpace ℝ (Fin N)}
    (hz : z ∉ extChartAt (𝓡∂ N) x₀ '' tsupport f) : chartFun N x₀ f z = 0 := by
  unfold chartFun
  split_ifs with ht
  · by_contra hne
    exact hz ⟨(extChartAt (𝓡∂ N) x₀).symm z, subset_tsupport _ hne,
      (extChartAt (𝓡∂ N) x₀).right_inv ht⟩
  · rfl

omit [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M] in
lemma isCompact_image_tsupport [CompactSpace M] (x₀ : M) {f : M → ℝ}
    (hf : tsupport f ⊆ (chartAt (EuclideanHalfSpace N) x₀).source) :
    IsCompact (extChartAt (𝓡∂ N) x₀ '' tsupport f) :=
  (isClosed_tsupport f).isCompact.image_of_continuousOn
    ((continuousOn_extChartAt x₀).mono (by rwa [extChartAt_source]))

omit [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M] in
lemma chartFun_eventuallyEq_zero [CompactSpace M] (x₀ : M) {f : M → ℝ}
    (hf : tsupport f ⊆ (chartAt (EuclideanHalfSpace N) x₀).source)
    {z : EuclideanSpace ℝ (Fin N)} (hz : z ∉ extChartAt (𝓡∂ N) x₀ '' tsupport f) :
    chartFun N x₀ f =ᶠ[𝓝 z] fun _ => 0 := by
  have hK := (isCompact_image_tsupport x₀ hf).isClosed
  filter_upwards [hK.isOpen_compl.mem_nhds hz] with w hw
  exact chartFun_eq_zero x₀ hw

omit [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M] in
/-- A function with support in the chart's source, read in the chart, is compactly supported. -/
lemma hasCompactSupport_chartFun [CompactSpace M] (x₀ : M) {f : M → ℝ}
    (hf : tsupport f ⊆ (chartAt (EuclideanHalfSpace N) x₀).source) :
    HasCompactSupport (chartFun N x₀ f) :=
  HasCompactSupport.intro (isCompact_image_tsupport x₀ hf) fun _ hz => chartFun_eq_zero x₀ hz

omit [MeasurableSpace M] [BorelSpace M] in
/-- A `C¹` function with support in the chart's source, read in the chart, is `C¹` on the closed
half-space. -/
lemma contDiffOn_chartFun [CompactSpace M] (x₀ : M) {f : M → ℝ} (hf1 : IsC1 N f)
    (hf : tsupport f ⊆ (chartAt (EuclideanHalfSpace N) x₀).source) :
    ContDiffOn ℝ 1 (chartFun N x₀ f) (Half.H N) := by
  intro z hz
  by_cases hzt : z ∈ (extChartAt (𝓡∂ N) x₀).target
  · have h1 : ContDiffWithinAt ℝ 1 (inChart N x₀ f) (extChartAt (𝓡∂ N) x₀).target z :=
      contDiffOn_inChart hf1 x₀ z hzt
    have hnhds : (extChartAt (𝓡∂ N) x₀).target ∈ 𝓝[Half.H N] z := by
      rw [Half.H_eq]; exact extChartAt_target_mem_nhdsWithin_of_mem hzt
    exact (h1.mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq
      (Filter.eventually_of_mem hnhds fun w hw => chartFun_eq_inChart x₀ f hw)
      (chartFun_eq_inChart x₀ f hzt)
  · have hzK : z ∉ extChartAt (𝓡∂ N) x₀ '' tsupport f := fun h =>
      hzt (image_chart_subset_target x₀ hf h)
    exact (contDiffAt_const (c := (0 : ℝ))).contDiffWithinAt.congr_of_eventuallyEq
      (nhdsWithin_le_nhds (chartFun_eventuallyEq_zero x₀ hf hzK)) (chartFun_eq_zero x₀ hzK)

omit [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M] in
/-- On the chart's image, the half-space derivative of `chartFun` is the chart derivative. -/
lemma fderivWithin_chartFun (x₀ : M) {y : M}
    (hy : y ∈ (chartAt (EuclideanHalfSpace N) x₀).source) (f : M → ℝ) :
    fderivWithin ℝ (chartFun N x₀ f) (Half.H N) (extChartAt (𝓡∂ N) x₀ y) = dChart N x₀ f y := by
  have hy' : y ∈ (extChartAt (𝓡∂ N) x₀).source := by rwa [extChartAt_source]
  have hmem := (extChartAt (𝓡∂ N) x₀).map_source hy'
  unfold dChart
  rw [← Half.H_eq]
  have hnhds : (extChartAt (𝓡∂ N) x₀).target ∈ 𝓝[Half.H N] (extChartAt (𝓡∂ N) x₀ y) := by
    rw [Half.H_eq]; exact extChartAt_target_mem_nhdsWithin_of_mem hmem
  exact Filter.EventuallyEq.fderivWithin_eq
    (Filter.eventually_of_mem hnhds fun w hw => chartFun_eq_inChart x₀ f hw)
    (chartFun_eq_inChart x₀ f hmem)

omit [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M] in
/-- Off the image of the support, the half-space derivative of `chartFun` vanishes. -/
lemma fderivWithin_chartFun_eq_zero [CompactSpace M] (x₀ : M) {f : M → ℝ}
    (hf : tsupport f ⊆ (chartAt (EuclideanHalfSpace N) x₀).source)
    {z : EuclideanSpace ℝ (Fin N)} (hz : z ∉ extChartAt (𝓡∂ N) x₀ '' tsupport f) :
    fderivWithin ℝ (chartFun N x₀ f) (Half.H N) z = 0 := by
  rw [Filter.EventuallyEq.fderivWithin_eq (nhdsWithin_le_nhds (chartFun_eventuallyEq_zero x₀ hf hz))
    (chartFun_eq_zero x₀ hz)]
  exact fderivWithin_const_apply _

omit [MeasurableSpace M] [BorelSpace M] in
/-- The product rule in a chart. -/
lemma dChart_mul (x₀ : M) {y : M} (hy : y ∈ (chartAt (EuclideanHalfSpace N) x₀).source)
    {ρ u : M → ℝ} (hρ : MDifferentiableAt (𝓡∂ N) 𝓘(ℝ, ℝ) ρ y)
    (hu : MDifferentiableAt (𝓡∂ N) 𝓘(ℝ, ℝ) u y) :
    dChart N x₀ (ρ * u) y = ρ y • dChart N x₀ u y + u y • dChart N x₀ ρ y := by
  have hy' : y ∈ (extChartAt (𝓡∂ N) x₀).source := by rwa [extChartAt_source]
  have hleft : (extChartAt (𝓡∂ N) x₀).symm (extChartAt (𝓡∂ N) x₀ y) = y :=
    (extChartAt (𝓡∂ N) x₀).left_inv hy'
  have he : inChart N x₀ (ρ * u) = inChart N x₀ ρ * inChart N x₀ u := rfl
  unfold dChart
  rw [he, fderivWithin_mul (uniqueDiffWithinAt_chart x₀ y hy)
    (hasFDerivWithinAt_inChart x₀ y hy ρ hρ).differentiableWithinAt
    (hasFDerivWithinAt_inChart x₀ y hy u hu).differentiableWithinAt]
  simp only [inChart, Function.comp_apply, hleft]

/-! ## 6. Good chart neighbourhoods, the local Sobolev estimate, and the assembly -/

/-- A *good chart neighbourhood* `V` of the chart at `x₀`: open, in the chart's source, on which
`μ` is comparable to Lebesgue measure (constant `Cμ`) and `|∇u|_g` to the chart derivative
(constant `Cg`). -/
structure GoodChart (g : RiemannianMetric N M) (μ : Measure M) (x₀ : M) (V : Set M) (Cμ : ℝ≥0)
    (Cg : ℝ) : Prop where
  isOpen : IsOpen V
  subset_source : V ⊆ (chartAt (EuclideanHalfSpace N) x₀).source
  Cμ_ne : Cμ ≠ 0
  Cg_pos : 0 < Cg
  vol : ∀ A ⊆ V, MeasurableSet A → μ A ≤ Cμ * volume (extChartAt (𝓡∂ N) x₀ '' A) ∧
    volume (extChartAt (𝓡∂ N) x₀ '' A) ≤ Cμ * μ A
  grad : ∀ y ∈ V, ∀ u : M → ℝ, MDifferentiableAt (𝓡∂ N) 𝓘(ℝ, ℝ) u y →
    gradNorm g u y ≤ Cg * ‖dChart N x₀ u y‖ ∧ ‖dChart N x₀ u y‖ ≤ Cg * gradNorm g u y

omit [BorelSpace M] in
/-- A good chart neighbourhood stays good on an open subset. -/
lemma GoodChart.mono {g : RiemannianMetric N M} {μ : Measure M} {x₀ : M} {V : Set M} {Cμ : ℝ≥0}
    {Cg : ℝ} (hG : GoodChart g μ x₀ V Cμ Cg) {W : Set M} (hW : IsOpen W) (hWV : W ⊆ V) :
    GoodChart g μ x₀ W Cμ Cg :=
  ⟨hW, hWV.trans hG.subset_source, hG.Cμ_ne, hG.Cg_pos, fun A hA hAm => hG.vol A (hA.trans hWV) hAm,
    fun y hy => hG.grad y (hWV hy)⟩

omit [BorelSpace M] in
/-- Every point has a good chart neighbourhood. -/
theorem exists_goodChart (g : RiemannianMetric N M) {μ : Measure M} (hμ : IsLocallyLebesgue N μ)
    (x₀ : M) : ∃ V Cμ Cg, x₀ ∈ V ∧ GoodChart g μ x₀ V Cμ Cg := by
  obtain ⟨U, hU, C₀, hC₀⟩ := hμ x₀
  obtain ⟨Cg, hCg, hev⟩ := chart_comparison g x₀
  refine ⟨interior (U ∩ {y | y ∈ (chartAt (EuclideanHalfSpace N) x₀).source ∧
    ∀ u : M → ℝ, MDifferentiableAt (𝓡∂ N) 𝓘(ℝ, ℝ) u y →
      gradNorm g u y ≤ Cg * ‖dChart N x₀ u y‖ ∧ ‖dChart N x₀ u y‖ ≤ Cg * gradNorm g u y}),
    max C₀ 1, Cg, mem_interior_iff_mem_nhds.mpr (inter_mem hU hev), ⟨isOpen_interior,
    fun y hy => (interior_subset hy).2.1, (lt_of_lt_of_le one_pos (le_max_right _ _)).ne',
    hCg, fun A hA hAm => ?_, fun y hy u hu => (interior_subset hy).2.2 u hu⟩⟩
  have hA' : A ⊆ U ∩ (chartAt (EuclideanHalfSpace N) x₀).source := fun y hy =>
    ⟨(interior_subset (hA hy)).1, (interior_subset (hA hy)).2.1⟩
  obtain ⟨h1, h2⟩ := hC₀ A hA' hAm
  have hle : (C₀ : ℝ≥0∞) ≤ (max C₀ 1 : ℝ≥0) := by exact_mod_cast le_max_left _ _
  exact ⟨h1.trans (mul_le_mul_left hle _), h2.trans (mul_le_mul_left hle _)⟩

/-- The `L²` norm of the chart derivative of `ρ u` on a good chart neighbourhood, by the
`W^{1,2}` norm of `u`. -/
theorem eLpNorm_dChart_mul_le {g : RiemannianMetric N M} {μ : Measure M} {x₀ : M} {V : Set M}
    {Cμ : ℝ≥0} {Cg : ℝ} (hG : GoodChart g μ x₀ V Cμ Cg) [CompactSpace M] {ρ : M → ℝ}
    (hρ : IsC1 N ρ) (hρ1 : ∀ y, |ρ y| ≤ 1) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ u : M → ℝ, IsC1 N u →
      eLpNorm (dChart N x₀ (ρ * u)) 2 (μ.restrict V) ≤ c * w12 g μ u := by
  obtain ⟨Kρ, hKρ⟩ := gradNorm_bdd g hρ
  set K := max Kρ 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hVm : MeasurableSet V := hG.isOpen.measurableSet
  have hVs := hG.subset_source
  have hCg := hG.Cg_pos
  refine ⟨ENNReal.ofReal (Cg * (1 + K)), ENNReal.ofReal_ne_top, fun u hu => ?_⟩
  have hpt : ∀ y ∈ V, ‖dChart N x₀ (ρ * u) y‖ ≤ ‖dChart N x₀ u y‖ + Cg * K * |u y| := by
    intro y hy
    rw [dChart_mul x₀ (hVs hy) (hρ.mdifferentiableAt one_ne_zero)
      (hu.mdifferentiableAt one_ne_zero)]
    have h1 := (hG.grad y hy ρ (hρ.mdifferentiableAt one_ne_zero)).2
    have h2 : ‖dChart N x₀ ρ y‖ ≤ Cg * K :=
      h1.trans (mul_le_mul_of_nonneg_left ((hKρ y).trans (le_max_left _ _)) hCg.le)
    calc ‖ρ y • dChart N x₀ u y + u y • dChart N x₀ ρ y‖
        ≤ ‖ρ y • dChart N x₀ u y‖ + ‖u y • dChart N x₀ ρ y‖ := norm_add_le _ _
      _ = |ρ y| * ‖dChart N x₀ u y‖ + |u y| * ‖dChart N x₀ ρ y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * ‖dChart N x₀ u y‖ + |u y| * (Cg * K) := by
          gcongr
          exact hρ1 y
      _ = _ := by ring
  have hdu_m : AEStronglyMeasurable (fun y => ‖dChart N x₀ u y‖) (μ.restrict V) :=
    ((continuousOn_dChart hu x₀).mono hVs).norm.aestronglyMeasurable hVm
  have hu_m : AEStronglyMeasurable (fun y => Cg * K * ‖u y‖) (μ.restrict V) :=
    (continuous_const.mul hu.continuous.norm).aestronglyMeasurable
  have hG1 : eLpNorm (fun y => ‖dChart N x₀ u y‖) 2 (μ.restrict V) ≤
      ENNReal.ofReal Cg * eLpNorm (gradNorm g u) 2 μ := by
    calc eLpNorm (fun y => ‖dChart N x₀ u y‖) 2 (μ.restrict V)
        ≤ eLpNorm (Cg • gradNorm g u : M → ℝ) 2 (μ.restrict V) := by
          refine eLpNorm_mono_ae ((ae_restrict_mem hVm).mono fun y hy => ?_)
          rw [norm_norm, Pi.smul_apply, smul_eq_mul,
            Real.norm_of_nonneg (mul_nonneg hCg.le (gradNorm_nonneg g u y))]
          exact (hG.grad y hy u (hu.mdifferentiableAt one_ne_zero)).2
      _ = ENNReal.ofReal Cg * eLpNorm (gradNorm g u) 2 (μ.restrict V) := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_pos hCg]
      _ ≤ ENNReal.ofReal Cg * eLpNorm (gradNorm g u) 2 μ := by
          gcongr; exact Measure.restrict_le_self
  have hG2 : eLpNorm (fun y => Cg * K * ‖u y‖) 2 (μ.restrict V) ≤
      ENNReal.ofReal (Cg * K) * eLpNorm u 2 μ := by
    calc eLpNorm (fun y => Cg * K * ‖u y‖) 2 (μ.restrict V)
        = eLpNorm ((Cg * K) • fun y => ‖u y‖) 2 (μ.restrict V) := rfl
      _ = ENNReal.ofReal (Cg * K) * eLpNorm u 2 (μ.restrict V) := by
          rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
            abs_of_nonneg (mul_nonneg hCg.le hK0), eLpNorm_norm]
      _ ≤ ENNReal.ofReal (Cg * K) * eLpNorm u 2 μ := by
          gcongr; exact Measure.restrict_le_self
  have hc1 : ENNReal.ofReal Cg ≤ ENNReal.ofReal (Cg * (1 + K)) :=
    ENNReal.ofReal_le_ofReal (by nlinarith)
  have hc2 : ENNReal.ofReal (Cg * K) ≤ ENNReal.ofReal (Cg * (1 + K)) :=
    ENNReal.ofReal_le_ofReal (by nlinarith)
  calc eLpNorm (dChart N x₀ (ρ * u)) 2 (μ.restrict V)
      ≤ eLpNorm ((fun y => ‖dChart N x₀ u y‖) + fun y => Cg * K * ‖u y‖) 2 (μ.restrict V) := by
        refine eLpNorm_mono_ae ((ae_restrict_mem hVm).mono fun y hy => ?_)
        rw [Pi.add_apply, Real.norm_of_nonneg (by positivity)]
        have := hpt y hy
        rwa [← Real.norm_eq_abs] at this
    _ ≤ eLpNorm (fun y => ‖dChart N x₀ u y‖) 2 (μ.restrict V) +
          eLpNorm (fun y => Cg * K * ‖u y‖) 2 (μ.restrict V) :=
        eLpNorm_add_le hdu_m hu_m (by norm_num)
    _ ≤ ENNReal.ofReal Cg * eLpNorm (gradNorm g u) 2 μ +
          ENNReal.ofReal (Cg * K) * eLpNorm u 2 μ := add_le_add hG1 hG2
    _ ≤ ENNReal.ofReal (Cg * (1 + K)) * eLpNorm (gradNorm g u) 2 μ +
          ENNReal.ofReal (Cg * (1 + K)) * eLpNorm u 2 μ := by gcongr
    _ = ENNReal.ofReal (Cg * (1 + K)) * w12 g μ u := by rw [w12]; exact (mul_add _ _ _).symm

omit [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M] in
lemma image_chart_subset_H (x₀ : M) {A : Set M}
    (hAs : A ⊆ (chartAt (EuclideanHalfSpace N) x₀).source) :
    extChartAt (𝓡∂ N) x₀ '' A ⊆ Half.H N := fun _ hz => by
  rw [Half.H_eq]; exact extChartAt_target_subset_range x₀ (image_chart_subset_target x₀ hAs hz)

/-- **The local Sobolev estimate**: on a good chart neighbourhood `V`, for a `C¹` cut-off `ρ`
supported in `V`, `‖ρ u‖_{L^{p*}(μ)} ≤ C ‖u‖_{W^{1,2}(μ)}`: the half-space Sobolev inequality
read through the chart. -/
theorem local_sobolev (hN : 3 ≤ N) [CompactSpace M] {g : RiemannianMetric N M} {μ : Measure M}
    {x₀ : M} {V : Set M} {Cμ : ℝ≥0} {Cg : ℝ} (hG : GoodChart g μ x₀ V Cμ Cg) {ρ : M → ℝ}
    (hρ : IsC1 N ρ) (hρV : tsupport ρ ⊆ V) (hρ1 : ∀ y, |ρ y| ≤ 1) :
    ∃ C : ℝ≥0, ∀ u : M → ℝ, IsC1 N u →
      eLpNorm (ρ * u) (ENNReal.ofReal (pStar N)) μ ≤ C * w12 g μ u := by
  obtain ⟨c, hc, hcu⟩ := eLpNorm_dChart_mul_le hG hρ hρ1
  obtain ⟨CH, hCH⟩ := Half.sobolev_halfSpace hN
  set φ := extChartAt (𝓡∂ N) x₀ with hφ
  set p := ENNReal.ofReal (pStar N) with hp
  have hVm : MeasurableSet V := hG.isOpen.measurableSet
  have hVs := hG.subset_source
  have hφV : MeasurableSet (φ '' V) := measurableSet_image_chart x₀ hVm hVs
  have htH : φ.target ⊆ Half.H N := fun z hz => by
    rw [Half.H_eq]; exact extChartAt_target_subset_range x₀ hz
  set c1 : ℝ≥0∞ := (Cμ : ℝ≥0∞) ^ (1 / p).toReal with hc1
  set c2 : ℝ≥0∞ := (Cμ : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal with hc2
  have hc1t : c1 ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
  have hc2t : c2 ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
  set B : ℝ≥0∞ := c1 * CH * c2 * c with hB
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hc1t
    ENNReal.coe_ne_top) hc2t) hc
  refine ⟨B.toNNReal, fun u hu => ?_⟩
  rw [ENNReal.coe_toNNReal hBt]
  set f := ρ * u with hf
  have hf1 : IsC1 N f := hρ.mul hu
  have hfV : tsupport f ⊆ V := (tsupport_mul_subset_left (f := ρ) (g := u)).trans hρV
  have hfs : tsupport f ⊆ (chartAt (EuclideanHalfSpace N) x₀).source := hfV.trans hVs
  set v := chartFun N x₀ f with hv
  have hvC : ContDiffOn ℝ 1 v (Half.H N) := contDiffOn_chartFun x₀ hf1 hfs
  have hvc : HasCompactSupport v := hasCompactSupport_chartFun x₀ hfs
  have hvm : AEStronglyMeasurable v (volume.restrict φ.target) :=
    (hvC.continuousOn.mono htH).aestronglyMeasurable (measurableSet_target x₀)
  have hDm : AEStronglyMeasurable (fderivWithin ℝ v (Half.H N)) (volume.restrict φ.target) :=
    ((hvC.continuousOn_fderivWithin Half.uniqueDiffOn_H le_rfl).mono htH).aestronglyMeasurable
      (measurableSet_target x₀)
  have hT1 := (eLpNorm_chart_comparable μ x₀ hVm hVs hG.Cμ_ne hG.vol hvm p).1
  have hT2 := (eLpNorm_chart_comparable μ x₀ hVm hVs hG.Cμ_ne hG.vol hDm 2).2
  have e1 : eLpNorm f p μ = eLpNorm (v ∘ φ) p (μ.restrict V) := by
    rw [← eLpNorm_restrict_eq_of_support_subset (s := V) ((subset_tsupport f).trans hfV)]
    refine eLpNorm_congr_ae ((ae_restrict_mem hVm).mono fun y hy => ?_)
    simp only [Function.comp_apply, hv]
    rw [chartFun_chart (hVs hy)]
  have hD0 : ∀ z ∈ Half.H N, z ∉ φ '' V → fderivWithin ℝ v (Half.H N) z = 0 := fun z _ hz =>
    fderivWithin_chartFun_eq_zero x₀ hfs fun h => hz (image_mono hfV h)
  have e2 := eLpNorm_restrict_le_of_vanish volume hφV Half.measurableSet_H hD0 2
  have e3 : eLpNorm (fderivWithin ℝ v (Half.H N) ∘ φ) 2 (μ.restrict V) =
      eLpNorm (dChart N x₀ f) 2 (μ.restrict V) :=
    eLpNorm_congr_ae ((ae_restrict_mem hVm).mono fun y hy => fderivWithin_chartFun x₀ (hVs hy) f)
  calc eLpNorm f p μ = eLpNorm (v ∘ φ) p (μ.restrict V) := e1
    _ ≤ c1 * eLpNorm v p (volume.restrict (φ '' V)) := hT1
    _ ≤ c1 * eLpNorm v p (volume.restrict (Half.H N)) := by
        gcongr
        exact image_chart_subset_H x₀ hVs
    _ ≤ c1 * (CH * eLpNorm (fderivWithin ℝ v (Half.H N)) 2 (volume.restrict (Half.H N))) := by
        gcongr; exact hCH v hvC hvc
    _ ≤ c1 * (CH * eLpNorm (fderivWithin ℝ v (Half.H N)) 2 (volume.restrict (φ '' V))) := by
        gcongr
    _ ≤ c1 * (CH * (c2 * eLpNorm (fderivWithin ℝ v (Half.H N) ∘ φ) 2 (μ.restrict V))) := by
        gcongr
    _ = c1 * (CH * (c2 * eLpNorm (dChart N x₀ f) 2 (μ.restrict V))) := by rw [e3]
    _ ≤ c1 * (CH * (c2 * (c * w12 g μ u))) := by gcongr; exact hcu u hu
    _ = B * w12 g μ u := by rw [hB]; ring

/-- **Assembly by a partition of unity.** If every point has an open neighbourhood with property
`Q`, and on every `Q`-set an estimate `‖ρ u‖_{L^p(ν)} ≤ C ‖u‖_{W^{1,2}(μ)}` holds for `C¹`
cut-offs `ρ` supported in it, then `‖u‖_{L^p(ν)} ≤ C ‖u‖_{W^{1,2}(μ)}` on the compact manifold. -/
theorem assemble [CompactSpace M] [T2Space M] (g : RiemannianMetric N M) (μ : Measure M)
    {ν : Measure M} {p : ℝ≥0∞} (hp : 1 ≤ p) (Q : Set M → Prop)
    (hQ : ∀ x₀ : M, ∃ V, IsOpen V ∧ x₀ ∈ V ∧ Q V)
    (hloc : ∀ V, Q V → ∀ ρ : M → ℝ, IsC1 N ρ → tsupport ρ ⊆ V → (∀ y, |ρ y| ≤ 1) →
      ∃ C : ℝ≥0, ∀ u : M → ℝ, IsC1 N u → eLpNorm (ρ * u) p ν ≤ C * w12 g μ u) :
    ∃ C : ℝ≥0, ∀ u : M → ℝ, IsC1 N u → eLpNorm u p ν ≤ C * w12 g μ u := by
  choose V hVo hxV hQV using hQ
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover V
    (fun x _ => (hVo x).mem_nhds (hxV x))
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡∂ N) isClosed_univ
    (fun i : t => V i) (fun i => hVo i) (by
      intro y _
      obtain ⟨x, hx, hy⟩ := mem_iUnion₂.mp (ht (mem_univ y))
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hy⟩)
  have hρC1 : ∀ i, IsC1 N (ρ i) := fun i => (ρ i).contMDiff.of_le (by exact_mod_cast le_top)
  have hρ1 : ∀ i y, |ρ i y| ≤ 1 := fun i y =>
    abs_le.mpr ⟨by linarith [ρ.nonneg i y], ρ.le_one i y⟩
  choose C hC using fun i : t => hloc (V i) (hQV i) (ρ i) (hρC1 i) (hρ i) (hρ1 i)
  refine ⟨∑ i, C i, fun u hu => ?_⟩
  have hsum : u = ∑ i : t, (ρ i : M → ℝ) * u := by
    funext y
    rw [Finset.sum_apply]
    simp only [Pi.mul_apply]
    rw [← Finset.sum_mul, ← finsum_eq_sum_of_fintype, ρ.sum_eq_one (mem_univ y), one_mul]
  calc eLpNorm u p ν = eLpNorm (∑ i : t, (ρ i : M → ℝ) * u) p ν := by rw [← hsum]
    _ ≤ ∑ i : t, eLpNorm ((ρ i : M → ℝ) * u) p ν :=
        eLpNorm_sum_le (fun i _ => ((hρC1 i).continuous.mul hu.continuous).aestronglyMeasurable)
          hp
    _ ≤ ∑ i : t, (C i : ℝ≥0∞) * w12 g μ u := Finset.sum_le_sum fun i _ => hC i u hu
    _ = ((∑ i, C i : ℝ≥0) : ℝ≥0∞) * w12 g μ u := by rw [← Finset.sum_mul]; push_cast; rfl

/-! ## 7. The boundary: the local trace estimate -/

omit [MeasurableSpace M] [BorelSpace M] in
/-- A boundary point of `M` in the source of the chart at `x₀` is sent to the boundary
hyperplane `{z₀ = 0}`. -/
lemma chart_boundary {x₀ y : M} (hb : y ∈ (𝓡∂ N).boundary M)
    (hy : y ∈ (chartAt (EuclideanHalfSpace N) x₀).source) : extChartAt (𝓡∂ N) x₀ y 0 = 0 := by
  have h := ((𝓡∂ N).isBoundaryPoint_iff_of_mem_atlas (n := ∞) (by simp)
    (chart_mem_atlas (EuclideanHalfSpace N) x₀) hy).mp hb
  have hy' : y ∈ (extChartAt (𝓡∂ N) x₀).source := by rwa [extChartAt_source]
  have hz : extChartAt (𝓡∂ N) x₀ y ∈ (extChartAt (𝓡∂ N) x₀).target :=
    (extChartAt (𝓡∂ N) x₀).map_source hy'
  have hnot : extChartAt (𝓡∂ N) x₀ y ∉ interior (extChartAt (𝓡∂ N) x₀).target := h.2
  have hO : IsOpen ((𝓡∂ N).symm ⁻¹' (chartAt (EuclideanHalfSpace N) x₀).target) :=
    (chartAt (EuclideanHalfSpace N) x₀).open_target.preimage (𝓡∂ N).continuous_symm
  rw [extChartAt_target] at hz hnot
  rw [interior_inter, hO.interior_eq, interior_range_modelWithCornersEuclideanHalfSpace] at hnot
  have h0 : 0 ≤ extChartAt (𝓡∂ N) x₀ y 0 := by
    have := hz.2
    rw [range_modelWithCornersEuclideanHalfSpace] at this
    exact this
  have h1 : ¬ 0 < extChartAt (𝓡∂ N) x₀ y 0 := fun hlt => hnot ⟨hz.1, hlt⟩
  exact le_antisymm (not_lt.mp h1) h0

omit [IsManifold (𝓡∂ N) ∞ M] in
/-- A measure on `M` bounded on the chart's source by a measure `λ` on `ℝ^N`, read in the chart. -/
theorem map_restrict_le_of (σ : Measure M) (lam : Measure (EuclideanSpace ℝ (Fin N))) (x₀ : M)
    {A : Set M} (hA : MeasurableSet A) (hAs : A ⊆ (chartAt (EuclideanHalfSpace N) x₀).source)
    {C : ℝ≥0} (hC : ∀ A' ⊆ A, MeasurableSet A' → σ A' ≤ C * lam (extChartAt (𝓡∂ N) x₀ '' A')) :
    Measure.map (extChartAt (𝓡∂ N) x₀) (σ.restrict A) ≤
      (C : ℝ≥0∞) • lam.restrict (extChartAt (𝓡∂ N) x₀ '' A) := by
  set φ := extChartAt (𝓡∂ N) x₀ with hφ
  have hφA : AEMeasurable φ (σ.restrict A) :=
    ((continuousOn_extChartAt x₀).mono (by rwa [extChartAt_source])).aemeasurable hA
  have himg : ∀ B : Set (EuclideanSpace ℝ (Fin N)), φ '' (A ∩ φ ⁻¹' B) = B ∩ φ '' A := by
    intro B
    ext z
    constructor
    · rintro ⟨y, ⟨hyA, hyB⟩, rfl⟩
      exact ⟨hyB, y, hyA, rfl⟩
    · rintro ⟨hzB, y, hyA, rfl⟩
      exact ⟨y, ⟨hyA, hzB⟩, rfl⟩
  rw [Measure.le_iff]
  intro B hB
  rw [Measure.map_apply_of_aemeasurable hφA hB, Measure.restrict_apply' hA, Measure.smul_apply,
    Measure.restrict_apply hB, smul_eq_mul, inter_comm, ← himg]
  exact hC _ inter_subset_left (measurableSet_inter_preimage_chart x₀ hA hAs hB)

/-- **The local trace estimate**: on a good chart neighbourhood `V` on which `σ` (carried by
`∂M`) is bounded by `μH[N-1]` of the chart image, for a `C¹` cut-off `ρ` supported in `V`,
`‖ρ u‖_{L^{p♯}(σ)} ≤ C ‖u‖_{W^{1,2}(μ)}`: the half-space trace inequality read through the
chart and the boundary hyperplane. -/
theorem local_trace (n : ℕ) (hNn : N = n + 1) (hN : 3 ≤ N) [CompactSpace M]
    {g : RiemannianMetric N M} {μ : Measure M} {σ : Measure M}
    (hσ0 : σ ((𝓡∂ N).boundary M)ᶜ = 0) {x₀ : M} {V : Set M} {Cμ : ℝ≥0} {Cg : ℝ}
    (hG : GoodChart g μ x₀ V Cμ Cg) {Cσ : ℝ≥0} (hCσ : Cσ ≠ 0)
    (hσV : ∀ A ⊆ V, MeasurableSet A →
      σ A ≤ Cσ * Measure.hausdorffMeasure ((N : ℝ) - 1) (extChartAt (𝓡∂ N) x₀ '' A))
    {ρ : M → ℝ} (hρ : IsC1 N ρ) (hρV : tsupport ρ ⊆ V) (hρ1 : ∀ y, |ρ y| ≤ 1) :
    ∃ C : ℝ≥0, ∀ u : M → ℝ, IsC1 N u →
      eLpNorm (ρ * u) (ENNReal.ofReal (pSharp N)) σ ≤ C * w12 g μ u := by
  subst hNn
  obtain ⟨c, hc, hcu⟩ := eLpNorm_dChart_mul_le hG hρ hρ1
  obtain ⟨CT, hCT⟩ := Half.trace_halfSpace' hN
  obtain ⟨K, hK0, hK⟩ := Half.eLpNorm_hyperplane_le n
  have hd : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
  rw [hd] at hσV
  set φ := extChartAt (𝓡∂ (n + 1)) x₀ with hφ
  set q := pSharp (n + 1) with hq
  have hq0 : 0 < q := lt_of_lt_of_le two_pos (two_le_pSharp hN)
  set p := ENNReal.ofReal q with hp
  have hp0 : p ≠ 0 := by rw [hp, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hq0
  have hptop : p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpq : p.toReal = q := ENNReal.toReal_ofReal hq0.le
  have hVm : MeasurableSet V := hG.isOpen.measurableSet
  have hVs := hG.subset_source
  have hφV : MeasurableSet (φ '' V) := measurableSet_image_chart x₀ hVm hVs
  have htH : φ.target ⊆ Half.H (n + 1) := fun z hz => by
    rw [Half.H_eq]; exact extChartAt_target_subset_range x₀ hz
  set P : Set (EuclideanSpace ℝ (Fin (n + 1))) := {z | z 0 = 0} with hP
  have hPm : MeasurableSet P := (Half.isClosed_hyperplane n).measurableSet
  have hPH : P ⊆ Half.H (n + 1) := fun z (hz : z 0 = 0) => by
    show (0 : ℝ) ≤ z 0
    rw [hz]
  set A := V ∩ φ ⁻¹' P with hAdef
  have hA : MeasurableSet A := measurableSet_inter_preimage_chart x₀ hVm hVs hPm
  have hAV : A ⊆ V := inter_subset_left
  have hAs : A ⊆ (chartAt (EuclideanHalfSpace (n + 1)) x₀).source := hAV.trans hVs
  have hφAP : φ '' A ⊆ P := image_subset_iff.mpr fun y hy => hy.2
  set c2 : ℝ≥0∞ := (Cμ : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal with hc2
  have hc2t : c2 ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
  set cσ : ℝ≥0∞ := (Cσ : ℝ≥0∞) ^ (1 / p).toReal with hcσ
  have hcσt : cσ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
  set cK : ℝ≥0∞ := (K : ℝ≥0∞) ^ (1 / p).toReal with hcK
  have hcKt : cK ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
  set cT : ℝ≥0∞ := (CT : ℝ≥0∞) ^ (1 / q) with hcT
  have hcTt : cT ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.coe_ne_top
  set B : ℝ≥0∞ := cσ * cK * cT * c2 * c with hB
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top hcσt hcKt) hcTt) hc2t) hc
  refine ⟨B.toNNReal, fun u hu => ?_⟩
  rw [ENNReal.coe_toNNReal hBt]
  set f := ρ * u with hf
  have hf1 : IsC1 (n + 1) f := hρ.mul hu
  have hfV : tsupport f ⊆ V := (tsupport_mul_subset_left (f := ρ) (g := u)).trans hρV
  have hfs : tsupport f ⊆ (chartAt (EuclideanHalfSpace (n + 1)) x₀).source := hfV.trans hVs
  set v := chartFun (n + 1) x₀ f with hv
  have hvC : ContDiffOn ℝ 1 v (Half.H (n + 1)) := contDiffOn_chartFun x₀ hf1 hfs
  have hvc : HasCompactSupport v := hasCompactSupport_chartFun x₀ hfs
  -- step 1: `σ` lives on `∂M`, so only `A` counts
  have hae : ∀ᵐ y ∂σ, y ∈ (𝓡∂ (n + 1)).boundary M := by
    rw [ae_iff]; exact hσ0
  have e1 : eLpNorm f p σ = eLpNorm f p (σ.restrict A) := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hA]
    refine eLpNorm_congr_ae (hae.mono fun y hy => ?_)
    by_cases hyA : y ∈ A
    · rw [indicator_of_mem hyA]
    · rw [indicator_of_notMem hyA]
      by_cases hyV : y ∈ V
      · exact absurd ⟨hyV, chart_boundary hy (hVs hyV)⟩ hyA
      · exact image_eq_zero_of_notMem_tsupport fun h => hyV (hfV h)
  have e2 : eLpNorm f p (σ.restrict A) = eLpNorm (v ∘ φ) p (σ.restrict A) := by
    refine eLpNorm_congr_ae ((ae_restrict_mem hA).mono fun y hy => ?_)
    simp only [Function.comp_apply, hv]
    rw [chartFun_chart (hAs hy)]
  have hmapA := map_restrict_le_of σ (Measure.hausdorffMeasure (n : ℝ)) x₀ hA hAs
    (fun A' hA' hA'm => hσV A' (hA'.trans hAV) hA'm)
  have hφA : AEMeasurable φ (σ.restrict A) :=
    ((continuousOn_extChartAt x₀).mono (by rwa [extChartAt_source])).aemeasurable hA
  have hvt : AEStronglyMeasurable v ((Measure.hausdorffMeasure (n : ℝ)).restrict φ.target) :=
    (hvC.continuousOn.mono htH).aestronglyMeasurable (measurableSet_target x₀)
  have hvA : AEStronglyMeasurable v ((Measure.hausdorffMeasure (n : ℝ)).restrict (φ '' A)) :=
    hvt.mono_measure (Measure.restrict_mono (image_chart_subset_target x₀ hAs) le_rfl)
  have hvmap : AEStronglyMeasurable v (Measure.map φ (σ.restrict A)) :=
    (hvA.smul_measure (Cσ : ℝ≥0∞)).mono_measure hmapA
  have hvP : AEStronglyMeasurable v ((Measure.hausdorffMeasure (n : ℝ)).restrict P) :=
    (hvC.continuousOn.mono hPH).aestronglyMeasurable hPm
  have e3 : eLpNorm (v ∘ φ) p (σ.restrict A) ≤
      cσ * eLpNorm v p ((Measure.hausdorffMeasure (n : ℝ)).restrict P) := by
    rw [← eLpNorm_map_measure hvmap hφA]
    calc eLpNorm v p (Measure.map φ (σ.restrict A))
        ≤ eLpNorm v p ((Cσ : ℝ≥0∞) • (Measure.hausdorffMeasure (n : ℝ)).restrict (φ '' A)) :=
          eLpNorm_mono_measure _ hmapA
      _ = cσ * eLpNorm v p ((Measure.hausdorffMeasure (n : ℝ)).restrict (φ '' A)) := by
          rw [eLpNorm_smul_measure_of_ne_zero (ENNReal.coe_ne_zero.mpr hCσ), smul_eq_mul]
      _ ≤ cσ * eLpNorm v p ((Measure.hausdorffMeasure (n : ℝ)).restrict P) := by
          gcongr
  have e4 := hK p v hvP
  -- the half-space trace inequality, as an `L^p` norm
  set D := eLpNorm (fderivWithin ℝ v (Half.H (n + 1))) 2 (volume.restrict (Half.H (n + 1)))
    with hD
  have e5 : eLpNorm (v ∘ Half.ι n) p volume ≤ cT * D := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop, hpq]
    have h1 := hCT v hvC hvc
    have h1' : ∫⁻ z, ‖(v ∘ Half.ι n) z‖ₑ ^ q ≤ CT * D ^ q := by
      simpa only [Function.comp_apply, Half.ι_apply] using h1
    calc (∫⁻ z, ‖(v ∘ Half.ι n) z‖ₑ ^ q) ^ (1 / q) ≤ ((CT : ℝ≥0∞) * D ^ q) ^ (1 / q) :=
          ENNReal.rpow_le_rpow h1' (by positivity)
      _ = cT * D := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
  -- the derivative, as in the Sobolev estimate
  have hDm : AEStronglyMeasurable (fderivWithin ℝ v (Half.H (n + 1))) (volume.restrict φ.target) :=
    ((hvC.continuousOn_fderivWithin Half.uniqueDiffOn_H le_rfl).mono htH).aestronglyMeasurable
      (measurableSet_target x₀)
  have hT2 := (eLpNorm_chart_comparable μ x₀ hVm hVs hG.Cμ_ne hG.vol hDm 2).2
  have hD0 : ∀ z ∈ Half.H (n + 1), z ∉ φ '' V → fderivWithin ℝ v (Half.H (n + 1)) z = 0 :=
    fun z _ hz => fderivWithin_chartFun_eq_zero x₀ hfs fun h => hz (image_mono hfV h)
  have e6 := eLpNorm_restrict_le_of_vanish volume hφV Half.measurableSet_H hD0 2
  have e7 : eLpNorm (fderivWithin ℝ v (Half.H (n + 1)) ∘ φ) 2 (μ.restrict V) =
      eLpNorm (dChart (n + 1) x₀ f) 2 (μ.restrict V) :=
    eLpNorm_congr_ae ((ae_restrict_mem hVm).mono fun y hy => fderivWithin_chartFun x₀ (hVs hy) f)
  have e8 : D ≤ c2 * (c * w12 g μ u) := by
    calc D ≤ eLpNorm (fderivWithin ℝ v (Half.H (n + 1))) 2 (volume.restrict (φ '' V)) := e6
      _ ≤ c2 * eLpNorm (fderivWithin ℝ v (Half.H (n + 1)) ∘ φ) 2 (μ.restrict V) := hT2
      _ = c2 * eLpNorm (dChart (n + 1) x₀ f) 2 (μ.restrict V) := by rw [e7]
      _ ≤ c2 * (c * w12 g μ u) := by gcongr; exact hcu u hu
  calc eLpNorm f p σ = eLpNorm (v ∘ φ) p (σ.restrict A) := by rw [e1, e2]
    _ ≤ cσ * eLpNorm v p ((Measure.hausdorffMeasure (n : ℝ)).restrict P) := e3
    _ ≤ cσ * (cK * eLpNorm (v ∘ Half.ι n) p volume) := by gcongr
    _ ≤ cσ * (cK * (cT * D)) := by gcongr
    _ ≤ cσ * (cK * (cT * (c2 * (c * w12 g μ u)))) := by gcongr
    _ = B * w12 g μ u := by rw [hB]; ring

end Mfd

end Yamabe
