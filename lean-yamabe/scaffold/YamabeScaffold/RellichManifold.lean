import YamabeScaffold.Rellich
import Yamabe.RellichCriterion

/-!
# Rellich–Kondrachov on a compact manifold with boundary: the manifold half

Labels (NOT marked: partial, see SCOPE):

* `lem:positivity` — `Yamabegap.tex:715` (statement l.715–718, proof l.719–721): the step « by the
  Rellich--Kondrachov theorem a subsequence converges in $L^2(\Sigma)$ » (l.720), on a compact
  Riemannian manifold with boundary, for a sequence bounded in `W^{1,2}` (read through `C¹`).

> By \eqref{eq:hoelder}, $(u_k)$ is bounded in $W^{1,2}(\Sigma)$, so by the Rellich--Kondrachov
> theorem a subsequence converges in $L^2(\Sigma)$ and weakly in $W^{1,2}(\Sigma)$ to some
> $u_\infty$ [...] (l.720)

## What is proved

* `Mfd.isLocallyFiniteMeasure_of_isLocallyLebesgue`, `Mfd.isFiniteMeasure_of_isLocallyLebesgue`:
  a locally-Lebesgue `μ` is locally finite (a chart neighbourhood with image in a ball has measure
  at most `C` times the ball's volume), hence finite on a compact manifold (Mathlib's
  `CompactSpace.isFiniteMeasure`);
* `Mfd.local_cell_approx`: on a good chart neighbourhood `V` (`Mfd.GoodChart`) and for a `C¹`
  cut-off `ρ` supported in `V`, the function `ρ u` is approximated in `L²(μ)` by the finite
  combination `∑_z avg_{C_z}(v) · 1_{V ∩ φ⁻¹ C_z}` of the averages of `v = (ρ u) ∘ φ⁻¹` on the grid
  cubes `C_z` of side `δ`, with error `≤ A δ ‖u‖_{W^{1,2}}`, `A` independent of `u` and `δ`: the
  Euclidean `Half.cell_approx` (`YamabeScaffold.Compactness`) read through the chart
  (`Mfd.eLpNorm_chart_comparable`) and the chart derivative bound `Mfd.eLpNorm_dChart_mul_le`;
* **`Mfd.rellich_kondrachov'`**, with exactly the statement of `Mfd.rellich_kondrachov`
  (`YamabeScaffold.Rellich`): every sequence of `C¹` functions bounded in `W^{1,2}(μ)` has a
  subsequence converging in `L²(μ)`. The partition of unity of `Mfd.assemble` sums the local
  approximations; the strict criterion `exists_subseq_tendsto_eLpNorm_two`
  (`Yamabe.RellichCriterion`, total boundedness in `Lp`) concludes. The statement is checked
  identical to the round-1 one by an `example` (`type_of% … = type_of% … := rfl`) and by an
  `Expr`-equality check of the two constants' types (`run_cmd`, binder names ignored).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ` a compact Riemannian `N`-manifold with boundary | ✓ carried: `CompactSpace`, `T2Space`, `IsManifold (𝓡∂ N) ∞ M`, smooth `g`, as in round 1 (OQ-93 (a)); `N ≥ 3` is not needed |
| `vol_g` | ⚠ read as every locally-Lebesgue `μ` (OQ-93 (a)), finiteness derived |
| `(u_k)` bounded in `W^{1,2}(Σ)` | ⚠ read as `u_k ∈ C¹(M)` with `‖∇u_k‖_{L²} + ‖u_k‖_{L²} ≤ K` (OQ-93 (b)) |
| the conclusion: a subsequence converging in `L²(Σ)` | ✓ to a limit `f ∈ L²(μ)` (`MemLp f 2 μ`), in `eLpNorm` |

## SCOPE (disclosed)

* The weak `W^{1,2}` convergence of l.720 is not stated here: as in round 1 it is carried by the
  constancy step (`Mfd.const_of_tendsto`, `ConstLimit`; OQ-93 (c)).
* `Mfd.rellich_kondrachov'` is the primed copy of the round-1 `sorry` `Mfd.rellich_kondrachov`;
  rewiring it (deleting the original, renaming the copy) is the integration's. Nothing here uses
  `YamabeScaffold.Rellich` except the two identity checks at the end: without them the file
  needs only `YamabeScaffold.Compactness` and `Yamabe.RellichCriterion`, so `YamabeScaffold.Rellich`
  can import it once the checks are dropped.
* No label is marked: this is one step of lem:positivity's proof, under the readings of OQ-93.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Manifold ContDiff Bundle

noncomputable section

namespace Yamabe

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M]

/-! ## 1. A locally-Lebesgue measure on a compact manifold is finite -/

omit [IsManifold (𝓡∂ N) ∞ M] in
/-- A locally-Lebesgue `μ` is locally finite: a chart neighbourhood of `x₀` with image in a ball
has measure at most `C` times the volume of the ball. -/
theorem isLocallyFiniteMeasure_of_isLocallyLebesgue {μ : Measure M}
    (hμ : IsLocallyLebesgue N μ) : IsLocallyFiniteMeasure μ := by
  refine ⟨fun x₀ => ?_⟩
  obtain ⟨U, hU, C, hC⟩ := hμ x₀
  set φ := extChartAt (𝓡∂ N) x₀ with hφ
  set W := interior U ∩ ((chartAt (EuclideanHalfSpace N) x₀).source ∩
    φ ⁻¹' Metric.ball (φ x₀) 1) with hW
  have hWo : IsOpen W := by
    refine isOpen_interior.inter ?_
    have h := (continuousOn_extChartAt (I := 𝓡∂ N) x₀).isOpen_inter_preimage
      (isOpen_extChartAt_source x₀) (Metric.isOpen_ball (x := φ x₀) (ε := 1))
    rwa [extChartAt_source] at h
  have hxW : x₀ ∈ W := ⟨mem_interior_iff_mem_nhds.mpr hU, mem_chart_source _ x₀,
    Metric.mem_ball_self one_pos⟩
  refine ⟨W, hWo.mem_nhds hxW, ?_⟩
  have hWsub : W ⊆ U ∩ (chartAt (EuclideanHalfSpace N) x₀).source := fun y hy =>
    ⟨interior_subset hy.1, hy.2.1⟩
  calc μ W ≤ C * volume (φ '' W) := (hC W hWsub hWo.measurableSet).1
    _ ≤ C * volume (Metric.ball (φ x₀) 1) := by
        gcongr
        exact image_subset_iff.mpr fun y hy => hy.2.2
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top measure_ball_lt_top

omit [IsManifold (𝓡∂ N) ∞ M] in
/-- **A locally-Lebesgue `μ` on a compact manifold is finite.** -/
theorem isFiniteMeasure_of_isLocallyLebesgue [CompactSpace M] {μ : Measure M}
    (hμ : IsLocallyLebesgue N μ) : IsFiniteMeasure μ := by
  haveI := isLocallyFiniteMeasure_of_isLocallyLebesgue hμ
  infer_instance

/-! ## 2. The cell approximation read in a good chart -/

/-- **The local cell approximation.** On a good chart neighbourhood `V` of the chart `φ` at `x₀`,
for a `C¹` cut-off `ρ` supported in `V` with `|ρ| ≤ 1`, there is `A < ∞` such that for every
`δ > 0` a finite set `Z` of grid cubes `C_z = Half.cube δ z` gives, for every `u ∈ C¹(M)`,
`‖ρ u − ∑_{z ∈ Z} avg_{C_z}((ρ u) ∘ φ⁻¹) · 1_{V ∩ φ⁻¹ C_z}‖_{L²(μ)} ≤ A δ ‖u‖_{W^{1,2}(μ)}`. -/
theorem local_cell_approx [CompactSpace M] {g : RiemannianMetric N M} {μ : Measure M} {x₀ : M}
    {V : Set M} {Cμ : ℝ≥0} {Cg : ℝ} (hG : GoodChart g μ x₀ V Cμ Cg) {ρ : M → ℝ}
    (hρ : IsC1 N ρ) (hρV : tsupport ρ ⊆ V) (hρ1 : ∀ y, |ρ y| ≤ 1) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ δ : ℝ, 0 < δ → ∃ Z : Finset (Fin N → ℤ), ∀ u : M → ℝ, IsC1 N u →
      eLpNorm (ρ * u - ∑ z ∈ Z, Half.avg δ z (chartFun N x₀ (ρ * u)) •
          (V ∩ extChartAt (𝓡∂ N) x₀ ⁻¹' Half.cube δ z).indicator (fun _ => (1 : ℝ))) 2 μ ≤
        A * ENNReal.ofReal δ * w12 g μ u := by
  obtain ⟨c, hc, hcu⟩ := eLpNorm_dChart_mul_le hG hρ hρ1
  set φ := extChartAt (𝓡∂ N) x₀ with hφ
  have hVm : MeasurableSet V := hG.isOpen.measurableSet
  have hVs := hG.subset_source
  have hφV : MeasurableSet (φ '' V) := measurableSet_image_chart x₀ hVm hVs
  have htH : φ.target ⊆ Half.H N := fun z hz => by
    rw [Half.H_eq]; exact extChartAt_target_subset_range x₀ hz
  have hρs : tsupport ρ ⊆ (chartAt (EuclideanHalfSpace N) x₀).source := hρV.trans hVs
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp (isCompact_image_tsupport x₀ hρs).isBounded
  set c2 : ℝ≥0∞ := (Cμ : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal with hc2
  have hc2t : c2 ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
  set B : ℝ := Real.sqrt (2 * 2 ^ N * N) with hB
  refine ⟨c2 * ENNReal.ofReal B * c2 * c,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hc2t ENNReal.ofReal_ne_top) hc2t) hc,
    fun δ hδ => ?_⟩
  have hcδ : ENNReal.ofReal (B * δ) ^ (2 : ℝ) = 2 * 2 ^ N * ENNReal.ofReal (N * δ ^ 2) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hδ.le) two_pos.le,
      Real.rpow_two, mul_pow, Real.sq_sqrt (by positivity),
      show (2 * 2 ^ N * (N : ℝ)) * δ ^ 2 = (2 * 2 ^ N) * (N * δ ^ 2) by ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  obtain ⟨Z, -, hZ⟩ := Half.cell_approx (N := N) R hδ
  refine ⟨Z, fun u hu => ?_⟩
  set f := ρ * u with hf
  have hf1 : IsC1 N f := hρ.mul hu
  have hfρ : tsupport f ⊆ tsupport ρ := tsupport_mul_subset_left
  have hfs : tsupport f ⊆ (chartAt (EuclideanHalfSpace N) x₀).source := hfρ.trans hρs
  set v := chartFun N x₀ f with hv
  have hvC : ContDiffOn ℝ 1 v (Half.H N) := contDiffOn_chartFun x₀ hf1 hfs
  have hvR : ∀ y, R < ‖y‖ → v y = 0 := fun y hy =>
    chartFun_eq_zero x₀ fun hy' => by
      have := hR y (image_mono hfρ hy')
      linarith
  set P : EuclideanSpace ℝ (Fin N) → ℝ := fun w =>
    ∑ z ∈ Z, (Half.cube δ z).indicator (fun _ => Half.avg δ z v) w with hP
  have hZv := hZ v hvC hvR
  -- the difference, on `M`
  have hdiff : f - ∑ z ∈ Z, Half.avg δ z v •
      (V ∩ φ ⁻¹' Half.cube δ z).indicator (fun _ => (1 : ℝ)) = V.indicator ((v - P) ∘ φ) := by
    funext y
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hy : y ∈ V
    · rw [indicator_of_mem hy]
      simp only [Function.comp_apply, Pi.sub_apply, hP, hv]
      rw [chartFun_chart (hVs hy)]
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hz : φ y ∈ Half.cube δ z
      · rw [indicator_of_mem (show y ∈ V ∩ φ ⁻¹' Half.cube δ z from ⟨hy, hz⟩),
          indicator_of_mem hz, mul_one]
      · rw [indicator_of_notMem (show y ∉ V ∩ φ ⁻¹' Half.cube δ z from fun h => hz h.2),
          indicator_of_notMem hz, mul_zero]
    · rw [indicator_of_notMem hy]
      have hfy : f y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hρV (hfρ h)))
      rw [hfy, Finset.sum_eq_zero fun z _ => by
        rw [indicator_of_notMem (show y ∉ V ∩ φ ⁻¹' Half.cube δ z from fun h => hy h.1),
          mul_zero], sub_zero]
  have hvm : AEStronglyMeasurable (v - P) (volume.restrict φ.target) := by
    refine ((hvC.continuousOn.mono htH).aestronglyMeasurable (measurableSet_target x₀)).sub ?_
    exact (Finset.measurable_sum Z fun z _ =>
      measurable_const.indicator (Half.measurableSet_cube δ z)).aestronglyMeasurable
  have hDm : AEStronglyMeasurable (fderivWithin ℝ v (Half.H N)) (volume.restrict φ.target) :=
    ((hvC.continuousOn_fderivWithin Half.uniqueDiffOn_H le_rfl).mono htH).aestronglyMeasurable
      (measurableSet_target x₀)
  have hT1 := (eLpNorm_chart_comparable μ x₀ hVm hVs hG.Cμ_ne hG.vol hvm 2).1
  have hT2 := (eLpNorm_chart_comparable μ x₀ hVm hVs hG.Cμ_ne hG.vol hDm 2).2
  have hD0 : ∀ z ∈ Half.H N, z ∉ φ '' V → fderivWithin ℝ v (Half.H N) z = 0 := fun z _ hz =>
    fderivWithin_chartFun_eq_zero x₀ hfs fun h => hz (image_mono (hfρ.trans hρV) h)
  have e2 := eLpNorm_restrict_le_of_vanish volume hφV Half.measurableSet_H hD0 2
  have e3 : eLpNorm (fderivWithin ℝ v (Half.H N) ∘ φ) 2 (μ.restrict V) =
      eLpNorm (dChart N x₀ f) 2 (μ.restrict V) :=
    eLpNorm_congr_ae ((ae_restrict_mem hVm).mono fun y hy => fderivWithin_chartFun x₀ (hVs hy) f)
  -- the Euclidean cell estimate, in `eLpNorm` form
  have hcell : eLpNorm (v - P) 2 (volume.restrict (Half.H N)) ≤
      ENNReal.ofReal (B * δ) *
        eLpNorm (fderivWithin ℝ v (Half.H N)) 2 (volume.restrict (Half.H N)) := by
    rw [← ENNReal.rpow_le_rpow_iff two_pos, ENNReal.mul_rpow_of_nonneg _ _ two_pos.le,
      ← lintegral_enorm_rpow_two_eq, ← lintegral_enorm_rpow_two_eq, hcδ]
    exact hZv
  rw [hdiff, eLpNorm_indicator_eq_eLpNorm_restrict hVm]
  calc eLpNorm ((v - P) ∘ φ) 2 (μ.restrict V)
      ≤ c2 * eLpNorm (v - P) 2 (volume.restrict (φ '' V)) := hT1
    _ ≤ c2 * eLpNorm (v - P) 2 (volume.restrict (Half.H N)) := by
        gcongr
        exact image_chart_subset_H x₀ hVs
    _ ≤ c2 * (ENNReal.ofReal (B * δ) *
          eLpNorm (fderivWithin ℝ v (Half.H N)) 2 (volume.restrict (Half.H N))) := by gcongr
    _ ≤ c2 * (ENNReal.ofReal (B * δ) *
          eLpNorm (fderivWithin ℝ v (Half.H N)) 2 (volume.restrict (φ '' V))) := by gcongr
    _ ≤ c2 * (ENNReal.ofReal (B * δ) *
          (c2 * eLpNorm (fderivWithin ℝ v (Half.H N) ∘ φ) 2 (μ.restrict V))) := by gcongr
    _ = c2 * (ENNReal.ofReal (B * δ) * (c2 * eLpNorm (dChart N x₀ f) 2 (μ.restrict V))) := by
        rw [e3]
    _ ≤ c2 * (ENNReal.ofReal (B * δ) * (c2 * (c * w12 g μ u))) := by
        gcongr; exact hcu u hu
    _ = c2 * ENNReal.ofReal B * c2 * c * ENNReal.ofReal δ * w12 g μ u := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]; ring

/-! ## 3. Rellich–Kondrachov -/

/-- **Rellich–Kondrachov** on a compact manifold with boundary (l.720): every sequence bounded in
`W^{1,2}(M)` has a subsequence converging in `L²(M)`. The statement of the round-1
`Mfd.rellich_kondrachov`, proved. -/
theorem rellich_kondrachov' [CompactSpace M] [T2Space M] (g : RiemannianMetric N M)
    {μ : Measure M} (hμ : IsLocallyLebesgue N μ)
    (u : ℕ → M → ℝ) (hu : ∀ k, IsC1 N (u k)) (hb : ∃ K : ℝ≥0, ∀ k, w12 g μ (u k) ≤ K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : M → ℝ, MemLp f 2 μ ∧
      Tendsto (fun k => eLpNorm (u (φ k) - f) 2 μ) atTop (𝓝 0) := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  obtain ⟨K, hK⟩ := hb
  choose V Cμ Cg hxV hG using exists_goodChart g hμ
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover V
    (fun x _ => (hG x).isOpen.mem_nhds (hxV x))
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡∂ N) isClosed_univ
    (fun i : t => V i) (fun i => (hG i).isOpen) (by
      intro y _
      obtain ⟨x, hx, hy⟩ := mem_iUnion₂.mp (ht (mem_univ y))
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hy⟩)
  have hρC1 : ∀ i, IsC1 N (ρ i) := fun i => (ρ i).contMDiff.of_le (by exact_mod_cast le_top)
  have hρ1 : ∀ i y, |ρ i y| ≤ 1 := fun i y =>
    abs_le.mpr ⟨by linarith [ρ.nonneg i y], ρ.le_one i y⟩
  choose A hA hAZ using fun i : t => local_cell_approx (hG i) (hρC1 i) (hρ i) (hρ1 i)
  have hsum : ∀ w : M → ℝ, w = ∑ i : t, (ρ i : M → ℝ) * w := by
    intro w
    funext y
    rw [Finset.sum_apply]
    simp only [Pi.mul_apply]
    rw [← Finset.sum_mul, ← finsum_eq_sum_of_fintype, ρ.sum_eq_one (mem_univ y), one_mul]
  refine exists_subseq_tendsto_eLpNorm_two (β := Σ _ : t, (Fin N → ℤ)) u
    (fun k => (hu k).continuous.aestronglyMeasurable)
    ⟨K, fun k => le_add_self.trans (hK k)⟩ (fun ε hε => ?_)
  set Atot : ℝ≥0∞ := ∑ i, A i with hAtot
  have hAtott : Atot ≠ ⊤ := ENNReal.sum_ne_top.mpr fun i _ => hA i
  set δ : ℝ := ε / (Atot.toReal * K + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  choose Z hZ using fun i : t => hAZ i δ hδ0
  set G : (Σ _ : t, (Fin N → ℤ)) → M → ℝ := fun p =>
    (V p.1 ∩ extChartAt (𝓡∂ N) (p.1 : M) ⁻¹' Half.cube δ p.2).indicator (fun _ => (1 : ℝ))
    with hGdef
  have hGm : ∀ p : Σ _ : t, (Fin N → ℤ),
      MeasurableSet (V p.1 ∩ extChartAt (𝓡∂ N) (p.1 : M) ⁻¹' Half.cube δ p.2) := fun p =>
    measurableSet_inter_preimage_chart _ (hG p.1).isOpen.measurableSet (hG p.1).subset_source
      (Half.measurableSet_cube δ p.2)
  refine ⟨Finset.univ.sigma Z, G, fun p _ => memLp_indicator_const 2 (hGm p) 1
    (Or.inr (measure_ne_top μ _)), fun k => ⟨fun p => Half.avg δ p.2
      (chartFun N (p.1 : M) ((ρ p.1 : M → ℝ) * u k)), ?_⟩⟩
  set F : t → M → ℝ := fun i => (ρ i : M → ℝ) * u k - ∑ z ∈ Z i,
    Half.avg δ z (chartFun N (i : M) ((ρ i : M → ℝ) * u k)) • G ⟨i, z⟩ with hF
  have hdec : u k - ∑ p ∈ Finset.univ.sigma Z, Half.avg δ p.2
      (chartFun N (p.1 : M) ((ρ p.1 : M → ℝ) * u k)) • G p = ∑ i : t, F i := by
    rw [Finset.sum_sigma, hF, Finset.sum_sub_distrib, ← hsum (u k)]
  have hFm : ∀ i ∈ (Finset.univ : Finset t), AEStronglyMeasurable (F i) μ := fun i _ =>
    ((hρC1 i).continuous.mul (hu k).continuous).aestronglyMeasurable.sub
      (Finset.aestronglyMeasurable_sum _ fun z _ =>
        ((measurable_const.indicator (hGm ⟨i, z⟩)).aestronglyMeasurable).const_smul _)
  have hfin : Atot * ENNReal.ofReal δ * K ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hAtott, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg hδ0.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have ha : 0 ≤ Atot.toReal * K := mul_nonneg ENNReal.toReal_nonneg K.2
    calc Atot.toReal * δ * K = ε * (Atot.toReal * K) / (Atot.toReal * K + 1) := by
          rw [hδ]; field_simp
      _ ≤ ε := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  rw [hdec]
  calc eLpNorm (∑ i : t, F i) 2 μ ≤ ∑ i : t, eLpNorm (F i) 2 μ := eLpNorm_sum_le hFm one_le_two
    _ ≤ ∑ i : t, A i * ENNReal.ofReal δ * w12 g μ (u k) :=
        Finset.sum_le_sum fun i _ => hZ i (u k) (hu k)
    _ ≤ ∑ i : t, A i * ENNReal.ofReal δ * K := by gcongr with i; exact hK k
    _ = Atot * ENNReal.ofReal δ * K := by rw [hAtot, Finset.sum_mul, Finset.sum_mul]
    _ ≤ ENNReal.ofReal ε := hfin

end Mfd

universe u in
/-- The primed copy has the round-1 statement (definitional check). -/
example : type_of% @Mfd.rellich_kondrachov.{u} = type_of% @Mfd.rellich_kondrachov'.{u} := rfl

open Lean in
/- The primed copy has the round-1 statement (syntactic check: the two types are `Expr`-equal,
binder names and binder info aside, after aligning the universe parameters). -/
run_cmd do
  let env ← getEnv
  let some a := env.find? ``Yamabe.Mfd.rellich_kondrachov | throwError "missing original"
  let some b := env.find? ``Yamabe.Mfd.rellich_kondrachov' | throwError "missing copy"
  unless a.levelParams.length == b.levelParams.length do throwError "universe parameters differ"
  let bt := b.type.instantiateLevelParams b.levelParams (a.levelParams.map Level.param)
  unless a.type == bt do throwError "the types of rellich_kondrachov and its copy differ"

end Yamabe
