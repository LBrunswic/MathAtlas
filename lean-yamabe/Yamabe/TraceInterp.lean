import Yamabe.RellichManifold

/-!
# The interpolation trace inequality `‖u‖_{L²(∂M)} ≤ C (δ ‖u‖_{W^{1,2}} + δ⁻¹ ‖u‖_{L²})`, on the half-space and on a compact manifold with boundary

Labels (NOT marked: infrastructure for `Mfd.trace_compact`, `Yamabe.TraceCompact`):

* `lem:positivity` — `Yamabegap.tex:715` (statement l.715–718, proof l.719–721): the compactness
  of the trace `W^{1,2}(Σ) → L²(∂Σ)` that its proof cites (l.720) rests on the interpolation
  inequality proved here, together with Rellich–Kondrachov (`Mfd.rellich_kondrachov`).

> The trace operator $W^{1,2}(\Sigma)\to L^2(\partial\Sigma)$ is compact, so the traces converge
> to $c$ in $L^2(\partial\Sigma)$; [...] (l.720)

## What is proved

* `Half.trace_interp_halfSpace`: for `v` `C¹` on the closed half-space `ℍ̄ ⊆ ℝ^{n+1}` with
  compact support and every `δ > 0`,
  `‖v(0, ·)‖_{L²(ℝ^n)} ≤ δ ‖Dv‖_{L²(ℍ̄)} + δ⁻¹ ‖v‖_{L²(ℍ̄)}`: the fundamental theorem of
  calculus in the normal direction (`trace_halfSpace` at `q = 2`, on the `C¹` reflection
  `Half.ext` read through `Half.Φ`) and `2ab ≤ δ²b² + δ⁻²a²` pointwise;
* `Mfd.assemble_family`: `Mfd.assemble` for a family of right-hand sides with constants
  independent of the index (the partition of unity of `Mfd.assemble`, any family of continuous
  functions);
* `Mfd.local_trace_interp`: on a good chart neighbourhood carrying the bound of
  `IsBoundaryMeasure`, for a `C¹` cut-off `ρ`, `C¹` functions `u, w` and every `δ > 0`,
  `‖ρ(u − w)‖_{L²(σ)} ≤ C (δ (‖u‖_{W^{1,2}} + ‖w‖_{W^{1,2}}) + δ⁻¹ ‖u − w‖_{L²(μ)})`, `C`
  independent of `δ, u, w`: the half-space inequality read through the chart, as `Mfd.local_trace`
  reads the critical one;
* **`Mfd.trace_interp_sub`**, **`Mfd.trace_interp`**: the global forms on a compact manifold with
  boundary, for every locally-Lebesgue `μ` and every boundary measure `σ`, any `N ≥ 1`;
* `Mfd.memLp_two_of_isC1`: a `C¹` function lies in `L²(σ)`.

The difference form is the one the compactness argument uses: `W^{1,2}` bounds of `u_k − u_l`
are not available from those of `u_k, u_l` without the measurability of `|∇u|_g`, which the library
does not prove; the derivative term is split in the chart, where it is measurable.

## Hypothesis checklist

| hypothesis | here |
|---|---|
| `Σ` compact Riemannian with boundary | ✓ carried as in `Yamabe.Trace`: `CompactSpace`, `T2Space`, smooth `g`; any `N` with `NeZero N` |
| the volume, the area of `∂Σ` | ⚠ read as in `Yamabe.Trace`: every `IsLocallyLebesgue` `μ`, every `IsBoundaryMeasure` `σ` |
| `u ∈ W^{1,2}(Σ)` | ⚠ read as `C¹(M)` (OQ-93 (b)) |

## SCOPE (disclosed)

* Infrastructure: no label is certified here. The interpolation inequality is not printed in the
  paper; it is the standard step from the trace theorem and Rellich–Kondrachov to the compactness
  of the trace (l.720).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Manifold ContDiff Bundle

noncomputable section

namespace Yamabe

namespace Half

/-- `Φ (1, 0)` is the first basis vector: it has norm `1`. -/
lemma norm_Φ_one_zero (n : ℕ) : ‖Φ n ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n)))‖ = 1 := by
  rw [Φ_apply, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
  simp

/-- **The interpolation trace inequality on the half-space**: for `v` `C¹` on `ℍ̄ ⊆ ℝ^{n+1}`
with compact support and `δ > 0`, `‖v(0, ·)‖_{L²(ℝ^n)} ≤ δ ‖Dv‖_{L²(ℍ̄)} + δ⁻¹ ‖v‖_{L²(ℍ̄)}`,
`Dv` the derivative within `ℍ̄`. -/
theorem trace_interp_halfSpace {n : ℕ} {v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hv : ContDiffOn ℝ 1 v (H (n + 1))) (hc : HasCompactSupport v) {δ : ℝ} (hδ : 0 < δ) :
    eLpNorm (v ∘ ι n) 2 volume ≤
      ENNReal.ofReal δ * eLpNorm (fderivWithin ℝ v (H (n + 1))) 2 (volume.restrict (H (n + 1))) +
        ENNReal.ofReal δ⁻¹ * eLpNorm v 2 (volume.restrict (H (n + 1))) := by
  set P : (ℝ × EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (Φ n : (ℝ × EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) with hP
  set w := ext (n + 1) v ∘ Φ n with hw
  have hwC : ContDiff ℝ 1 w := (contDiff_ext hv).comp (Φ n).contDiff
  have hwc : HasCompactSupport w := (hasCompactSupport_ext hc).comp_homeomorph (Φ n).toHomeomorph
  have hT := trace_halfSpace (q := 2) le_rfl hwC hwc
  set S : Set (ℝ × EuclideanSpace ℝ (Fin n)) := Ioi (0 : ℝ) ×ˢ univ with hS
  have hSH : S ⊆ Φ n ⁻¹' H (n + 1) := fun p hp => by
    show (0 : ℝ) ≤ Φ n p 0
    rw [Φ_apply_zero]; exact le_of_lt hp.1
  set D := eLpNorm (fderivWithin ℝ v (H (n + 1))) 2 (volume.restrict (H (n + 1))) with hD
  set Vn := eLpNorm v 2 (volume.restrict (H (n + 1))) with hVn
  set a : ℝ × EuclideanSpace ℝ (Fin n) → ℝ := fun p => |w p| with ha
  set b : ℝ × EuclideanSpace ℝ (Fin n) → ℝ := fun p => ‖extD (n + 1) v (Φ n p)‖ with hb
  have hac : Continuous a := hwC.continuous.abs
  have hbc : Continuous b := ((continuous_extD hv).comp (Φ n).continuous).norm
  have hfd : ∀ p, fderiv ℝ w p = (fderiv ℝ (ext (n + 1) v) (Φ n p)).comp P := fun p =>
    ((((contDiff_ext hv).differentiable one_ne_zero) _).hasFDerivAt.comp p
      P.hasFDerivAt).fderiv
  have hpt : ∀ p, |w p| ^ ((2 : ℝ) - 1) * |fderiv ℝ w p (1, 0)| ≤ a p * b p := by
    intro p
    have h1 : |fderiv ℝ w p (1, 0)| ≤ b p := by
      rw [hfd p, fderiv_ext hv, ContinuousLinearMap.comp_apply, ← Real.norm_eq_abs]
      have h0 : P ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n))) = Φ n (1, 0) := rfl
      have := (extD (n + 1) v (Φ n p)).le_opNorm (Φ n ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n))))
      rw [norm_Φ_one_zero, mul_one] at this
      rw [h0]
      exact this
    have h2 : |w p| ^ ((2 : ℝ) - 1) = a p := by norm_num [ha]
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hamgm : ∀ p, 2 * (a p * b p) ≤ δ ^ 2 * b p ^ 2 + δ⁻¹ ^ 2 * a p ^ 2 := by
    intro p
    have h0 := sq_nonneg (δ * b p - δ⁻¹ * a p)
    have h1 : δ * b p * (δ⁻¹ * a p) = a p * b p := by field_simp
    nlinarith [h1]
  have hemb : MeasurableEmbedding (Φ n) := (Φ n).toHomeomorph.measurableEmbedding
  have hMP := measurePreserving_Φ n
  -- the left side
  have hlhs : eLpNorm (v ∘ ι n) 2 volume ^ (2 : ℝ) =
      ∫⁻ z, ENNReal.ofReal (|w (0, z)| ^ (2 : ℝ)) := by
    rw [← lintegral_enorm_rpow_two_eq]
    refine lintegral_congr fun z => ?_
    have e1 : (v ∘ ι n) z = w (0, z) := by
      simp only [Function.comp_apply, hw, ι_apply]
      rw [ext_of_mem]
      show (0 : ℝ) ≤ Φ n (0, z) 0
      rw [Φ_apply_zero]
    rw [e1, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) zero_le_two]
  -- the two terms
  have hbD : ∫⁻ p in S, ENNReal.ofReal (b p ^ 2) ≤ D ^ (2 : ℝ) := by
    calc ∫⁻ p in S, ENNReal.ofReal (b p ^ 2)
        ≤ ∫⁻ p in Φ n ⁻¹' H (n + 1), ENNReal.ofReal (‖extD (n + 1) v (Φ n p)‖ ^ 2) :=
          lintegral_mono_set hSH
      _ = ∫⁻ z in H (n + 1), ENNReal.ofReal (‖extD (n + 1) v z‖ ^ 2) :=
          hMP.setLIntegral_comp_preimage_emb hemb
            (fun z => ENNReal.ofReal (‖extD (n + 1) v z‖ ^ 2)) _
      _ = ∫⁻ z in H (n + 1), ‖fderivWithin ℝ v (H (n + 1)) z‖ₑ ^ (2 : ℝ) := by
          refine setLIntegral_congr_fun measurableSet_H fun z hz => ?_
          rw [extD, if_pos (show (0 : ℝ) ≤ z 0 from hz), ← ofReal_norm,
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two, Real.rpow_two]
      _ = D ^ (2 : ℝ) := lintegral_enorm_rpow_two_eq _ _
  have haV : ∫⁻ p in S, ENNReal.ofReal (a p ^ 2) ≤ Vn ^ (2 : ℝ) := by
    calc ∫⁻ p in S, ENNReal.ofReal (a p ^ 2)
        ≤ ∫⁻ p in Φ n ⁻¹' H (n + 1), ENNReal.ofReal (|ext (n + 1) v (Φ n p)| ^ 2) :=
          lintegral_mono_set hSH
      _ = ∫⁻ z in H (n + 1), ENNReal.ofReal (|ext (n + 1) v z| ^ 2) :=
          hMP.setLIntegral_comp_preimage_emb hemb
            (fun z => ENNReal.ofReal (|ext (n + 1) v z| ^ 2)) _
      _ = ∫⁻ z in H (n + 1), ‖v z‖ₑ ^ (2 : ℝ) := by
          refine setLIntegral_congr_fun measurableSet_H fun z hz => ?_
          rw [ext_of_mem hz, Real.enorm_eq_ofReal_abs,
            ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) zero_le_two, Real.rpow_two]
      _ = Vn ^ (2 : ℝ) := lintegral_enorm_rpow_two_eq _ _
  have hbm : Measurable fun p => ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal (b p ^ 2) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp (hbc.pow 2).measurable)
  have ham : Measurable fun p => ENNReal.ofReal (a p ^ 2) :=
    ENNReal.measurable_ofReal.comp (hac.pow 2).measurable
  have hbm' : Measurable fun p => ENNReal.ofReal (b p ^ 2) :=
    ENNReal.measurable_ofReal.comp (hbc.pow 2).measurable
  have hmain : eLpNorm (v ∘ ι n) 2 volume ^ (2 : ℝ) ≤
      ENNReal.ofReal (δ ^ 2) * D ^ (2 : ℝ) + ENNReal.ofReal (δ⁻¹ ^ 2) * Vn ^ (2 : ℝ) := by
    rw [hlhs]
    calc ∫⁻ z, ENNReal.ofReal (|w (0, z)| ^ (2 : ℝ))
        ≤ ENNReal.ofReal 2 * ∫⁻ p in S,
            ENNReal.ofReal (|w p| ^ ((2 : ℝ) - 1) * |fderiv ℝ w p (1, 0)|) := hT
      _ ≤ ENNReal.ofReal 2 * ∫⁻ p in S, ENNReal.ofReal (a p * b p) := by
          exact mul_le_mul_right (lintegral_mono fun p => ENNReal.ofReal_le_ofReal (hpt p)) _
      _ = ∫⁻ p in S, ENNReal.ofReal (2 * (a p * b p)) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun p => ?_
          rw [ENNReal.ofReal_mul zero_le_two]
      _ ≤ ∫⁻ p in S, (ENNReal.ofReal (δ ^ 2) * ENNReal.ofReal (b p ^ 2) +
            ENNReal.ofReal (δ⁻¹ ^ 2) * ENNReal.ofReal (a p ^ 2)) := by
          refine lintegral_mono fun p => ?_
          rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hamgm p)
      _ = ENNReal.ofReal (δ ^ 2) * (∫⁻ p in S, ENNReal.ofReal (b p ^ 2)) +
            ENNReal.ofReal (δ⁻¹ ^ 2) * (∫⁻ p in S, ENNReal.ofReal (a p ^ 2)) := by
          rw [lintegral_add_left hbm, lintegral_const_mul _ hbm', lintegral_const_mul _ ham]
      _ ≤ ENNReal.ofReal (δ ^ 2) * D ^ (2 : ℝ) + ENNReal.ofReal (δ⁻¹ ^ 2) * Vn ^ (2 : ℝ) := by
          gcongr
  have hsq : ENNReal.ofReal (δ ^ 2) * D ^ (2 : ℝ) + ENNReal.ofReal (δ⁻¹ ^ 2) * Vn ^ (2 : ℝ) ≤
      (ENNReal.ofReal δ * D + ENNReal.ofReal δ⁻¹ * Vn) ^ (2 : ℝ) := by
    rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.ofReal_pow hδ.le,
      ENNReal.ofReal_pow (inv_nonneg.mpr hδ.le), add_sq, mul_pow, mul_pow]
    exact add_le_add le_self_add le_rfl
  exact (ENNReal.rpow_le_rpow_iff two_pos).1 (hmain.trans hsq)

end Half

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- **Assembly by a partition of unity, for a family.** If every point has an open neighbourhood
with property `Q`, and on every `Q`-set an estimate `‖ρ F_j‖_{L^p(ν)} ≤ C R_j` holds for `C¹`
cut-offs `ρ` supported in it, with `C` independent of `j`, then `‖F_j‖_{L^p(ν)} ≤ C R_j` on the
compact manifold, `C` independent of `j`. -/
theorem assemble_family [CompactSpace M] [T2Space M] {ν : Measure M} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (Q : Set M → Prop) (hQ : ∀ x₀ : M, ∃ V, IsOpen V ∧ x₀ ∈ V ∧ Q V)
    {J : Type*} (F : J → M → ℝ) (hF : ∀ j, Continuous (F j)) (R : J → ℝ≥0∞)
    (hloc : ∀ V, Q V → ∀ ρ : M → ℝ, IsC1 N ρ → tsupport ρ ⊆ V → (∀ y, |ρ y| ≤ 1) →
      ∃ C : ℝ≥0, ∀ j, eLpNorm (ρ * F j) p ν ≤ C * R j) :
    ∃ C : ℝ≥0, ∀ j, eLpNorm (F j) p ν ≤ C * R j := by
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
  refine ⟨∑ i, C i, fun j => ?_⟩
  have hsum : F j = ∑ i : t, (ρ i : M → ℝ) * F j := by
    funext y
    rw [Finset.sum_apply]
    simp only [Pi.mul_apply]
    rw [← Finset.sum_mul, ← finsum_eq_sum_of_fintype, ρ.sum_eq_one (mem_univ y), one_mul]
  calc eLpNorm (F j) p ν = eLpNorm (∑ i : t, (ρ i : M → ℝ) * F j) p ν := by rw [← hsum]
    _ ≤ ∑ i : t, eLpNorm ((ρ i : M → ℝ) * F j) p ν :=
        eLpNorm_sum_le (fun i _ => ((hρC1 i).continuous.mul (hF j)).aestronglyMeasurable) hp
    _ ≤ ∑ i : t, (C i : ℝ≥0∞) * R j := Finset.sum_le_sum fun i _ => hC i j
    _ = ((∑ i, C i : ℝ≥0) : ℝ≥0∞) * R j := by rw [← Finset.sum_mul]; push_cast; rfl

/-- **The local interpolation trace estimate**: on a good chart neighbourhood `V` on which `σ`
(carried by `∂M`) is bounded by `μH[N-1]` of the chart image, for a `C¹` cut-off `ρ` supported
in `V`, `C¹` functions `u, w` and `δ > 0`,
`‖ρ(u − w)‖_{L²(σ)} ≤ C (δ (‖u‖_{W^{1,2}} + ‖w‖_{W^{1,2}}) + δ⁻¹ ‖u − w‖_{L²(μ)})`, `C`
independent of `δ, u, w`. -/
theorem local_trace_interp (n : ℕ) (hNn : N = n + 1) [CompactSpace M]
    {g : RiemannianMetric N M} {μ : Measure M} {σ : Measure M}
    (hσ0 : σ ((𝓡∂ N).boundary M)ᶜ = 0) {x₀ : M} {V : Set M} {Cμ : ℝ≥0} {Cg : ℝ}
    (hG : GoodChart g μ x₀ V Cμ Cg) {Cσ : ℝ≥0} (hCσ : Cσ ≠ 0)
    (hσV : ∀ A ⊆ V, MeasurableSet A →
      σ A ≤ Cσ * Measure.hausdorffMeasure ((N : ℝ) - 1) (extChartAt (𝓡∂ N) x₀ '' A))
    {ρ : M → ℝ} (hρ : IsC1 N ρ) (hρV : tsupport ρ ⊆ V) (hρ1 : ∀ y, |ρ y| ≤ 1) :
    ∃ C : ℝ≥0, ∀ δ : ℝ, 0 < δ → ∀ u w : M → ℝ, IsC1 N u → IsC1 N w →
      eLpNorm (ρ * (u - w)) 2 σ ≤ C * (ENNReal.ofReal δ * (w12 g μ u + w12 g μ w) +
        ENNReal.ofReal δ⁻¹ * eLpNorm (u - w) 2 μ) := by
  subst hNn
  obtain ⟨c, hc, hcu⟩ := eLpNorm_dChart_mul_le hG hρ hρ1
  obtain ⟨K, hK0, hK⟩ := Half.eLpNorm_hyperplane_le n
  have hd : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
  rw [hd] at hσV
  set φ := extChartAt (𝓡∂ (n + 1)) x₀ with hφ
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
  set c2 : ℝ≥0∞ := (Cμ : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal with hc2
  have hc2t : c2 ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
  set cσ : ℝ≥0∞ := (Cσ : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal with hcσ
  have hcσt : cσ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
  set cK : ℝ≥0∞ := (K : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal with hcK
  have hcKt : cK ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
  set B : ℝ≥0∞ := cσ * cK * c2 * (c + 1) with hB
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hcσt hcKt) hc2t)
    (ENNReal.add_ne_top.mpr ⟨hc, ENNReal.one_ne_top⟩)
  have hρs : tsupport ρ ⊆ (chartAt (EuclideanHalfSpace (n + 1)) x₀).source := hρV.trans hVs
  -- the half-space derivative of a cut-off function read in the chart, by its `W^{1,2}` norm
  have hDb : ∀ u' : M → ℝ, IsC1 (n + 1) u' →
      eLpNorm (fderivWithin ℝ (chartFun (n + 1) x₀ (ρ * u')) (Half.H (n + 1))) 2
        (volume.restrict (Half.H (n + 1))) ≤ c2 * (c * w12 g μ u') := by
    intro u' hu'
    have hf1 : IsC1 (n + 1) (ρ * u') := hρ.mul hu'
    have hfV : tsupport (ρ * u') ⊆ V := (tsupport_mul_subset_left (f := ρ) (g := u')).trans hρV
    have hfs := hfV.trans hVs
    have hvC : ContDiffOn ℝ 1 (chartFun (n + 1) x₀ (ρ * u')) (Half.H (n + 1)) :=
      contDiffOn_chartFun x₀ hf1 hfs
    have hDm : AEStronglyMeasurable (fderivWithin ℝ (chartFun (n + 1) x₀ (ρ * u'))
        (Half.H (n + 1))) (volume.restrict φ.target) :=
      ((hvC.continuousOn_fderivWithin Half.uniqueDiffOn_H le_rfl).mono htH).aestronglyMeasurable
        (measurableSet_target x₀)
    have hT2 := (eLpNorm_chart_comparable μ x₀ hVm hVs hG.Cμ_ne hG.vol hDm 2).2
    have hD0 : ∀ z ∈ Half.H (n + 1), z ∉ φ '' V →
        fderivWithin ℝ (chartFun (n + 1) x₀ (ρ * u')) (Half.H (n + 1)) z = 0 :=
      fun z _ hz => fderivWithin_chartFun_eq_zero x₀ hfs fun h => hz (image_mono hfV h)
    have e6 := eLpNorm_restrict_le_of_vanish volume hφV Half.measurableSet_H hD0 2
    have e7 : eLpNorm (fderivWithin ℝ (chartFun (n + 1) x₀ (ρ * u')) (Half.H (n + 1)) ∘ φ) 2
        (μ.restrict V) = eLpNorm (dChart (n + 1) x₀ (ρ * u')) 2 (μ.restrict V) :=
      eLpNorm_congr_ae ((ae_restrict_mem hVm).mono fun y hy =>
        fderivWithin_chartFun x₀ (hVs hy) (ρ * u'))
    calc _ ≤ eLpNorm (fderivWithin ℝ (chartFun (n + 1) x₀ (ρ * u')) (Half.H (n + 1))) 2
          (volume.restrict (φ '' V)) := e6
      _ ≤ c2 * eLpNorm (fderivWithin ℝ (chartFun (n + 1) x₀ (ρ * u')) (Half.H (n + 1)) ∘ φ) 2
          (μ.restrict V) := hT2
      _ = c2 * eLpNorm (dChart (n + 1) x₀ (ρ * u')) 2 (μ.restrict V) := by rw [e7]
      _ ≤ c2 * (c * w12 g μ u') := by gcongr; exact hcu u' hu'
  refine ⟨B.toNNReal, fun δ hδ u w hu hw => ?_⟩
  rw [ENNReal.coe_toNNReal hBt]
  set f := ρ * (u - w) with hf
  have hf1 : IsC1 (n + 1) f := hρ.mul (hu.sub hw)
  have hfV : tsupport f ⊆ V := (tsupport_mul_subset_left (f := ρ) (g := u - w)).trans hρV
  have hfs : tsupport f ⊆ (chartAt (EuclideanHalfSpace (n + 1)) x₀).source := hfV.trans hVs
  set v := chartFun (n + 1) x₀ f with hv
  have hvC : ContDiffOn ℝ 1 v (Half.H (n + 1)) := contDiffOn_chartFun x₀ hf1 hfs
  have hvc : HasCompactSupport v := hasCompactSupport_chartFun x₀ hfs
  -- step 1: `σ` lives on `∂M`, so only `A` counts
  have hae : ∀ᵐ y ∂σ, y ∈ (𝓡∂ (n + 1)).boundary M := by
    rw [ae_iff]; exact hσ0
  have e1 : eLpNorm f 2 σ = eLpNorm f 2 (σ.restrict A) := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hA]
    refine eLpNorm_congr_ae (hae.mono fun y hy => ?_)
    by_cases hyA : y ∈ A
    · rw [indicator_of_mem hyA]
    · rw [indicator_of_notMem hyA]
      by_cases hyV : y ∈ V
      · exact absurd ⟨hyV, chart_boundary hy (hVs hyV)⟩ hyA
      · exact image_eq_zero_of_notMem_tsupport fun h => hyV (hfV h)
  have e2 : eLpNorm f 2 (σ.restrict A) = eLpNorm (v ∘ φ) 2 (σ.restrict A) := by
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
  have e3 : eLpNorm (v ∘ φ) 2 (σ.restrict A) ≤
      cσ * eLpNorm v 2 ((Measure.hausdorffMeasure (n : ℝ)).restrict P) := by
    rw [← eLpNorm_map_measure hvmap hφA]
    calc eLpNorm v 2 (Measure.map φ (σ.restrict A))
        ≤ eLpNorm v 2 ((Cσ : ℝ≥0∞) • (Measure.hausdorffMeasure (n : ℝ)).restrict (φ '' A)) :=
          eLpNorm_mono_measure _ hmapA
      _ = cσ * eLpNorm v 2 ((Measure.hausdorffMeasure (n : ℝ)).restrict (φ '' A)) := by
          rw [eLpNorm_smul_measure_of_ne_zero (ENNReal.coe_ne_zero.mpr hCσ), smul_eq_mul]
      _ ≤ cσ * eLpNorm v 2 ((Measure.hausdorffMeasure (n : ℝ)).restrict P) := by
          gcongr
          exact image_subset_iff.mpr fun y hy => hy.2
  have e4 := hK 2 v hvP
  -- step 5: the half-space interpolation inequality
  set D := eLpNorm (fderivWithin ℝ v (Half.H (n + 1))) 2 (volume.restrict (Half.H (n + 1)))
    with hD
  set Vn := eLpNorm v 2 (volume.restrict (Half.H (n + 1))) with hVn
  have e5 := Half.trace_interp_halfSpace hvC hvc hδ
  -- step 6: the derivative, split in the chart
  have hsplit : v = chartFun (n + 1) x₀ (ρ * u) - chartFun (n + 1) x₀ (ρ * w) := by
    funext z
    simp only [hv, hf, chartFun, Pi.sub_apply, Pi.mul_apply]
    split_ifs <;> ring
  have hvuC : ContDiffOn ℝ 1 (chartFun (n + 1) x₀ (ρ * u)) (Half.H (n + 1)) :=
    contDiffOn_chartFun x₀ (hρ.mul hu)
      ((tsupport_mul_subset_left (f := ρ) (g := u)).trans hρs)
  have hvwC : ContDiffOn ℝ 1 (chartFun (n + 1) x₀ (ρ * w)) (Half.H (n + 1)) :=
    contDiffOn_chartFun x₀ (hρ.mul hw)
      ((tsupport_mul_subset_left (f := ρ) (g := w)).trans hρs)
  have e6 : D ≤ c2 * (c * w12 g μ u) + c2 * (c * w12 g μ w) := by
    have hDu := hDb u hu
    have hDw := hDb w hw
    have hmu : AEStronglyMeasurable (fderivWithin ℝ (chartFun (n + 1) x₀ (ρ * u))
        (Half.H (n + 1))) (volume.restrict (Half.H (n + 1))) :=
      (hvuC.continuousOn_fderivWithin Half.uniqueDiffOn_H le_rfl).aestronglyMeasurable
        Half.measurableSet_H
    have hmw : AEStronglyMeasurable (fderivWithin ℝ (chartFun (n + 1) x₀ (ρ * w))
        (Half.H (n + 1))) (volume.restrict (Half.H (n + 1))) :=
      (hvwC.continuousOn_fderivWithin Half.uniqueDiffOn_H le_rfl).aestronglyMeasurable
        Half.measurableSet_H
    have heq : fderivWithin ℝ v (Half.H (n + 1)) =ᵐ[volume.restrict (Half.H (n + 1))]
        fderivWithin ℝ (chartFun (n + 1) x₀ (ρ * u)) (Half.H (n + 1)) -
          fderivWithin ℝ (chartFun (n + 1) x₀ (ρ * w)) (Half.H (n + 1)) := by
      refine (ae_restrict_mem Half.measurableSet_H).mono fun z hz => ?_
      rw [hsplit, Pi.sub_apply]
      exact fderivWithin_sub (Half.uniqueDiffOn_H z hz)
        ((hvuC.differentiableOn one_ne_zero) z hz) ((hvwC.differentiableOn one_ne_zero) z hz)
    rw [hD, eLpNorm_congr_ae heq]
    exact (eLpNorm_sub_le hmu hmw one_le_two).trans (add_le_add hDu hDw)
  -- step 7: the function itself
  have e7 : Vn ≤ c2 * eLpNorm (u - w) 2 μ := by
    have hv0 : ∀ z ∈ Half.H (n + 1), z ∉ φ '' V → v z = 0 := fun z _ hz =>
      chartFun_eq_zero x₀ fun h => hz (image_mono hfV h)
    have hvm : AEStronglyMeasurable v (volume.restrict φ.target) :=
      (hvC.continuousOn.mono htH).aestronglyMeasurable (measurableSet_target x₀)
    have hT1 := (eLpNorm_chart_comparable μ x₀ hVm hVs hG.Cμ_ne hG.vol hvm 2).2
    have hcomp : eLpNorm (v ∘ φ) 2 (μ.restrict V) = eLpNorm f 2 (μ.restrict V) := by
      refine eLpNorm_congr_ae ((ae_restrict_mem hVm).mono fun y hy => ?_)
      simp only [Function.comp_apply, hv]
      rw [chartFun_chart (hVs hy)]
    have hfle : eLpNorm f 2 μ ≤ eLpNorm (u - w) 2 μ := by
      refine eLpNorm_mono fun y => ?_
      simp only [hf, Pi.mul_apply, Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hρ1 y)
    calc Vn ≤ eLpNorm v 2 (volume.restrict (φ '' V)) :=
          eLpNorm_restrict_le_of_vanish volume hφV Half.measurableSet_H hv0 2
      _ ≤ c2 * eLpNorm (v ∘ φ) 2 (μ.restrict V) := hT1
      _ = c2 * eLpNorm f 2 (μ.restrict V) := by rw [hcomp]
      _ ≤ c2 * eLpNorm f 2 μ := by gcongr; exact Measure.restrict_le_self
      _ ≤ c2 * eLpNorm (u - w) 2 μ := by gcongr
  have hcK2 : (K : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal = cK := rfl
  calc eLpNorm f 2 σ = eLpNorm (v ∘ φ) 2 (σ.restrict A) := by rw [e1, e2]
    _ ≤ cσ * eLpNorm v 2 ((Measure.hausdorffMeasure (n : ℝ)).restrict P) := e3
    _ ≤ cσ * (cK * eLpNorm (v ∘ Half.ι n) 2 volume) := by gcongr
    _ ≤ cσ * (cK * (ENNReal.ofReal δ * D + ENNReal.ofReal δ⁻¹ * Vn)) := by gcongr
    _ ≤ cσ * (cK * (ENNReal.ofReal δ * (c2 * (c * w12 g μ u) + c2 * (c * w12 g μ w)) +
          ENNReal.ofReal δ⁻¹ * (c2 * eLpNorm (u - w) 2 μ))) := by gcongr
    _ ≤ cσ * (cK * (ENNReal.ofReal δ * (c2 * ((c + 1) * w12 g μ u) + c2 * ((c + 1) * w12 g μ w)) +
          ENNReal.ofReal δ⁻¹ * (c2 * ((c + 1) * eLpNorm (u - w) 2 μ)))) := by
        gcongr
        · exact le_self_add
        · exact le_self_add
        · exact le_mul_of_one_le_left' le_add_self
    _ = B * (ENNReal.ofReal δ * (w12 g μ u + w12 g μ w) +
          ENNReal.ofReal δ⁻¹ * eLpNorm (u - w) 2 μ) := by
        rw [hB]; ring

/-- **The interpolation trace inequality, difference form**, on a compact manifold with
boundary: `‖u − w‖_{L²(σ)} ≤ C (δ (‖u‖_{W^{1,2}} + ‖w‖_{W^{1,2}}) + δ⁻¹ ‖u − w‖_{L²(μ)})` for
`C¹` functions `u, w` and every `δ > 0`, `C` independent of `δ, u, w`. -/
theorem trace_interp_sub [CompactSpace M] [T2Space M] (g : RiemannianMetric N M)
    {μ : Measure M} (hμ : IsLocallyLebesgue N μ) {σ : Measure M} (hσ : IsBoundaryMeasure N σ) :
    ∃ C : ℝ≥0, ∀ δ : ℝ, 0 < δ → ∀ u w : M → ℝ, IsC1 N u → IsC1 N w →
      eLpNorm (u - w) 2 σ ≤ C * (ENNReal.ofReal δ * (w12 g μ u + w12 g μ w) +
        ENNReal.ofReal δ⁻¹ * eLpNorm (u - w) 2 μ) := by
  obtain ⟨n, hn⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_ne_zero (NeZero.ne N)).symm⟩
  obtain ⟨C, hC⟩ := assemble_family (ν := σ) one_le_two
    (fun V => ∃ x₀ Cμ Cg, ∃ Cσ : ℝ≥0, GoodChart g μ x₀ V Cμ Cg ∧ Cσ ≠ 0 ∧ ∀ A ⊆ V,
      MeasurableSet A →
        σ A ≤ Cσ * Measure.hausdorffMeasure ((N : ℝ) - 1) (extChartAt (𝓡∂ N) x₀ '' A))
    (fun x₀ => by
      obtain ⟨V, Cμ, Cg, hx, hG⟩ := exists_goodChart g hμ x₀
      obtain ⟨U, hU, C₀, hC₀⟩ := hσ.2 x₀
      refine ⟨V ∩ interior U, hG.isOpen.inter isOpen_interior,
        ⟨hx, mem_interior_iff_mem_nhds.mpr hU⟩, x₀, Cμ, Cg, max C₀ 1,
        hG.mono (hG.isOpen.inter isOpen_interior) inter_subset_left,
        (lt_of_lt_of_le one_pos (le_max_right _ _)).ne', fun A hA hAm => ?_⟩
      have hA' : A ⊆ U ∩ (chartAt (EuclideanHalfSpace N) x₀).source := fun y hy =>
        ⟨interior_subset (hA hy).2, hG.subset_source (hA hy).1⟩
      have hle : (C₀ : ℝ≥0∞) ≤ (max C₀ 1 : ℝ≥0) := by exact_mod_cast le_max_left _ _
      exact (hC₀ A hA' hAm).trans (mul_le_mul_left hle _))
    (J := {j : ℝ × (M → ℝ) × (M → ℝ) // 0 < j.1 ∧ IsC1 N j.2.1 ∧ IsC1 N j.2.2})
    (fun j => j.1.2.1 - j.1.2.2) (fun j => j.2.2.1.continuous.sub j.2.2.2.continuous)
    (fun j => ENNReal.ofReal j.1.1 * (w12 g μ j.1.2.1 + w12 g μ j.1.2.2) +
      ENNReal.ofReal j.1.1⁻¹ * eLpNorm (j.1.2.1 - j.1.2.2) 2 μ)
    (by
      rintro V ⟨x₀, Cμ, Cg, Cσ, hG, hCσ, hσV⟩ ρ hρ hρV hρ1
      obtain ⟨C, hC⟩ := local_trace_interp n hn hσ.1 hG hCσ hσV hρ hρV hρ1
      exact ⟨C, fun j => hC j.1.1 j.2.1 j.1.2.1 j.1.2.2 j.2.2.1 j.2.2.2⟩)
  exact ⟨C, fun δ hδ u w hu hw => hC ⟨(δ, u, w), hδ, hu, hw⟩⟩

/-- **The interpolation trace inequality** on a compact manifold with boundary:
`‖u‖_{L²(σ)} ≤ C (δ ‖u‖_{W^{1,2}(μ)} + δ⁻¹ ‖u‖_{L²(μ)})` for `u ∈ C¹(M)` and every `δ > 0`, `C`
independent of `δ` and `u`. -/
theorem trace_interp [CompactSpace M] [T2Space M] (g : RiemannianMetric N M)
    {μ : Measure M} (hμ : IsLocallyLebesgue N μ) {σ : Measure M} (hσ : IsBoundaryMeasure N σ) :
    ∃ C : ℝ≥0, ∀ δ : ℝ, 0 < δ → ∀ u : M → ℝ, IsC1 N u →
      eLpNorm u 2 σ ≤ C * (ENNReal.ofReal δ * w12 g μ u + ENNReal.ofReal δ⁻¹ * eLpNorm u 2 μ) := by
  obtain ⟨C, hC⟩ := trace_interp_sub g hμ hσ
  refine ⟨C, fun δ hδ u hu => ?_⟩
  have h0 : w12 g μ (0 : M → ℝ) = 0 := by
    have : gradNorm g (0 : M → ℝ) = 0 := funext fun x => gradNorm_const_zero g x
    rw [w12, this, eLpNorm_zero, add_zero]
  have := hC δ hδ u 0 hu contMDiff_const
  rwa [sub_zero, h0, add_zero] at this

/-- A `C¹` function on a compact manifold with boundary lies in `L²(σ)` of every boundary
measure. -/
theorem memLp_two_of_isC1 [CompactSpace M] [T2Space M] (g : RiemannianMetric N M)
    {μ : Measure M} (hμ : IsLocallyLebesgue N μ) {σ : Measure M} (hσ : IsBoundaryMeasure N σ)
    {u : M → ℝ} (hu : IsC1 N u) : MemLp u 2 σ := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  obtain ⟨C, hC⟩ := trace_interp g hμ hσ
  refine ⟨hu.continuous.aestronglyMeasurable, (hC 1 one_pos u hu).trans_lt ?_⟩
  have h1 : w12 g μ u ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨(eLpNorm_gradNorm_lt_top g hu).ne, (memLp_of_isC1 hu 2).eLpNorm_ne_top⟩
  have h2 : eLpNorm u 2 μ ≠ ⊤ := (memLp_of_isC1 hu 2).eLpNorm_ne_top
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1.lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2.lt_top⟩)

end Mfd

end Yamabe
