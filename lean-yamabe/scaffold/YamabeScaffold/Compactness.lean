import YamabeScaffold.ManifoldTheorems

/-!
# The Poincaré double-integral estimate, and the constancy of energy-free limits on a connected manifold

Labels (NOT marked: see SCOPE):

* `lem:positivity` — `Yamabegap.tex:715` (statement l.715–718, proof l.719–721): the step
  « a subsequence converges [...] to some $u_\infty$ with
  $\|\nabla u_\infty\|_{L^2}\le\liminf\|\nabla u_k\|_{L^2}=0$; since $\Sigma$ is connected,
  $u_\infty\equiv c$ is constant » (l.720), on a compact connected manifold with boundary.

> a subsequence converges in $L^2(\Sigma)$ and weakly in $W^{1,2}(\Sigma)$ to some
> $u_\infty$ with $\|\nabla u_\infty\|_{L^2}\le\liminf\|\nabla u_k\|_{L^2}=0$; since $\Sigma$ is
> connected, $u_\infty\equiv c$ is constant. (l.720)

## What is proved

* `Half.segment_estimate`: `|v(y) - v(x)|² ≤ |y - x|² ∫_0^1 |Dv(x + t(y - x))|² dt` on a convex set
  (fundamental theorem of calculus along the segment and Cauchy–Schwarz on `[0, 1]`);
* `Half.double_integral_le`: the Poincaré double-integral estimate on a convex set `Q` of
  diameter `≤ d`, `∫_Q ∫_Q |v(y) - v(x)|² ≤ 2^{N+1} d² |Q| ∫_Q |Dv|²` (the segment estimate, the
  changes of variables `x ↦ (1 - t)x + ty`, `y ↦ (1 - t)x + ty`, Tonelli);
* `Half.cell_approx` (towards Rellich–Kondrachov): on the half-space, for `v` `C¹` on `ℍ̄` vanishing
  outside a ball of radius `R`, the piecewise-constant function of its averages on the grid cubes
  `Half.cube δ z` of side `δ` (a finite set of cubes depending on `R`, `δ` only) approximates it:
  `‖v − P_δ v‖²_{L²(ℍ̄)} ≤ 2·2^N N δ² ‖Dv‖²_{L²(ℍ̄)}` (Jensen for cell averages,
  `Half.enorm_sub_avg_sq_le`, and the double-integral estimate on each cube);
* `Mfd.const_of_tendsto_of_aestronglyMeasurable`: on a compact **connected** manifold with
  boundary, an `L²(μ)` limit `f` **which is `μ`-a.e. strongly measurable** of `C¹` functions whose
  Dirichlet energy tends to `0` is `μ`-a.e. constant;
* `Mfd.not_const_of_tendsto`: the round-1 statement `Mfd.const_of_tendsto`, which asks
  no measurability of `f`, fails as soon as `M` carries a set `S` with `μ S ≠ 0` all of whose
  measurable subsets are `μ`-null (a Vitali set in a chart is one): `f = 1_S`, `u_k = 0`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ` compact connected Riemannian with boundary | ✓ carried (`CompactSpace`, `T2Space`, `ConnectedSpace`, smooth `g`), as round 1 |
| `u_∞` the weak `W^{1,2}` limit | ⚠ read (OQ-93 (c)) as an `L²` limit of `C¹` functions with energy → 0, **measurable** |

## SCOPE (disclosed)

* Rellich–Kondrachov on `M` is not proved: the Euclidean cell approximation is; what remains is its
  chart-level assembly (cut-offs read in good charts, `Mfd.chartFun`), the finiteness of a
  locally-Lebesgue `μ`, and the total-boundedness wrapper in `Lp ℝ 2 μ`.
* **Finding on the round-1 statement** `Mfd.const_of_tendsto` (`YamabeScaffold.Rellich`): it is
  false as stated, because `eLpNorm` of a non-measurable function is an inner integral; the
  measurability hypothesis is added here, and it costs nothing at l.720: the limit there is
  given by Rellich–Kondrachov in `L²`, hence measurable. The same defect sits in the model Prop
  `MeasuredModel.ConstLimit` for a model reading a manifold; `lem_positivity` applies it only to
  an `L²` limit (`MemLp`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Manifold ContDiff

noncomputable section

namespace Yamabe

namespace Half

variable {N : ℕ}

/-! ## 1. The segment estimate and the Poincaré double-integral estimate -/

/-- **The segment estimate**: on a convex set, `|v(y) - v(x)|² ≤ |y - x|² ∫_0^1 |Dv(γ t)|² dt`,
`γ t = x + t (y - x)`. -/
theorem segment_estimate {Q : Set (EuclideanSpace ℝ (Fin N))} (hQ : Convex ℝ Q)
    {v : EuclideanSpace ℝ (Fin N) → ℝ} {D : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ}
    (hv : ∀ z ∈ Q, HasFDerivWithinAt v (D z) Q z) (hD : ContinuousOn D Q)
    {x y : EuclideanSpace ℝ (Fin N)} (hx : x ∈ Q) (hy : y ∈ Q) :
    ‖v y - v x‖ₑ ^ (2 : ℝ) ≤
      ‖y - x‖ₑ ^ (2 : ℝ) * ∫⁻ t in Icc (0 : ℝ) 1, ‖D (x + t • (y - x))‖ₑ ^ (2 : ℝ) := by
  set γ : ℝ → EuclideanSpace ℝ (Fin N) := fun t => x + t • (y - x) with hγ
  have hγQ : MapsTo γ (Icc 0 1) Q := fun t ht => hQ.add_smul_sub_mem hx hy ht
  have hγc : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hγd : ∀ t, HasDerivAt γ (y - x) t := fun t => by
    have h := ((hasDerivAt_id t).smul_const (y - x)).const_add x
    rw [one_smul] at h
    exact h
  set g' : ℝ → ℝ := fun t => D (γ t) (y - x) with hg'
  have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (v ∘ γ) (g' t) (Icc 0 1) t := fun t ht =>
    (hv (γ t) (hγQ ht)).comp_hasDerivWithinAt t (hγd t).hasDerivWithinAt hγQ
  have hgc : ContinuousOn (v ∘ γ) (Icc 0 1) := fun t ht => (hg t ht).continuousWithinAt
  have hDγ : ContinuousOn (fun t => D (γ t)) (Icc 0 1) := hD.comp hγc.continuousOn hγQ
  have hg'c : ContinuousOn g' (Icc 0 1) := hDγ.clm_apply continuousOn_const
  have hFTC : ∫ t in (0 : ℝ)..1, g' t = (v ∘ γ) 1 - (v ∘ γ) 0 :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hgc
      (fun t ht => ((hg t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)).hasDerivWithinAt)
      (hg'c.intervalIntegrable_of_Icc zero_le_one)
  have h1 : (v ∘ γ) 1 = v y := by simp [hγ]
  have h0 : (v ∘ γ) 0 = v x := by simp [hγ]
  rw [h1, h0, intervalIntegral.integral_of_le zero_le_one] at hFTC
  set a : ℝ → ℝ≥0∞ := fun t => ‖D (γ t)‖ₑ with ha
  have ham : AEMeasurable a (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hDγ.enorm.aestronglyMeasurable measurableSet_Icc).aemeasurable
  have hstep : ‖v y - v x‖ₑ ≤ ‖y - x‖ₑ * ∫⁻ t in Icc (0 : ℝ) 1, a t := by
    rw [← hFTC]
    calc ‖∫ t in Ioc (0 : ℝ) 1, g' t‖ₑ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖g' t‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖g' t‖ₑ := lintegral_mono_set Ioc_subset_Icc_self
      _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖y - x‖ₑ * a t := by
          refine lintegral_mono fun t => ?_
          rw [mul_comm]
          exact ContinuousLinearMap.le_opENorm _ _
      _ = ‖y - x‖ₑ * ∫⁻ t in Icc (0 : ℝ) 1, a t := lintegral_const_mul' _ _ enorm_ne_top
  -- Cauchy–Schwarz on `[0, 1]`
  have hCS : (∫⁻ t in Icc (0 : ℝ) 1, a t) ^ (2 : ℝ) ≤ ∫⁻ t in Icc (0 : ℝ) 1, a t ^ (2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Icc (0 : ℝ) 1))
      Real.HolderConjugate.two_two ham (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply,
      MeasurableSet.univ, univ_inter, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
      ENNReal.one_rpow] at h
    have h' := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
    rwa [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one] at h'
  calc ‖v y - v x‖ₑ ^ (2 : ℝ) ≤ (‖y - x‖ₑ * ∫⁻ t in Icc (0 : ℝ) 1, a t) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow hstep (by norm_num)
    _ = ‖y - x‖ₑ ^ (2 : ℝ) * (∫⁻ t in Icc (0 : ℝ) 1, a t) ^ (2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ ‖y - x‖ₑ ^ (2 : ℝ) * ∫⁻ t in Icc (0 : ℝ) 1, a t ^ (2 : ℝ) := by gcongr

/-- The change of variables `x ↦ r x + b` in a lower Lebesgue integral on `ℝ^N`. -/
lemma lintegral_comp_smul_add (F : EuclideanSpace ℝ (Fin N) → ℝ≥0∞) (hF : Measurable F) {r : ℝ}
    (hr : r ≠ 0) (b : EuclideanSpace ℝ (Fin N)) :
    ∫⁻ x, F (r • x + b) = ENNReal.ofReal |(r ^ N)⁻¹| * ∫⁻ x, F x := by
  have hs : Measurable fun x : EuclideanSpace ℝ (Fin N) => r • x := (continuous_const_smul r).measurable
  have ha : Measurable fun x : EuclideanSpace ℝ (Fin N) => x + b := measurable_add_const b
  have h1 : ∫⁻ x, F (r • x + b) = ∫⁻ x, F (x + b) ∂(Measure.map (fun x => r • x) volume) :=
    (lintegral_map (f := fun x => F (x + b)) (hF.comp ha) hs).symm
  rw [h1, Measure.map_addHaar_smul volume hr, lintegral_smul_measure, finrank_euclideanSpace_fin,
    smul_eq_mul]
  congr 1
  rw [← lintegral_map hF ha, map_add_right_eq_self]

lemma ofReal_inv_pow_le {r : ℝ} (hr : 1 / 2 ≤ r) :
    ENNReal.ofReal |(r ^ N)⁻¹| ≤ 2 ^ N := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have h1 : |(r ^ N)⁻¹| ≤ 2 ^ N := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos hr0 N)), ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr hr0.le)
      (by rw [inv_le_comm₀ hr0 (by norm_num)]; linarith) N
  calc ENNReal.ofReal |(r ^ N)⁻¹| ≤ ENNReal.ofReal (2 ^ N) := ENNReal.ofReal_le_ofReal h1
    _ = 2 ^ N := by rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

/-- **The Poincaré double-integral estimate** on a convex set `Q` of diameter `≤ d`:
`∫_Q ∫_Q |v(y) - v(x)|² ≤ 2 · 2^N d² |Q| ∫_Q |Dv|²`. -/
theorem double_integral_le {Q : Set (EuclideanSpace ℝ (Fin N))} (hQ : Convex ℝ Q)
    (hQm : MeasurableSet Q) {d : ℝ} (hd : ∀ x ∈ Q, ∀ y ∈ Q, ‖y - x‖ ≤ d)
    {v : EuclideanSpace ℝ (Fin N) → ℝ} {D : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ}
    (hv : ∀ z ∈ Q, HasFDerivWithinAt v (D z) Q z) (hD : ContinuousOn D Q) :
    ∫⁻ x in Q, ∫⁻ y in Q, ‖v y - v x‖ₑ ^ (2 : ℝ) ≤
      2 * 2 ^ N * ENNReal.ofReal (d ^ 2) * volume Q * ∫⁻ z in Q, ‖D z‖ₑ ^ (2 : ℝ) := by
  classical
  set G : EuclideanSpace ℝ (Fin N) → ℝ≥0∞ := fun z => ‖(Q.piecewise D 0) z‖ₑ ^ (2 : ℝ) with hG
  have hGm : Measurable G :=
    (hD.measurable_piecewise continuousOn_const hQm).enorm.pow_const _
  have hGQ : ∀ z ∈ Q, G z = ‖D z‖ₑ ^ (2 : ℝ) := fun z hz => by
    simp only [hG, piecewise_eq_of_mem _ _ _ hz]
  have hGI : ∫⁻ z, G z = ∫⁻ z in Q, ‖D z‖ₑ ^ (2 : ℝ) := by
    rw [← lintegral_indicator hQm]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ Q
    · rw [indicator_of_mem hz, hGQ z hz]
    · rw [indicator_of_notMem hz]
      simp only [hG, piecewise_eq_of_notMem _ _ _ hz, Pi.zero_apply]
      rw [enorm_eq_nnnorm, nnnorm_zero, ENNReal.coe_zero]
      exact ENNReal.zero_rpow_of_pos two_pos
  set I := ∫⁻ z, G z with hI
  set ψ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) → ℝ → ℝ≥0∞ :=
    fun x y t => G ((1 - t) • x + t • y) with hψ
  have hψm : Measurable fun q : (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) × ℝ =>
      ψ q.1.1 q.1.2 q.2 := hGm.comp (by fun_prop)
  -- the pointwise bound
  have hpt : ∀ x ∈ Q, ∀ y ∈ Q, ‖v y - v x‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (d ^ 2) * ∫⁻ t in Icc (0 : ℝ) 1, ψ x y t := by
    intro x hx y hy
    have h := segment_estimate hQ hv hD hx hy
    have he : ‖y - x‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (d ^ 2) := by
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) two_pos.le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.rpow_two]
      exact pow_le_pow_left₀ (norm_nonneg _) (hd x hx y hy) 2
    have hseg : ∫⁻ t in Icc (0 : ℝ) 1, ‖D (x + t • (y - x))‖ₑ ^ (2 : ℝ) =
        ∫⁻ t in Icc (0 : ℝ) 1, ψ x y t := by
      refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
      have hxy : (1 - t) • x + t • y = x + t • (y - x) := by
        rw [sub_smul, one_smul, smul_sub]; abel
      simp only [hψ]
      rw [hxy, hGQ _ (hQ.add_smul_sub_mem hx hy ht)]
    calc ‖v y - v x‖ₑ ^ (2 : ℝ)
        ≤ ‖y - x‖ₑ ^ (2 : ℝ) * ∫⁻ t in Icc (0 : ℝ) 1, ‖D (x + t • (y - x))‖ₑ ^ (2 : ℝ) := h
      _ ≤ ENNReal.ofReal (d ^ 2) * ∫⁻ t in Icc (0 : ℝ) 1, ψ x y t := by rw [hseg]; gcongr
  -- the split of `[0, 1]`
  have hsplit : ∀ x y, ∫⁻ t in Icc (0 : ℝ) 1, ψ x y t ≤
      (∫⁻ t in Icc (0 : ℝ) (1 / 2), ψ x y t) + ∫⁻ t in Icc (1 / 2 : ℝ) 1, ψ x y t := by
    intro x y
    rw [← Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    exact lintegral_union_le (μ := volume) (fun t => ψ x y t) (Icc (0 : ℝ) (1 / 2))
      (Icc (1 / 2 : ℝ) 1)
  -- the two changes of variables
  have hcv1 : ∀ y, ∀ t ∈ Icc (0 : ℝ) (1 / 2), ∫⁻ x, ψ x y t ≤ 2 ^ N * I := by
    intro y t ht
    simp only [hψ]
    rw [lintegral_comp_smul_add G hGm (r := 1 - t) (by linarith [ht.2]) (t • y)]
    gcongr
    exact ofReal_inv_pow_le (by linarith [ht.2])
  have hcv2 : ∀ x, ∀ t ∈ Icc (1 / 2 : ℝ) 1, ∫⁻ y, ψ x y t ≤ 2 ^ N * I := by
    intro x t ht
    simp only [hψ]
    have he : ∀ y, (1 - t) • x + t • y = t • y + (1 - t) • x := fun y => add_comm _ _
    simp only [he]
    rw [lintegral_comp_smul_add G hGm (r := t) (by linarith [ht.1]) ((1 - t) • x)]
    gcongr
    exact ofReal_inv_pow_le ht.1
  have hvol : ∀ a b : ℝ, a ≤ b → b - a ≤ 1 → volume (Icc a b) ≤ 1 := fun a b _ h => by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_le_one.mpr h
  -- `T₁`: integrate in `x` first
  have hT1 : ∫⁻ x in Q, ∫⁻ y in Q, ∫⁻ t in Icc (0 : ℝ) (1 / 2), ψ x y t ≤ volume Q * (2 ^ N * I) := by
    rw [lintegral_lintegral_swap ((Measurable.lintegral_prod_right'
      (f := fun q : (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) × ℝ => ψ q.1.1 q.1.2 q.2)
      hψm).aemeasurable)]
    calc ∫⁻ y in Q, ∫⁻ x in Q, ∫⁻ t in Icc (0 : ℝ) (1 / 2), ψ x y t
        = ∫⁻ y in Q, ∫⁻ t in Icc (0 : ℝ) (1 / 2), ∫⁻ x in Q, ψ x y t := by
          refine lintegral_congr fun y => ?_
          exact lintegral_lintegral_swap ((hψm.comp (by fun_prop :
            Measurable fun q : EuclideanSpace ℝ (Fin N) × ℝ => ((q.1, y), q.2))).aemeasurable)
      _ ≤ ∫⁻ y in Q, ∫⁻ t in Icc (0 : ℝ) (1 / 2), 2 ^ N * I := by
          refine lintegral_mono fun y => setLIntegral_mono' measurableSet_Icc fun t ht => ?_
          exact (setLIntegral_le_lintegral _ _).trans (hcv1 y t ht)
      _ ≤ volume Q * (2 ^ N * I) := by
          simp only [lintegral_const, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
          calc 2 ^ N * I * volume (Icc (0 : ℝ) (1 / 2)) * volume Q
              ≤ 2 ^ N * I * 1 * volume Q := by gcongr; exact hvol _ _ (by norm_num) (by norm_num)
            _ = volume Q * (2 ^ N * I) := by ring
  -- `T₂`: integrate in `y` first
  have hT2 : ∫⁻ x in Q, ∫⁻ y in Q, ∫⁻ t in Icc (1 / 2 : ℝ) 1, ψ x y t ≤ volume Q * (2 ^ N * I) := by
    calc ∫⁻ x in Q, ∫⁻ y in Q, ∫⁻ t in Icc (1 / 2 : ℝ) 1, ψ x y t
        = ∫⁻ x in Q, ∫⁻ t in Icc (1 / 2 : ℝ) 1, ∫⁻ y in Q, ψ x y t := by
          refine lintegral_congr fun x => ?_
          exact lintegral_lintegral_swap ((hψm.comp (by fun_prop :
            Measurable fun q : EuclideanSpace ℝ (Fin N) × ℝ => ((x, q.1), q.2))).aemeasurable)
      _ ≤ ∫⁻ x in Q, ∫⁻ t in Icc (1 / 2 : ℝ) 1, 2 ^ N * I := by
          refine lintegral_mono fun x => setLIntegral_mono' measurableSet_Icc fun t ht => ?_
          exact (setLIntegral_le_lintegral _ _).trans (hcv2 x t ht)
      _ ≤ volume Q * (2 ^ N * I) := by
          simp only [lintegral_const, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
          calc 2 ^ N * I * volume (Icc (1 / 2 : ℝ) 1) * volume Q
              ≤ 2 ^ N * I * 1 * volume Q := by gcongr; exact hvol _ _ (by norm_num) (by norm_num)
            _ = volume Q * (2 ^ N * I) := by ring
  have hm1 : ∀ x, Measurable fun y => ∫⁻ t in Icc (0 : ℝ) (1 / 2), ψ x y t := fun x =>
    (Measurable.lintegral_prod_right' (hψm.comp (by fun_prop :
      Measurable fun q : EuclideanSpace ℝ (Fin N) × ℝ => ((x, q.1), q.2))))
  have hm1' : Measurable fun x => ∫⁻ y in Q, ∫⁻ t in Icc (0 : ℝ) (1 / 2), ψ x y t :=
    Measurable.lintegral_prod_right' ((Measurable.lintegral_prod_right'
      (f := fun q : (EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N)) × ℝ => ψ q.1.1 q.1.2 q.2)
      hψm).comp (by fun_prop : Measurable fun q : EuclideanSpace ℝ (Fin N) ×
        EuclideanSpace ℝ (Fin N) => q))
  have hsum : (∫⁻ x in Q, ∫⁻ y in Q,
      ((∫⁻ t in Icc (0 : ℝ) (1 / 2), ψ x y t) + ∫⁻ t in Icc (1 / 2 : ℝ) 1, ψ x y t)) =
      (∫⁻ x in Q, ∫⁻ y in Q, ∫⁻ t in Icc (0 : ℝ) (1 / 2), ψ x y t) +
        ∫⁻ x in Q, ∫⁻ y in Q, ∫⁻ t in Icc (1 / 2 : ℝ) 1, ψ x y t := by
    calc (∫⁻ x in Q, ∫⁻ y in Q,
          ((∫⁻ t in Icc (0 : ℝ) (1 / 2), ψ x y t) + ∫⁻ t in Icc (1 / 2 : ℝ) 1, ψ x y t))
        = ∫⁻ x in Q, ((∫⁻ y in Q, ∫⁻ t in Icc (0 : ℝ) (1 / 2), ψ x y t) +
            ∫⁻ y in Q, ∫⁻ t in Icc (1 / 2 : ℝ) 1, ψ x y t) :=
          lintegral_congr fun x => lintegral_add_left (hm1 x) _
      _ = _ := lintegral_add_left hm1' _
  have hc : ENNReal.ofReal (d ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc ∫⁻ x in Q, ∫⁻ y in Q, ‖v y - v x‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal (d ^ 2) *
          ((∫⁻ t in Icc (0 : ℝ) (1 / 2), ψ x y t) + ∫⁻ t in Icc (1 / 2 : ℝ) 1, ψ x y t) := by
        refine setLIntegral_mono' hQm fun x hx => setLIntegral_mono' hQm fun y hy => ?_
        exact (hpt x hx y hy).trans (mul_le_mul' le_rfl (hsplit x y))
    _ = ENNReal.ofReal (d ^ 2) * ∫⁻ x in Q, ∫⁻ y in Q,
          ((∫⁻ t in Icc (0 : ℝ) (1 / 2), ψ x y t) + ∫⁻ t in Icc (1 / 2 : ℝ) 1, ψ x y t) := by
        rw [← lintegral_const_mul' _ _ hc]
        exact lintegral_congr fun x => lintegral_const_mul' _ _ hc
    _ = ENNReal.ofReal (d ^ 2) * ((∫⁻ x in Q, ∫⁻ y in Q, ∫⁻ t in Icc (0 : ℝ) (1 / 2), ψ x y t) +
          ∫⁻ x in Q, ∫⁻ y in Q, ∫⁻ t in Icc (1 / 2 : ℝ) 1, ψ x y t) := by rw [hsum]
    _ ≤ ENNReal.ofReal (d ^ 2) * (volume Q * (2 ^ N * I) + volume Q * (2 ^ N * I)) := by
        gcongr
    _ = 2 * 2 ^ N * ENNReal.ofReal (d ^ 2) * volume Q * ∫⁻ z in Q, ‖D z‖ₑ ^ (2 : ℝ) := by
        rw [← hGI]; ring

/-! ## 4. Grid cubes and the cell approximation on the half-space -/

/-- The half-open grid cube `∏_j [δ z_j, δ (z_j + 1))`. -/
def cube (δ : ℝ) (z : Fin N → ℤ) : Set (EuclideanSpace ℝ (Fin N)) :=
  {y | ∀ j, δ * z j ≤ y j ∧ y j < δ * (z j + 1)}

lemma cube_eq (δ : ℝ) (z : Fin N → ℤ) :
    cube δ z = WithLp.ofLp ⁻¹' (Set.pi univ fun j => Ico (δ * z j) (δ * (z j + 1))) := by
  ext y
  simp [cube, Set.mem_pi]

lemma measurableSet_cube (δ : ℝ) (z : Fin N → ℤ) : MeasurableSet (cube δ z) := by
  rw [cube_eq]
  exact (PiLp.continuous_ofLp 2 _).measurable (MeasurableSet.univ_pi fun j => measurableSet_Ico)

lemma volume_cube (δ : ℝ) (z : Fin N → ℤ) :
    volume (cube δ z) = ENNReal.ofReal δ ^ N := by
  rw [cube_eq, (PiLp.volume_preserving_ofLp (Fin N)).measure_preimage
    (MeasurableSet.univ_pi fun j => measurableSet_Ico).nullMeasurableSet, volume_pi_pi]
  simp only [Real.volume_Ico]
  rw [Finset.prod_congr rfl (fun j _ => by rw [show δ * (z j + 1) - δ * z j = δ by ring]),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma convex_cube (δ : ℝ) (z : Fin N → ℤ) : Convex ℝ (cube δ z) := by
  intro x hx y hy a b ha hb hab j
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain ⟨hx1, hx2⟩ := hx j
  obtain ⟨hy1, hy2⟩ := hy j
  have hb' : b = 1 - a := by linarith
  subst hb'
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hx1 ha, mul_le_mul_of_nonneg_left hy1 hb]
  · rcases ha.lt_or_eq with ha' | ha'
    · nlinarith [mul_lt_mul_of_pos_left hx2 ha', mul_le_mul_of_nonneg_left hy2.le hb]
    · subst ha'; simpa using hy2

lemma norm_sub_le_of_mem_cube {δ : ℝ} (hδ : 0 ≤ δ) {z : Fin N → ℤ} {x y : EuclideanSpace ℝ (Fin N)}
    (hx : x ∈ cube δ z) (hy : y ∈ cube δ z) : ‖y - x‖ ≤ Real.sqrt N * δ := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hδ, ← Real.sqrt_mul (Nat.cast_nonneg N)]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ j, ‖(y - x) j‖ ^ 2 ≤ ∑ _j : Fin N, δ ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        obtain ⟨hx1, hx2⟩ := hx j
        obtain ⟨hy1, hy2⟩ := hy j
        rw [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
        nlinarith
    _ = N * δ ^ 2 := by simp

lemma cube_subset_H {δ : ℝ} (hδ : 0 ≤ δ) [NeZero N] {z : Fin N → ℤ} (hz : 0 ≤ z 0) :
    cube δ z ⊆ H N := fun y hy => by
  show (0 : ℝ) ≤ y 0
  have := (hy 0).1
  have h0 : (0 : ℝ) ≤ δ * z 0 := mul_nonneg hδ (by exact_mod_cast hz)
  linarith

lemma mem_cube_floor {δ : ℝ} (hδ : 0 < δ) (y : EuclideanSpace ℝ (Fin N)) :
    y ∈ cube δ (fun j => ⌊y j / δ⌋) := by
  intro j
  constructor
  · have := Int.floor_le (y j / δ)
    rw [le_div_iff₀ hδ] at this
    linarith
  · have := Int.lt_floor_add_one (y j / δ)
    rw [div_lt_iff₀ hδ] at this
    linarith

lemma eq_of_mem_cube {δ : ℝ} (hδ : 0 < δ) {z z' : Fin N → ℤ} {y : EuclideanSpace ℝ (Fin N)}
    (hz : y ∈ cube δ z) (hz' : y ∈ cube δ z') : z = z' := by
  funext j
  have h1 : ⌊y j / δ⌋ = z j := by
    rw [Int.floor_eq_iff]
    obtain ⟨a, b⟩ := hz j
    constructor
    · rw [le_div_iff₀ hδ]; linarith
    · rw [div_lt_iff₀ hδ]; linarith
  have h2 : ⌊y j / δ⌋ = z' j := by
    rw [Int.floor_eq_iff]
    obtain ⟨a, b⟩ := hz' j
    constructor
    · rw [le_div_iff₀ hδ]; linarith
    · rw [div_lt_iff₀ hδ]; linarith
  rw [← h1, ← h2]

lemma pairwiseDisjoint_cube {δ : ℝ} (hδ : 0 < δ) (s : Set (Fin N → ℤ)) :
    s.PairwiseDisjoint (cube δ) := fun _ _ _ _ hzz' =>
  Set.disjoint_left.mpr fun _ hy hy' => hzz' (eq_of_mem_cube hδ hy hy')

/-- **Jensen for a cell average**: `|v(x) − avg_C v|² ≤ |C|⁻¹ ∫_C |v(x) − v(y)|² dy`. -/
lemma enorm_sub_avg_sq_le {C : Set (EuclideanSpace ℝ (Fin N))} (hC0 : volume C ≠ 0)
    (hCt : volume C ≠ ⊤) {v : EuclideanSpace ℝ (Fin N) → ℝ} (hv : IntegrableOn v C)
    (x : EuclideanSpace ℝ (Fin N)) :
    ‖v x - (volume.real C)⁻¹ * ∫ y in C, v y‖ₑ ^ (2 : ℝ) ≤
      (volume C)⁻¹ * ∫⁻ y in C, ‖v x - v y‖ₑ ^ (2 : ℝ) := by
  haveI : IsFiniteMeasure (volume.restrict C) := ⟨by rw [Measure.restrict_apply_univ]; exact hCt.lt_top⟩
  set c := volume.real C with hc
  have hcpos : 0 < c := ENNReal.toReal_pos hC0 hCt
  have heq : v x - c⁻¹ * ∫ y in C, v y = c⁻¹ * ∫ y in C, (v x - v y) := by
    rw [integral_sub (integrable_const _) hv, setIntegral_const, smul_eq_mul, ← hc]
    field_simp
  set A := ∫⁻ y in C, ‖v x - v y‖ₑ ^ (2 : ℝ) with hA
  have hm : AEMeasurable (fun y => ‖v x - v y‖ₑ) (volume.restrict C) :=
    (aestronglyMeasurable_const.sub hv.1).enorm
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict C) Real.HolderConjugate.two_two
    hm (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ, one_mul] at hH
  have hcinv : ENNReal.ofReal c⁻¹ = (volume C)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hcpos, hc, Measure.real, ENNReal.ofReal_toReal hCt]
  have h1 : ‖v x - c⁻¹ * ∫ y in C, v y‖ₑ ≤
      (volume C)⁻¹ * (A ^ (1 / (2 : ℝ)) * volume C ^ (1 / (2 : ℝ))) := by
    rw [heq, enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hcpos), hcinv]
    gcongr
    exact (enorm_integral_le_lintegral_enorm _).trans hH
  calc ‖v x - c⁻¹ * ∫ y in C, v y‖ₑ ^ (2 : ℝ)
      ≤ ((volume C)⁻¹ * (A ^ (1 / (2 : ℝ)) * volume C ^ (1 / (2 : ℝ)))) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow h1 (by norm_num)
    _ = (volume C)⁻¹ ^ (2 : ℝ) * (A * volume C) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num
    _ = (volume C)⁻¹ * A := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast, pow_two, mul_comm A,
          ← mul_assoc, mul_assoc _ _ (volume C), ENNReal.inv_mul_cancel hC0 hCt, mul_one]

/-- The average of `v` on the cube `C_z`. -/
def avg (δ : ℝ) (z : Fin N → ℤ) (v : EuclideanSpace ℝ (Fin N) → ℝ) : ℝ :=
  (volume.real (cube δ z))⁻¹ * ∫ y in cube δ z, v y

/-- **The cell approximation on the half-space**: for `v` `C¹` on `ℍ̄` and vanishing outside
the ball of radius `R`, the piecewise-constant function of its averages on the grid cubes of side
`δ` approximates it in `L²(ℍ̄)` with error `≤ 2·2^N N δ² ‖Dv‖²_{L²(ℍ̄)}`, the finite set of cubes
depending on `R` and `δ` only. -/
theorem cell_approx [NeZero N] (R : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Z : Finset (Fin N → ℤ), (∀ z ∈ Z, 0 ≤ z 0) ∧ ∀ v : EuclideanSpace ℝ (Fin N) → ℝ,
      ContDiffOn ℝ 1 v (H N) → (∀ y, R < ‖y‖ → v y = 0) →
      ∫⁻ y in H N, ‖v y - ∑ z ∈ Z, (cube δ z).indicator (fun _ => avg δ z v) y‖ₑ ^ (2 : ℝ) ≤
        2 * 2 ^ N * ENNReal.ofReal (N * δ ^ 2) *
          ∫⁻ y in H N, ‖fderivWithin ℝ v (H N) y‖ₑ ^ (2 : ℝ) := by
  classical
  set L : ℤ := ⌈R / δ⌉ + 1 with hL
  set Z := (Fintype.piFinset fun _ : Fin N => Finset.Icc (-L) L).filter (fun z => 0 ≤ z 0) with hZ
  refine ⟨Z, fun z hz => (Finset.mem_filter.mp hz).2, fun v hv hR => ?_⟩
  set U := ⋃ z ∈ Z, cube δ z with hU
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion _ fun z _ => measurableSet_cube δ z
  have hUH : U ⊆ H N := iUnion₂_subset fun z hz => cube_subset_H hδ.le (Finset.mem_filter.mp hz).2
  have hcover : ∀ y ∈ H N, ‖y‖ ≤ R → y ∈ U := by
    intro y hyH hyR
    refine mem_iUnion₂.mpr ⟨fun j => ⌊y j / δ⌋, ?_, mem_cube_floor hδ y⟩
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun j => ?_, ?_⟩
    · have hj : |y j| ≤ R := by
        have := PiLp.norm_apply_le y j
        rw [Real.norm_eq_abs] at this
        linarith
      have h1 : y j / δ ≤ R / δ := div_le_div_of_nonneg_right (le_abs_self _ |>.trans hj) hδ.le
      have h2 : -(R / δ) ≤ y j / δ := by
        rw [← neg_div]; exact div_le_div_of_nonneg_right (by linarith [neg_abs_le (y j)]) hδ.le
      rw [Finset.mem_Icc]
      constructor
      · have := Int.lt_floor_add_one (y j / δ)
        have h3 := Int.le_ceil (R / δ)
        have h4 : (-(L : ℝ)) < ⌊y j / δ⌋ + 1 := by push_cast [hL]; linarith
        have h5 : -L < ⌊y j / δ⌋ + 1 := by exact_mod_cast h4
        omega
      · have h3 : ⌊y j / δ⌋ ≤ ⌈R / δ⌉ := (Int.floor_mono h1).trans (Int.floor_le_ceil _)
        omega
    · exact Int.floor_nonneg.mpr (div_nonneg hyH hδ.le)
  -- `v` is bounded on `ℍ̄`
  have hvc : ContinuousOn v (H N) := hv.continuousOn
  obtain ⟨B, hB⟩ := (((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin N)) R).inter_right
    isClosed_H)).exists_bound_of_continuousOn (hvc.mono inter_subset_right)
  have hbound : ∀ y ∈ H N, ‖v y‖ ≤ max B 0 := by
    intro y hy
    by_cases hyR : ‖y‖ ≤ R
    · exact (hB y ⟨mem_closedBall_zero_iff.mpr hyR, hy⟩).trans (le_max_left _ _)
    · rw [hR y (not_le.mp hyR), norm_zero]; exact le_max_right _ _
  have hint : ∀ z ∈ Z, IntegrableOn v (cube δ z) := fun z hz => by
    have hzH := cube_subset_H hδ.le (Finset.mem_filter.mp hz).2
    refine IntegrableOn.of_bound (by rw [volume_cube]; exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
      ((hvc.mono hzH).aestronglyMeasurable (measurableSet_cube δ z)) (max B 0)
      ((ae_restrict_mem (measurableSet_cube δ z)).mono fun y hy => hbound y (hzH hy))
  set F : EuclideanSpace ℝ (Fin N) → ℝ≥0∞ := fun y =>
    ‖v y - ∑ z ∈ Z, (cube δ z).indicator (fun _ => avg δ z v) y‖ₑ ^ (2 : ℝ) with hF
  set G : EuclideanSpace ℝ (Fin N) → ℝ≥0∞ := fun y => ‖fderivWithin ℝ v (H N) y‖ₑ ^ (2 : ℝ)
    with hG
  set c : ℝ≥0∞ := 2 * 2 ^ N * ENNReal.ofReal (N * δ ^ 2) with hc
  -- on a cube of `Z`, the sum is the cube's average
  have hsum : ∀ z ∈ Z, ∀ y ∈ cube δ z,
      ∑ z' ∈ Z, (cube δ z').indicator (fun _ => avg δ z' v) y = avg δ z v := by
    intro z hz y hy
    rw [Finset.sum_eq_single z (fun z' _ hz' => indicator_of_notMem
      (fun hy' => hz' (eq_of_mem_cube hδ hy' hy)) _) (fun h => absurd hz h),
      indicator_of_mem hy]
  -- off `U` in `ℍ̄`, the integrand vanishes
  have hoff : ∀ y ∈ H N \ U, F y = 0 := by
    intro y ⟨hyH, hyU⟩
    have hyR : R < ‖y‖ := not_le.mp fun h => hyU (hcover y hyH h)
    have h0 : ∑ z ∈ Z, (cube δ z).indicator (fun _ => avg δ z v) y = 0 :=
      Finset.sum_eq_zero fun z hz => indicator_of_notMem (fun hy => hyU (mem_iUnion₂.mpr ⟨z, hz, hy⟩)) _
    simp only [hF, h0, hR y hyR, sub_zero, enorm_zero]
    exact ENNReal.zero_rpow_of_pos two_pos
  -- the estimate on one cube
  have hcube : ∀ z ∈ Z, ∫⁻ y in cube δ z, F y ≤ c * ∫⁻ y in cube δ z, G y := by
    intro z hz
    have hzH := cube_subset_H hδ.le (Finset.mem_filter.mp hz).2
    have hC0 : volume (cube δ z) ≠ 0 := by
      rw [volume_cube]; exact pow_ne_zero _ (ENNReal.ofReal_pos.mpr hδ).ne'
    have hCt : volume (cube δ z) ≠ ⊤ := by
      rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hdiff : DifferentiableOn ℝ v (H N) := hv.differentiableOn one_ne_zero
    have hDQ : ∀ w ∈ cube δ z, HasFDerivWithinAt v (fderivWithin ℝ v (H N) w) (cube δ z) w :=
      fun w hw => ((hdiff w (hzH hw)).hasFDerivWithinAt).mono hzH
    have hDc : ContinuousOn (fderivWithin ℝ v (H N)) (cube δ z) :=
      (hv.continuousOn_fderivWithin uniqueDiffOn_H le_rfl).mono hzH
    have hd : ∀ x ∈ cube δ z, ∀ y ∈ cube δ z, ‖y - x‖ ≤ Real.sqrt N * δ := fun x hx y hy =>
      norm_sub_le_of_mem_cube hδ.le hx hy
    have hdouble := double_integral_le (convex_cube δ z) (measurableSet_cube δ z) hd hDQ hDc
    have hd2 : (Real.sqrt N * δ) ^ 2 = N * δ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    rw [hd2] at hdouble
    calc ∫⁻ y in cube δ z, F y
        = ∫⁻ y in cube δ z, ‖v y - avg δ z v‖ₑ ^ (2 : ℝ) :=
          setLIntegral_congr_fun (measurableSet_cube δ z) fun y hy => by
            simp only [hF]; rw [hsum z hz y hy]
      _ ≤ ∫⁻ y in cube δ z, (volume (cube δ z))⁻¹ *
            ∫⁻ y' in cube δ z, ‖v y - v y'‖ₑ ^ (2 : ℝ) :=
          lintegral_mono fun y => enorm_sub_avg_sq_le hC0 hCt (hint z hz) y
      _ = (volume (cube δ z))⁻¹ * ∫⁻ y in cube δ z, ∫⁻ y' in cube δ z, ‖v y' - v y‖ₑ ^ (2 : ℝ) := by
          rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hC0)]
          congr 1
          refine lintegral_congr fun y => lintegral_congr fun y' => ?_
          rw [enorm_sub_rev]
      _ ≤ (volume (cube δ z))⁻¹ * (c * volume (cube δ z) * ∫⁻ w in cube δ z, G w) := by
          gcongr
      _ = c * ∫⁻ w in cube δ z, G w := by
          rw [show c * volume (cube δ z) * ∫⁻ w in cube δ z, G w =
            volume (cube δ z) * (c * ∫⁻ w in cube δ z, G w) by ring, ← mul_assoc,
            ENNReal.inv_mul_cancel hC0 hCt, one_mul]
  have hdisj := pairwiseDisjoint_cube hδ (Z : Set (Fin N → ℤ))
  calc ∫⁻ y in H N, F y ≤ ∫⁻ y in U ∪ (H N \ U), F y :=
        lintegral_mono_set (fun y hy => by by_cases h : y ∈ U <;> simp [h, hy])
    _ ≤ (∫⁻ y in U, F y) + ∫⁻ y in H N \ U, F y := lintegral_union_le (μ := volume) _ _ _
    _ = ∫⁻ y in U, F y := by
        rw [setLIntegral_congr_fun (measurableSet_H.diff hUm) hoff]
        simp
    _ = ∑ z ∈ Z, ∫⁻ y in cube δ z, F y :=
        lintegral_biUnion_finset hdisj (fun z _ => measurableSet_cube δ z) F
    _ ≤ ∑ z ∈ Z, c * ∫⁻ y in cube δ z, G y := Finset.sum_le_sum hcube
    _ = c * ∫⁻ y in U, G y := by
        rw [← Finset.mul_sum, lintegral_biUnion_finset hdisj (fun z _ => measurableSet_cube δ z) G]
    _ ≤ c * ∫⁻ y in H N, G y := by gcongr

end Half

namespace Half

variable {N : ℕ} [NeZero N]

lemma convex_H : Convex ℝ (H N) := by
  intro x hx y hy a b ha hb _
  show (0 : ℝ) ≤ (a • x + b • y) 0
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

end Half

/-! ## 2. Helpers on `L²` norms -/

lemma lintegral_enorm_rpow_two_eq {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {G : Type*} [NormedAddCommGroup G] (F : α → G) :
    ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) ∂ν = eLpNorm F 2 ν ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, ← ENNReal.rpow_mul]
  norm_num

/-- `‖g ∘ snd‖_{L²(ν₁ ⊗ ν₂)} = ν₁(univ)^{1/2} ‖g‖_{L²(ν₂)}`. -/
lemma eLpNorm_comp_snd {α : Type*} [MeasurableSpace α] (ν₁ ν₂ : Measure α) [SFinite ν₂]
    {g : α → ℝ} (hg : AEStronglyMeasurable g ν₂) :
    eLpNorm (fun z : α × α => g z.2) 2 (ν₁.prod ν₂) = ν₁ univ ^ (1 / 2 : ℝ) * eLpNorm g 2 ν₂ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  have h : ∫⁻ z : α × α, ‖g z.2‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(ν₁.prod ν₂) =
      ν₁ univ * ∫⁻ y, ‖g y‖ₑ ^ (2 : ℝ≥0∞).toReal ∂ν₂ := by
    have := lintegral_prod_mul (μ := ν₁) (ν := ν₂) (f := fun _ => (1 : ℝ≥0∞))
      (g := fun y => ‖g y‖ₑ ^ (2 : ℝ≥0∞).toReal) aemeasurable_const
      (hg.enorm.pow_const _)
    simpa using this
  rw [h, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  norm_num

/-- `‖g ∘ fst‖_{L²(ν₁ ⊗ ν₂)} = ν₂(univ)^{1/2} ‖g‖_{L²(ν₁)}`. -/
lemma eLpNorm_comp_fst {α : Type*} [MeasurableSpace α] (ν₁ ν₂ : Measure α) [SFinite ν₂]
    {g : α → ℝ} (hg : AEStronglyMeasurable g ν₁) :
    eLpNorm (fun z : α × α => g z.1) 2 (ν₁.prod ν₂) = ν₂ univ ^ (1 / 2 : ℝ) * eLpNorm g 2 ν₁ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  have h : ∫⁻ z : α × α, ‖g z.1‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(ν₁.prod ν₂) =
      (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂ν₁) * ν₂ univ := by
    have := lintegral_prod_mul (μ := ν₁) (ν := ν₂) (f := fun x => ‖g x‖ₑ ^ (2 : ℝ≥0∞).toReal)
      (g := fun _ => (1 : ℝ≥0∞)) (hg.enorm.pow_const _) aemeasurable_const
    simpa using this
  rw [h, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), mul_comm]
  norm_num

/-! ## 3. On the manifold: chart images, local constancy -/

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M]

omit [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M] in
/-- The chart image of an open subset of the chart's source is a neighbourhood of each of its
points within the half-space: it contains `ball(φ y, ε) ∩ ℍ̄`. -/
lemma exists_ball_inter_H_subset {x₀ : M} {V : Set M} (hVo : IsOpen V)
    (hVs : V ⊆ (chartAt (EuclideanHalfSpace N) x₀).source) {y : M} (hy : y ∈ V) :
    ∃ ε > 0, Metric.ball (extChartAt (𝓡∂ N) x₀ y) ε ∩ Half.H N ⊆ extChartAt (𝓡∂ N) x₀ '' V := by
  have hys : y ∈ (extChartAt (𝓡∂ N) x₀).source := by rw [extChartAt_source]; exact hVs hy
  have h1 := extChartAt_preimage_mem_nhdsWithin' (I := 𝓡∂ N) (s := univ) hys
    (nhdsWithin_le_nhds (hVo.mem_nhds hy))
  rw [preimage_univ, univ_inter] at h1
  have h2 := extChartAt_target_mem_nhdsWithin_of_mem (I := 𝓡∂ N) (x := x₀)
    ((extChartAt (𝓡∂ N) x₀).map_source hys)
  have h3 : extChartAt (𝓡∂ N) x₀ '' V ∈ 𝓝[range (𝓡∂ N)] (extChartAt (𝓡∂ N) x₀ y) := by
    refine Filter.mem_of_superset (Filter.inter_mem h2 h1) fun z hz => ?_
    exact ⟨(extChartAt (𝓡∂ N) x₀).symm z, hz.2, (extChartAt (𝓡∂ N) x₀).right_inv hz.1⟩
  rw [← Half.H_eq] at h3
  exact Metric.mem_nhdsWithin_iff.mp h3

/-- **A locally-Lebesgue measure charges every nonempty open set.** -/
theorem measure_pos_of_isOpen (g : RiemannianMetric N M) {μ : Measure M}
    (hμ : IsLocallyLebesgue N μ) {O : Set M} (hO : IsOpen O) (hne : O.Nonempty) : 0 < μ O := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨V, Cμ, Cg, hyV, hG⟩ := exists_goodChart g hμ y
  set O' := O ∩ V
  have hO'o : IsOpen O' := hO.inter hG.isOpen
  have hO's : O' ⊆ (chartAt (EuclideanHalfSpace N) y).source := inter_subset_right.trans hG.subset_source
  obtain ⟨ε, hε, hball⟩ := exists_ball_inter_H_subset hO'o hO's ⟨hy, hyV⟩
  set p := extChartAt (𝓡∂ N) y y
  set q : EuclideanSpace ℝ (Fin N) := p + (ε / 2) • EuclideanSpace.single (0 : Fin N) (1 : ℝ)
  have hp0 : 0 ≤ p 0 := (image_chart_subset_H y (subset_refl _)) ⟨y, mem_chart_source _ y, rfl⟩
  have hsub : Metric.ball q (ε / 4) ⊆ extChartAt (𝓡∂ N) y '' O' := by
    intro z hz
    refine hball ⟨?_, ?_⟩
    · rw [Metric.mem_ball] at hz ⊢
      have hq : dist q p = ε / 2 := by
        rw [dist_eq_norm, show q - p = (ε / 2) • EuclideanSpace.single (0 : Fin N) (1 : ℝ) by
          simp [q], norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
          abs_of_pos (half_pos hε)]
      linarith [dist_triangle z q p]
    · show (0 : ℝ) ≤ z 0
      have h1 : |z 0 - q 0| ≤ ‖z - q‖ := by
        have := PiLp.norm_apply_le (z - q) 0
        rwa [Real.norm_eq_abs, PiLp.sub_apply] at this
      have h2 : q 0 = p 0 + ε / 2 := by simp [q]
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have := (abs_le.mp h1).1
      linarith
  have hvol : 0 < volume (extChartAt (𝓡∂ N) y '' O') :=
    lt_of_lt_of_le (Metric.measure_ball_pos volume q (by positivity)) (measure_mono hsub)
  have h := (hG.vol O' inter_subset_right hO'o.measurableSet).2
  have hμ' : 0 < μ O' := by
    by_contra h0
    rw [not_lt, nonpos_iff_eq_zero] at h0
    rw [h0, mul_zero] at h
    exact hvol.ne' (le_antisymm h bot_le)
  exact lt_of_lt_of_le hμ' (measure_mono inter_subset_left)

/-- On a good chart neighbourhood, `‖D(u ∘ φ⁻¹) ∘ φ‖_{L²(μ|V)} ≤ Cg ‖∇u‖_{L²(μ)}`. -/
lemma eLpNorm_dChart_le {g : RiemannianMetric N M} {μ : Measure M} {x₀ : M} {V : Set M}
    {Cμ : ℝ≥0} {Cg : ℝ} (hG : GoodChart g μ x₀ V Cμ Cg) {u : M → ℝ} (hu : IsC1 N u) :
    eLpNorm (dChart N x₀ u) 2 (μ.restrict V) ≤ ENNReal.ofReal Cg * eLpNorm (gradNorm g u) 2 μ := by
  have hVm : MeasurableSet V := hG.isOpen.measurableSet
  have hCg := hG.Cg_pos
  calc eLpNorm (dChart N x₀ u) 2 (μ.restrict V)
      ≤ eLpNorm (Cg • gradNorm g u : M → ℝ) 2 (μ.restrict V) := by
        refine eLpNorm_mono_ae ((ae_restrict_mem hVm).mono fun y hy => ?_)
        rw [Pi.smul_apply, smul_eq_mul,
          Real.norm_of_nonneg (mul_nonneg hCg.le (gradNorm_nonneg g u y))]
        exact (hG.grad y hy u (hu.mdifferentiableAt one_ne_zero)).2
    _ = ENNReal.ofReal Cg * eLpNorm (gradNorm g u) 2 (μ.restrict V) := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_pos hCg]
    _ ≤ ENNReal.ofReal Cg * eLpNorm (gradNorm g u) 2 μ := by
        gcongr; exact Measure.restrict_le_self

/-- **Local constancy.** Every point `x₀` of a good chart neighbourhood has an open neighbourhood
`W` on which every `μ`-measurable `L²(μ)` limit of `C¹` functions whose Dirichlet energy tends to
`0` is `μ`-a.e. constant: the Poincaré double-integral estimate on `ball(φ x₀, ε/2) ∩ ℍ̄`, read
through the chart, and the passage to the limit in `L²(μ|_A ⊗ μ|_A)`. -/
theorem local_const {g : RiemannianMetric N M} {μ : Measure M} {x₀ : M} {V : Set M} {Cμ : ℝ≥0}
    {Cg : ℝ} (hG : GoodChart g μ x₀ V Cμ Cg) (hx₀ : x₀ ∈ V) :
    ∃ W : Set M, IsOpen W ∧ x₀ ∈ W ∧ ∀ (u : ℕ → M → ℝ), (∀ k, IsC1 N (u k)) →
      ∀ f : M → ℝ, AEStronglyMeasurable f μ →
      Tendsto (fun k => eLpNorm (gradNorm g (u k)) 2 μ) atTop (𝓝 0) →
      Tendsto (fun k => eLpNorm (u k - f) 2 μ) atTop (𝓝 0) →
        ∃ c : ℝ, f =ᵐ[μ.restrict W] fun _ => c := by
  classical
  set φ := extChartAt (𝓡∂ N) x₀ with hφ
  have hVs := hG.subset_source
  have hVm : MeasurableSet V := hG.isOpen.measurableSet
  obtain ⟨ε, hε, hball⟩ := exists_ball_inter_H_subset hG.isOpen hVs hx₀
  set p := φ x₀ with hp
  set Q : Set (EuclideanSpace ℝ (Fin N)) := Metric.closedBall p (ε / 2) ∩ Half.H N with hQdef
  have hQc : Convex ℝ Q := (convex_closedBall p _).inter Half.convex_H
  have hQm : MeasurableSet Q := Metric.isClosed_closedBall.measurableSet.inter Half.measurableSet_H
  have hQd : ∀ x ∈ Q, ∀ y ∈ Q, ‖y - x‖ ≤ ε := by
    intro x hx y hy
    have h1 := Metric.mem_closedBall.mp hx.1
    have h2 := Metric.mem_closedBall.mp hy.1
    rw [← dist_eq_norm]
    linarith [dist_triangle y p x, dist_comm x p]
  have hQV : Q ⊆ φ '' V := fun z hz =>
    hball ⟨Metric.closedBall_subset_ball (half_lt_self hε) hz.1, hz.2⟩
  have hQt : Q ⊆ φ.target := hQV.trans (image_chart_subset_target x₀ hVs)
  have hQr : Q ⊆ range (𝓡∂ N) := fun z hz => by rw [← Half.H_eq]; exact hz.2
  have hQvol : volume Q ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono inter_subset_left) measure_closedBall_lt_top).ne
  set W := (chartAt (EuclideanHalfSpace N) x₀).source ∩ φ ⁻¹' Metric.ball p (ε / 2) with hWdef
  have hWo : IsOpen W := by
    have hc : ContinuousOn φ (chartAt (EuclideanHalfSpace N) x₀).source := by
      rw [← extChartAt_source (I := 𝓡∂ N)]; exact continuousOn_extChartAt x₀
    exact hc.isOpen_inter_preimage (chartAt (EuclideanHalfSpace N) x₀).open_source
      Metric.isOpen_ball
  have hxW : x₀ ∈ W := ⟨mem_chart_source _ x₀, Metric.mem_ball_self (half_pos hε)⟩
  set A := V ∩ φ ⁻¹' Q with hAdef
  have hA : MeasurableSet A := measurableSet_inter_preimage_chart x₀ hVm hVs hQm
  have hAs : A ⊆ (chartAt (EuclideanHalfSpace N) x₀).source := inter_subset_left.trans hVs
  have hWA : W ⊆ A := by
    rintro y ⟨hys, hyb⟩
    have hyH : φ y ∈ Half.H N := image_chart_subset_H x₀ (subset_refl _) ⟨y, hys, rfl⟩
    have hyQ : φ y ∈ Q := ⟨Metric.ball_subset_closedBall hyb, hyH⟩
    obtain ⟨v, hv, hvy⟩ := hQV hyQ
    have hvs : v ∈ φ.source := by rw [extChartAt_source]; exact hVs hv
    have hys' : y ∈ φ.source := by rw [extChartAt_source]; exact hys
    have : v = y := φ.injOn hvs hys' hvy
    exact ⟨this ▸ hv, hyQ⟩
  have hφAQ : φ '' A ⊆ Q := image_subset_iff.mpr fun y hy => hy.2
  have hμA : μ A ≠ ⊤ := by
    have h := (hG.vol A inter_subset_left hA).1
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ne_top_of_le_ne_top hQvol (measure_mono hφAQ))) h
  haveI : IsFiniteMeasure (μ.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμA.lt_top⟩
  have hmap := (map_restrict_comparable μ x₀ hA hAs
    (fun A' hA' hA'm => hG.vol A' (hA'.trans inter_subset_left) hA'm)).1
  have hφA : AEMeasurable φ (μ.restrict A) :=
    ((continuousOn_extChartAt x₀).mono (by rw [extChartAt_source]; exact hAs)).aemeasurable hA
  refine ⟨W, hWo, hxW, fun u hu f hf hgrad hlim => ?_⟩
  -- the functions read in the chart
  set D : ℕ → EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ :=
    fun k => fderivWithin ℝ (inChart N x₀ (u k)) (range (𝓡∂ N)) with hD
  set w : ℕ → EuclideanSpace ℝ (Fin N) → ℝ := fun k => Q.piecewise (inChart N x₀ (u k)) 0
    with hw
  have hcont : ∀ k, ContinuousOn (inChart N x₀ (u k)) Q := fun k =>
    (contDiffOn_inChart (hu k) x₀).continuousOn.mono hQt
  have hwm : ∀ k, Measurable (w k) := fun k =>
    (hcont k).measurable_piecewise continuousOn_const hQm
  have hwQ : ∀ k, ∀ z ∈ Q, w k z = inChart N x₀ (u k) z := fun k z hz =>
    piecewise_eq_of_mem _ _ _ hz
  have hDt : ∀ k, ContinuousOn (D k) φ.target := fun k =>
    ((contDiffOn_inChart (hu k) x₀).continuousOn_fderivWithin (uniqueDiffOn_extChartAt_target x₀)
      le_rfl).congr fun z hz => (fderivWithin_target_eq x₀ _ hz).symm
  have hwD : ∀ k, ∀ z ∈ Q, HasFDerivWithinAt (w k) (D k z) Q z := by
    intro k z hz
    have hzt := hQt hz
    have hys : φ.symm z ∈ (chartAt (EuclideanHalfSpace N) x₀).source := by
      rw [← extChartAt_source (I := 𝓡∂ N)]; exact φ.map_target hzt
    have hφy : φ (φ.symm z) = z := φ.right_inv hzt
    have h1 := (hasFDerivWithinAt_inChart x₀ (φ.symm z) hys (u k)
      ((hu k).mdifferentiableAt one_ne_zero)).differentiableWithinAt
    rw [hφy] at h1
    exact (h1.hasFDerivWithinAt.mono hQr).congr (fun z' hz' => hwQ k z' hz') (hwQ k z hz)
  set CQ : ℝ≥0∞ := 2 * 2 ^ N * ENNReal.ofReal (ε ^ 2) * volume Q with hCQ
  have hCQt : CQ ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
    ENNReal.ofReal_ne_top) hQvol
  have hdouble : ∀ k, ∫⁻ a in Q, ∫⁻ b in Q, ‖w k b - w k a‖ₑ ^ (2 : ℝ) ≤
      CQ * ∫⁻ z in Q, ‖D k z‖ₑ ^ (2 : ℝ) := fun k =>
    Half.double_integral_le hQc hQm hQd (hwD k) ((hDt k).mono hQt)
  set c2 : ℝ≥0∞ := (Cμ : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞)).toReal with hc2
  have hc2t : c2 ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top
  set G : ℕ → ℝ≥0∞ := fun k => eLpNorm (gradNorm g (u k)) 2 μ with hGdef
  have hDbound : ∀ k, ∫⁻ z in Q, ‖D k z‖ₑ ^ (2 : ℝ) ≤
      (c2 * (ENNReal.ofReal Cg * G k)) ^ (2 : ℝ) := by
    intro k
    have hDm : AEStronglyMeasurable (D k) (volume.restrict φ.target) :=
      (hDt k).aestronglyMeasurable (measurableSet_target x₀)
    have hT2 := (eLpNorm_chart_comparable μ x₀ hVm hVs hG.Cμ_ne hG.vol hDm 2).2
    have he : (D k ∘ φ) = dChart N x₀ (u k) := rfl
    rw [he] at hT2
    calc ∫⁻ z in Q, ‖D k z‖ₑ ^ (2 : ℝ) ≤ ∫⁻ z in φ '' V, ‖D k z‖ₑ ^ (2 : ℝ) :=
          lintegral_mono_set hQV
      _ = eLpNorm (D k) 2 (volume.restrict (φ '' V)) ^ (2 : ℝ) :=
          lintegral_enorm_rpow_two_eq _ _
      _ ≤ (c2 * eLpNorm (dChart N x₀ (u k)) 2 (μ.restrict V)) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hT2 (by norm_num)
      _ ≤ (c2 * (ENNReal.ofReal Cg * G k)) ^ (2 : ℝ) := by
          gcongr; exact eLpNorm_dChart_le hG (hu k)
  -- transfer of the double integral to `M`
  have htransfer : ∀ k, ∫⁻ x in A, ∫⁻ y in A, ‖u k y - u k x‖ₑ ^ (2 : ℝ) ∂μ ∂μ ≤
      (Cμ : ℝ≥0∞) * ((Cμ : ℝ≥0∞) * ∫⁻ a in Q, ∫⁻ b in Q, ‖w k b - w k a‖ₑ ^ (2 : ℝ)) := by
    intro k
    set F : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin N) → ℝ≥0∞ :=
      fun q => ‖w k q.2 - w k q.1‖ₑ ^ (2 : ℝ) with hF
    have hFm : Measurable F :=
      (((hwm k).comp measurable_snd).sub ((hwm k).comp measurable_fst)).enorm.pow_const _
    have hval : ∀ x ∈ A, u k x = w k (φ x) := fun x hx => by
      rw [hwQ k _ hx.2]
      simp only [inChart, Function.comp_apply]
      rw [φ.left_inv (by rw [extChartAt_source]; exact hAs hx)]
    have hinner : ∀ x ∈ A, ∫⁻ y in A, ‖u k y - u k x‖ₑ ^ (2 : ℝ) ∂μ ≤
        (Cμ : ℝ≥0∞) * ∫⁻ b in Q, F (φ x, b) := by
      intro x hx
      calc ∫⁻ y in A, ‖u k y - u k x‖ₑ ^ (2 : ℝ) ∂μ = ∫⁻ y in A, F (φ x, φ y) ∂μ :=
            setLIntegral_congr_fun hA fun y hy => by
              simp only [hF]; rw [hval y hy, hval x hx]
        _ = ∫⁻ b, F (φ x, b) ∂(Measure.map φ (μ.restrict A)) :=
            (lintegral_map' (hFm.comp measurable_prodMk_left).aemeasurable hφA).symm
        _ ≤ ∫⁻ b, F (φ x, b) ∂((Cμ : ℝ≥0∞) • volume.restrict (φ '' A)) :=
            lintegral_mono' hmap le_rfl
        _ = (Cμ : ℝ≥0∞) * ∫⁻ b in φ '' A, F (φ x, b) := by
            rw [lintegral_smul_measure, smul_eq_mul]
        _ ≤ (Cμ : ℝ≥0∞) * ∫⁻ b in Q, F (φ x, b) := by
            gcongr
    have hm2 : Measurable fun a => ∫⁻ b in Q, F (a, b) := Measurable.lintegral_prod_right' hFm
    calc ∫⁻ x in A, ∫⁻ y in A, ‖u k y - u k x‖ₑ ^ (2 : ℝ) ∂μ ∂μ
        ≤ ∫⁻ x in A, (Cμ : ℝ≥0∞) * (∫⁻ b in Q, F (φ x, b)) ∂μ := setLIntegral_mono' hA hinner
      _ = (Cμ : ℝ≥0∞) * ∫⁻ x in A, (∫⁻ b in Q, F (φ x, b)) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = (Cμ : ℝ≥0∞) * ∫⁻ a, (∫⁻ b in Q, F (a, b)) ∂(Measure.map φ (μ.restrict A)) := by
          rw [lintegral_map' hm2.aemeasurable hφA]
      _ ≤ (Cμ : ℝ≥0∞) * ∫⁻ a, (∫⁻ b in Q, F (a, b)) ∂((Cμ : ℝ≥0∞) • volume.restrict (φ '' A)) :=
          mul_le_mul' le_rfl (lintegral_mono' hmap le_rfl)
      _ = (Cμ : ℝ≥0∞) * ((Cμ : ℝ≥0∞) * ∫⁻ a in φ '' A, ∫⁻ b in Q, F (a, b)) := by
          simp only [lintegral_smul_measure, smul_eq_mul]
      _ ≤ (Cμ : ℝ≥0∞) * ((Cμ : ℝ≥0∞) * ∫⁻ a in Q, ∫⁻ b in Q, F (a, b)) := by
          gcongr
  -- the `L²(μ|_A ⊗ μ|_A)` norms of the differences
  set ν := (μ.restrict A).prod (μ.restrict A) with hν
  have hΔm : ∀ k, Measurable fun z : M × M => u k z.2 - u k z.1 := fun k =>
    ((hu k).continuous.measurable.comp measurable_snd).sub
      ((hu k).continuous.measurable.comp measurable_fst)
  have hΔint : ∀ k, eLpNorm (fun z : M × M => u k z.2 - u k z.1) 2 ν ^ (2 : ℝ) ≤
      (Cμ : ℝ≥0∞) * ((Cμ : ℝ≥0∞) * (CQ * (c2 * (ENNReal.ofReal Cg * G k)) ^ (2 : ℝ))) := by
    intro k
    rw [← lintegral_enorm_rpow_two_eq,
      lintegral_prod _ ((hΔm k).enorm.pow_const _).aemeasurable]
    exact (htransfer k).trans (by gcongr; exact (hdouble k).trans (by gcongr; exact hDbound k))
  have hB : Tendsto (fun k => (Cμ : ℝ≥0∞) * ((Cμ : ℝ≥0∞) *
      (CQ * (c2 * (ENNReal.ofReal Cg * G k)) ^ (2 : ℝ)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ENNReal.ofReal Cg * G k) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hgrad (Or.inr ENNReal.ofReal_ne_top)
    have h2 : Tendsto (fun k => c2 * (ENNReal.ofReal Cg * G k)) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr hc2t)
    have h3 : Tendsto (fun k => (c2 * (ENNReal.ofReal Cg * G k)) ^ (2 : ℝ)) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0).comp h2
      simpa [ENNReal.zero_rpow_of_pos, Function.comp_def] using this
    have h4 := ENNReal.Tendsto.const_mul h3 (Or.inr hCQt)
    have h5 := ENNReal.Tendsto.const_mul h4 (Or.inr (ENNReal.coe_ne_top (r := Cμ)))
    have h6 := ENNReal.Tendsto.const_mul h5 (Or.inr (ENNReal.coe_ne_top (r := Cμ)))
    simpa using h6
  have hX2 : Tendsto (fun k => eLpNorm (fun z : M × M => u k z.2 - u k z.1) 2 ν ^ (2 : ℝ))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB (fun k => bot_le) hΔint
  have hX : Tendsto (fun k => eLpNorm (fun z : M × M => u k z.2 - u k z.1) 2 ν) atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hX2
    have e : ∀ k, (eLpNorm (fun z : M × M => u k z.2 - u k z.1) 2 ν ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
        eLpNorm (fun z : M × M => u k z.2 - u k z.1) 2 ν := fun k => by
      rw [← ENNReal.rpow_mul]; norm_num
    have h' : (fun k => eLpNorm (fun z : M × M => u k z.2 - u k z.1) 2 ν) =
        (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) ∘
          (fun k => eLpNorm (fun z : M × M => u k z.2 - u k z.1) 2 ν ^ (2 : ℝ)) :=
      funext fun k => (e k).symm
    rw [h']
    convert this using 2
    rw [ENNReal.zero_rpow_of_pos (by norm_num)]
  -- the limit
  have hfA : AEStronglyMeasurable f (μ.restrict A) := hf.restrict
  have hΔf_m : AEStronglyMeasurable (fun z : M × M => f z.2 - f z.1) ν :=
    hfA.comp_snd.sub hfA.comp_fst
  set a : ℝ≥0∞ := (μ.restrict A univ) ^ (1 / 2 : ℝ) with ha
  have hat : a ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hbound : ∀ k, eLpNorm (fun z : M × M => f z.2 - f z.1) 2 ν ≤
      (a * eLpNorm (u k - f) 2 μ + a * eLpNorm (u k - f) 2 μ) +
        eLpNorm (fun z : M × M => u k z.2 - u k z.1) 2 ν := by
    intro k
    have hgk : AEStronglyMeasurable (f - u k) (μ.restrict A) :=
      hfA.sub (hu k).continuous.aestronglyMeasurable
    have hsplit : (fun z : M × M => f z.2 - f z.1) =
        ((fun z : M × M => (f - u k) z.2) - (fun z : M × M => (f - u k) z.1)) +
          (fun z : M × M => u k z.2 - u k z.1) := by
      funext z; simp only [Pi.add_apply, Pi.sub_apply]; ring
    have hle : eLpNorm (f - u k) 2 (μ.restrict A) ≤ eLpNorm (u k - f) 2 μ := by
      rw [eLpNorm_sub_comm]; exact eLpNorm_mono_measure _ Measure.restrict_le_self
    rw [hsplit]
    calc eLpNorm (((fun z : M × M => (f - u k) z.2) - (fun z : M × M => (f - u k) z.1)) +
          (fun z : M × M => u k z.2 - u k z.1)) 2 ν
        ≤ eLpNorm ((fun z : M × M => (f - u k) z.2) - (fun z : M × M => (f - u k) z.1)) 2 ν +
            eLpNorm (fun z : M × M => u k z.2 - u k z.1) 2 ν :=
          eLpNorm_add_le (hgk.comp_snd.sub hgk.comp_fst) (hΔm k).aestronglyMeasurable
            (by norm_num)
      _ ≤ (eLpNorm (fun z : M × M => (f - u k) z.2) 2 ν +
            eLpNorm (fun z : M × M => (f - u k) z.1) 2 ν) +
            eLpNorm (fun z : M × M => u k z.2 - u k z.1) 2 ν := by
          gcongr; exact eLpNorm_sub_le hgk.comp_snd hgk.comp_fst (by norm_num)
      _ = (a * eLpNorm (f - u k) 2 (μ.restrict A) + a * eLpNorm (f - u k) 2 (μ.restrict A)) +
            eLpNorm (fun z : M × M => u k z.2 - u k z.1) 2 ν := by
          rw [hν, eLpNorm_comp_snd _ _ hgk, eLpNorm_comp_fst _ _ hgk]
      _ ≤ _ := by gcongr
  have hRHS : Tendsto (fun k => (a * eLpNorm (u k - f) 2 μ + a * eLpNorm (u k - f) 2 μ) +
      eLpNorm (fun z : M × M => u k z.2 - u k z.1) 2 ν) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => a * eLpNorm (u k - f) 2 μ) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hlim (Or.inr hat)
    simpa using (h1.add h1).add hX
  have hzero : eLpNorm (fun z : M × M => f z.2 - f z.1) 2 ν = 0 :=
    le_antisymm (ge_of_tendsto' hRHS hbound) bot_le
  have hae := (eLpNorm_eq_zero_iff hΔf_m two_ne_zero).mp hzero
  have hae2 := Measure.ae_ae_of_ae_prod hae
  by_cases hA0 : μ.restrict A = 0
  · refine ⟨0, ?_⟩
    have : μ.restrict W = 0 := le_antisymm ((Measure.restrict_mono hWA le_rfl).trans
      hA0.le) bot_le
    rw [this]
    exact ae_zero.symm ▸ Filter.eventually_bot
  · haveI := ae_neBot.mpr hA0
    obtain ⟨x, hx⟩ := hae2.exists
    refine ⟨f x, ae_restrict_of_ae_restrict_of_subset hWA (hx.mono fun y hy => ?_)⟩
    simp only [Pi.zero_apply] at hy
    linarith

/-- **Constancy of energy-free limits** on a compact connected manifold with boundary (l.720),
for a **measurable** limit: if `u_k ∈ C¹(M)`, `‖∇u_k‖_{L²(μ)} → 0` and `u_k → f` in `L²(μ)` with
`f` `μ`-a.e. strongly measurable, then `f` is `μ`-a.e. constant. This is round 1's
`Mfd.const_of_tendsto` with the hypothesis `AEStronglyMeasurable f μ` added, which that statement
needs (`not_const_of_tendsto`). -/
theorem const_of_tendsto_of_aestronglyMeasurable [CompactSpace M] [T2Space M] [ConnectedSpace M]
    (g : RiemannianMetric N M) {μ : Measure M} (hμ : IsLocallyLebesgue N μ)
    (u : ℕ → M → ℝ) (hu : ∀ k, IsC1 N (u k)) (f : M → ℝ) (hf : AEStronglyMeasurable f μ)
    (hgrad : Tendsto (fun k => eLpNorm (gradNorm g (u k)) 2 μ) atTop (𝓝 0))
    (hlim : Tendsto (fun k => eLpNorm (u k - f) 2 μ) atTop (𝓝 0)) :
    ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  have hloc : ∀ x₀ : M, ∃ W : Set M, IsOpen W ∧ x₀ ∈ W ∧
      ∃ c : ℝ, f =ᵐ[μ.restrict W] fun _ => c := by
    intro x₀
    obtain ⟨V, Cμ, Cg, hxV, hG⟩ := exists_goodChart g hμ x₀
    obtain ⟨W, hWo, hxW, hW⟩ := local_const hG hxV
    exact ⟨W, hWo, hxW, hW u hu f hf hgrad hlim⟩
  choose W hWo hxW c hc using hloc
  have hc' : ∀ x, ∀ᵐ z ∂μ, z ∈ W x → f z = c x := fun x =>
    (ae_restrict_iff' (hWo x).measurableSet).mp (hc x)
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [(hWo x).mem_nhds (hxW x)] with y hy
    by_contra hne
    have hpos := measure_pos_of_isOpen g hμ ((hWo x).inter (hWo y)) ⟨y, hy, hxW y⟩
    have h0 : μ (W x ∩ W y) = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hc' x, hc' y] with z hzx hzy hz
      exact hne ((hzy hz.2).symm.trans (hzx hz.1))
    exact hpos.ne' h0
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₁⟩⟩
  · exact ⟨0, Filter.Eventually.of_forall fun z => (IsEmpty.false z).elim⟩
  · refine ⟨c x₁, ?_⟩
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover W
      (fun x _ => (hWo x).mem_nhds (hxW x))
    have hall : ∀ᵐ z ∂μ, ∀ x ∈ t, z ∈ W x → f z = c x :=
      (Filter.eventually_all_finset t).mpr fun x _ => hc' x
    filter_upwards [hall] with z hz
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (ht (mem_univ z))
    rw [hz x hx hzx, hlc.apply_eq_of_preconnectedSpace x x₁]

omit [MeasurableSpace M] [BorelSpace M] in
lemma gradNorm_const_zero (g : RiemannianMetric N M) (x : M) :
    gradNorm g (fun _ : M => (0 : ℝ)) x = 0 := by
  refine le_antisymm ?_ (gradNorm_nonneg g _ x)
  refine csSup_le ⟨0, 0, by simp, by simp; rfl⟩ ?_
  rintro _ ⟨v, -, rfl⟩
  simp; rfl

omit [BorelSpace M] in
/-- **The round-1 statement `Mfd.const_of_tendsto` needs the measurability of the limit.** If `μ`
charges a set `S` all of whose measurable subsets are `μ`-null (classically, a Vitali set in a
chart), then `u_k = 0` and `f = 1_S` satisfy its hypotheses (`eLpNorm` of a non-measurable
function is an inner integral, here `0`), while `f` is not `μ`-a.e. constant. -/
theorem not_const_of_tendsto (g : RiemannianMetric N M) {μ : Measure M} {S : Set M}
    (hS : ∀ T ⊆ S, MeasurableSet T → μ T = 0) (hSμ : μ S ≠ 0) :
    ¬ ∀ (u : ℕ → M → ℝ), (∀ k, IsC1 N (u k)) → ∀ f : M → ℝ,
      Tendsto (fun k => eLpNorm (gradNorm g (u k)) 2 μ) atTop (𝓝 0) →
      Tendsto (fun k => eLpNorm (u k - f) 2 μ) atTop (𝓝 0) → ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  classical
  intro h
  set f : M → ℝ := S.indicator 1 with hf
  have hE : eLpNorm (gradNorm g (fun _ : M => (0 : ℝ))) 2 μ = 0 := by
    have : gradNorm g (fun _ : M => (0 : ℝ)) = 0 := funext (gradNorm_const_zero g)
    rw [this, eLpNorm_zero]
  have hL : eLpNorm ((fun _ : M => (0 : ℝ)) - f) 2 μ = 0 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    obtain ⟨ψ, hψm, hψle, hψeq⟩ := exists_measurable_le_lintegral_eq μ
      (fun x => ‖((fun _ : M => (0 : ℝ)) - f) x‖ₑ ^ (2 : ℝ≥0∞).toReal)
    have hsub : {x | ψ x ≠ 0} ⊆ S := by
      intro x hx
      by_contra hxS
      have h0 : ‖((fun _ : M => (0 : ℝ)) - f) x‖ₑ ^ (2 : ℝ≥0∞).toReal = 0 := by
        simp [hf, hxS]
      exact hx (le_antisymm ((hψle x).trans h0.le) bot_le)
    have hnull : μ {x | ψ x ≠ 0} = 0 :=
      hS _ hsub (hψm (measurableSet_singleton 0)).compl
    have hψ0 : ∫⁻ x, ψ x ∂μ = 0 := by
      rw [lintegral_eq_zero_iff hψm]
      exact measure_eq_zero_iff_ae_notMem.mp hnull |>.mono fun x hx => by simpa using hx
    rw [hψeq, hψ0, ENNReal.zero_rpow_of_pos (by norm_num)]
  obtain ⟨c, hc⟩ := h (fun _ _ => 0) (fun _ => contMDiff_const) f
    (by simp only [hE]; exact tendsto_const_nhds) (by simp only [hL]; exact tendsto_const_nhds)
  have hc' : μ {x | f x ≠ c} = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at hc; exact hc
  by_cases hc0 : c = 0
  · apply hSμ
    refine measure_mono_null (fun x hx => ?_) hc'
    show f x ≠ c
    rw [hc0, hf, indicator_of_mem hx]; norm_num
  · have hSc : μ Sᶜ = 0 := by
      refine measure_mono_null (fun x hx => ?_) hc'
      show f x ≠ c
      rw [hf, indicator_of_notMem hx]; exact Ne.symm hc0
    obtain ⟨Z, hSZ, hZm, hZ0⟩ := exists_measurable_superset_of_null hSc
    have hZc : μ Zᶜ = 0 := hS _ (fun x hx => by
      by_contra hxS; exact hx (hSZ hxS)) hZm.compl
    apply hSμ
    refine measure_mono_null (subset_univ S) ?_
    have := measure_union_le (μ := μ) Z Zᶜ
    rw [union_compl_self, hZ0, hZc, add_zero] at this
    exact le_antisymm this bot_le

namespace Reads

variable {D : Type*} [AddCommGroup D] [Module ℝ D] {n : ℕ} {Mm : MeasuredModel M D N n}
  {gm : FrameMetric M N} {g : RiemannianMetric N M} {μ : Measure M} {σ : Fin n → Measure M}

/-- The constancy step of l.720 on a model reading a compact connected manifold, **for a
measurable limit**: the corrected form of the round-1 `Mfd.Reads.constLimit` (whose conclusion
`MeasuredModel.ConstLimit` quantifies over every `f`, measurable or not, and is refuted by
`not_const_of_tendsto` as soon as `μ` charges a set without non-null measurable subsets). -/
theorem constLimit_of_aestronglyMeasurable [CompactSpace M] [T2Space M] [ConnectedSpace M]
    [IsFiniteMeasure μ] (hr : Reads Mm gm g μ σ) (hμ : IsLocallyLebesgue N μ) :
    ∀ (u : ℕ → D) (f : M → ℝ), AEStronglyMeasurable f (Mm.vol gm) →
      Tendsto (fun k => Mm.dirichlet gm (u k)) atTop (𝓝 0) →
      Tendsto (fun k => eLpNorm (Mm.val (u k) - f) 2 (Mm.vol gm)) atTop (𝓝 0) →
        ∃ c : ℝ, f =ᵐ[Mm.vol gm] fun _ => c := by
  intro u f hfm hdir hlim
  rw [hr.vol_eq] at hlim hfm ⊢
  have hf := fun k => hr.c1 (u k)
  have hgrad : Tendsto (fun k => eLpNorm (gradNorm g (Mm.val (u k))) 2 μ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => normSq μ 2 (gradNorm g (Mm.val (u k)))) atTop (𝓝 0) :=
      hdir.congr fun k => hr.dirichlet_eq (u k)
    have h2 := tendsto_eLpNorm_of_normSq (fun k => by
      rw [ENNReal.ofReal_ofNat]; exact (eLpNorm_gradNorm_lt_top' g (hf k)).ne) h1
    rwa [ENNReal.ofReal_ofNat] at h2
  exact const_of_tendsto_of_aestronglyMeasurable g hμ (fun k => Mm.val (u k)) hf f hfm hgrad hlim

end Reads

end Mfd

end Yamabe
