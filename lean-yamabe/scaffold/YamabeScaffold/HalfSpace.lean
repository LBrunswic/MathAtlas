import YamabeScaffold.Trace

/-!
# The Sobolev and trace inequalities on the closed half-space, with the gradient over the half-space only

Labels (NOT marked: infrastructure for the manifold theorems of `YamabeScaffold.ManifoldTheorems`):

* `lem:kobayashi` — `Yamabegap.tex:613` (statement l.613–625, proof l.626–638): the Sobolev
  embedding the proof cites (l.637), in the half-space chart.
* `lem:positivity` — `Yamabegap.tex:715` (statement l.715–718, proof l.719–721): the trace theorem
  of l.491 that its quotient uses, in the half-space chart.

> by the Sobolev embedding $W^{1,2}(\Sigma)\hookrightarrow L^{\pstar}(\Sigma)$ on compact manifolds
> with boundary \cite{Hebey1996}. (l.637)

> where the boundary norms are those of the trace of $u$, which is well defined in
> $L^{\psharp}(\partial\Sigma)$ by the trace theorem. (l.491)

## What is proved

For `v : ℝ^N → ℝ`, `C¹` on the closed half-space `ℍ̄ = {z₀ ≥ 0}` (`ContDiffOn ℝ 1 v ℍ̄`, the
derivative being `fderivWithin ℝ v ℍ̄`, which is what a function `C¹` up to the boundary of a
manifold has in a chart) and compactly supported:

* `Half.contDiff_ext`, `Half.hasCompactSupport_ext`: the **reflection**
  `Ev(z', -t) = -3 v(z', t) + 4 v(z', t/2)` (`t > 0`) is `C¹` on all of `ℝ^N`, compactly supported,
  equal to `v` on `ℍ̄`; `Half.eLpNorm_fderiv_ext_le`: `‖D(Ev)‖_{L²(ℝ^N)} ≤ C ‖Dv‖_{L²(ℍ̄)}`
  (the two reflections are linear automorphisms, which scale Lebesgue measure by constants);
* `Half.sobolev_halfSpace`: `‖v‖_{L^{p*}(ℍ̄)} ≤ C ‖Dv‖_{L²(ℍ̄)}` (Mathlib's
  Gagliardo–Nirenberg–Sobolev inequality, through `sobolev_euclidean`, applied to `Ev`);
* `Half.trace_halfSpace'`: `∫_{ℝ^{N-1}} |v(0, z')|^{p♯} dz' ≤ C ‖Dv‖^{p♯}_{L²(ℍ̄)}` (round 1's
  `trace_critical` applied to `Ev` read in `ℝ × ℝ^{N-1}`, through the measure-preserving linear
  equivalence `Half.Φ`);
* the boundary hyperplane: `Half.ι` (`z' ↦ (0, z')`, an isometry onto `{z₀ = 0}`),
  `Half.hausdorffMeasure_le_volume` (`μH[n] ≤ K vol` on `ℝ^n` with the Euclidean metric) and
  `Half.eLpNorm_hyperplane_le` (`L^p` norms for `μH[N-1]` on `{z₀ = 0}` by Lebesgue `L^p` norms
  on `ℝ^{N-1}`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `u ∈ W^{1,2}` near the boundary | ⚠ read as `C¹` up to the boundary with compact support (OQ-93 (b)) |

## SCOPE (disclosed)

* Infrastructure only: no label of the paper is certified here. The constants are not sharp.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Manifold ContDiff

noncomputable section

namespace Yamabe

namespace Half

variable {N : ℕ} [NeZero N]

/-! ## 1. The half-space and the reflections -/

variable (N) in
/-- The closed half-space `ℍ̄ = {z | 0 ≤ z₀}` (Mathlib's `range (𝓡∂ N)`). -/
def H : Set (EuclideanSpace ℝ (Fin N)) := {z | 0 ≤ z 0}

variable (N) in
/-- The closed lower half-space `{z | z₀ ≤ 0}`. -/
def L : Set (EuclideanSpace ℝ (Fin N)) := {z | z 0 ≤ 0}

lemma H_eq : H N = range (𝓡∂ N) := (range_modelWithCornersEuclideanHalfSpace N).symm

lemma continuous_coord0 : Continuous fun z : EuclideanSpace ℝ (Fin N) => z 0 := by fun_prop

lemma isClosed_H : IsClosed (H N) := isClosed_le continuous_const continuous_coord0

lemma isClosed_L : IsClosed (L N) := isClosed_le continuous_coord0 continuous_const

lemma measurableSet_H : MeasurableSet (H N) := isClosed_H.measurableSet

lemma uniqueDiffOn_H : UniqueDiffOn ℝ (H N) := by
  rw [H_eq]; exact (𝓡∂ N).uniqueDiffOn

lemma H_union_L : H N ∪ L N = univ := by
  ext z
  simp only [H, L, mem_union, mem_setOf_eq, mem_univ, iff_true]
  exact le_total _ _

lemma H_mem_nhds {z : EuclideanSpace ℝ (Fin N)} (hz : 0 < z 0) : H N ∈ 𝓝 z :=
  mem_of_superset ((isOpen_lt continuous_const continuous_coord0).mem_nhds hz)
    fun y (hy : 0 < y 0) => hy.le

lemma L_mem_nhds {z : EuclideanSpace ℝ (Fin N)} (hz : z 0 < 0) : L N ∈ 𝓝 z :=
  mem_of_superset ((isOpen_lt continuous_coord0 continuous_const).mem_nhds hz)
    fun y (hy : y 0 < 0) => hy.le

variable (N) in
/-- `R_c z = z + (c z₀) e₀`: the first coordinate is multiplied by `1 + c`. -/
def refl (c : ℝ) : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  ContinuousLinearMap.id ℝ _ +
    (EuclideanSpace.proj (0 : Fin N) : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).smulRight
      (c • EuclideanSpace.single (0 : Fin N) (1 : ℝ))

lemma proj_zero_apply (z : EuclideanSpace ℝ (Fin N)) :
    (EuclideanSpace.proj (0 : Fin N) : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) z = z 0 := rfl

lemma refl_apply' (c : ℝ) (z : EuclideanSpace ℝ (Fin N)) :
    refl N c z = z + (z 0) • (c • EuclideanSpace.single (0 : Fin N) (1 : ℝ)) := rfl

lemma refl_apply (c : ℝ) (z : EuclideanSpace ℝ (Fin N)) (j : Fin N) :
    refl N c z j = if j = 0 then (1 + c) * z 0 else z j := by
  rw [refl_apply']
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  split_ifs with h
  · subst h; ring
  · ring

lemma refl_apply_zero (c : ℝ) (z : EuclideanSpace ℝ (Fin N)) : refl N c z 0 = (1 + c) * z 0 := by
  rw [refl_apply, if_pos rfl]

lemma refl_of_zero (c : ℝ) {z : EuclideanSpace ℝ (Fin N)} (hz : z 0 = 0) : refl N c z = z := by
  ext j
  rw [refl_apply]
  split_ifs with h
  · subst h; rw [hz, mul_zero]
  · rfl

lemma refl_refl (c c' : ℝ) (z : EuclideanSpace ℝ (Fin N)) :
    refl N c (refl N c' z) = refl N (c + c' + c * c') z := by
  ext j
  simp only [refl_apply]
  split_ifs with h
  · ring
  · rfl

lemma refl_zero (z : EuclideanSpace ℝ (Fin N)) : refl N 0 z = z := by
  ext j
  rw [refl_apply]
  split_ifs with h
  · subst h; ring
  · rfl

lemma norm_refl_le (c : ℝ) : ‖refl N c‖ ≤ 1 + |c| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  have h0 : |z 0| ≤ ‖z‖ := by
    have := PiLp.norm_apply_le z 0
    rwa [Real.norm_eq_abs] at this
  calc ‖refl N c z‖
      = ‖z + (z 0) • (c • EuclideanSpace.single (0 : Fin N) (1 : ℝ))‖ := by
        rw [refl_apply']
    _ ≤ ‖z‖ + ‖(z 0) • (c • EuclideanSpace.single (0 : Fin N) (1 : ℝ))‖ := norm_add_le _ _
    _ = ‖z‖ + |z 0| * |c| := by
        rw [norm_smul, norm_smul, PiLp.norm_single, norm_one, mul_one,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖z‖ + ‖z‖ * |c| := by gcongr
    _ = (1 + |c|) * ‖z‖ := by ring

/-- `R_c` as a linear automorphism, with inverse `R_{c'}` when `(1 + c)(1 + c') = 1`. -/
def reflE (c c' : ℝ) (h : c + c' + c * c' = 0) (h' : c' + c + c' * c = 0) :
    EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
  ContinuousLinearEquiv.equivOfInverse (refl N c) (refl N c')
    (fun z => by rw [refl_refl, h', refl_zero]) (fun z => by rw [refl_refl, h, refl_zero])

lemma reflE_apply (c c' : ℝ) (h : c + c' + c * c' = 0) (h' : c' + c + c' * c = 0)
    (z : EuclideanSpace ℝ (Fin N)) : reflE c c' h h' z = refl N c z := rfl

/-- `R₁`, the reflection `z₀ ↦ -z₀`. -/
abbrev R₁ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
  reflE (-2) (-2) (by norm_num) (by norm_num)

/-- `R₂`, `z₀ ↦ -z₀/2`. -/
abbrev R₂ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
  reflE (-3/2) (-3) (by norm_num) (by norm_num)

lemma R₁_mapsTo : MapsTo (refl N (-2)) (L N) (H N) := fun z (hz : z 0 ≤ 0) => by
  show 0 ≤ refl N (-2) z 0
  rw [refl_apply_zero]; linarith

lemma R₂_mapsTo : MapsTo (refl N (-3/2)) (L N) (H N) := fun z (hz : z 0 ≤ 0) => by
  show 0 ≤ refl N (-3/2) z 0
  rw [refl_apply_zero]; linarith

/-- The derivative identity at the boundary: `-3 Λ ∘ R₁ + 4 Λ ∘ R₂ = Λ`. -/
lemma deriv_identity (Λ : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) :
    (-3 : ℝ) • Λ.comp (refl N (-2)) + (4 : ℝ) • Λ.comp (refl N (-3/2)) = Λ := by
  ext z
  have e : ∀ c : ℝ, Λ (refl N c z) = Λ z + z 0 * (c * Λ (EuclideanSpace.single (0 : Fin N) 1)) := by
    intro c
    rw [refl_apply', map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp only [FunLike.coe_add, FunLike.coe_smul,
    ContinuousLinearMap.coe_comp, Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
    e]
  ring

/-! ## 2. Linear changes of variables -/

omit [NeZero N] in
/-- A linear automorphism of `ℝ^N` scales Lebesgue measure by a constant. -/
lemma map_equiv_volume (e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)) :
    Measure.map e volume = ENNReal.ofReal
      |(LinearMap.det (e.toLinearEquiv : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] _))⁻¹| • volume := by
  have hdet : LinearMap.det (e.toLinearEquiv : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] _) ≠ 0 :=
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet

omit [NeZero N] in
/-- `‖f ∘ e‖_{L²} ≤ C ‖f‖_{L²}` for a linear automorphism `e`. -/
lemma exists_eLpNorm_comp_le (e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)) :
    ∃ C : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin N) → ℝ, AEStronglyMeasurable f volume →
      AEStronglyMeasurable (f ∘ e) volume ∧ eLpNorm (f ∘ e) 2 volume ≤ C * eLpNorm f 2 volume := by
  set c := ENNReal.ofReal
      |(LinearMap.det (e.toLinearEquiv : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] _))⁻¹| with hc
  have hdet : LinearMap.det (e.toLinearEquiv : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] _) ≠ 0 :=
    (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hc0 : c ≠ 0 := by
    rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.mpr (inv_ne_zero hdet)
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨(c ^ (1 / 2 : ℝ)).toNNReal, fun f hf => ?_⟩
  have hmap := map_equiv_volume e
  have hf' : AEStronglyMeasurable f (Measure.map e volume) := by
    rw [hmap]; exact hf.smul_measure c
  have hem : AEMeasurable e volume := e.continuous.measurable.aemeasurable
  refine ⟨hf'.comp_aemeasurable hem, ?_⟩
  rw [← eLpNorm_map_measure hf' hem, hmap, eLpNorm_smul_measure_of_ne_zero hc0,
    ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hctop), smul_eq_mul]
  norm_num

/-! ## 3. The reflected extension -/

variable (N) in
/-- The extension of `v` across `{z₀ = 0}`: `v` on `ℍ̄`, `-3 v ∘ R₁ + 4 v ∘ R₂` below. -/
def ext (v : EuclideanSpace ℝ (Fin N) → ℝ) : EuclideanSpace ℝ (Fin N) → ℝ := fun z =>
  if 0 ≤ z 0 then v z else -3 * v (refl N (-2) z) + 4 * v (refl N (-3/2) z)

variable (N) in
/-- The derivative of the extension. -/
def extD (v : EuclideanSpace ℝ (Fin N) → ℝ) :
    EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := fun z =>
  if 0 ≤ z 0 then fderivWithin ℝ v (H N) z else
    (-3 : ℝ) • (fderivWithin ℝ v (H N) (refl N (-2) z)).comp (refl N (-2)) +
      (4 : ℝ) • (fderivWithin ℝ v (H N) (refl N (-3/2) z)).comp (refl N (-3/2))

lemma ext_of_mem {v : EuclideanSpace ℝ (Fin N) → ℝ} {z : EuclideanSpace ℝ (Fin N)}
    (hz : z ∈ H N) : ext N v z = v z := if_pos hz

lemma hasFDerivAt_ext {v : EuclideanSpace ℝ (Fin N) → ℝ} (hv : ContDiffOn ℝ 1 v (H N))
    (z : EuclideanSpace ℝ (Fin N)) : HasFDerivAt (ext N v) (extD N v z) z := by
  set Dv := fderivWithin ℝ v (H N) with hDv
  have hdiff : DifferentiableOn ℝ v (H N) := hv.differentiableOn one_ne_zero
  have hvH : ∀ y ∈ H N, HasFDerivWithinAt v (Dv y) (H N) y := fun y hy =>
    (hdiff y hy).hasFDerivWithinAt
  set w : EuclideanSpace ℝ (Fin N) → ℝ := fun z =>
    -3 * v (refl N (-2) z) + 4 * v (refl N (-3/2) z) with hw
  set w' : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := fun z =>
    (-3 : ℝ) • (Dv (refl N (-2) z)).comp (refl N (-2)) +
      (4 : ℝ) • (Dv (refl N (-3/2) z)).comp (refl N (-3/2)) with hw'
  have hwL : ∀ y ∈ L N, HasFDerivWithinAt w (w' y) (L N) y := by
    intro y hy
    have h1 : HasFDerivWithinAt (fun z => v (refl N (-2) z))
        ((Dv (refl N (-2) y)).comp (refl N (-2))) (L N) y :=
      (hvH _ (R₁_mapsTo hy)).comp y (refl N (-2)).hasFDerivWithinAt R₁_mapsTo
    have h2 : HasFDerivWithinAt (fun z => v (refl N (-3/2) z))
        ((Dv (refl N (-3/2) y)).comp (refl N (-3/2))) (L N) y :=
      (hvH _ (R₂_mapsTo hy)).comp y (refl N (-3/2)).hasFDerivWithinAt R₂_mapsTo
    exact (h1.const_mul (-3)).add (h2.const_mul 4)
  have hextL : ∀ y ∈ L N, ext N v y = w y := by
    intro y hy
    by_cases h0 : 0 ≤ y 0
    · have hy0 : y 0 = 0 := le_antisymm hy h0
      rw [ext, if_pos h0]
      simp only [hw, refl_of_zero _ hy0]
      ring
    · rw [ext, if_neg h0]
  have hbd : ∀ y : EuclideanSpace ℝ (Fin N), y 0 = 0 → w' y = Dv y := by
    intro y hy
    simp only [hw', refl_of_zero _ hy]
    exact deriv_identity _
  rcases lt_trichotomy (z 0) 0 with hneg | hzero | hpos
  · have hzL : z ∈ L N := hneg.le
    have h := ((hwL z hzL).congr (fun y hy => hextL y hy) (hextL z hzL)).hasFDerivAt
      (L_mem_nhds hneg)
    have he : extD N v z = w' z := by rw [extD, if_neg (not_le.mpr hneg)]
    rw [he]; exact h
  · have hzL : z ∈ L N := hzero.le
    have hzH : z ∈ H N := hzero.ge
    have h1 : HasFDerivWithinAt (ext N v) (Dv z) (H N) z :=
      (hvH z hzH).congr (fun y hy => ext_of_mem hy) (ext_of_mem hzH)
    have h2 : HasFDerivWithinAt (ext N v) (Dv z) (L N) z := by
      rw [← hbd z hzero]
      exact (hwL z hzL).congr (fun y hy => hextL y hy) (hextL z hzL)
    have h := h1.union h2
    rw [H_union_L, hasFDerivWithinAt_univ] at h
    have he : extD N v z = Dv z := by rw [extD, if_pos (show (0 : ℝ) ≤ z 0 from hzH)]
    rw [he]; exact h
  · have hzH : z ∈ H N := hpos.le
    have h := ((hvH z hzH).congr (fun y hy => ext_of_mem hy) (ext_of_mem hzH)).hasFDerivAt
      (H_mem_nhds hpos)
    have he : extD N v z = Dv z := by rw [extD, if_pos (show (0 : ℝ) ≤ z 0 from hzH)]
    rw [he]; exact h

lemma continuous_extD {v : EuclideanSpace ℝ (Fin N) → ℝ} (hv : ContDiffOn ℝ 1 v (H N)) :
    Continuous (extD N v) := by
  set Dv := fderivWithin ℝ v (H N) with hDv
  have hDc : ContinuousOn Dv (H N) := hv.continuousOn_fderivWithin uniqueDiffOn_H le_rfl
  have h1 : ContinuousOn (extD N v) (H N) := hDc.congr fun y hy => by
    show extD N v y = Dv y
    rw [extD, if_pos (show (0 : ℝ) ≤ y 0 from hy)]
  have hw' : ContinuousOn (fun z => (-3 : ℝ) • (Dv (refl N (-2) z)).comp (refl N (-2)) +
      (4 : ℝ) • (Dv (refl N (-3/2) z)).comp (refl N (-3/2))) (L N) := by
    refine ContinuousOn.add (ContinuousOn.const_smul ?_ _) (ContinuousOn.const_smul ?_ _)
    · exact (hDc.comp (refl N (-2)).continuous.continuousOn R₁_mapsTo).clm_comp
        continuousOn_const
    · exact (hDc.comp (refl N (-3/2)).continuous.continuousOn R₂_mapsTo).clm_comp
        continuousOn_const
  have h2 : ContinuousOn (extD N v) (L N) := hw'.congr fun y (hy : y 0 ≤ 0) => by
    by_cases h0 : 0 ≤ y 0
    · have hy0 : y 0 = 0 := le_antisymm hy h0
      rw [extD, if_pos h0]
      simp only [refl_of_zero _ hy0]
      exact (deriv_identity _).symm
    · rw [extD, if_neg h0]
  have h3 := h1.union_of_isClosed h2 isClosed_H isClosed_L
  rw [H_union_L] at h3
  exact continuousOn_univ.mp h3

lemma fderiv_ext {v : EuclideanSpace ℝ (Fin N) → ℝ} (hv : ContDiffOn ℝ 1 v (H N)) :
    fderiv ℝ (ext N v) = extD N v :=
  funext fun z => (hasFDerivAt_ext hv z).fderiv

/-- **The extension is `C¹` on `ℝ^N`.** -/
theorem contDiff_ext {v : EuclideanSpace ℝ (Fin N) → ℝ} (hv : ContDiffOn ℝ 1 v (H N)) :
    ContDiff ℝ 1 (ext N v) :=
  contDiff_one_iff_fderiv.mpr ⟨fun z => (hasFDerivAt_ext hv z).differentiableAt,
    by rw [fderiv_ext hv]; exact continuous_extD hv⟩

/-- The extension of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_ext {v : EuclideanSpace ℝ (Fin N) → ℝ} (hc : HasCompactSupport v) :
    HasCompactSupport (ext N v) := by
  set K := tsupport v
  have hK : IsCompact K := hc
  have hK1 : IsCompact ((R₁ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _) ⁻¹' K) :=
    (R₁ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _).toHomeomorph.isCompact_preimage.mpr hK
  have hK2 : IsCompact ((R₂ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _) ⁻¹' K) :=
    (R₂ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _).toHomeomorph.isCompact_preimage.mpr hK
  refine HasCompactSupport.intro ((hK.union hK1).union hK2) fun z hz => ?_
  simp only [mem_union, not_or] at hz
  obtain ⟨⟨hz0, hz1⟩, hz2⟩ := hz
  have e0 : v z = 0 := image_eq_zero_of_notMem_tsupport hz0
  have e1 : v (refl N (-2) z) = 0 := image_eq_zero_of_notMem_tsupport hz1
  have e2 : v (refl N (-3/2) z) = 0 := image_eq_zero_of_notMem_tsupport hz2
  unfold ext
  split_ifs
  · exact e0
  · rw [e1, e2]; ring

/-- **The `L²` norm of the extension's derivative** is controlled by the half-space one. -/
theorem eLpNorm_fderiv_ext_le :
    ∃ C : ℝ≥0, ∀ v : EuclideanSpace ℝ (Fin N) → ℝ, ContDiffOn ℝ 1 v (H N) →
      eLpNorm (fderiv ℝ (ext N v)) 2 volume ≤
        C * eLpNorm (fderivWithin ℝ v (H N)) 2 (volume.restrict (H N)) := by
  obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_comp_le (R₁ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _)
  obtain ⟨C₂, hC₂⟩ := exists_eLpNorm_comp_le (R₂ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _)
  refine ⟨1 + 9 * C₁ + 10 * C₂, fun v hv => ?_⟩
  set Dv := fderivWithin ℝ v (H N) with hDv
  have hDc : ContinuousOn Dv (H N) := hv.continuousOn_fderivWithin uniqueDiffOn_H le_rfl
  set h₀ : EuclideanSpace ℝ (Fin N) → ℝ := (H N).indicator fun y => ‖Dv y‖ with hh₀
  have hh₀m : AEStronglyMeasurable h₀ volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_H).mpr
      (hDc.norm.aestronglyMeasurable measurableSet_H)
  have hh₀n : ∀ y, 0 ≤ h₀ y := fun y =>
    Set.indicator_nonneg (fun y _ => norm_nonneg (Dv y)) y
  have hh₀H : ∀ y ∈ H N, h₀ y = ‖Dv y‖ := fun y hy => Set.indicator_of_mem hy _
  obtain ⟨hm1, hb1⟩ := hC₁ h₀ hh₀m
  obtain ⟨hm2, hb2⟩ := hC₂ h₀ hh₀m
  have hR1 : ‖refl N (-2)‖ ≤ 3 := (norm_refl_le _).trans (by norm_num)
  have hR2 : ‖refl N (-3/2)‖ ≤ 5/2 := (norm_refl_le _).trans (by norm_num [abs_of_neg])
  -- the pointwise bound
  have hpt : ∀ z, ‖extD N v z‖ ≤
      ‖(h₀ + (9 : ℝ) • (h₀ ∘ (R₁ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _)) +
        (10 : ℝ) • (h₀ ∘ (R₂ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _))) z‖ := by
    intro z
    have hn1 := hh₀n ((R₁ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _) z)
    have hn2 := hh₀n ((R₂ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _) z)
    have hn0 := hh₀n z
    have hsum : 0 ≤ (h₀ + (9 : ℝ) • (h₀ ∘ (R₁ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _)) +
        (10 : ℝ) • (h₀ ∘ (R₂ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _))) z := by
      simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
      positivity
    rw [Real.norm_of_nonneg hsum]
    simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
    by_cases hz : 0 ≤ z 0
    · rw [extD, if_pos hz, ← hh₀H z (show z ∈ H N from hz)]
      nlinarith
    · have hzL : z ∈ L N := (not_le.mp hz).le
      rw [extD, if_neg hz]
      have e1 : h₀ ((R₁ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _) z) = ‖Dv (refl N (-2) z)‖ :=
        hh₀H _ (R₁_mapsTo hzL)
      have e2 : h₀ ((R₂ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _) z) = ‖Dv (refl N (-3/2) z)‖ :=
        hh₀H _ (R₂_mapsTo hzL)
      rw [e1, e2]
      calc ‖(-3 : ℝ) • (Dv (refl N (-2) z)).comp (refl N (-2)) +
            (4 : ℝ) • (Dv (refl N (-3/2) z)).comp (refl N (-3/2))‖
          ≤ ‖(-3 : ℝ) • (Dv (refl N (-2) z)).comp (refl N (-2))‖ +
            ‖(4 : ℝ) • (Dv (refl N (-3/2) z)).comp (refl N (-3/2))‖ := norm_add_le _ _
        _ ≤ 3 * (‖Dv (refl N (-2) z)‖ * ‖refl N (-2)‖) +
            4 * (‖Dv (refl N (-3/2) z)‖ * ‖refl N (-3/2)‖) := by
          rw [norm_smul, norm_smul]
          norm_num
          gcongr <;> exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 3 * (‖Dv (refl N (-2) z)‖ * 3) + 4 * (‖Dv (refl N (-3/2) z)‖ * (5/2)) := by
          gcongr
        _ ≤ h₀ z + 9 * ‖Dv (refl N (-2) z)‖ + 10 * ‖Dv (refl N (-3/2) z)‖ := by
          nlinarith
  rw [fderiv_ext hv]
  calc eLpNorm (extD N v) 2 volume
      ≤ eLpNorm (h₀ + (9 : ℝ) • (h₀ ∘ (R₁ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _)) +
          (10 : ℝ) • (h₀ ∘ (R₂ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _))) 2 volume := eLpNorm_mono hpt
    _ ≤ eLpNorm h₀ 2 volume + eLpNorm ((9 : ℝ) • (h₀ ∘ (R₁ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _)))
          2 volume + eLpNorm ((10 : ℝ) • (h₀ ∘ (R₂ : EuclideanSpace ℝ (Fin N) ≃L[ℝ] _))) 2 volume := by
        refine (eLpNorm_add_le (hh₀m.add (hm1.const_smul _)) (hm2.const_smul _) (by norm_num)).trans
          ?_
        gcongr
        exact eLpNorm_add_le hh₀m (hm1.const_smul _) (by norm_num)
    _ ≤ eLpNorm h₀ 2 volume + 9 * (C₁ * eLpNorm h₀ 2 volume) +
          10 * (C₂ * eLpNorm h₀ 2 volume) := by
        rw [eLpNorm_const_smul, eLpNorm_const_smul]
        have e9 : ‖(9 : ℝ)‖ₑ = 9 := by
          rw [Real.enorm_eq_ofReal_abs, abs_of_pos (by norm_num : (0 : ℝ) < 9), ENNReal.ofReal_ofNat]
        have e10 : ‖(10 : ℝ)‖ₑ = 10 := by
          rw [Real.enorm_eq_ofReal_abs, abs_of_pos (by norm_num : (0 : ℝ) < 10),
            ENNReal.ofReal_ofNat]
        rw [e9, e10]
        gcongr
    _ = ((1 + 9 * C₁ + 10 * C₂ : ℝ≥0) : ℝ≥0∞) * eLpNorm h₀ 2 volume := by
        push_cast; ring
    _ = ((1 + 9 * C₁ + 10 * C₂ : ℝ≥0) : ℝ≥0∞) * eLpNorm Dv 2 (volume.restrict (H N)) := by
        rw [hh₀, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_H, eLpNorm_norm]

/-! ## 4. The half-space Sobolev inequality -/

/-- **Sobolev on the half-space**, `N ≥ 3`: for `v` `C¹` on `ℍ̄` with compact support,
`‖v‖_{L^{p*}(ℍ̄)} ≤ C ‖Dv‖_{L²(ℍ̄)}`, `Dv` the derivative within `ℍ̄`. -/
theorem sobolev_halfSpace (hN : 3 ≤ N) :
    ∃ C : ℝ≥0, ∀ v : EuclideanSpace ℝ (Fin N) → ℝ, ContDiffOn ℝ 1 v (H N) → HasCompactSupport v →
      eLpNorm v (ENNReal.ofReal (pStar N)) (volume.restrict (H N)) ≤
        C * eLpNorm (fderivWithin ℝ v (H N)) 2 (volume.restrict (H N)) := by
  obtain ⟨C₁, hC₁⟩ := sobolev_euclidean hN
  obtain ⟨C₂, hC₂⟩ := eLpNorm_fderiv_ext_le (N := N)
  refine ⟨C₁ * C₂, fun v hv hc => ?_⟩
  have he : ext N v =ᵐ[volume.restrict (H N)] v :=
    (ae_restrict_mem measurableSet_H).mono fun z hz => ext_of_mem hz
  calc eLpNorm v (ENNReal.ofReal (pStar N)) (volume.restrict (H N))
      = eLpNorm (ext N v) (ENNReal.ofReal (pStar N)) (volume.restrict (H N)) :=
        (eLpNorm_congr_ae he).symm
    _ ≤ eLpNorm (ext N v) (ENNReal.ofReal (pStar N)) volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ C₁ * eLpNorm (fderiv ℝ (ext N v)) 2 volume :=
        hC₁ _ (contDiff_ext hv) (hasCompactSupport_ext hc)
    _ ≤ C₁ * (C₂ * eLpNorm (fderivWithin ℝ v (H N)) 2 (volume.restrict (H N))) := by
        gcongr; exact hC₂ v hv
    _ = ((C₁ * C₂ : ℝ≥0) : ℝ≥0∞) * eLpNorm (fderivWithin ℝ v (H N)) 2 (volume.restrict (H N)) := by
        push_cast; ring

/-! ## 5. `ℝ × ℝ^n` as `ℝ^{n+1}`, and the half-space trace inequality -/

/-- `(t, z') ↦ (t, z'₀, …, z'_{n-1})`, as a linear equivalence. -/
def Φl (n : ℕ) : (ℝ × EuclideanSpace ℝ (Fin n)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun p := WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))
  invFun q := (q 0, WithLp.toLp 2 (Fin.tail (WithLp.ofLp q)))
  map_add' p q := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c p := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  left_inv p := by
    ext
    · simp
    · simp [Fin.tail]
  right_inv q := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]

/-- `(t, z') ↦ (t, z')` from `ℝ × ℝ^n` to `ℝ^{n+1}`, a continuous linear equivalence. -/
def Φ (n : ℕ) : (ℝ × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (Φl n).toContinuousLinearEquiv

lemma Φ_apply (n : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    Φ n p = WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) := rfl

lemma Φ_apply_zero (n : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin n)) : Φ n p 0 = p.1 := by
  simp [Φ_apply]

/-- `Φ` preserves Lebesgue measure. -/
theorem measurePreserving_Φ (n : ℕ) : MeasurePreserving (Φ n) volume volume := by
  have h1 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (WithLp.ofLp (p := 2)
      (V := Fin n → ℝ))) (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    rw [Measure.volume_eq_prod]
    exact MeasurePreserving.id _ |>.prod (PiLp.volume_preserving_ofLp (Fin n))
  have h2 := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ))
    0).symm
  have h3 := PiLp.volume_preserving_toLp (Fin (n + 1))
  have h := h3.comp (h2.comp h1)
  have he : (Φ n : (ℝ × EuclideanSpace ℝ (Fin n)) → EuclideanSpace ℝ (Fin (n + 1))) =
      WithLp.toLp 2 ∘ ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm ∘
        Prod.map id WithLp.ofLp := by
    funext p
    simp [Φ_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero']
  rw [he]
  exact h

/-- **The trace inequality on the half-space**, `N = n + 1 ≥ 3`: for `v` `C¹` on `ℍ̄` with
compact support, `∫_{ℝ^n} |v(0, z')|^{p♯} dz' ≤ C ‖Dv‖_{L²(ℍ̄)}^{p♯}`, `Dv` the derivative
within `ℍ̄`. -/
theorem trace_halfSpace' {n : ℕ} (hN : 3 ≤ n + 1) :
    ∃ C : ℝ≥0, ∀ v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiffOn ℝ 1 v (H (n + 1)) →
      HasCompactSupport v →
        ∫⁻ z, ‖v (Φ n (0, z))‖ₑ ^ pSharp (n + 1) ≤
          C * eLpNorm (fderivWithin ℝ v (H (n + 1))) 2 (volume.restrict (H (n + 1))) ^
            pSharp (n + 1) := by
  obtain ⟨C₀, hC₀⟩ := trace_critical hN
  obtain ⟨C₂, hC₂⟩ := eLpNorm_fderiv_ext_le (N := n + 1)
  have hps : 0 ≤ pSharp (n + 1) := (zero_le_two.trans (two_le_pSharp hN))
  set P : (ℝ × EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (Φ n : (ℝ × EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))) with hP
  refine ⟨C₀ * (‖P‖₊ * C₂) ^ pSharp (n + 1), fun v hv hc => ?_⟩
  set w := ext (n + 1) v ∘ Φ n with hw
  have hwC : ContDiff ℝ 1 w := (contDiff_ext hv).comp (Φ n).contDiff
  have hwc : HasCompactSupport w := (hasCompactSupport_ext hc).comp_homeomorph (Φ n).toHomeomorph
  have h1 := hC₀ w hwC hwc
  have hval : ∀ z, w (0, z) = v (Φ n (0, z)) := fun z => ext_of_mem (by
    show (0 : ℝ) ≤ Φ n (0, z) 0
    rw [Φ_apply_zero])
  have hfd : ∀ p, fderiv ℝ w p = (fderiv ℝ (ext (n + 1) v) (Φ n p)).comp P := fun p =>
    ((((contDiff_ext hv).differentiable one_ne_zero) _).hasFDerivAt.comp p
      P.hasFDerivAt).fderiv
  have hcont : Continuous (fderiv ℝ (ext (n + 1) v)) := by
    rw [fderiv_ext hv]; exact continuous_extD hv
  have hD : eLpNorm (fderiv ℝ w) 2 volume ≤
      ‖P‖₊ * eLpNorm (fderiv ℝ (ext (n + 1) v)) 2 volume := by
    calc eLpNorm (fderiv ℝ w) 2 volume
        ≤ eLpNorm (‖P‖ • fun p => ‖fderiv ℝ (ext (n + 1) v) (Φ n p)‖) 2 volume := by
          refine eLpNorm_mono fun p => ?_
          rw [hfd p, Pi.smul_apply, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)
      _ = ‖P‖₊ * eLpNorm (fderiv ℝ (ext (n + 1) v) ∘ Φ n) 2 volume := by
          rw [eLpNorm_const_smul, eLpNorm_norm (fun p => fderiv ℝ (ext (n + 1) v) (Φ n p))]
          congr 1
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (norm_nonneg _), ofReal_norm, enorm_eq_nnnorm]
      _ = ‖P‖₊ * eLpNorm (fderiv ℝ (ext (n + 1) v)) 2 volume := by
          rw [eLpNorm_comp_measurePreserving hcont.aestronglyMeasurable (measurePreserving_Φ n)]
  have hD' : eLpNorm (fderiv ℝ w) 2 volume ≤ ‖P‖₊ * (C₂ *
      eLpNorm (fderivWithin ℝ v (H (n + 1))) 2 (volume.restrict (H (n + 1)))) :=
    hD.trans (by gcongr; exact hC₂ v hv)
  calc ∫⁻ z, ‖v (Φ n (0, z))‖ₑ ^ pSharp (n + 1) = ∫⁻ z, ‖w (0, z)‖ₑ ^ pSharp (n + 1) := by
        simp only [hval]
    _ ≤ C₀ * eLpNorm (fderiv ℝ w) 2 volume ^ pSharp (n + 1) := h1
    _ ≤ C₀ * (‖P‖₊ * (C₂ * eLpNorm (fderivWithin ℝ v (H (n + 1))) 2
          (volume.restrict (H (n + 1))))) ^ pSharp (n + 1) := by
        gcongr
    _ = ((C₀ * (‖P‖₊ * C₂) ^ pSharp (n + 1) : ℝ≥0) : ℝ≥0∞) *
          eLpNorm (fderivWithin ℝ v (H (n + 1))) 2 (volume.restrict (H (n + 1))) ^
            pSharp (n + 1) := by
        simp only [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ hps,
          ENNReal.mul_rpow_of_nonneg _ _ hps]
        ring

/-! ## 6. The boundary hyperplane and its `(N-1)`-dimensional Hausdorff measure -/

/-- `z' ↦ (0, z')`: the boundary hyperplane `{z₀ = 0}` of `ℝ^{n+1}`, parametrised by `ℝ^n`. -/
def ι (n : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (Φ n : (ℝ × EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))).comp
    (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n)))

lemma ι_apply (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) : ι n z = Φ n (0, z) := rfl

lemma norm_ι (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) : ‖ι n z‖ = ‖z‖ := by
  rw [ι_apply, Φ_apply, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
  simp

lemma isometry_ι (n : ℕ) : Isometry (ι n) := AddMonoidHomClass.isometry_of_norm (ι n) (norm_ι n)

lemma range_ι (n : ℕ) : range (ι n) = {z : EuclideanSpace ℝ (Fin (n + 1)) | z 0 = 0} := by
  ext z
  constructor
  · rintro ⟨z', rfl⟩
    show (ι n z') 0 = 0
    rw [ι_apply, Φ_apply_zero]
  · intro hz
    refine ⟨WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)), ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [ι_apply, Φ_apply_zero]; exact hz.symm
    · simp [ι_apply, Φ_apply, Fin.tail]

lemma isClosed_hyperplane (n : ℕ) :
    IsClosed {z : EuclideanSpace ℝ (Fin (n + 1)) | z 0 = 0} :=
  isClosed_eq continuous_coord0 continuous_const

/-- On `ℝ^n` with the Euclidean metric, `μH[n] ≤ K vol` (`toLp` is Lipschitz from the sup metric,
on which `μH[n]` is Lebesgue measure). -/
theorem hausdorffMeasure_le_volume (n : ℕ) :
    ∃ K : ℝ≥0, K ≠ 0 ∧ (Measure.hausdorffMeasure (n : ℝ) : Measure (EuclideanSpace ℝ (Fin n))) ≤
      (K : ℝ≥0∞) • volume := by
  set L : ℝ≥0 := (Fintype.card (Fin n) : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal with hL
  have hLip : LipschitzWith L (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)
  refine ⟨max (L ^ (n : ℝ)) 1, (lt_of_lt_of_le one_pos (le_max_right _ _)).ne', ?_⟩
  rw [Measure.le_iff]
  intro T hT
  have himg : WithLp.toLp 2 '' (WithLp.ofLp '' T) = T := by
    rw [image_image]; simp
  have hpre : (WithLp.ofLp '' T : Set (Fin n → ℝ)) = WithLp.toLp 2 ⁻¹' T := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨WithLp.toLp 2 x, hx, by simp⟩
  have h1 := hLip.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    (WithLp.ofLp '' T)
  rw [himg] at h1
  have hvol : (Measure.hausdorffMeasure (n : ℝ) : Measure (Fin n → ℝ)) = volume := by
    have := hausdorffMeasure_pi_real (ι := Fin n)
    rwa [Fintype.card_fin] at this
  rw [hvol, hpre, (PiLp.volume_preserving_toLp (Fin n)).measure_preimage hT.nullMeasurableSet]
    at h1
  rw [Measure.smul_apply, smul_eq_mul]
  refine h1.trans (mul_le_mul_left ?_ _)
  rw [← ENNReal.coe_rpow_of_nonneg _ (Nat.cast_nonneg n)]
  exact_mod_cast le_max_left _ _

/-- `L^p` norms on the boundary hyperplane for its `n`-dimensional Hausdorff measure, by the
Lebesgue `L^p` norm of the function read on `ℝ^n`. -/
theorem eLpNorm_hyperplane_le (n : ℕ) :
    ∃ K : ℝ≥0, K ≠ 0 ∧ ∀ (p : ℝ≥0∞) (G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
      AEStronglyMeasurable G ((Measure.hausdorffMeasure (n : ℝ)).restrict
        {z : EuclideanSpace ℝ (Fin (n + 1)) | z 0 = 0}) →
      eLpNorm G p ((Measure.hausdorffMeasure (n : ℝ)).restrict
        {z : EuclideanSpace ℝ (Fin (n + 1)) | z 0 = 0}) ≤
        (K : ℝ≥0∞) ^ (1 / p).toReal * eLpNorm (G ∘ ι n) p volume := by
  obtain ⟨K, hK0, hK⟩ := hausdorffMeasure_le_volume n
  refine ⟨K, hK0, fun p G hG => ?_⟩
  have hmap : Measure.map (ι n) (Measure.hausdorffMeasure (n : ℝ)) =
      (Measure.hausdorffMeasure (n : ℝ)).restrict {z : EuclideanSpace ℝ (Fin (n + 1)) | z 0 = 0} := by
    rw [(isometry_ι n).map_hausdorffMeasure (Or.inl (Nat.cast_nonneg n)), range_ι]
  rw [← hmap] at hG ⊢
  rw [eLpNorm_map_measure hG (ι n).continuous.aemeasurable]
  calc eLpNorm (G ∘ ι n) p (Measure.hausdorffMeasure (n : ℝ))
      ≤ eLpNorm (G ∘ ι n) p ((K : ℝ≥0∞) • volume) := eLpNorm_mono_measure _ hK
    _ = _ := by rw [eLpNorm_smul_measure_of_ne_zero (ENNReal.coe_ne_zero.mpr hK0), smul_eq_mul]

end Half

end Yamabe
