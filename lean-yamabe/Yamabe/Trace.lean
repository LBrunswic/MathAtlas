import Yamabe.Sobolev

/-!
# The trace inequality: Euclidean and on the model; the boundary measures of a compact manifold with boundary

Labels (NOT marked: partial, see SCOPE):

* `lem:positivity` — `Yamabegap.tex:715` (statement l.715–718, proof l.719–721): the two trace
  facts its proof uses, the compact trace `W^{1,2}(Σ) → L²(∂Σ)` (l.720) and, through the
  quotient eq:trace-sobolev (l.486–491), the trace theorem `W^{1,2}(Σ) → L^{p♯}(∂Σ)`: here, the
  Euclidean critical trace inequality, the trace theorem as a property of the measured model, and
  the boundary measures of the manifold layer. The trace theorem on the manifold,
  `Mfd.trace_embedding`, and its bridge `Mfd.Reads.traceIneq` are in `Yamabe.ManifoldTheorems`;
  the compact trace on a compact Riemannian manifold with boundary, `Mfd.trace_compact`, is
  stated in the scaffold module `YamabeScaffold.TraceCompact`.

> where the boundary norms are those of the trace of $u$, which is well defined in
> $L^{\psharp}(\partial\Sigma)$ by the trace theorem. (l.491)

> The trace operator $W^{1,2}(\Sigma)\to L^2(\partial\Sigma)$ is compact, so the traces converge
> to $c$ in $L^2(\partial\Sigma)$; but
> $\|u_k\|_{L^2(B_j)}\le\Vol(B_j)^{1/(N-1)}\|u_k\|_{L^{\psharp}(B_j)}\to0$, whence $c=0$. (l.720)

## The setting

As in `Yamabe.Sobolev`: `M` a compact smooth manifold with boundary modelled on
`EuclideanHalfSpace N`, `g` a smooth Riemannian metric, `μ` a locally-Lebesgue volume. A boundary
measure is any `σ` with `Mfd.IsBoundaryMeasure N σ`: carried by `∂M`, and near every point, in its
chart, bounded by a constant times the `(N-1)`-dimensional Hausdorff measure of the chart image
(the induced Riemannian area of `∂M`, or of one of its components `B_j`, is one). On the model,
`TraceIneq` is the trace theorem into `L^{p♯}(B_j)`.

## What is proved

`trace_halfLine` (the one-dimensional trace inequality `|f(0)|^q ≤ q ∫_0^∞ |f|^{q-1} |f'|` for
`f ∈ C¹_c(ℝ)`, `q ≥ 2`, by the fundamental theorem of calculus); `trace_halfSpace` (its integral
over the boundary hyperplane, by Tonelli: `∫_{ℝ^n} |u(0,z)|^q dz ≤ q ∫_{(0,∞) × ℝ^n} |u|^{q-1}
|∂_t u|` for `u ∈ C¹_c(ℝ × ℝ^n)`); `pSharp_sub_one` (`p♯ - 1 = p*/2`); `trace_critical` (the
critical trace inequality `‖u(0,·)‖^{p♯}_{L^{p♯}(ℝ^{N-1})} ≤ C ‖Du‖^{p♯}_{L²(ℝ^N)}`, from
`trace_halfSpace`, Hölder and Mathlib's Gagliardo–Nirenberg–Sobolev inequality);
`MeasuredModel.traceL2_of_traceIneq` (the trace into `L²(B_j)` from the trace into `L^{p♯}(B_j)`,
through the corrected eq:hoelder).

## What is stated with `sorry`

Nothing. Round 1 stated `Mfd.trace_compact` here with `sorry`; nothing depends on it, and
T-yamabe-graduate-analysis moved it unchanged to the scaffold module `YamabeScaffold.TraceCompact`,
downstream of `Mfd.rellich_kondrachov` (`Yamabe.RellichManifold`), which its proof needs. Round 1
also stated `Mfd.trace_embedding` here with `sorry`, and `Mfd.Reads.traceIneq` on it; the
integration of round 2 (T-yamabe-integrate-r2) deleted both and gave the proved copies of
`Yamabe.ManifoldTheorems` (through `Yamabe.HalfSpace` and `Yamabe.Localisation`, which import
this file) the round-1 names, with the round-1 statements unchanged.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ` compact Riemannian with boundary, `N ≥ 3` | ✓ carried, as in `Yamabe.Sobolev` (`μ` ⚠ read) |
| the induced measure of `∂Σ` | ⚠ read: any `σ` with `IsBoundaryMeasure N σ` (a weakening: only an upper bound is asked) |
| `u ∈ W^{1,2}(Σ)` | ⚠ read: `u ∈ C¹(M)` |

## SCOPE (disclosed)

* **Remark on l.720.** The proof of lem:positivity needs only the *continuity* of the trace
  `W^{1,2}(Σ) → L²(∂Σ)`, not its compactness: since `‖∇u_k‖_{L²} → 0` and `u_k → c` in `L²(Σ)`,
  `u_k → c` in `W^{1,2}(Σ)` strongly, and the continuity gives the traces' convergence.
  `lem_positivity` (`Yamabe.Rellich`) uses only `TraceIneq`; the compactness the paper states is
  `Mfd.trace_compact`, stated for completeness in the scaffold module `YamabeScaffold.TraceCompact`
  (`sorry`; what Mathlib lacks is listed there).
* Fubini over the boundary hyperplane is proved here (`trace_halfSpace`, for `C¹_c` functions on
  `ℝᴺ`). The half-space version with the gradient over the half-space only is
  `Half.trace_halfSpace'` (`Yamabe.HalfSpace`), and its chart localisation is
  `Mfd.local_trace` (`Yamabe.Localisation`); `Mfd.trace_embedding` assembles them.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Manifold ContDiff Bundle

noncomputable section

namespace Yamabe

/-! ## 1. The one-dimensional trace inequality (proved) -/

/-- The trace inequality on the half-line: for `f ∈ C¹_c(ℝ)` and `q ≥ 2`,
`|f(0)|^q ≤ q ∫_{(0,∞)} |f|^{q-1} |f'|`. -/
theorem trace_halfLine {q : ℝ} (hq : 2 ≤ q) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    |f 0| ^ q ≤ q * ∫ t in Ioi 0, |f t| ^ (q - 1) * |deriv f t| := by
  have hq0 : 0 < q := by linarith
  have hq2 : 1 ≤ q / 2 := by linarith
  -- `h = |f|^q = (f²)^{q/2}` is `C¹` with compact support
  set h : ℝ → ℝ := fun t => (f t ^ 2) ^ (q / 2) with hh
  set h' : ℝ → ℝ := fun t => 2 * f t * deriv f t * (q / 2) * (f t ^ 2) ^ (q / 2 - 1) with hh'
  have hfd : ∀ t, HasDerivAt f (deriv f t) t := fun t =>
    (hf.differentiable one_ne_zero t).hasDerivAt
  have hderiv : ∀ t, HasDerivAt h (h' t) t := by
    intro t
    have h1 : HasDerivAt (fun t => f t ^ 2) (2 * f t * deriv f t) t := by
      refine ((hfd t).fun_pow 2).congr_deriv ?_
      simp
    exact h1.rpow_const (Or.inr hq2)
  have hsq : ∀ x : ℝ, (x ^ 2) ^ (q / 2) = |x| ^ q := by
    intro x
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]
    congr 1
    push_cast
    ring
  have habs : ∀ t, |h' t| = q * (|f t| ^ (q - 1) * |deriv f t|) := by
    intro t
    have e1 : (f t ^ 2) ^ (q / 2 - 1) = |f t| ^ (q - 2) := by
      rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      push_cast
      ring
    have e2 : |f t| ^ (q - 1) = |f t| ^ (q - 2) * |f t| := by
      rw [show q - 1 = (q - 2) + 1 by ring, Real.rpow_add' (abs_nonneg _) (by linarith),
        Real.rpow_one]
    simp only [hh']
    rw [e1, e2, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), abs_of_pos (by positivity : (0:ℝ) < q / 2),
      abs_two]
    ring
  have hcont_h' : Continuous h' := by
    have hc1 : Continuous (deriv f) := hf.continuous_deriv le_rfl
    have hc2 : Continuous fun t => (f t ^ 2) ^ (q / 2 - 1) :=
      (Real.continuous_rpow_const (by linarith)).comp (hf.continuous.pow 2)
    exact (((continuous_const.mul hf.continuous).mul hc1).mul continuous_const).mul hc2
  have hsupp_h' : HasCompactSupport h' := by
    refine hfc.mono' fun t ht => subset_tsupport f ?_
    intro h0
    apply ht
    simp [hh', h0]
  have hint : IntegrableOn h' (Ioi 0) :=
    (hcont_h'.integrable_of_hasCompactSupport hsupp_h').integrableOn
  have hsupp_h : HasCompactSupport h := by
    have : h = (fun x : ℝ => (x ^ 2) ^ (q / 2)) ∘ f := rfl
    rw [this]
    refine hfc.comp_left ?_
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact Real.zero_rpow (by positivity)
  have hlim : Tendsto h atTop (𝓝 0) :=
    hsupp_h.is_zero_at_infty.mono_left atTop_le_cocompact
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hderiv x) hint hlim
  have h0 : h 0 = |f 0| ^ q := hsq (f 0)
  have hle : -∫ x in Ioi 0, h' x ≤ ∫ x in Ioi 0, |h' x| :=
    (neg_le_abs _).trans (abs_integral_le_integral_abs)
  have heq : ∫ x in Ioi 0, |h' x| = q * ∫ t in Ioi 0, |f t| ^ (q - 1) * |deriv f t| := by
    simp only [habs]
    rw [integral_const_mul]
  rw [← h0]
  linarith

/-- **The trace inequality on the half-space** `(0, ∞) × ℝ^n`, by Tonelli from `trace_halfLine`:
for `u ∈ C¹_c(ℝ × ℝ^n)` and `q ≥ 2`,
`∫_{ℝ^n} |u(0, z)|^q dz ≤ q ∫_{(0,∞) × ℝ^n} |u|^{q-1} |∂_t u|`. -/
theorem trace_halfSpace {n : ℕ} {q : ℝ} (hq : 2 ≤ q)
    {u : ℝ × EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    ∫⁻ z, ENNReal.ofReal (|u (0, z)| ^ q) ≤
      ENNReal.ofReal q * ∫⁻ p in Ioi (0 : ℝ) ×ˢ univ,
        ENNReal.ofReal (|u p| ^ (q - 1) * |fderiv ℝ u p (1, 0)|) := by
  set h : ℝ × EuclideanSpace ℝ (Fin n) → ℝ := fun p => |u p| ^ (q - 1) * |fderiv ℝ u p (1, 0)|
    with hh
  have hq1 : 0 < q - 1 := by linarith
  have hcont : Continuous h := by
    have h1 : Continuous fun p => fderiv ℝ u p (1, 0) :=
      (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact ((Real.continuous_rpow_const hq1.le).comp hu.continuous.abs).mul h1.abs
  have hnn : ∀ p, 0 ≤ h p := fun p => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (abs_nonneg _)
  have hmeas : Measurable fun p => ENNReal.ofReal (h p) :=
    ENNReal.measurable_ofReal.comp hcont.measurable
  set K : Set ℝ := Prod.fst '' tsupport u with hK
  have hKc : IsCompact K := hc.image continuous_fst
  have hzero : ∀ z t, t ∉ K → u (t, z) = 0 := fun z t ht =>
    image_eq_zero_of_notMem_tsupport fun hmem => ht ⟨(t, z), hmem, rfl⟩
  -- the slices `t ↦ u(t, z)`
  have hslice : ∀ z, |u (0, z)| ^ q ≤ q * ∫ t in Ioi 0, h (t, z) := by
    intro z
    set f : ℝ → ℝ := fun t => u (t, z) with hf
    have hfd : ∀ t, HasDerivAt f (fderiv ℝ u (t, z) (1, 0)) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => (t, z)) ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n))) t :=
        (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
      exact ((hu.differentiable one_ne_zero (t, z)).hasFDerivAt).comp_hasDerivAt t h1
    have hfC : ContDiff ℝ 1 f := hu.comp (contDiff_id.prodMk contDiff_const)
    have hfc : HasCompactSupport f := HasCompactSupport.intro hKc fun t ht => hzero z t ht
    have h2 := trace_halfLine hq hfC hfc
    have hd : ∀ t, deriv f t = fderiv ℝ u (t, z) (1, 0) := fun t => (hfd t).deriv
    simpa only [hd] using h2
  have hint : ∀ z, ENNReal.ofReal (∫ t in Ioi 0, h (t, z)) =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (h (t, z)) := by
    intro z
    have hcz : Continuous fun t => h (t, z) := hcont.comp (continuous_id.prodMk continuous_const)
    have hsz : HasCompactSupport fun t => h (t, z) := HasCompactSupport.intro hKc fun t ht => by
      simp only [hh, hzero z t ht, abs_zero, Real.zero_rpow hq1.ne', zero_mul]
    exact ofReal_integral_eq_lintegral_ofReal
      (hcz.integrable_of_hasCompactSupport hsz).integrableOn (ae_of_all _ fun t => hnn _)
  calc ∫⁻ z, ENNReal.ofReal (|u (0, z)| ^ q)
      ≤ ∫⁻ z, ENNReal.ofReal q * ENNReal.ofReal (∫ t in Ioi 0, h (t, z)) :=
        lintegral_mono fun z => by
          rw [← ENNReal.ofReal_mul (by linarith)]
          exact ENNReal.ofReal_le_ofReal (hslice z)
    _ = ENNReal.ofReal q * ∫⁻ z, ∫⁻ t in Ioi 0, ENNReal.ofReal (h (t, z)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp only [hint]
    _ = ENNReal.ofReal q * ∫⁻ p in Ioi (0 : ℝ) ×ˢ univ, ENNReal.ofReal (h p) := by
        congr 1
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
          lintegral_prod_symm' _ hmeas]

lemma pSharp_sub_one (N : ℕ) (hN : 3 ≤ N) : pSharp N - 1 = pStar N / 2 := by
  have := three_le_cast hN
  have h2 : (N : ℝ) - 2 ≠ 0 := by linarith
  unfold pSharp pStar
  field_simp
  ring

/-- **The critical trace inequality on `ℝ^N = ℝ × ℝ^n`**, `N = n + 1 ≥ 3` (the inequality of
Escobar1988, with a non-sharp constant): for `u ∈ C¹_c(ℝ × ℝ^n)`, its trace on the hyperplane
`{0} × ℝ^n` satisfies `∫_{ℝ^n} |u(0, z)|^{p♯} dz ≤ C ‖Du‖_{L²(ℝ^N)}^{p♯}`. From `trace_halfSpace`
at `q = p♯`, Hölder on the half-space (`2(p♯ - 1) = p*`) and Mathlib's Gagliardo–Nirenberg–Sobolev
inequality on `ℝ × ℝ^n`. The half-space form (`‖Du‖` over `(0, ∞) × ℝ^n` only, for functions on
the half-space) is `Half.trace_halfSpace'` (`Yamabe.HalfSpace`, through the reflection). -/
theorem trace_critical {n : ℕ} (hN : 3 ≤ n + 1) :
    ∃ C : ℝ≥0, ∀ u : ℝ × EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 u → HasCompactSupport u →
      ∫⁻ z, ‖u (0, z)‖ₑ ^ pSharp (n + 1) ≤
        C * eLpNorm (fderiv ℝ u) 2 volume ^ pSharp (n + 1) := by
  set N := n + 1 with hNdef
  haveI : (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  have hN' := three_le_cast hN
  have hps : 2 ≤ pSharp N := two_le_pSharp hN
  have hps1 : 0 ≤ pSharp N - 1 := by linarith
  have hpst : 0 < pStar N := pStar_pos hN
  set CS : ℝ≥0 := SNormLESNormFDerivOfEqConst ℝ
    (volume : Measure (ℝ × EuclideanSpace ℝ (Fin n))) ((2 : ℝ≥0) : ℝ) with hCS
  refine ⟨(pSharp N).toNNReal * CS ^ (pSharp N - 1), fun u hu hc => ?_⟩
  -- Sobolev on `ℝ × ℝ^n`
  have hfin : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin n)) = N := by
    rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, hNdef, add_comm]
  have hp' : (((pStar N).toNNReal : ℝ≥0) : ℝ)⁻¹ =
      ((2 : ℝ≥0) : ℝ)⁻¹ - (Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin n)) : ℝ)⁻¹ := by
    rw [hfin, Real.coe_toNNReal _ hpst.le]
    push_cast
    exact pStar_inv N hN
  have hS := eLpNorm_le_eLpNorm_fderiv_of_eq (F := ℝ) volume hu hc (p := 2)
    (p' := (pStar N).toNNReal) (by norm_num) (by rw [hfin]; omega) hp'
  have e0 : ((((pStar N).toNNReal : ℝ≥0) : ℝ≥0∞)) = ENNReal.ofReal (pStar N) := rfl
  rw [e0] at hS
  simp only [ENNReal.coe_ofNat] at hS
  set D := eLpNorm (fderiv ℝ u) 2 volume with hD
  set Lu := eLpNorm u (ENNReal.ofReal (pStar N)) volume with hLu
  -- the half-space trace inequality at `q = p♯`
  have hT := trace_halfSpace hps hu hc
  set ℍ : Set (ℝ × EuclideanSpace ℝ (Fin n)) := Ioi (0 : ℝ) ×ˢ univ with hℍ
  have hlhs : ∫⁻ z, ‖u (0, z)‖ₑ ^ pSharp N = ∫⁻ z, ENNReal.ofReal (|u (0, z)| ^ pSharp N) := by
    refine lintegral_congr fun z => ?_
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by linarith)]
  -- Hölder with `2 (p♯ - 1) = p*`
  set f : ℝ × EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun p => ENNReal.ofReal (|u p| ^ (pSharp N - 1))
  set g : ℝ × EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun p => ENNReal.ofReal |fderiv ℝ u p (1, 0)|
  have hfm : AEMeasurable f (volume.restrict ℍ) :=
    (ENNReal.measurable_ofReal.comp
      ((Real.continuous_rpow_const (by linarith)).comp hu.continuous.abs).measurable).aemeasurable
  have hgm : AEMeasurable g (volume.restrict ℍ) :=
    (ENNReal.measurable_ofReal.comp
      (((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).abs).measurable).aemeasurable
  have hprod : ∫⁻ p in ℍ, ENNReal.ofReal (|u p| ^ (pSharp N - 1) * |fderiv ℝ u p (1, 0)|) =
      ∫⁻ p in ℍ, (f * g) p := by
    refine lintegral_congr fun p => ?_
    simp only [Pi.mul_apply, f, g]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict ℍ) Real.HolderConjugate.two_two
    hfm hgm
  have hf2 : ∫⁻ p in ℍ, f p ^ (2 : ℝ) ≤ Lu ^ pStar N := by
    have e1 : ∀ p, f p ^ (2 : ℝ) = ‖u p‖ₑ ^ pStar N := by
      intro p
      simp only [f]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by norm_num),
        ← Real.rpow_mul (abs_nonneg _), pSharp_sub_one N hN,
        show pStar N / 2 * 2 = pStar N by ring, Real.enorm_eq_ofReal_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpst.le]
    simp only [e1]
    rw [hLu, eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hpst) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hpst.le, ← ENNReal.rpow_mul, one_div_mul_cancel hpst.ne',
      ENNReal.rpow_one]
    exact setLIntegral_le_lintegral _ _
  have hg2 : ∫⁻ p in ℍ, g p ^ (2 : ℝ) ≤ D ^ (2 : ℝ) := by
    have e1 : ∀ p, g p ^ (2 : ℝ) ≤ ‖fderiv ℝ u p‖ₑ ^ (2 : ℝ) := by
      intro p
      simp only [g]
      gcongr
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := (fderiv ℝ u p).le_opNorm ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n)))
      have h2 : ‖((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n)))‖ = 1 := by simp [Prod.norm_def]
      rw [h2, mul_one, Real.norm_eq_abs] at h1
      exact h1
    calc ∫⁻ p in ℍ, g p ^ (2 : ℝ) ≤ ∫⁻ p in ℍ, ‖fderiv ℝ u p‖ₑ ^ (2 : ℝ) := lintegral_mono e1
      _ ≤ ∫⁻ p, ‖fderiv ℝ u p‖ₑ ^ (2 : ℝ) := setLIntegral_le_lintegral _ _
      _ = D ^ (2 : ℝ) := by
        rw [hD, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
          ← ENNReal.rpow_mul]
        norm_num
  have hmain : ∫⁻ p in ℍ, (f * g) p ≤ Lu ^ (pSharp N - 1) * D := by
    refine hH.trans ?_
    gcongr
    · calc (∫⁻ p in ℍ, f p ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ (Lu ^ pStar N) ^ (1 / (2 : ℝ)) := by
            gcongr
        _ = Lu ^ (pSharp N - 1) := by
            rw [← ENNReal.rpow_mul, pSharp_sub_one N hN]
            congr 1
            ring
    · calc (∫⁻ p in ℍ, g p ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ (D ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
            gcongr
        _ = D := by
            rw [← ENNReal.rpow_mul]
            norm_num
  have hLu' : Lu ^ (pSharp N - 1) ≤ ((CS : ℝ≥0∞) * D) ^ (pSharp N - 1) :=
    ENNReal.rpow_le_rpow hS hps1
  rw [hlhs]
  calc ∫⁻ z, ENNReal.ofReal (|u (0, z)| ^ pSharp N)
      ≤ ENNReal.ofReal (pSharp N) * ∫⁻ p in ℍ,
          ENNReal.ofReal (|u p| ^ (pSharp N - 1) * |fderiv ℝ u p (1, 0)|) := hT
    _ ≤ ENNReal.ofReal (pSharp N) * (((CS : ℝ≥0∞) * D) ^ (pSharp N - 1) * D) := by
        rw [hprod]
        gcongr
        exact hmain.trans (mul_le_mul_left hLu' D)
    _ = ((pSharp N).toNNReal * CS ^ (pSharp N - 1) : ℝ≥0) * D ^ pSharp N := by
        have e2 : D ^ pSharp N = D ^ (pSharp N - 1) * D := by
          conv_lhs => rw [show pSharp N = (pSharp N - 1) + 1 by ring]
          rw [ENNReal.rpow_add_of_nonneg _ _ hps1 zero_le_one, ENNReal.rpow_one]
        rw [ENNReal.mul_rpow_of_nonneg _ _ hps1, ENNReal.coe_mul,
          ENNReal.coe_rpow_of_nonneg _ hps1, e2,
          show ENNReal.ofReal (pSharp N) = ((pSharp N).toNNReal : ℝ≥0∞) from rfl]
        ring

/-! ## 2. The model layer -/

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : FrameMetric X N)

/-- The trace theorem on the model: every trace lies in `L^{p♯}(B_j)` (l.491) and
`‖tr u‖²_{L^{p♯}(B_j)} ≤ C ‖u‖²_{W^{1,2}(Σ)}`. -/
def TraceIneq : Prop :=
  ∃ C : ℝ, ∀ u : D, ∀ j, MemLp (M.tr u) (ENNReal.ofReal (pSharp N)) (M.bvol g j) ∧
    normSq (M.bvol g j) (pSharp N) (M.tr u) ≤ C * M.w12Sq g u

/-- The trace into `L²(B_j)` (l.720), from the trace into `L^{p♯}(B_j)` and the corrected
eq:hoelder (`hoelder_boundary`): `‖tr u‖²_{L²(B_j)} ≤ C' ‖u‖²_{W^{1,2}(Σ)}`. -/
theorem traceL2_of_traceIneq (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hT : M.TraceIneq g) :
    ∃ C : ℝ, ∀ u : D, ∀ j, MemLp (M.tr u) 2 (M.bvol g j) ∧
      normSq (M.bvol g j) 2 (M.tr u) ≤ C * M.w12Sq g u := by
  obtain ⟨C, hC⟩ := hT
  refine ⟨(∑ j, (M.bvol g j Set.univ).toReal ^ (1 / ((N : ℝ) - 1))) * max C 0, fun u j => ?_⟩
  obtain ⟨hmem, hle⟩ := hC u j
  have hmem2 : MemLp (M.tr u) 2 (M.bvol g j) :=
    hmem.mono_exponent (by
      rw [← ENNReal.ofReal_ofNat]; exact ENNReal.ofReal_le_ofReal (two_le_pSharp hN))
  refine ⟨hmem2, ?_⟩
  have hH := hoelder_boundary hN hmem
  have ha : 0 ≤ (M.bvol g j Set.univ).toReal ^ (1 / ((N : ℝ) - 1)) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hw := M.w12Sq_nonneg g u
  have hsum : (M.bvol g j Set.univ).toReal ^ (1 / ((N : ℝ) - 1)) ≤
      ∑ j, (M.bvol g j Set.univ).toReal ^ (1 / ((N : ℝ) - 1)) :=
    Finset.single_le_sum (f := fun j => (M.bvol g j Set.univ).toReal ^ (1 / ((N : ℝ) - 1)))
      (fun j _ => Real.rpow_nonneg ENNReal.toReal_nonneg _) (Finset.mem_univ j)
  calc normSq (M.bvol g j) 2 (M.tr u)
      ≤ (M.bvol g j Set.univ).toReal ^ (1 / ((N : ℝ) - 1)) *
          normSq (M.bvol g j) (pSharp N) (M.tr u) := hH
    _ ≤ (M.bvol g j Set.univ).toReal ^ (1 / ((N : ℝ) - 1)) * (C * M.w12Sq g u) :=
        mul_le_mul_of_nonneg_left hle ha
    _ ≤ (M.bvol g j Set.univ).toReal ^ (1 / ((N : ℝ) - 1)) * (max C 0 * M.w12Sq g u) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_left _ _) hw) ha
    _ ≤ (∑ j, (M.bvol g j Set.univ).toReal ^ (1 / ((N : ℝ) - 1))) * (max C 0 * M.w12Sq g u) :=
        mul_le_mul_of_nonneg_right hsum (mul_nonneg (le_max_right _ _) hw)
    _ = _ := by ring

end MeasuredModel

/-! ## 3. The manifold layer -/

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M]

variable (N) in
/-- `σ` is a boundary measure on `M`: it is carried by `∂M`, and near every point `x₀`, in the
chart at `x₀`, it is at most a constant times the `(N-1)`-dimensional Hausdorff measure of the
chart image (which lies in the boundary hyperplane `{y₀ = 0}`). The induced Riemannian area of
`∂M`, and its restriction to any union of components, are such measures. -/
def IsBoundaryMeasure (σ : Measure M) : Prop :=
  σ ((𝓡∂ N).boundary M)ᶜ = 0 ∧
    ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ C : ℝ≥0, ∀ A ⊆ U ∩ (chartAt (EuclideanHalfSpace N) x₀).source,
      MeasurableSet A →
        σ A ≤ C * Measure.hausdorffMeasure ((N : ℝ) - 1) (extChartAt (𝓡∂ N) x₀ '' A)

end Mfd

end Yamabe
