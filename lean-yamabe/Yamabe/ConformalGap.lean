import Yamabe.ClosedLeaves
import Yamabe.TraceInterp

/-!
# Yamabe § 3, the gap and the conformal gap: `δ(Σ) ≤ δ_conf(Σ) = σ^∂(Σ) − Y_[g](Σ)`

Label (lines of `papers/yamabe/legacy/labeled/Yamabegap.tex`). NOT marked: the row is partial
(the model's readings of OQ-133 (a)/(b) and OQ-93, see SCOPE).

* `rem:conformal-gap` — `Yamabegap.tex:421` (l.421–424): `EH(Σ, g) ≥ Y_[g](Σ)` by
  eq:relative-yamabe, hence `δ(Σ) ≤ δ_conf(Σ)`, with equality for constant scalar curvature,
  minimal boundary and `R_g ≤ 0` (fact (iii), l.334, = lem:kobayashi (a)); and « Sec. torus treats
  minimal boundaries, for which `δ = δ_conf` ».

> By \eqref{eq:relative-yamabe}, $\EH(\Sigma,\g)\ge\Y_{[\g]}(\Sigma)$, so that
> $\delta(\Sigma)\le\delta_{\mathrm{conf}}(\Sigma):=\sigbd(\Sigma)-\Y_{[\g]}(\Sigma)$, with equality
> when $\g$ has constant scalar curvature, minimal boundary and $\Rs_\g\le0$ (fact (iii) above).
> Sec.~\ref{sec:torus} treats minimal boundaries, for which $\delta=\delta_{\mathrm{conf}}$.
> (l.423)

> \item[(iii)] If $\g$ has constant scalar curvature and minimal boundary, then $\Rs_\g\le0$ if and
> only if $\Y_{[\g]}(\Sigma)\le0$, and in that case $\EH(\Sigma,\g)=\Y_{[\g]}(\Sigma)$
> (Lemma~\ref{lem:kobayashi}, cf.\ \cite[Proposition~6.1]{MR1957657}). (l.334)

> \paragraph*{Setting.} A metric $\g$ on $\Sigma$ is called \emph{Schwarzschild-like punctured} if
> $\g$ has constant scalar curvature, $\partial\Sigma$ is minimal ($H_\g\equiv0$), and each
> $(B_j,\g|_{B_j})$ is a round sphere of radius $r_j$. (l.467)

## The model

As in `Yamabe.BoundaryGap`: `Σ` is a `MeasuredModel`, `g` a `CurvedMetric`, `Y_[g]` the strict
library's infimum of the conformal energies over the positive competitors (eq:relative-yamabe
through the conformal law, `Y_eq_inf_EH`), `σ^∂ = sigmaBdry C` the `EReal` supremum of `Y_[g']`
over a parameter set `C` of metrics (kb/0083, kb/0090), `δ = gapBdryE C g`, and for a real value
`σb` of `σ^∂`, `δ = gapBdry σb g`. New here: `deltaConfE C g = σ^∂ − Y_[g]` (`EReal`) and
`deltaConf σb g = σb − Y_[g]` (real), the conformal gap.

## What is proved (no `sorry`, standard axioms)

* `conformalGap_Y_le_EH`: `Y_[g] ≤ EH(Σ, g)` for **any** boundary, given that the conformal
  energies are bounded below (`Y_[g] > −∞`, the model's reading of the finiteness of the
  infimum; for `Vol = 0` both sides are `0`);
* `conformalGap_Y_le_EH_of_minimal`: the same, unconditionally, on a minimal boundary (the strict
  `Y_le_EH`, plus the `Vol = 0` case);
* `rem_conformal_gap_le`, `rem_conformal_gap_le_of_minimal`: `δ ≤ δ_conf` (`EReal` and real);
* `rem_conformal_gap_eq`: equality for `R_g ≡ c ≤ 0` and minimal boundary (fact (iii));
* `Mfd.Reads.conformalGap_bddBelow`: on a model reading a compact manifold with boundary, the
  conformal energies are bounded below **for every bounded `H_g`**: the interpolation trace
  inequality (`Mfd.trace_interp`) absorbs the boundary term into the Dirichlet term, and the
  interior Hölder inequality bounds `‖u‖²_{L²}` by `Vol^{2/N} ‖u‖²_{L^{p*}}`;
* `Mfd.Reads.rem_conformal_gap`: the assembly on such a model: `δ ≤ δ_conf` for every metric (no
  minimality), equality for constant `R_g ≤ 0` and minimal boundary, and the torus sentence:
  equality for constant `R_g` and minimal boundary as soon as `Y_[g] ≤ 0` (prop:nonpositive's first
  sentence; fact (iii)'s converse through lem:kobayashi (b), `Mfd.Reads.prop_nonpositive_csc`);
* `rem_conformal_gap_toy_strict`: **finding** — on the two-point toy model with one boundary
  component, `R_g ≡ 100` (constant) and `H_g ≡ 0` (minimal), `δ < δ_conf`: minimality alone,
  even with constant scalar curvature, does not give `δ = δ_conf`; the sign `R_g ≤ 0` is needed;
* `rem_conformal_gap_toy_eq`: the equality's hypotheses are satisfiable, not vacuously
  (`toyCurved`, `R_g ≡ −1`, minimal boundary: `δ = δ_conf = 0` over `C = {g}`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `(Σ, g)` compact, `N ≥ 3`, `∂Σ = ⊔ B_j` | ⚠ read in the measured model (OQ-44), compactness as `IsFiniteMeasure (vol_g)`; in `Mfd.Reads.*` a model reading a compact manifold with boundary (OQ-93 (a)/(b)); `N ≥ 3` ✓ carried |
| `EH ≥ Y_[g]` "by eq:relative-yamabe", any `g` | ✓ model: carried as `BddBelow` of the conformal energies (`Y_[g] > −∞`, true on a compact manifold); manifold: discharged (`conformalGap_bddBelow`) |
| `σ^∂(Σ) = sup_{[g]} Y_[g](Σ)` | ⚠ read (OQ-133 (b)): `EReal` sup over a parameter set `C`; real form for every value `σb` |
| equality: `R_g` constant | ✓ carried; model: `R_g = c` a.e.; manifold: `R_g x = c` everywhere |
| equality: minimal boundary | ✓ carried (`MinimalBoundary`, a.e.) |
| equality: `R_g ≤ 0` | ✓ carried as `c ≤ 0`; torus clause: as `Y_[g] ≤ 0` (fact (iii)) |
| `u ∈ W^{1,2}` | ⚠ read as `C¹(M)` on the manifold layer (OQ-93 (b)); measurable values on the model (`hD`) |

## SCOPE (disclosed)

* The readings are T-yamabe-boundary-gap's (OQ-133 (a)/(b)) and the manifold layer's (OQ-93):
  the row is partial.
* `EH ≥ Y` on the model needs `Y_[g] > −∞`: the model's `Y` is a `Real.sInf`, junk `0` on a set
  unbounded below, and nothing in the abstract model bounds the boundary term
  `2(N−1) ∫ H u²` for non-minimal `H`. On a minimal boundary the bound is lem:kobayashi (a); on a
  model reading a manifold it is proved here from the interpolation trace inequality.
* The torus sentence is read in Sec. torus's setting (constant scalar curvature and minimal
  boundary, l.467), with prop:nonpositive's first sentence `Y_[g] ≤ 0` carried (its own row).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Manifold ContDiff

noncomputable section

namespace Yamabe

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n)

/-- The conformal gap `δ_conf(Σ) = σ^∂(Σ) − Y_[g](Σ)` (l.423), in `EReal`. -/
def deltaConfE (C : Set (CurvedMetric X N)) (g : CurvedMetric X N) : EReal :=
  M.sigmaBdry C - (M.Y g : EReal)

/-- The conformal gap for a real value `σb` of `σ^∂(Σ)`. -/
def deltaConf (σb : ℝ) (g : CurvedMetric X N) : ℝ := σb - M.Y g

/-- With `Vol(Σ, g) = 0`, `EH(Σ, g) = Y_[g](Σ) = 0`. -/
theorem conformalGap_EH_Y_of_vol_eq_zero (hN : 3 ≤ N) (g : CurvedMetric X N)
    (hV : M.vol g.toFrameMetric = 0) : M.EH g = 0 ∧ M.Y g = 0 := by
  have hN' := three_le_cast hN
  refine ⟨?_, ?_⟩
  · unfold EH
    rw [hV]
    have : (((N : ℝ) - 2) / N) ≠ 0 := by
      have : (0 : ℝ) < ((N : ℝ) - 2) / N := div_pos (by linarith) (by linarith)
      exact this.ne'
    simp [Real.zero_rpow this]
  · unfold Y infConf
    have hempty : {u | u ∈ {u | M.Pos u} ∧ M.Adm g.toFrameMetric u} = ∅ := by
      ext u
      simp [Adm, normSq, hV]
    rw [hempty, Set.image_empty, Real.sInf_empty]

/-- `Y_[g](Σ) ≤ EH(Σ, g)` for any boundary, when the conformal energies are bounded below
(`Y_[g] > −∞`): `1` is a competitor. -/
theorem conformalGap_Y_le_EH (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hbdd : BddBelow (M.confEnergy g '' {u | u ∈ {u | M.Pos u} ∧ M.Adm g.toFrameMetric u})) :
    M.Y g ≤ M.EH g := by
  by_cases hV : M.vol g.toFrameMetric = 0
  · obtain ⟨h1, h2⟩ := M.conformalGap_EH_Y_of_vol_eq_zero hN g hV
    rw [h1, h2]
  have hVpos : 0 < (M.vol g.toFrameMetric Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  have hadm : M.Adm g.toFrameMetric M.one := by
    unfold Adm
    rw [M.val_one, normSq_one _ (pStar_pos hN)]
    exact Real.rpow_pos_of_pos hVpos _
  have hpos1 : M.Pos M.one := fun x => by rw [M.val_one]; exact one_pos
  rw [M.EH_eq_confEnergy_one g hN]
  exact csInf_le hbdd ⟨M.one, ⟨hpos1, hadm⟩, rfl⟩

/-- `Y_[g](Σ) ≤ EH(Σ, g)` on a minimal boundary, with no further hypothesis. -/
theorem conformalGap_Y_le_EH_of_minimal (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) : M.Y g ≤ M.EH g := by
  by_cases hV : M.vol g.toFrameMetric = 0
  · obtain ⟨h1, h2⟩ := M.conformalGap_EH_Y_of_vol_eq_zero hN g hV
    rw [h1, h2]
  exact M.Y_le_EH g hN hV hD hH

/-- From `Y ≤ EH` to `δ ≤ δ_conf`, in `EReal` and for every real value of `σ^∂`. -/
theorem conformalGap_le_of_Y_le_EH (C : Set (CurvedMetric X N)) {g : CurvedMetric X N}
    (h : M.Y g ≤ M.EH g) :
    M.gapBdryE C g ≤ M.deltaConfE C g ∧ ∀ σb : ℝ, M.gapBdry σb g ≤ M.deltaConf σb g := by
  refine ⟨?_, fun σb => ?_⟩
  · unfold gapBdryE deltaConfE
    exact EReal.sub_le_sub le_rfl (EReal.coe_le_coe_iff.mpr h)
  · unfold gapBdry deltaConf
    linarith

/-- rem:conformal-gap, the inequality, any boundary: `δ(Σ) ≤ δ_conf(Σ)` when `Y_[g] > −∞`. -/
theorem rem_conformal_gap_le (hN : 3 ≤ N) (C : Set (CurvedMetric X N)) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hbdd : BddBelow (M.confEnergy g '' {u | u ∈ {u | M.Pos u} ∧ M.Adm g.toFrameMetric u})) :
    M.gapBdryE C g ≤ M.deltaConfE C g ∧ ∀ σb : ℝ, M.gapBdry σb g ≤ M.deltaConf σb g := by
  exact M.conformalGap_le_of_Y_le_EH C (M.conformalGap_Y_le_EH hN g hbdd)

/-- rem:conformal-gap, the inequality on a minimal boundary, unconditionally. -/
theorem rem_conformal_gap_le_of_minimal (hN : 3 ≤ N) (C : Set (CurvedMetric X N))
    (g : CurvedMetric X N) [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) :
    M.gapBdryE C g ≤ M.deltaConfE C g ∧ ∀ σb : ℝ, M.gapBdry σb g ≤ M.deltaConf σb g := by
  exact M.conformalGap_le_of_Y_le_EH C (M.conformalGap_Y_le_EH_of_minimal hN g hD hH)

/-- rem:conformal-gap, the equality: constant `R_g = c ≤ 0` and minimal boundary give
`δ(Σ) = δ_conf(Σ)` (fact (iii) = lem:kobayashi (a)). -/
theorem rem_conformal_gap_eq (hN : 3 ≤ N) (C : Set (CurvedMetric X N)) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {c : ℝ} (hc : c ≤ 0)
    (hR : ∀ᵐ x ∂(M.vol g.toFrameMetric), g.R x = c) :
    M.gapBdryE C g = M.deltaConfE C g ∧ ∀ σb : ℝ, M.gapBdry σb g = M.deltaConf σb g := by
  have h := M.EH_eq_Y g hN hD hH hc hR
  refine ⟨?_, fun σb => ?_⟩
  · unfold gapBdryE deltaConfE
    rw [h]
  · unfold gapBdry deltaConf
    rw [h]

end MeasuredModel

/-! ## On a model reading a compact manifold with boundary -/

namespace Mfd

variable {N : ℕ} [NeZero N]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M] [MeasurableSpace M] [BorelSpace M]

namespace Reads

variable {D : Type*} [AddCommGroup D] [Module ℝ D] {n : ℕ} {Mm : MeasuredModel M D N n}
  {g : RiemannianMetric N M} {μ : Measure M} {σ : Fin n → Measure M}

/-- On a model reading a compact manifold with boundary, the conformal energies of every curved
metric (any bounded `R_g`, `H_g`) are bounded below: `Y_[g](Σ) > −∞`. -/
theorem conformalGap_bddBelow (hN : 3 ≤ N) [CompactSpace M] [T2Space M]
    {gc : CurvedMetric M N} (hr : Reads Mm gc.toFrameMetric g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hσ : ∀ j, IsBoundaryMeasure N (σ j)) :
    BddBelow (Mm.confEnergy gc '' {u | u ∈ {u | Mm.Pos u} ∧ Mm.Adm gc.toFrameMetric u}) := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  have hN' := three_le_cast hN
  obtain ⟨Rb, hRb⟩ := gc.R_bdd
  obtain ⟨Hb, hHb⟩ := gc.H_bdd
  set R0 := max Rb 0 with hR0
  set H0 := max Hb 0 with hH0
  have hR0x : ∀ x, |gc.R x| ≤ R0 := fun x => (hRb x).trans (le_max_left _ _)
  have hH0x : ∀ x, |gc.H x| ≤ H0 := fun x => (hHb x).trans (le_max_left _ _)
  have hR00 : 0 ≤ R0 := le_max_right _ _
  have hH00 : 0 ≤ H0 := le_max_right _ _
  choose Ct hCt using fun j => trace_interp g hμ (hσ j)
  set S : ℝ := ∑ j, ((Ct j : ℝ)) ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  set A : ℝ := 4 * ((N : ℝ) - 1) * H0 * S with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ (N : ℝ) - 1 := by linarith
    positivity
  have haN := aN_pos hN
  set δ : ℝ := aN N / (aN N + A) with hδdef
  have hδ : 0 < δ := div_pos haN (by linarith)
  have hδ1 : δ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hAδ : A * δ ^ 2 ≤ aN N := by
    have h1 : A * δ ^ 2 ≤ A * δ := by
      apply mul_le_mul_of_nonneg_left _ hA0
      nlinarith
    have h2 : A * δ = aN N * (A / (aN N + A)) := by rw [hδdef]; ring
    have h3 : A / (aN N + A) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    nlinarith
  set K0 : ℝ := R0 + 2 * ((N : ℝ) - 1) * H0 * (2 * S * (δ + δ⁻¹) ^ 2) with hK0
  have hK00 : 0 ≤ K0 := by
    have : 0 ≤ (N : ℝ) - 1 := by linarith
    positivity
  set V2 : ℝ := (μ Set.univ).toReal ^ (2 / (N : ℝ)) with hV2
  refine ⟨-(K0 * V2), ?_⟩
  rintro _ ⟨u, ⟨-, hadm⟩, rfl⟩
  set f := Mm.val u with hfdef
  have hf : IsC1 N f := hr.c1 u
  have ha : eLpNorm (gradNorm g f) 2 μ ≠ ⊤ := (eLpNorm_gradNorm_lt_top g hf).ne
  have hb : eLpNorm f 2 μ ≠ ⊤ := (memLp_of_isC1 hf 2).eLpNorm_ne_top
  set Gr := (eLpNorm (gradNorm g f) 2 μ).toReal with hGr
  set L := (eLpNorm f 2 μ).toReal with hL
  have hdir : Mm.dirichlet gc.toFrameMetric u = Gr ^ 2 := by
    rw [hr.dirichlet_eq u]; unfold normSq; rw [ENNReal.ofReal_ofNat]
  have hL2 : normSq μ 2 f = L ^ 2 := by unfold normSq; rw [ENNReal.ofReal_ofNat]
  -- the interpolation trace inequality, squared, on each `B_j`
  have hT : ∀ j, normSq (σ j) 2 f ≤
      2 * (Ct j : ℝ) ^ 2 * δ ^ 2 * Gr ^ 2 + 2 * (Ct j : ℝ) ^ 2 * (δ + δ⁻¹) ^ 2 * L ^ 2 := by
    intro j
    have h := hCt j δ hδ f hf
    unfold w12 at h
    have hw : eLpNorm (gradNorm g f) 2 μ + eLpNorm f 2 μ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ha, hb⟩
    have h1 : ENNReal.ofReal δ * (eLpNorm (gradNorm g f) 2 μ + eLpNorm f 2 μ) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw
    have h2 : ENNReal.ofReal δ⁻¹ * eLpNorm f 2 μ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb
    have hrhs : (Ct j : ℝ≥0∞) * (ENNReal.ofReal δ * (eLpNorm (gradNorm g f) 2 μ + eLpNorm f 2 μ) +
        ENNReal.ofReal δ⁻¹ * eLpNorm f 2 μ) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.mpr ⟨h1, h2⟩)
    have h' := ENNReal.toReal_mono hrhs h
    rw [ENNReal.toReal_mul, ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_add ha hb, ENNReal.toReal_ofReal hδ.le,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hδ.le), ENNReal.coe_toReal] at h'
    rw [← hGr, ← hL] at h'
    have hT0 : 0 ≤ (eLpNorm f 2 (σ j)).toReal := ENNReal.toReal_nonneg
    have hC0 : 0 ≤ (Ct j : ℝ) := (Ct j).2
    have hsq := pow_le_pow_left₀ hT0 h' 2
    have he : normSq (σ j) 2 f = (eLpNorm f 2 (σ j)).toReal ^ 2 := by
      unfold normSq; rw [ENNReal.ofReal_ofNat]
    rw [he]
    have hx : ((Ct j : ℝ) * (δ * (Gr + L) + δ⁻¹ * L)) ^ 2 =
        (Ct j : ℝ) ^ 2 * (δ * Gr + (δ + δ⁻¹) * L) ^ 2 := by ring
    rw [hx] at hsq
    nlinarith [mul_nonneg (sq_nonneg (Ct j : ℝ)) (sq_nonneg (δ * Gr - (δ + δ⁻¹) * L))]
  -- the boundary terms
  have hB : ∀ j, -H0 * (2 * (Ct j : ℝ) ^ 2 * δ ^ 2 * Gr ^ 2 +
      2 * (Ct j : ℝ) ^ 2 * (δ + δ⁻¹) ^ 2 * L ^ 2) ≤ ∫ x, gc.H x * f x ^ 2 ∂(σ j) := by
    intro j
    have hmem2 := memLp_two_of_isC1 g hμ (hσ j) hf
    have hsq : Integrable (fun x => f x ^ 2) (σ j) := hmem2.integrable_sq
    have hHi : Integrable (fun x => gc.H x * f x ^ 2) (σ j) :=
      hsq.bdd_mul gc.H_measurable.aestronglyMeasurable
        (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hH0x x)
    have hle : -H0 * normSq (σ j) 2 f ≤ ∫ x, gc.H x * f x ^ 2 ∂(σ j) := by
      rw [← integral_sq_eq_normSq hmem2, ← integral_const_mul]
      refine integral_mono (hsq.const_mul _) hHi fun x => ?_
      exact mul_le_mul_of_nonneg_right (neg_le_of_abs_le (hH0x x)) (sq_nonneg _)
    have := mul_le_mul_of_nonneg_left (hT j) hH00
    linarith
  -- the interior term
  have hRi : -R0 * L ^ 2 ≤ ∫ x, gc.R x * f x ^ 2 ∂μ := by
    have hmem2 : MemLp f 2 μ := memLp_of_isC1 hf 2
    have hsq : Integrable (fun x => f x ^ 2) μ := hmem2.integrable_sq
    have hRint : Integrable (fun x => gc.R x * f x ^ 2) μ :=
      hsq.bdd_mul gc.R_measurable.aestronglyMeasurable
        (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hR0x x)
    rw [← hL2, ← integral_sq_eq_normSq hmem2, ← integral_const_mul]
    refine integral_mono (hsq.const_mul _) hRint fun x => ?_
    exact mul_le_mul_of_nonneg_right (neg_le_of_abs_le (hR0x x)) (sq_nonneg _)
  have hsum : S * (-H0 * (2 * δ ^ 2 * Gr ^ 2 + 2 * (δ + δ⁻¹) ^ 2 * L ^ 2)) ≤
      ∑ j, ∫ x, gc.H x * f x ^ 2 ∂(σ j) := by
    rw [hS, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have := hB j
    nlinarith
  have hact : -(K0 * L ^ 2) ≤ Mm.confAction gc u := by
    unfold MeasuredModel.confAction
    rw [hdir, hr.tr_eq u, hr.vol_eq]
    simp only [hr.bvol_eq]
    have hN1 : 0 ≤ (N : ℝ) - 1 := by linarith
    have hs2 := mul_le_mul_of_nonneg_left hsum (by linarith : (0 : ℝ) ≤ 2 * ((N : ℝ) - 1))
    have hG : 0 ≤ aN N * Gr ^ 2 - A * δ ^ 2 * Gr ^ 2 := by
      have := mul_nonneg (sub_nonneg.mpr hAδ) (sq_nonneg Gr)
      linarith [show (aN N - A * δ ^ 2) * Gr ^ 2 = aN N * Gr ^ 2 - A * δ ^ 2 * Gr ^ 2 by ring]
    have hexp : 2 * ((N : ℝ) - 1) * (S * (-H0 * (2 * δ ^ 2 * Gr ^ 2 + 2 * (δ + δ⁻¹) ^ 2 * L ^ 2))) =
        -(A * δ ^ 2 * Gr ^ 2) - 2 * ((N : ℝ) - 1) * H0 * (2 * S * (δ + δ⁻¹) ^ 2) * L ^ 2 := by
      rw [hA]; ring
    have hKL : K0 * L ^ 2 =
        R0 * L ^ 2 + 2 * ((N : ℝ) - 1) * H0 * (2 * S * (δ + δ⁻¹) ^ 2) * L ^ 2 := by
      rw [hK0]; ring
    have hRi' : -(R0 * L ^ 2) ≤ ∫ x, gc.R x * f x ^ 2 ∂μ := by
      have := hRi; rwa [neg_mul] at this
    linarith
  -- Hölder: `‖u‖²_{L²} ≤ Vol^{2/N} ‖u‖²_{L^{p*}}`
  have hH := hoelder_interior hN (ν := μ) (memLp_of_isC1 hf (ENNReal.ofReal (pStar N)))
  rw [hL2] at hH
  unfold MeasuredModel.Adm at hadm
  rw [hr.vol_eq] at hadm
  unfold MeasuredModel.confEnergy
  rw [hr.vol_eq, le_div_iff₀ hadm]
  have hK := mul_le_mul_of_nonneg_left hH hK00
  rw [← hV2] at hK
  have e : -(K0 * V2) * normSq μ (pStar N) f = -(K0 * (V2 * normSq μ (pStar N) f)) := by ring
  rw [e]
  linarith

/-- rem:conformal-gap on a model reading a compact manifold with boundary:
(1) `δ ≤ δ_conf` for every metric (any boundary), in `EReal` and for every real `σb`;
(2) equality for constant `R_g = c ≤ 0` and minimal boundary (fact (iii));
(3) Sec. torus's sentence: for constant `R_g` and minimal boundary, equality as soon as
`Y_[g](Σ) ≤ 0` (prop:nonpositive's first sentence, carried). -/
theorem rem_conformal_gap (hN : 3 ≤ N) [CompactSpace M] [T2Space M]
    {gc : CurvedMetric M N} (hr : Reads Mm gc.toFrameMetric g μ σ) (hμ : IsLocallyLebesgue N μ)
    (hσ : ∀ j, IsBoundaryMeasure N (σ j)) (C : Set (CurvedMetric M N)) :
    (Mm.gapBdryE C gc ≤ Mm.deltaConfE C gc ∧
      ∀ σb : ℝ, Mm.gapBdry σb gc ≤ Mm.deltaConf σb gc) ∧
    (Mm.MinimalBoundary gc → ∀ c : ℝ, c ≤ 0 → (∀ x, gc.R x = c) →
      Mm.gapBdryE C gc = Mm.deltaConfE C gc ∧
        ∀ σb : ℝ, Mm.gapBdry σb gc = Mm.deltaConf σb gc) ∧
    (Mm.MinimalBoundary gc → ∀ c : ℝ, (∀ x, gc.R x = c) → Mm.Y gc ≤ 0 →
      Mm.gapBdryE C gc = Mm.deltaConfE C gc ∧
        ∀ σb : ℝ, Mm.gapBdry σb gc = Mm.deltaConf σb gc) := by
  haveI := isFiniteMeasure_of_isLocallyLebesgue hμ
  haveI : IsFiniteMeasure (Mm.vol gc.toFrameMetric) := by rw [hr.vol_eq]; infer_instance
  have heq : Mm.EH gc = Mm.Y gc → Mm.gapBdryE C gc = Mm.deltaConfE C gc ∧
      ∀ σb : ℝ, Mm.gapBdry σb gc = Mm.deltaConf σb gc := by
    intro h
    refine ⟨?_, fun σb => ?_⟩
    · unfold MeasuredModel.gapBdryE MeasuredModel.deltaConfE; rw [h]
    · unfold MeasuredModel.gapBdry MeasuredModel.deltaConf; rw [h]
  refine ⟨Mm.rem_conformal_gap_le hN C gc (hr.conformalGap_bddBelow hN hμ hσ),
    fun hH c hc hR => Mm.rem_conformal_gap_eq hN C gc hr.hD hH hc (ae_of_all _ hR),
    fun hH c hR hY => heq ?_⟩
  by_cases hV : μ = 0
  · have h := Mm.conformalGap_EH_Y_of_vol_eq_zero hN gc (by rw [hr.vol_eq]; exact hV)
    rw [h.1, h.2]
  · exact (hr.prop_nonpositive_csc hN hμ hV hH hR hY).2

end Reads

end Mfd

/-! ## Finding: minimality alone does not give `δ = δ_conf` -/

/-- **Finding** (l.423): on the two-point toy model with one boundary component, the metric
`toyConst 100` has constant scalar curvature `100` and minimal boundary, and `δ < δ_conf` (in
`EReal`, with `σ^∂` over `C = {g}`, and for every real `σb`): the equality of rem:conformal-gap
needs `R_g ≤ 0`, and « minimal boundaries, for which `δ = δ_conf` » needs Sec. torus's
constant-curvature setting and `R_g ≤ 0`. -/
theorem rem_conformal_gap_toy_strict :
    toyModel.MinimalBoundary (toyConst 100) ∧ (∀ x, (toyConst 100).R x = 100) ∧
      toyModel.gapBdryE {toyConst 100} (toyConst 100) <
        toyModel.deltaConfE {toyConst 100} (toyConst 100) ∧
      ∀ σb : ℝ, toyModel.gapBdry σb (toyConst 100) < toyModel.deltaConf σb (toyConst 100) := by
  have hval : ∀ w : Bool → ℝ, toyModel.val w = w := fun _ => rfl
  haveI : IsFiniteMeasure (toyModel.vol (toyConst 100).toFrameMetric) := by
    rw [toyConst_toFrameMetric, toy_vol]; infer_instance
  have hint : ∀ f : Bool → ℝ,
      ∫ x, f x ∂(toyModel.vol (toyConst 100).toFrameMetric) = f true + f false := by
    intro f
    rw [toyConst_toFrameMetric, toy_vol, integral_fintype]
    · simp [Measure.real]
    · exact .of_finite
  have hYlt : toyModel.Y (toyConst 100) < toyModel.EH (toyConst 100) := by
    set u : Bool → ℝ := fun b => if b then 1 else 1 / 10 with hu
    have hEH : toyModel.EH (toyConst 100) = 100 * (2 : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [toyModel.EH_eq_const_mul (toyConst 100) (le_refl 3) (toyConst_minimal 100) (c := 100)
        (ae_of_all _ fun _ => rfl), toyConst_toFrameMetric, toy_vol, toy_count_univ]
      norm_num
    have hden : 1 ≤ normSq (toyModel.vol (toyConst 100).toFrameMetric) (pStar 3)
        (toyModel.val u) := by
      rw [hval, toyConst_toFrameMetric, toy_normSq_vol_eq]
      exact Real.one_le_rpow (by simp [hu]) (by norm_num)
    have hnum : toyModel.confAction (toyConst 100) u ≤ 114 := by
      rw [toyModel.confAction_of_minimal _ (toyConst_minimal 100), hint, toyConst_toFrameMetric,
        toy_dirichlet, aN_three]
      simp [hu, toyConst, hval]
      norm_num
    have hnn : 0 ≤ toyModel.confAction (toyConst 100) u := by
      rw [toyModel.confAction_of_minimal _ (toyConst_minimal 100), hint, toyConst_toFrameMetric,
        toy_dirichlet, aN_three]
      simp [hu, toyConst, hval]
      norm_num
    have hE : toyModel.confEnergy (toyConst 100) u ≤ 114 := by
      unfold MeasuredModel.confEnergy
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hbdd : BddBelow (toyModel.confEnergy (toyConst 100) ''
        {w | w ∈ {w | toyModel.Pos w} ∧ toyModel.Adm (toyConst 100).toFrameMetric w}) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨w, -, rfl⟩
      unfold MeasuredModel.confEnergy
      refine div_nonneg ?_ (normSq_nonneg _ _ _)
      rw [toyModel.confAction_of_minimal _ (toyConst_minimal 100), hint]
      have := toyModel.dirichlet_nonneg (toyConst 100).toFrameMetric w
      have ha := aN_pos (le_refl 3)
      simp only [toyConst, hval]
      positivity
    have hY : toyModel.Y (toyConst 100) ≤ toyModel.confEnergy (toyConst 100) u := by
      unfold MeasuredModel.Y MeasuredModel.infConf
      refine csInf_le hbdd ⟨u, ⟨fun b => ?_, ?_⟩, rfl⟩
      · rw [hval]; cases b <;> simp [hu]
      · unfold MeasuredModel.Adm; linarith
    have h2 := six_fifths_le_two_rpow
    rw [hEH]
    linarith
  refine ⟨toyConst_minimal 100, fun _ => rfl, ?_, fun σb => ?_⟩
  · unfold MeasuredModel.gapBdryE MeasuredModel.deltaConfE MeasuredModel.sigmaBdry
    simp only [Set.mem_singleton_iff, iSup_iSup_eq_left]
    rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_lt_coe_iff]
    linarith
  · unfold MeasuredModel.gapBdry MeasuredModel.deltaConf
    linarith

/-- The equality of rem:conformal-gap is not vacuous: on the toy model, `toyCurved` (`R_g ≡ −1`,
minimal boundary) has `δ = δ_conf = 0` over `C = {toyCurved}`. -/
theorem rem_conformal_gap_toy_eq :
    toyModel.gapBdryE {toyCurved} toyCurved = toyModel.deltaConfE {toyCurved} toyCurved ∧
      toyModel.deltaConfE {toyCurved} toyCurved = 0 := by
  refine ⟨?_, ?_⟩
  · rw [toy_prop_gap_bdry_nonneg]
    unfold MeasuredModel.deltaConfE MeasuredModel.sigmaBdry
    simp only [Set.mem_singleton_iff, iSup_iSup_eq_left]
    rw [← EReal.coe_sub, sub_self, EReal.coe_zero]
  · unfold MeasuredModel.deltaConfE MeasuredModel.sigmaBdry
    simp only [Set.mem_singleton_iff, iSup_iSup_eq_left]
    rw [← EReal.coe_sub, sub_self, EReal.coe_zero]

end Yamabe
