import Yamabe.Negative

/-!
# The Sobolev inequality and lem:kobayashi (b) on the model; the manifold layer's definitions

Labels (NOT marked: partial, see SCOPE):

* `lem:kobayashi` — `Yamabegap.tex:613` (statement l.613–625, proof l.626–638): part (b)
  (l.623, proof l.632–637) over the measured model of `Yamabe.Kobayashi`, from the Sobolev
  inequality; the assembly (a) ∧ (b); the Euclidean inequality behind the Sobolev embedding the
  proof cites (l.637, and again in lem:positivity, l.720, `Hebey1996`); and the definitions of the
  manifold layer on which that embedding is stated and proved (`Mfd.sobolev_embedding`, in
  `Yamabe.ManifoldTheorems`).

> \item[(b)] If $\min_\Sigma\Rs_\g>0$, then $\Y_{[\g]}(\Sigma)>0$. (l.623)

> (b) If $\Rs_\g\ge\rho_0>0$, then
> $\EH\big(u^{4/(N-2)}\g\big)\,\|u\|^2_{\pstar}\ \ge\ \min(\aN,\rho_0)\,\|u\|^2_{W^{1,2}}
> \ \ge\ C^{-1}\min(\aN,\rho_0)\,\|u\|^2_{\pstar}$
> by the Sobolev embedding $W^{1,2}(\Sigma)\hookrightarrow L^{\pstar}(\Sigma)$ on compact manifolds
> with boundary \cite{Hebey1996}. (l.632–637)

> If moreover $\g$ has constant scalar curvature and minimal boundary,
> Lemma~\ref{lem:kobayashi}(b) excludes $\Rs_\g>0$ [...] (l.645)

## The setting

Two layers.

* **The manifold layer** (`Yamabe.Mfd`): `M` a compact Hausdorff smooth manifold with boundary
  modelled on Mathlib's `EuclideanHalfSpace N` (`𝓡∂ N`), with a smooth Riemannian metric
  `g : Mfd.RiemannianMetric N M` (Mathlib's `Bundle.ContMDiffRiemannianMetric` on the tangent
  bundle). `|∇u|_g` is `Mfd.gradNorm g u`, the `g`-dual norm of `mfderiv u`. Mathlib has no
  Riemannian volume: a volume is any measure `μ` with `Mfd.IsLocallyLebesgue N μ` (near every
  point, in its chart, bounded above and below by constants times Lebesgue measure; the
  Riemannian volume `√det g_{ab} dy` of a continuous metric is one). `W^{1,2}(M)` is read through
  `C¹(M)` (`Mfd.IsC1 N`), which is dense in it: a `W^{1,2}` inequality is its inequality on `C¹`.
* **The model layer** (`Yamabe.MeasuredModel`, the strict frame model): `SobolevIneq` is the
  inequality on a model; `Mfd.Reads` says that a model reads `(M, g, μ, σ)` (its volume is `μ`,
  its functions are `C¹`, its `|∇u|²` is `|∇u|²_g`); `Mfd.Reads.sobolevIneq`
  (`Yamabe.ManifoldTheorems`) transports the manifold theorem to it.

The manifold theorems themselves, `Mfd.sobolev_embedding` and `Mfd.eLpNorm_gradNorm_lt_top`, and
their bridges to the model `Mfd.Reads.sobolevIneq`, `Mfd.Reads.kobayashiB`,
`Mfd.Reads.prop_nonpositive_csc`, are in `Yamabe.ManifoldTheorems`, proved through
`Yamabe.HalfSpace` and `Yamabe.Localisation`, which import this file. Round 1
stated them here with `sorry`; the integration of round 2 (T-yamabe-integrate-r2) deleted those
and gave the proved copies the round-1 names, with the round-1 statements unchanged.

## What is proved (no `sorry` in this file)

`sobolev_euclidean` (Gagliardo–Nirenberg–Sobolev on `ℝ^N` at `p = 2`, `p' = p*`, for `C¹`
compactly supported functions, from Mathlib's `eLpNorm_le_eLpNorm_fderiv_of_eq`);
`normSq_smul`, `tendsto_eLpNorm_of_normSq`, `tendsto_normSq_of_eLpNorm`;
`MeasuredModel.dirichlet_smul`, `MeasuredModel.F_smul`, `MeasuredModel.dirichlet_sub_smul_one`,
`MeasuredModel.val_sub_smul_one`, `MeasuredModel.tr_sub_smul_one`, `MeasuredModel.w12Sq_nonneg`;
`MeasuredModel.kobayashiB_of_sobolev` (lem:kobayashi (b) over the model from `SobolevIneq`, every
step of l.632–637), `MeasuredModel.lem_kobayashi` (the assembly (a) ∧ (b)),
`MeasuredModel.prop_nonpositive_csc_of_sobolev` (the strict `prop_nonpositive_csc` with
`KobayashiB` discharged); on the manifold layer `Mfd.Reads.hD`, `Mfd.Reads.dirichlet_eq`,
`Mfd.memLp_of_isC1`, `Mfd.sq_le_of_le_mul_add`, and **`Reads` is satisfiable**:
`Mfd.reads_readingModel` (for every `(M, g, μ, σ)`, the model `Mfd.readingModel` on `C¹(M)` with a
`g_x`-orthonormal frame), through `Mfd.gradNorm_sq` (`|∇u|²_g` is the sum of squares of the frame
components of `du_x`: Riesz and Parseval for `g_x`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ` a compact Riemannian `N`-manifold with boundary, `N ≥ 3` (l.605) | ✓ carried: `CompactSpace`, `T2Space`, `IsManifold (𝓡∂ N) ∞ M`, smooth `g`, `3 ≤ N`; `vol_g` ⚠ read as any locally-Lebesgue `μ` (SCOPE) |
| `u ∈ W^{1,2}(Σ)` (l.637) | ⚠ read: `u ∈ C¹(M)` (dense in `W^{1,2}`); the model's `D` |
| `H_g ≡ 0` (standing assumption of lem:kobayashi, l.615) | ✓ carried (`MinimalBoundary`) |
| `min_Σ R_g > 0` (l.623) | ✓ carried as `0 < ⨅ x, R_g x` (as in the strict `KobayashiB`) |
| `Σ ≠ ∅` | ✓ carried as `vol_g ≠ 0` on the model |
| the Sobolev embedding (l.637, Hebey1996) | on the model: `SobolevIneq` (a hypothesis of the model, discharged for a model reading a manifold by `Mfd.Reads.sobolevIneq`, from `Mfd.sobolev_embedding`, both proved in `Yamabe.ManifoldTheorems`) |

## SCOPE (disclosed)

* `Mfd.sobolev_embedding` (`Yamabe.ManifoldTheorems`) is stated in its strongest usual
  form, in `ℝ≥0∞` (so finiteness is part of the conclusion), for every locally-Lebesgue `μ`:
  Lean ≥ paper, since the Riemannian volume is such a measure (OQ-93 (a)). It is proved there,
  sorry-free, from the Euclidean inequality of this file (`sobolev_euclidean`) through the
  half-space reflection and the chart localisation.
* `SobolevIneq` is junk-prone in the strict model's conventions (`normSq`, `dirichlet` are `0` when
  infinite). For a model reading a manifold (`Mfd.Reads`) every energy and norm is finite, so the
  inequality is genuine there (`Mfd.Reads.sobolevIneq`).
* A model reading `(M, g, μ, σ)` exists for all data (`Mfd.reads_readingModel`): the transported
  theorems are not vacuous. Its frame is chosen pointwise (the model asks no measurability of a
  frame), so `gradNorm` is checked against the model's `du ⬝ G⁻¹ du`.
* `Mfd.gradNorm` is the `g`-dual norm of `mfderiv`; `Mfd.RiemannianMetric` is smooth (`∞`); only
  its continuity is used by the proof of the embedding.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Manifold ContDiff Bundle Matrix

noncomputable section

namespace Yamabe

/-! ## 1. The Euclidean inequality (proved, from Mathlib's Gagliardo–Nirenberg–Sobolev) -/

section Euclidean

lemma pStar_inv (N : ℕ) (hN : 3 ≤ N) : (pStar N)⁻¹ = 2⁻¹ - (N : ℝ)⁻¹ := by
  have := three_le_cast hN
  have h2 : (N : ℝ) - 2 ≠ 0 := by linarith
  have h0 : (N : ℝ) ≠ 0 := by linarith
  unfold pStar
  field_simp

/-- The Sobolev inequality on `ℝ^N` (`N ≥ 3`), `p = 2`: for `u ∈ C¹_c(ℝ^N)`,
`‖u‖_{L^{p*}} ≤ C ‖Du‖_{L²}`. This is Mathlib's Gagliardo–Nirenberg–Sobolev inequality
`eLpNorm_le_eLpNorm_fderiv_of_eq` at `p = 2`, `p' = p* = 2N/(N-2)`. -/
theorem sobolev_euclidean {N : ℕ} (hN : 3 ≤ N) :
    ∃ C : ℝ≥0, ∀ u : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u (ENNReal.ofReal (pStar N)) volume ≤ C * eLpNorm (fderiv ℝ u) 2 volume := by
  refine ⟨SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin N)))
    ((2 : ℝ≥0) : ℝ), fun u hu hc => ?_⟩
  have hp' : (((pStar N).toNNReal : ℝ≥0) : ℝ)⁻¹ =
      ((2 : ℝ≥0) : ℝ)⁻¹ - (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) : ℝ)⁻¹ := by
    rw [finrank_euclideanSpace_fin, Real.coe_toNNReal _ (pStar_pos hN).le]
    push_cast
    exact pStar_inv N hN
  have h := eLpNorm_le_eLpNorm_fderiv_of_eq (F := ℝ) volume hu hc (p := 2)
    (p' := (pStar N).toNNReal) (by norm_num) (by rw [finrank_euclideanSpace_fin]; omega) hp'
  have e : ENNReal.ofReal (pStar N) = (((pStar N).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [e]
  simpa using h

end Euclidean

/-! ## 2. The model layer -/

section NormSq

variable {X : Type*} [MeasurableSpace X]

/-- `‖c f‖²_{L^q} = c² ‖f‖²_{L^q}`. -/
lemma normSq_smul (ν : Measure X) (q : ℝ) (c : ℝ) (f : X → ℝ) :
    normSq ν q (c • f) = c ^ 2 * normSq ν q f := by
  unfold normSq
  rw [eLpNorm_const_smul, ENNReal.toReal_mul, mul_pow, Real.enorm_eq_ofReal_abs,
    ENNReal.toReal_ofReal (abs_nonneg c), sq_abs]

/-- Convergence of squared norms to `0` gives convergence of the norms to `0`, for finite norms. -/
lemma tendsto_eLpNorm_of_normSq {ι : Type*} {l : Filter ι} {ν : Measure X} {q : ℝ}
    {f : ι → X → ℝ} (hf : ∀ i, eLpNorm (f i) (ENNReal.ofReal q) ν ≠ ⊤)
    (h : Tendsto (fun i => normSq ν q (f i)) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i) (ENNReal.ofReal q) ν) l (𝓝 0) := by
  have e : ∀ i, eLpNorm (f i) (ENNReal.ofReal q) ν = ENNReal.ofReal (Real.sqrt (normSq ν q (f i))) := by
    intro i
    unfold normSq
    rw [Real.sqrt_sq ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hf i)]
  simp only [e]
  have h2 : Tendsto (fun i => Real.sqrt (normSq ν q (f i))) l (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h
  simpa using ENNReal.tendsto_ofReal h2

/-- Convergence of norms to `0` gives convergence of the squared norms to `0`. -/
lemma tendsto_normSq_of_eLpNorm {ι : Type*} {l : Filter ι} {ν : Measure X} {q : ℝ}
    {f : ι → X → ℝ} (h : Tendsto (fun i => eLpNorm (f i) (ENNReal.ofReal q) ν) l (𝓝 0)) :
    Tendsto (fun i => normSq ν q (f i)) l (𝓝 0) := by
  have h1 : Tendsto (fun i => (eLpNorm (f i) (ENNReal.ofReal q) ν).toReal) l (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [normSq] using h1.pow 2

end NormSq

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : FrameMetric X N)

/-- The squared `W^{1,2}` norm on the model: `‖∇u‖²_{L²(Σ,g)} + ‖u‖²_{L²(Σ,g)}`. -/
def w12Sq (u : D) : ℝ := M.dirichlet g u + normSq (M.vol g) 2 (M.val u)

/-- The Sobolev inequality `‖u‖²_{L^{p*}} ≤ C ‖u‖²_{W^{1,2}}` on the model: the embedding
`W^{1,2}(Σ) ↪ L^{p*}(Σ)` cited at l.637 and l.720 (Hebey1996). -/
def SobolevIneq : Prop :=
  ∃ C : ℝ, ∀ u : D, normSq (M.vol g) (pStar N) (M.val u) ≤ C * M.w12Sq g u

lemma w12Sq_nonneg (u : D) : 0 ≤ M.w12Sq g u :=
  add_nonneg (M.dirichlet_nonneg g u) (normSq_nonneg _ _ _)

/-- `‖∇(c u)‖² = c² ‖∇u‖²`. -/
lemma dirichlet_smul (c : ℝ) (u : D) : M.dirichlet g (c • u) = c ^ 2 * M.dirichlet g u := by
  simp only [dirichlet, M.gradSq_smul]
  have : ∀ x, ENNReal.ofReal (c ^ 2 * M.gradSq g u x) =
      ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (M.gradSq g u x) :=
    fun x => ENNReal.ofReal_mul (sq_nonneg c)
  simp only [this]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg c)]

/-- `F^(β)_g` is homogeneous of degree `0`: `F(c u) = F(u)` for `c ≠ 0`. -/
lemma F_smul (β : Fin n → ℝ) {c : ℝ} (hc : c ≠ 0) (u : D) : M.F g β (c • u) = M.F g β u := by
  unfold F traceSobolevQuot
  rw [M.dirichlet_smul g c u, map_smul, map_smul, normSq_smul]
  simp only [normSq_smul]
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have e : aN N * (c ^ 2 * M.dirichlet g u) +
      ∑ j, β j * (c ^ 2 * normSq (M.bvol g j) (pSharp N) (M.tr u)) =
      c ^ 2 * (aN N * M.dirichlet g u + ∑ j, β j * normSq (M.bvol g j) (pSharp N) (M.tr u)) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      ring
  rw [e, mul_div_mul_left _ _ hc2]

/-- The differential of a constant vanishes, so `‖∇(u - c·1)‖² = ‖∇u‖²`. -/
lemma dirichlet_sub_smul_one (c : ℝ) (u : D) :
    M.dirichlet g (u - c • M.one) = M.dirichlet g u := by
  unfold dirichlet gradSq
  rw [map_sub, map_smul, M.d_one, smul_zero, sub_zero]

lemma val_sub_smul_one (c : ℝ) (u : D) : M.val (u - c • M.one) = M.val u - fun _ => c := by
  rw [map_sub, map_smul, M.val_one]
  funext x
  simp

lemma tr_sub_smul_one (c : ℝ) (u : D) : M.tr (u - c • M.one) = M.tr u - fun _ => c := by
  rw [map_sub, map_smul, M.tr_one]
  funext x
  simp

/-- lem:kobayashi (b) (l.623, proof l.632–637) over the model: with `H_g ≡ 0` and the Sobolev
inequality, `min_Σ R_g > 0` gives `Y_[g](Σ) > 0`. -/
theorem kobayashiB_of_sobolev (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)] (hV : M.vol g.toFrameMetric ≠ 0)
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) (hS : M.SobolevIneq g.toFrameMetric) : M.KobayashiB g := by
  intro hρ
  obtain ⟨C, hC⟩ := hS
  set ν := M.vol g.toFrameMetric with hν
  set ρ := ⨅ x, g.R x with hρdef
  have hRge : ∀ x, ρ ≤ g.R x := fun x => ciInf_le g.bddBelow_R x
  have hVpos : 0 < (ν Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  -- the constant `1` is a competitor
  have hadm1 : M.Adm g.toFrameMetric M.one := by
    unfold Adm
    rw [M.val_one, normSq_one _ (pStar_pos hN)]
    exact Real.rpow_pos_of_pos hVpos _
  have hpos1 : M.Pos M.one := fun x => by rw [M.val_one]; exact one_pos
  -- the Sobolev constant is positive
  have hCpos : 0 < C := by
    have h1 := hC M.one
    have hw : M.w12Sq g.toFrameMetric M.one = normSq ν 2 (fun _ => 1) := by
      unfold w12Sq
      rw [M.dirichlet_one, M.val_one, zero_add]
    rw [hw] at h1
    have h2 : 0 < normSq ν 2 (fun _ => (1 : ℝ)) := by
      rw [normSq_one _ two_pos]
      exact Real.rpow_pos_of_pos hVpos _
    have h0 : 0 < normSq ν (pStar N) (M.val M.one) := hadm1
    by_contra hc
    rw [not_lt] at hc
    nlinarith
  set κ := min (aN N) ρ / C with hκdef
  have hκ : 0 < κ := div_pos (lt_min (aN_pos hN) hρ) hCpos
  -- every competitor has conformal energy at least `κ` (l.633–637)
  have hbound : ∀ u, M.Adm g.toFrameMetric u → κ ≤ M.confEnergy g u := by
    intro u hu
    have hmem : MemLp (M.val u) (ENNReal.ofReal (pStar N)) ν := by
      refine ⟨hD u, lt_top_iff_ne_top.mpr fun htop => ?_⟩
      have hu' : 0 < normSq ν (pStar N) (M.val u) := hu
      simp [normSq, htop] at hu'
    have hu2 : MemLp (M.val u) 2 ν := memLp_two_of_pStar hN hmem
    have hint : ∫ x, M.val u x ^ 2 ∂ν = normSq ν 2 (M.val u) := integral_sq_eq_normSq hu2
    have hRi := M.integrable_R_mul_sq g hN u hmem
    have hscal : ρ * normSq ν 2 (M.val u) ≤ ∫ x, g.R x * M.val u x ^ 2 ∂ν := by
      rw [← hint, ← integral_const_mul]
      exact integral_mono (hu2.integrable_sq.const_mul ρ) hRi fun x =>
        mul_le_mul_of_nonneg_right (hRge x) (sq_nonneg _)
    have hact : min (aN N) ρ * M.w12Sq g.toFrameMetric u ≤ M.confAction g u := by
      rw [M.confAction_of_minimal g hH u]
      unfold w12Sq
      have h1 : min (aN N) ρ * M.dirichlet g.toFrameMetric u ≤
          aN N * M.dirichlet g.toFrameMetric u :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (M.dirichlet_nonneg _ u)
      have h2 : min (aN N) ρ * normSq ν 2 (M.val u) ≤ ρ * normSq ν 2 (M.val u) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (normSq_nonneg _ _ _)
      linarith
    have hsob := hC u
    have hu' : 0 < normSq ν (pStar N) (M.val u) := hu
    unfold confEnergy
    rw [le_div_iff₀ hu']
    calc κ * normSq ν (pStar N) (M.val u) ≤ κ * (C * M.w12Sq g.toFrameMetric u) :=
          mul_le_mul_of_nonneg_left hsob hκ.le
      _ = min (aN N) ρ * M.w12Sq g.toFrameMetric u := by
          rw [hκdef]; field_simp
      _ ≤ M.confAction g u := hact
  have hne : (M.confEnergy g '' {u | u ∈ {u | M.Pos u} ∧ M.Adm g.toFrameMetric u}).Nonempty :=
    ⟨_, M.one, ⟨hpos1, hadm1⟩, rfl⟩
  have hY : κ ≤ M.Y g := by
    unfold Y infConf
    exact le_csInf hne (by rintro _ ⟨u, ⟨-, ha⟩, rfl⟩; exact hbound u ha)
  linarith

/-- lem:kobayashi, (a) and (b), over the model (l.613–625): the strict `lem_kobayashi_a` and
`kobayashiB_of_sobolev`. -/
theorem lem_kobayashi (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)] (hV : M.vol g.toFrameMetric ≠ 0)
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) (hS : M.SobolevIneq g.toFrameMetric) :
    ((∀ u : D, aN N * M.dirichlet g.toFrameMetric u /
          normSq (M.vol g.toFrameMetric) (pStar N) (M.val u) +
        g.kobM * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤
      M.confEnergy g u) ∧
      g.kobM * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ)) ≤ M.Y g ∧
      ∀ c : ℝ, c ≤ 0 → (∀ᵐ x ∂(M.vol g.toFrameMetric), g.R x = c) →
        M.EH g = M.Y g ∧ M.Y g = c * (M.vol g.toFrameMetric Set.univ).toReal ^ (2 / (N : ℝ))) ∧
    M.KobayashiB g :=
  ⟨M.lem_kobayashi_a g hN hD hH, M.kobayashiB_of_sobolev hN g hV hD hH hS⟩

/-- prop:nonpositive, second sentence (l.478, proof l.645), with lem:kobayashi (b) discharged from
the Sobolev inequality: `R_g ≡ c`, minimal boundary and `Y_[g](Σ) ≤ 0` (the first sentence,
carried) give `R_g ≤ 0` and `EH(Σ, g) = Y_[g](Σ)`. -/
theorem prop_nonpositive_csc_of_sobolev (hN : 3 ≤ N) (g : CurvedMetric X N)
    [IsFiniteMeasure (M.vol g.toFrameMetric)] (hV : M.vol g.toFrameMetric ≠ 0)
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g.toFrameMetric))
    (hH : M.MinimalBoundary g) {c : ℝ} (hRc : ∀ x, g.R x = c) (hY : M.Y g ≤ 0)
    (hS : M.SobolevIneq g.toFrameMetric) :
    (∀ x, g.R x ≤ 0) ∧ M.EH g = M.Y g :=
  M.prop_nonpositive_csc hN g hD hH hRc hY (M.kobayashiB_of_sobolev hN g hV hD hH hS)

end MeasuredModel

/-! ## 3. The manifold layer -/

namespace Mfd

variable {N : ℕ} [NeZero N]

/-- A smooth Riemannian metric on a manifold `M` with boundary modelled on `EuclideanHalfSpace N`:
Mathlib's `Bundle.ContMDiffRiemannianMetric` on the tangent bundle. -/
abbrev RiemannianMetric (N : ℕ) [NeZero N] (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace N) M] [IsManifold (𝓡∂ N) ∞ M] :=
  Bundle.ContMDiffRiemannianMetric (𝓡∂ N) ∞ (EuclideanSpace ℝ (Fin N))
    (TangentSpace (𝓡∂ N) : M → Type)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace N) M]
  [IsManifold (𝓡∂ N) ∞ M]

/-- `|∇u|_g(x)`: the `g_x`-dual norm of the differential, `sup {|du_x(v)| : g_x(v, v) ≤ 1}`. -/
def gradNorm (g : RiemannianMetric N M) (u : M → ℝ) (x : M) : ℝ :=
  sSup ((fun v => |mfderiv (𝓡∂ N) 𝓘(ℝ, ℝ) u x v|) ''
    {v : TangentSpace (𝓡∂ N) x | g.inner x v v ≤ 1})

variable (N) in
/-- `u` is `C¹` up to the boundary. -/
def IsC1 (u : M → ℝ) : Prop := ContMDiff (𝓡∂ N) 𝓘(ℝ, ℝ) 1 u

variable [MeasurableSpace M]

/-- `‖u‖_{W^{1,2}(M, g, μ)} = ‖∇u‖_{L²(μ)} + ‖u‖_{L²(μ)}`, in `ℝ≥0∞`. -/
def w12 (g : RiemannianMetric N M) (μ : Measure M) (u : M → ℝ) : ℝ≥0∞ :=
  eLpNorm (gradNorm g u) 2 μ + eLpNorm u 2 μ

variable (N) in
/-- `μ` is a volume on `M`: near every point `x₀`, in the chart at `x₀`, it is bounded above and
below by constant multiples of Lebesgue measure. The Riemannian volume `√det(g_{ab}) dy` of a
continuous Riemannian metric is such a measure (`√det(g_{ab})` is continuous and positive). -/
def IsLocallyLebesgue (μ : Measure M) : Prop :=
  ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ C : ℝ≥0, ∀ A ⊆ U ∩ (chartAt (EuclideanHalfSpace N) x₀).source,
    MeasurableSet A →
      μ A ≤ C * volume (extChartAt (𝓡∂ N) x₀ '' A) ∧
        volume (extChartAt (𝓡∂ N) x₀ '' A) ≤ C * μ A

variable [BorelSpace M]

/-- A measured model of `Yamabe.Quotient` (with `X = M`) *reads* `(M, g, μ, σ)`: its volume is
`μ`, its boundary measures are the `σ j`, its functions are `C¹` with their restriction as trace,
and its `|∇u|²` is `|∇u|²_g`. -/
structure Reads {D : Type*} [AddCommGroup D] [Module ℝ D] {n : ℕ} (Mm : MeasuredModel M D N n)
    (gm : FrameMetric M N) (g : RiemannianMetric N M) (μ : Measure M) (σ : Fin n → Measure M) :
    Prop where
  vol_eq : Mm.vol gm = μ
  bvol_eq : ∀ j, Mm.bvol gm j = σ j
  c1 : ∀ u, IsC1 N (Mm.val u)
  tr_eq : ∀ u, Mm.tr u = Mm.val u
  grad_eq : ∀ u x, Mm.gradSq gm u x = gradNorm g (Mm.val u) x ^ 2

namespace Reads

variable {D : Type*} [AddCommGroup D] [Module ℝ D] {n : ℕ} {Mm : MeasuredModel M D N n}
  {gm : FrameMetric M N} {g : RiemannianMetric N M} {μ : Measure M} {σ : Fin n → Measure M}

/-- The values of a model reading `M` are measurable (they are continuous). -/
lemma hD (hr : Reads Mm gm g μ σ) (u : D) : AEStronglyMeasurable (Mm.val u) (Mm.vol gm) := by
  rw [hr.vol_eq]
  exact (hr.c1 u).continuous.aestronglyMeasurable

omit [BorelSpace M] in
/-- The model's Dirichlet energy is `‖∇u‖²_{L²(μ)}`, `|∇u|` the `g`-norm of the differential. -/
lemma dirichlet_eq (hr : Reads Mm gm g μ σ) (u : D) :
    Mm.dirichlet gm u = normSq μ 2 (gradNorm g (Mm.val u)) := by
  unfold MeasuredModel.dirichlet
  rw [normSq_eq_lintegral two_pos, hr.vol_eq, div_self two_ne_zero, Real.rpow_one]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [hr.grad_eq, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) two_pos.le,
    Real.rpow_two, sq_abs]

end Reads

omit [IsManifold (𝓡∂ N) ∞ M] in
/-- A `C¹` function on a compact manifold lies in every `L^p` of a finite measure. -/
lemma memLp_of_isC1 [CompactSpace M] {ν : Measure M} [IsFiniteMeasure ν] {f : M → ℝ}
    (hf : IsC1 N f) (p : ℝ≥0∞) : MemLp f p ν :=
  hf.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- From the `ℝ≥0∞` form `‖f‖ ≤ C (‖∇u‖ + ‖u‖)` with finite right side to the squared real form
`‖f‖² ≤ 2 C² (‖∇u‖² + ‖u‖²)`. -/
lemma sq_le_of_le_mul_add {x a b : ℝ≥0∞} {C : ℝ≥0} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h : x ≤ C * (a + b)) :
    x.toReal ^ 2 ≤ 2 * (C : ℝ) ^ 2 * (a.toReal ^ 2 + b.toReal ^ 2) := by
  have hrhs : (C : ℝ≥0∞) * (a + b) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.mpr ⟨ha, hb⟩)
  have h' := ENNReal.toReal_mono hrhs h
  rw [ENNReal.toReal_mul, ENNReal.toReal_add ha hb, ENNReal.coe_toReal] at h'
  have hx : 0 ≤ x.toReal := ENNReal.toReal_nonneg
  have hC0 : 0 ≤ (C : ℝ) := C.2
  have h2 : x.toReal ^ 2 ≤ ((C : ℝ) * (a.toReal + b.toReal)) ^ 2 := pow_le_pow_left₀ hx h' 2
  nlinarith [mul_nonneg (sq_nonneg (C : ℝ)) (sq_nonneg (a.toReal - b.toReal))]

/-! ### A model reading every `(M, g, μ, σ)`: `Reads` is satisfiable

The functions are `C¹(M)`; the frame of `T_x M` is a `g_x`-orthonormal basis (chosen at each
point, no measurability being asked of a frame), so the Gram matrix is `1`, the frame measure is
`μ` itself and `|∇u|²_g` is the sum of squares of the frame components of `du_x`
(`gradNorm_sq`). This checks the manifold-layer definitions against the model's. -/

section Reading

variable (N M) in
/-- `C¹(M)`, as a real vector space. -/
def C1 : Submodule ℝ (M → ℝ) where
  carrier := {u | IsC1 N u}
  add_mem' := fun ha hb => ContMDiff.add ha hb
  zero_mem' := contMDiff_const
  smul_mem' := fun c _ hu =>
    ((contMDiff_const : ContMDiff (𝓡∂ N) 𝓘(ℝ, ℝ) 1 (fun _ : M => c)).smul hu)

/-- A `g_x`-orthonormal frame of `T_x M`. -/
noncomputable def onb (g : RiemannianMetric N M) (x : M) : Fin N → TangentSpace (𝓡∂ N) x :=
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace (𝓡∂ N) x) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace (𝓡∂ N) x) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin N)))
  fun a => (stdOrthonormalBasis ℝ (TangentSpace (𝓡∂ N) x)).reindex
    (finCongr finrank_euclideanSpace_fin) a

/-- `du_x`, as a covector on `T_x M`. -/
noncomputable def dcov (u : M → ℝ) (x : M) : TangentSpace (𝓡∂ N) x →L[ℝ] ℝ :=
  mfderiv (𝓡∂ N) 𝓘(ℝ, ℝ) u x

omit [MeasurableSpace M] [BorelSpace M] in
/-- `|∇u|²_g(x)` is the sum of the squares of the components of `du_x` in a `g_x`-orthonormal
frame (Riesz and Parseval for the inner product `g_x`). -/
theorem gradNorm_sq (g : RiemannianMetric N M) (u : M → ℝ) (x : M) :
    gradNorm g u x ^ 2 = ∑ a, (dcov u x (onb g x a)) ^ 2 := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace (𝓡∂ N) x) := ⟨g.toRiemannianMetric⟩
  haveI : FiniteDimensional ℝ (TangentSpace (𝓡∂ N) x) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin N)))
  set ℓ : TangentSpace (𝓡∂ N) x →L[ℝ] ℝ := dcov u x with hℓ
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
  have hG : gradNorm g u x = ‖ℓ‖ := by
    unfold gradNorm
    rw [hset, ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
    rfl
  rw [hG]
  set w := (InnerProductSpace.toDual ℝ (TangentSpace (𝓡∂ N) x)).symm ℓ with hw
  have hwn : ‖w‖ = ‖ℓ‖ := by
    rw [hw]; exact LinearIsometryEquiv.norm_map _ _
  have hℓw : ∀ v, ℓ v = inner ℝ w v := fun v => by
    rw [hw, InnerProductSpace.toDual_symm_apply]
  rw [← hwn]
  have := ((stdOrthonormalBasis ℝ (TangentSpace (𝓡∂ N) x)).reindex
    (finCongr finrank_euclideanSpace_fin)).sum_sq_inner_left w
  rw [← this]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hℓw]
  rfl

variable (N) in
/-- The boundary frame of the reading: the first `N - 1` vectors of the ambient frame. -/
def frameP : Matrix (Fin N) (Fin (N - 1)) ℝ :=
  Matrix.of fun a b => if a = Fin.castLE (Nat.sub_le N 1) b then 1 else 0

omit [NeZero N] in
lemma frameP_transpose_mul : (frameP N)ᵀ * frameP N = 1 := by
  ext b c
  simp only [frameP, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  by_cases h : b = c
  · subst h; simp
  · have h' : Fin.castLE (Nat.sub_le N 1) c ≠ Fin.castLE (Nat.sub_le N 1) b :=
      fun e => h (Fin.castLE_injective _ e).symm
    simp [h, h']

omit [NeZero N] in
lemma frameP_injective : Function.Injective (frameP N).mulVec := by
  intro v w h
  have h' := congrArg (fun z => (frameP N)ᵀ *ᵥ z) h
  simp only [Matrix.mulVec_mulVec, frameP_transpose_mul, Matrix.one_mulVec] at h'
  exact h'

/-- The frame components of the differential, `du_x(e_a)` in the orthonormal frame. -/
noncomputable def dFrame (g : RiemannianMetric N M) : C1 N M →ₗ[ℝ] M → Fin N → ℝ where
  toFun u := fun x a => dcov (u : M → ℝ) x (onb g x a)
  map_add' u v := by
    funext x a
    simp only [dcov, Submodule.coe_add, Pi.add_apply]
    rw [mfderiv_add ((show IsC1 N (u : M → ℝ) from u.2).mdifferentiableAt one_ne_zero)
      ((show IsC1 N (v : M → ℝ) from v.2).mdifferentiableAt one_ne_zero)]
    rfl
  map_smul' c u := by
    funext x a
    simp only [dcov, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [const_smul_mfderiv ((show IsC1 N (u : M → ℝ) from u.2).mdifferentiableAt one_ne_zero)]
    rfl

/-- The measured model reading `(M, g, μ, σ)`. -/
noncomputable def readingModel (g : RiemannianMetric N M) (μ : Measure M) {n : ℕ}
    (σ : Fin n → Measure M) : MeasuredModel M (C1 N M) N n where
  μ := μ
  μb := σ
  P := fun _ => frameP N
  P_injective := fun _ => frameP_injective
  val := (C1 N M).subtype
  tr := (C1 N M).subtype
  d := dFrame g
  one := ⟨fun _ => 1, contMDiff_const⟩
  val_one := rfl
  tr_one := rfl
  d_one := by
    funext x a
    simp [dFrame, dcov]
    rfl

variable (N M) in
/-- The Gram matrix of an orthonormal frame. -/
def flatFrame : FrameMetric M N where
  G := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one

omit [BorelSpace M] in
/-- **`Reads` is satisfiable**: the reading model reads `(M, g, μ, σ)`, for every smooth metric
`g` and all measures `μ`, `σ j`. -/
theorem reads_readingModel (g : RiemannianMetric N M) (μ : Measure M) {n : ℕ}
    (σ : Fin n → Measure M) : Reads (readingModel g μ σ) (flatFrame N M) g μ σ where
  vol_eq := by
    simp [MeasuredModel.vol, readingModel, flatFrame]
  bvol_eq := fun j => by
    simp [MeasuredModel.bvol, readingModel, flatFrame, frameP_transpose_mul]
  c1 := fun u => u.2
  tr_eq := fun _ => rfl
  grad_eq := fun u x => by
    rw [gradNorm_sq]
    simp only [MeasuredModel.gradSq, readingModel, flatFrame, inv_one, Matrix.one_mulVec,
      dotProduct, dFrame, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_subtype, sq]

end Reading

end Mfd

end Yamabe
