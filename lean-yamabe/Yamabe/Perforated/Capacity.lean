import Yamabe.Negative

/-!
# The relative capacity with neutralising background, the capacitary trace-Poincaré inequality and the optimally weighted Hölder step, over the measured model

Labels (the companion BrunswicPerforated, `papers/perforated`; lines of
`papers/perforated/legacy/labeled/perforated.tex`):

* **`def:capstar`** — `perforated.tex:163` (l.163–173), with eq:ell (l.155–161) and eq:S
  (l.119–122): `ell`, `capStar`, `theta`, with `bdryS`, `capWeight`, `volMean`, `bdryAvg`;
* `lem:capstar` — `perforated.tex:376` (statement l.376–390, proof l.392–407): NOT marked,
  partial (see SCOPE): `lem_capstar`, `lem_capstar_minimiser`;
* `lem:capacitary` — `perforated.tex:468` (statement l.468–472, proof l.474–476): NOT marked,
  partial (see SCOPE): `lem_capacitary`;
* **`lem:holder`** — `perforated.tex:478` (statement l.478–483, proof l.485–495): `lem_holder`.

> Put $w_j:=|B_j|^{2/\psharp}/S$, so $w_j\ge0$ and $\sum_jw_j=1$, and let
> $\ell(v):=\frac1V\int_\Sigma v\dd V-\sum_{j=1}^{n}\frac{w_j}{|B_j|}\int_{B_j}v\dd\sigma$,
> a bounded linear functional on $W^{1,2}(\Sigma)$ vanishing on constants. (l.155–161)

> The \emph{relative capacity with neutralising background} of $(\Sigma,g)$ is
> $\cpstar(\Sigma,g):=\inf\bigl\{\|\nabla v\|^2_{L^2(\Sigma,g)}\;:\;
> v\in W^{1,2}(\Sigma),\ \ell(v)=1\bigr\}$,
> and the \emph{capacity--area ratio} is
> $\displaystyle\theta(\Sigma,g):=\frac{\aN\cpstar(\Sigma,g)}{\cN S}$. (l.165–172)

> Let $(\Sigma,g)$ be compact, \emph{connected}, with non-empty Lipschitz boundary.
> Then $0<\cpstar(\Sigma,g)<\infty$, the infimum in \eqref{eq:capstar} is attained,
> and for every $u\in W^{1,2}(\Sigma)$
> $\bar u-\sum_{j}\frac{w_j}{|B_j|}\int_{B_j}u\dd\sigma
> \;\le\;\frac{\|\nabla u\|_{L^2(\Sigma)}}{\sqrt{\cpstar}}$.
> The minimiser $v$ solves $\Delta v=\mu/(2V)$ in $\Sigma$ with
> $\partial_\nu v=-\mu w_j/(2|B_j|)$ on $B_j$, where $\mu=2\cpstar$ [...] (l.378–389)

> $\displaystyle \bar u\;\le\;\sum_j\frac{w_j}{|B_j|}\int_{B_j}u\dd\sigma
>    \;+\;\frac{X}{\sqrt{\cpstar}}$. (l.470–471)

> $\displaystyle\sum_j\frac{w_j}{|B_j|}\int_{B_j}u\dd\sigma\;\le\;\frac{Y}{\sqrt S}$,
> and the weights $w_j=|B_j|^{2/\psharp}/S$ are the unique minimisers of
> $\sum_jw_j^2|B_j|^{-2/\psharp}$ subject to $w_j\ge0$, $\sum_jw_j=1$. (l.480–482)

## The model

Yamabe's `MeasuredModel` (strict `Yamabe.Quotient`, the model of record by DEC-186): `D` the
admissible functions with values `val`, trace `tr`, differential `d`; `vol g`, `bvol g j`. Here
`V = (vol g univ).toReal`, `|B_j| = (bvol g j univ).toReal`, `ū = volMean`, `X = √(dirichlet u)`,
`Y = bdryY u`. `‖∇v‖²` in eq:capstar is the honest energy `energy v ∈ [0, ∞]` (a lintegral), so
`cap* ∈ [0, ∞]` with `inf ∅ = ∞`; `dirichlet = energy.toReal`. `Fq` is the companion's `F_g`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `N ≥ 3` (l.106) | ✓ carried |
| `Σ` compact (l.117, l.311, l.378) | ✓ carried as `IsFiniteMeasure (vol g)`, `IsFiniteMeasure (bvol g j)` |
| `Σ ≠ ∅` | ✓ carried as `vol g ≠ 0` |
| `Σ` connected (l.378) | ⚠ read: the Poincaré inequality `MeanPoincare` (« by Poincaré », l.394; rem:connected, l.413) |
| non-empty Lipschitz boundary (l.378) | ⚠ read: `∃ j, bvol g j ≠ 0` (`S > 0`) and the trace theorem `TraceBound` (l.393) |
| `u ∈ W^{1,2}(Σ)` | ⚠ read: `u ∈ D` (DEC-186, the model of record) |
| the trace of `u` lies in `L^{p♯}(B_j)` (l.134) | ✓ carried, per `u`, in lem:holder (`hu`) |
| `v` supported in the interior with `∫_Σ v ≠ 0` (l.401) | ⚠ carried: `InteriorBump` (finiteness only) |
| the direct method in `W^{1,2}` (l.402–404) | ⚠ carried: `DirectMethod` (attainment only) |
| `∇v` measurable (implicit in `W^{1,2}`) | ⚠ carried: `GradMeasurable` (Euler–Lagrange system only) |
| `u ≥ 0` (standing in § 4, l.460) | ⚠ weakened: not used; lem:capacitary, lem:holder, eq:linear hold for every `u` |
| every `|B_j| > 0` (implicit in `|B_j|^{-2/p♯}`, l.482), `n ≥ 1` | ✓ carried (DEC-186: `n ≥ 1` standing) |

## SCOPE (disclosed)

* **Proved.** def:capstar: the definitions, `w_j ≥ 0`, `Σ w_j = 1` (`sum_capWeight`), `ℓ` linear
  (`ell_smul`, `ell_add`), vanishing on constants (`ell_one`), bounded on `W^{1,2}` under the trace
  theorem (`ell_bounded`). lem:capstar: `0 < cap*` (`capStar_pos`, with the paper's bound
  `cap* ≥ [Λ(1 + λ_1^{-1/2})]⁻²` as `capStar_ge`), `cap* < ∞` (`capStar_lt_top`), eq:capineq for
  every `u ∈ D` (`capineq`; in multiplied form for every `u` of finite energy, `sqrt_capStar_mul_ell_le`),
  the attainment (`capStar_attained`), the Euler–Lagrange system in weak form
  `∫ ⟨∇v, ∇φ⟩ = (μ/2) ℓ(φ)` and the pairing `‖∇v‖² = (μ/2) ℓ(v) = μ/2` (`euler_lagrange`).
  lem:capacitary for every `u` (`lem_capacitary`). lem:holder in full (`lem_holder`,
  `holderObj_eq`). Beyond the labels: eq:linear with `|ū|` (`eq_linear`), eq:calib (`eq_calib`),
  `F_g(1) = c_N S / V^{(N-2)/N}` (`Fq_one_eq`).
* **Why lem:capstar and lem:capacitary are partial.** Their positivity rests on the carried
  `MeanPoincare` (T-perf-poincare discharges it) and `TraceBound` (definitionally
  `Yamabe.Trace`'s `TraceIneq`, whose manifold discharge is `Mfd.Reads.traceIneq`), the
  finiteness on `InteriorBump`, the attainment on `DirectMethod` (a `W^{1,2}` reading: the `C¹`
  reading of OQ-93 (b) is not weakly closed), the Euler–Lagrange system on `GradMeasurable`. The
  strong form `Δv = μ/(2V)`, `∂_ν v = −μ w_j/(2|B_j|)` is not formalized: the model has no
  Laplacian and no normal derivative.
* **Finding (sign, l.386).** With the Laplacian of l.249 (`−Δ + V` positive, `Δ = div ∇`) and the
  outward normal, the printed system is inconsistent: the divergence theorem gives
  `∫_Σ Δv = μ/2` and `∫_{∂Σ} ∂_ν v = −(μ/2) Σ w_j = −μ/2`, forcing `μ = 0 ≠ 2 cap*`. The
  Euler–Lagrange system of eq:capstar is `−Δv = μ/(2V)`, `∂_ν v = −μ w_j/(2|B_j|)` (`ν` outward),
  i.e. the printed one with `Δ = −div ∇`; its weak form is what `euler_lagrange` proves.
* **Remark l.497–500.** For `n` components of equal area the optimal weights are uniform
  (`capWeight_of_equal`); the factor `n^{1/(N-1)}` is `S / |∂Σ|^{2/p♯}` (`bdryS_of_equal`), lost
  by one Hölder over all of `∂Σ`, not by a choice of weights.
* **Junk values.** `ℓ` uses Bochner integrals (`0` off `L¹`); under `MeanPoincare` and
  `TraceBound` every `u ∈ D` has integrable values and traces, so `ℓ` is the paper's. `θ` uses
  `cap*.toReal` (`0` if `cap* = ∞`, excluded by `lem_capstar`).
* **Witness.** On the two-point toy model every hypothesis of `lem_capstar_minimiser` holds
  (`toy_lem_capstar_hyps`), `cap* = 8` (`toy_capStar`) and `θ = 64/c_3` (`toy_theta`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Matrix

noncomputable section

namespace Yamabe

/-! ## Hölder against a finite measure -/

section Hoelder

variable {X : Type*} [MeasurableSpace X]

/-- `√‖f‖²_{L^q} = ‖f‖_{L^q}`. -/
lemma sqrt_normSq (ν : Measure X) (q : ℝ) (f : X → ℝ) :
    Real.sqrt (normSq ν q f) = (eLpNorm f (ENNReal.ofReal q) ν).toReal := by
  unfold normSq
  exact Real.sqrt_sq ENNReal.toReal_nonneg

lemma sqrt_normSq_two (ν : Measure X) (f : X → ℝ) :
    Real.sqrt (normSq ν 2 f) = (eLpNorm f 2 ν).toReal := by
  rw [sqrt_normSq, ENNReal.ofReal_ofNat]

/-- Hölder against `1` on a finite measure: `|∫ f| ≤ ν(X)^{1 - 1/q} ‖f‖_{L^q}` for `q ≥ 1`. -/
theorem abs_integral_le_mul_eLpNorm {ν : Measure X} [IsFiniteMeasure ν] {q : ℝ} (hq : 1 ≤ q)
    {f : X → ℝ} (hf : MemLp f (ENNReal.ofReal q) ν) :
    |∫ x, f x ∂ν| ≤ (ν Set.univ).toReal ^ (1 - 1 / q) * (eLpNorm f (ENNReal.ofReal q) ν).toReal := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
  have hq0 : 0 ≤ q := by linarith
  have hexp : 0 ≤ 1 - 1 / q := by
    rw [sub_nonneg, div_le_one (by linarith)]; exact hq
  have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ h1 hf.aestronglyMeasurable
  rw [ENNReal.toReal_ofReal hq0, ENNReal.toReal_one] at hH
  have hfin : eLpNorm f (ENNReal.ofReal q) ν * ν Set.univ ^ (1 / 1 - 1 / q) ≠ ⊤ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by simpa using hexp) (measure_ne_top _ _))
  have h2 := ENNReal.toReal_mono hfin hH
  have h3 := norm_integral_le_lintegral_norm f (μ := ν)
  have e : ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂ν = eLpNorm f 1 ν := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    congr 1; funext a; exact ofReal_norm (f a)
  rw [e, Real.norm_eq_abs] at h3
  refine h3.trans (h2.trans (le_of_eq ?_))
  rw [ENNReal.toReal_mul, ENNReal.toReal_rpow, mul_comm, div_one]

/-- Hölder against `1`, `q = 2`: `|∫ f| ≤ ν(X)^{1/2} ‖f‖_{L²}`. -/
theorem abs_integral_le_mul_eLpNorm_two {ν : Measure X} [IsFiniteMeasure ν]
    {f : X → ℝ} (hf : MemLp f 2 ν) :
    |∫ x, f x ∂ν| ≤ (ν Set.univ).toReal ^ (1 / 2 : ℝ) * (eLpNorm f 2 ν).toReal := by
  have h := abs_integral_le_mul_eLpNorm (q := 2) one_le_two (by rwa [ENNReal.ofReal_ofNat])
  rw [ENNReal.ofReal_ofNat] at h
  norm_num at h ⊢
  exact h

end Hoelder

/-! ## The model: `ℓ`, `cap*`, `θ` (def:capstar) -/

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : FrameMetric X N)

/-- `‖∇u‖²_{L²(Σ,g)} ∈ [0, ∞]`, the honest energy (`dirichlet = energy.toReal`). -/
def energy (u : D) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (M.gradSq g u x) ∂(M.vol g)

/-- The mean `ū = V⁻¹ ∫_Σ u dV` (l.313). -/
def volMean (u : D) : ℝ := (M.vol g Set.univ).toReal⁻¹ * ∫ x, M.val u x ∂(M.vol g)

/-- `S = Σ_j |B_j|^{(N-2)/(N-1)}` (eq:S, l.122). -/
def bdryS : ℝ := ∑ j, (M.bvol g j Set.univ).toReal ^ (((N : ℝ) - 2) / ((N : ℝ) - 1))

/-- The weights `w_j = |B_j|^{2/p♯} / S` (l.156). -/
def capWeight (j : Fin n) : ℝ := (M.bvol g j Set.univ).toReal ^ (2 / pSharp N) / M.bdryS g

/-- The weighted boundary average `Σ_j (w_j/|B_j|) ∫_{B_j} u dσ` (l.159, l.470, l.480). -/
def bdryAvg (u : D) : ℝ :=
  ∑ j, M.capWeight g j / (M.bvol g j Set.univ).toReal * ∫ x, M.tr u x ∂(M.bvol g j)

/-- The neutralising-background functional `ℓ(v) = V⁻¹ ∫_Σ v dV − Σ_j (w_j/|B_j|) ∫_{B_j} v dσ`
(eq:ell, l.159). -/
def ell (v : D) : ℝ := M.volMean g v - M.bdryAvg g v

/-- The relative capacity with neutralising background
`cap* = inf {‖∇v‖²_{L²} : ℓ(v) = 1} ∈ [0, ∞]` (eq:capstar, l.168). -/
def capStar : ℝ≥0∞ := ⨅ (v : D) (_ : M.ell g v = 1), M.energy g v

/-- The capacity–area ratio `θ = a_N cap* / (c_N S)` (l.172). -/
def theta : ℝ := aN N * (M.capStar g).toReal / (cN N * M.bdryS g)

/-- `Y = (Σ_j ‖u‖²_{L^{p♯}(B_j)})^{1/2}` (l.464). -/
def bdryY (u : D) : ℝ := Real.sqrt (∑ j, normSq (M.bvol g j) (pSharp N) (M.tr u))

/-- The Poincaré inequality around the mean (l.320–321, l.394), with the values in `L²`:
`‖v − v̄‖²_{L²} ≤ K ‖∇v‖²_{L²}`. The paper's `λ_1 > 0` is `K = λ_1⁻¹`. -/
def MeanPoincare : Prop :=
  ∃ K : ℝ, ∀ v : D, MemLp (M.val v) 2 (M.vol g) ∧
    normSq (M.vol g) 2 (M.val v - fun _ => M.volMean g v) ≤ K * M.dirichlet g v

/-- The trace theorem on the model (l.134, l.393): every trace lies in `L^{p♯}(B_j)` and
`‖tr u‖²_{L^{p♯}(B_j)} ≤ C ‖u‖²_{W^{1,2}(Σ)}`. This is `TraceIneq` of `Yamabe.Trace`
with its `w12Sq` unfolded (definitionally equal), restated here because `Yamabe.Trace` was a
scaffold module, which the strict library cannot import, when this file was written. -/
def TraceBound : Prop :=
  ∃ C : ℝ, ∀ u : D, ∀ j, MemLp (M.tr u) (ENNReal.ofReal (pSharp N)) (M.bvol g j) ∧
    normSq (M.bvol g j) (pSharp N) (M.tr u) ≤ C * (M.dirichlet g u + normSq (M.vol g) 2 (M.val u))

/-- The paper's witness of `ℓ ≢ 0` (l.401): a function of finite energy, supported in the
interior (zero trace on every `B_j`), with `∫_Σ v ≠ 0`. -/
def InteriorBump : Prop :=
  ∃ v : D, M.energy g v ≠ ⊤ ∧ (∀ j, M.tr v =ᵐ[M.bvol g j] 0) ∧ ∫ x, M.val v x ∂(M.vol g) ≠ 0

/-- The direct method in `W^{1,2}(Σ)` (l.402–404): a sequence of finite energies, bounded in
`W^{1,2}`, whose energies converge to `e`, has a subsequence converging in `L²(Σ)` and in every
`L²(B_j)` (Rellich–Kondrachov and the compact trace) to some `v ∈ D` of energy at most `e` (weak
compactness of the ball and weak lower semicontinuity of the energy). -/
def DirectMethod : Prop :=
  ∀ (u : ℕ → D) (e : ℝ), (∀ k, M.energy g (u k) ≠ ⊤) →
    (∃ K : ℝ, ∀ k, M.dirichlet g (u k) + normSq (M.vol g) 2 (M.val (u k)) ≤ K) →
    Tendsto (fun k => M.dirichlet g (u k)) atTop (𝓝 e) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : D, M.energy g v ≤ ENNReal.ofReal e ∧
      Tendsto (fun k => eLpNorm (M.val (u (φ k)) - M.val v) 2 (M.vol g)) atTop (𝓝 0) ∧
      ∀ j, Tendsto (fun k => eLpNorm (M.tr (u (φ k)) - M.tr v) 2 (M.bvol g j)) atTop (𝓝 0)

/-- `⟨∇u, ∇w⟩_g = du ⬝ G⁻¹ dw`, so `gradSq u = gradInner u u`. -/
def gradInner (u w : D) (x : X) : ℝ := M.d u x ⬝ᵥ ((g.G x)⁻¹ *ᵥ M.d w x)

/-- The energy densities are measurable (as for `u ∈ W^{1,2}` on a manifold). -/
def GradMeasurable : Prop := ∀ u : D, AEStronglyMeasurable (M.gradSq g u) (M.vol g)

/-! ### Basic facts on `ℓ` -/

lemma dirichlet_eq_toReal_energy (u : D) : M.dirichlet g u = (M.energy g u).toReal := rfl

lemma energy_smul (c : ℝ) (u : D) : M.energy g (c • u) = ENNReal.ofReal (c ^ 2) * M.energy g u := by
  unfold energy
  simp only [M.gradSq_smul]
  have : ∀ x, ENNReal.ofReal (c ^ 2 * M.gradSq g u x) =
      ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (M.gradSq g u x) :=
    fun x => ENNReal.ofReal_mul (sq_nonneg c)
  simp only [this]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma gradSq_sub_smul_one (c : ℝ) (u : D) (x : X) :
    M.gradSq g (u - c • M.one) x = M.gradSq g u x := by
  unfold gradSq
  rw [map_sub, map_smul, M.d_one, smul_zero, sub_zero]

lemma energy_sub_smul_one (c : ℝ) (u : D) : M.energy g (u - c • M.one) = M.energy g u := by
  unfold energy
  simp only [M.gradSq_sub_smul_one]

lemma bdryS_eq (hN : 3 ≤ N) : M.bdryS g = ∑ j, (M.bvol g j Set.univ).toReal ^ (2 / pSharp N) := by
  rw [two_div_pSharp hN]; rfl

lemma bdryS_nonneg : 0 ≤ M.bdryS g :=
  Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _

/-- `S > 0` once some `B_j` has positive area. -/
lemma bdryS_pos [∀ j, IsFiniteMeasure (M.bvol g j)] (hB : ∃ j, M.bvol g j ≠ 0) :
    0 < M.bdryS g := by
  obtain ⟨j, hj⟩ := hB
  have hpos : 0 < (M.bvol g j Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hj) (measure_ne_top _ _)
  calc 0 < (M.bvol g j Set.univ).toReal ^ (((N : ℝ) - 2) / ((N : ℝ) - 1)) :=
        Real.rpow_pos_of_pos hpos _
    _ ≤ M.bdryS g :=
        Finset.single_le_sum (f := fun j => (M.bvol g j Set.univ).toReal ^ (((N : ℝ) - 2) / ((N : ℝ) - 1)))
          (fun _ _ => Real.rpow_nonneg ENNReal.toReal_nonneg _) (Finset.mem_univ j)

lemma capWeight_nonneg (j : Fin n) : 0 ≤ M.capWeight g j :=
  div_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (M.bdryS_nonneg g)

/-- `Σ_j w_j = 1` (l.156), once `S ≠ 0`. -/
lemma sum_capWeight (hN : 3 ≤ N) (hS : M.bdryS g ≠ 0) : ∑ j, M.capWeight g j = 1 := by
  unfold capWeight
  rw [← Finset.sum_div, ← M.bdryS_eq g hN, div_self hS]

lemma volMean_smul (c : ℝ) (v : D) : M.volMean g (c • v) = c * M.volMean g v := by
  unfold volMean
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, integral_const_mul]
  ring

lemma bdryAvg_smul (c : ℝ) (v : D) : M.bdryAvg g (c • v) = c * M.bdryAvg g v := by
  unfold bdryAvg
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, integral_const_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `ℓ(c v) = c ℓ(v)` (no integrability needed). -/
lemma ell_smul (c : ℝ) (v : D) : M.ell g (c • v) = c * M.ell g v := by
  unfold ell
  rw [M.volMean_smul, M.bdryAvg_smul, mul_sub]

/-- `ℓ` is additive on functions with integrable values and traces. -/
lemma ell_add {u v : D} (hu : Integrable (M.val u) (M.vol g)) (hv : Integrable (M.val v) (M.vol g))
    (hu' : ∀ j, Integrable (M.tr u) (M.bvol g j)) (hv' : ∀ j, Integrable (M.tr v) (M.bvol g j)) :
    M.ell g (u + v) = M.ell g u + M.ell g v := by
  unfold ell volMean bdryAvg
  simp only [map_add, Pi.add_apply]
  rw [integral_add hu hv]
  have : ∀ j, ∫ x, (M.tr u x + M.tr v x) ∂(M.bvol g j) =
      ∫ x, M.tr u x ∂(M.bvol g j) + ∫ x, M.tr v x ∂(M.bvol g j) :=
    fun j => integral_add (hu' j) (hv' j)
  simp only [this, mul_add, Finset.sum_add_distrib]
  ring

/-- `ℓ` is subtractive on functions with integrable values and traces. -/
lemma ell_sub {u v : D} (hu : Integrable (M.val u) (M.vol g)) (hv : Integrable (M.val v) (M.vol g))
    (hu' : ∀ j, Integrable (M.tr u) (M.bvol g j)) (hv' : ∀ j, Integrable (M.tr v) (M.bvol g j)) :
    M.ell g (u - v) = M.ell g u - M.ell g v := by
  unfold ell volMean bdryAvg
  simp only [map_sub, Pi.sub_apply]
  rw [integral_sub hu hv]
  have : ∀ j, ∫ x, (M.tr u x - M.tr v x) ∂(M.bvol g j) =
      ∫ x, M.tr u x ∂(M.bvol g j) - ∫ x, M.tr v x ∂(M.bvol g j) :=
    fun j => integral_sub (hu' j) (hv' j)
  simp only [this, mul_sub, Finset.sum_sub_distrib]
  ring

lemma volMean_one [IsFiniteMeasure (M.vol g)] (hV : M.vol g ≠ 0) : M.volMean g M.one = 1 := by
  unfold volMean
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  rw [M.val_one, integral_const, smul_eq_mul, mul_one, measureReal_def, inv_mul_cancel₀ hVpos.ne']

lemma bdryAvg_one (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)] (hS : M.bdryS g ≠ 0) :
    M.bdryAvg g M.one = 1 := by
  unfold bdryAvg
  rw [← M.sum_capWeight g hN hS]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [M.tr_one, integral_const, smul_eq_mul, mul_one, measureReal_def]
  rcases eq_or_ne (M.bvol g j Set.univ).toReal 0 with h0 | h0
  · have hp : 2 / pSharp N ≠ 0 := (div_pos two_pos (pSharp_pos hN)).ne'
    rw [h0, mul_zero]
    unfold capWeight
    rw [h0, Real.zero_rpow hp, zero_div]
  · exact div_mul_cancel₀ _ h0

/-- `ℓ` vanishes on constants (l.161). -/
lemma ell_one (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hS : M.bdryS g ≠ 0) : M.ell g M.one = 0 := by
  unfold ell
  rw [M.volMean_one g hV, M.bdryAvg_one g hN hS, sub_self]

lemma val_sub_smul_one' (c : ℝ) (v : D) : M.val (v - c • M.one) = M.val v - fun _ => c := by
  rw [map_sub, map_smul, M.val_one]
  funext x
  simp

lemma tr_sub_smul_one' (c : ℝ) (v : D) : M.tr (v - c • M.one) = M.tr v - fun _ => c := by
  rw [map_sub, map_smul, M.tr_one]
  funext x
  simp

/-- `ℓ(v − c) = ℓ(v)`: `ℓ` vanishes on constants and is linear. -/
lemma ell_sub_smul_one (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hS : M.bdryS g ≠ 0) {v : D} (hv : Integrable (M.val v) (M.vol g))
    (hv' : ∀ j, Integrable (M.tr v) (M.bvol g j)) (c : ℝ) :
    M.ell g (v - c • M.one) = M.ell g v := by
  have h1 : Integrable (M.val (c • M.one)) (M.vol g) := by
    rw [map_smul, M.val_one]; exact (integrable_const 1).smul c
  have h2 : ∀ j, Integrable (M.tr (c • M.one)) (M.bvol g j) := fun j => by
    rw [map_smul, M.tr_one]; exact (integrable_const 1).smul c
  rw [M.ell_sub g hv h1 hv' h2, M.ell_smul, M.ell_one g hN hV hS, mul_zero, sub_zero]

/-- A competitor bounds `cap*` from above. -/
lemma capStar_le {v : D} (hv : M.ell g v = 1) : M.capStar g ≤ M.energy g v :=
  iInf₂_le v hv

/-! ### `ℓ` is bounded on `W^{1,2}` (l.161, l.393) -/

/-- The coefficient `(w_j/|B_j|) |B_j|^{1 - 1/p♯}` of the boundary Hölder step. -/
def bdryCoef (j : Fin n) : ℝ :=
  M.capWeight g j / (M.bvol g j Set.univ).toReal * (M.bvol g j Set.univ).toReal ^ (1 - 1 / pSharp N)

lemma bdryCoef_nonneg (j : Fin n) : 0 ≤ M.bdryCoef g j :=
  mul_nonneg (div_nonneg (M.capWeight_nonneg g j) ENNReal.toReal_nonneg)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)

/-- `(w_j/|B_j|) |B_j|^{1 - 1/p♯} = |B_j|^{1/p♯}/S` (the proof of lem:holder, l.486–491). -/
lemma bdryCoef_eq (hN : 3 ≤ N) (j : Fin n) :
    M.bdryCoef g j = (M.bvol g j Set.univ).toReal ^ (1 / pSharp N) / M.bdryS g := by
  have hp := pSharp_pos hN
  unfold bdryCoef capWeight
  set b := (M.bvol g j Set.univ).toReal with hb
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg : 0 ≤ (M.bvol g j Set.univ).toReal) with h0 | h0
  · rw [← hb] at h0
    rw [← h0, div_zero, zero_mul, Real.zero_rpow (one_div_pos.mpr hp).ne', zero_div]
  · rw [← hb] at h0
    have e : b ^ (2 / pSharp N) * b ^ (1 - 1 / pSharp N) = b ^ (1 / pSharp N) * b := by
      rw [← Real.rpow_add h0, show 2 / pSharp N + (1 - 1 / pSharp N) = 1 / pSharp N + 1 by ring,
        Real.rpow_add h0, Real.rpow_one]
    rw [div_div, div_mul_eq_mul_div, e, mul_div_mul_right _ _ h0.ne']

lemma abs_volMean_le [IsFiniteMeasure (M.vol g)] (u : D) (hu : MemLp (M.val u) 2 (M.vol g)) :
    |M.volMean g u| ≤ (M.vol g Set.univ).toReal⁻¹ * (M.vol g Set.univ).toReal ^ (1 / 2 : ℝ) *
      (eLpNorm (M.val u) 2 (M.vol g)).toReal := by
  unfold volMean
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg), mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_integral_le_mul_eLpNorm_two hu)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- The boundary Hölder step, before Cauchy–Schwarz (l.486–487). -/
lemma abs_bdryAvg_le_sum (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)] (u : D)
    (hu : ∀ j, MemLp (M.tr u) (ENNReal.ofReal (pSharp N)) (M.bvol g j)) :
    |M.bdryAvg g u| ≤
      ∑ j, M.bdryCoef g j * (eLpNorm (M.tr u) (ENNReal.ofReal (pSharp N)) (M.bvol g j)).toReal := by
  unfold bdryAvg
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hc : 0 ≤ M.capWeight g j / (M.bvol g j Set.univ).toReal :=
    div_nonneg (M.capWeight_nonneg g j) ENNReal.toReal_nonneg
  rw [abs_mul, abs_of_nonneg hc, bdryCoef, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_le_mul_eLpNorm (by linarith [two_le_pSharp hN]) (hu j)) hc

/-- `ℓ` is bounded on `W^{1,2}(Σ)` by the trace theorem (l.161, l.393):
`|ℓ(w)| ≤ Λ ‖w‖_{W^{1,2}}`. -/
theorem ell_bounded (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hL2 : ∀ u, MemLp (M.val u) 2 (M.vol g)) (hT : M.TraceBound g) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ w : D,
      |M.ell g w| ≤ Λ * Real.sqrt (M.dirichlet g w + normSq (M.vol g) 2 (M.val w)) := by
  obtain ⟨C, hC⟩ := hT
  set A := (M.vol g Set.univ).toReal⁻¹ * (M.vol g Set.univ).toReal ^ (1 / 2 : ℝ) with hA
  have hA0 : 0 ≤ A := mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  refine ⟨A + ∑ j, M.bdryCoef g j * Real.sqrt (max C 0), add_nonneg hA0
    (Finset.sum_nonneg fun j _ => mul_nonneg (M.bdryCoef_nonneg g j) (Real.sqrt_nonneg _)),
    fun w => ?_⟩
  set W := M.dirichlet g w + normSq (M.vol g) 2 (M.val w) with hW
  have hW0 : 0 ≤ W := add_nonneg (M.dirichlet_nonneg g w) (normSq_nonneg _ _ _)
  have h1 : |M.volMean g w| ≤ A * Real.sqrt W := by
    refine (M.abs_volMean_le g w (hL2 w)).trans (mul_le_mul_of_nonneg_left ?_ hA0)
    rw [← sqrt_normSq_two]
    exact Real.sqrt_le_sqrt (by linarith [M.dirichlet_nonneg g w])
  have h2 : |M.bdryAvg g w| ≤ (∑ j, M.bdryCoef g j * Real.sqrt (max C 0)) * Real.sqrt W := by
    refine (M.abs_bdryAvg_le_sum g hN w fun j => (hC w j).1).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (M.bdryCoef_nonneg g j)
    rw [← sqrt_normSq, ← Real.sqrt_mul (le_max_right _ _)]
    refine Real.sqrt_le_sqrt ((hC w j).2.trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hW0
  unfold ell
  calc |M.volMean g w - M.bdryAvg g w| ≤ |M.volMean g w| + |M.bdryAvg g w| := abs_sub _ _
    _ ≤ A * Real.sqrt W + (∑ j, M.bdryCoef g j * Real.sqrt (max C 0)) * Real.sqrt W :=
        add_le_add h1 h2
    _ = _ := by ring

/-! ### eq:capineq from the definition of `cap*` as an infimum -/

/-- eq:capineq in multiplied form, from the definition of `cap*` alone (no hypothesis): for
every `u` of finite energy, `√cap* · ℓ(u) ≤ ‖∇u‖_{L²}`. -/
theorem sqrt_capStar_mul_ell_le (u : D) (hu : M.energy g u ≠ ⊤) :
    Real.sqrt (M.capStar g).toReal * M.ell g u ≤ Real.sqrt (M.dirichlet g u) := by
  set t := M.ell g u with ht
  rcases le_or_gt t 0 with h | h
  · exact (mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) h).trans (Real.sqrt_nonneg _)
  · have hv : M.ell g (t⁻¹ • u) = 1 := by rw [M.ell_smul, ← ht, inv_mul_cancel₀ h.ne']
    have hle := M.capStar_le g hv
    rw [M.energy_smul] at hle
    have hfin : ENNReal.ofReal ((t⁻¹) ^ 2) * M.energy g u ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu
    have h1 := ENNReal.toReal_mono hfin hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), ← dirichlet_eq_toReal_energy] at h1
    have h2 : (M.capStar g).toReal * t ^ 2 ≤ M.dirichlet g u := by
      have ht2 : 0 < t ^ 2 := by positivity
      calc (M.capStar g).toReal * t ^ 2 ≤ (t⁻¹) ^ 2 * M.dirichlet g u * t ^ 2 :=
            mul_le_mul_of_nonneg_right h1 ht2.le
        _ = M.dirichlet g u := by field_simp
    calc Real.sqrt (M.capStar g).toReal * t = Real.sqrt ((M.capStar g).toReal * t ^ 2) := by
          rw [Real.sqrt_mul ENNReal.toReal_nonneg, Real.sqrt_sq h.le]
      _ ≤ Real.sqrt (M.dirichlet g u) := Real.sqrt_le_sqrt h2

/-- If `cap* = ∞`, `ℓ` vanishes on every function of finite energy. -/
lemma ell_eq_zero_of_capStar_eq_top (h : M.capStar g = ⊤) (u : D) (hu : M.energy g u ≠ ⊤) :
    M.ell g u = 0 := by
  by_contra ht
  have hv : M.ell g ((M.ell g u)⁻¹ • u) = 1 := by rw [M.ell_smul, inv_mul_cancel₀ ht]
  have hle := M.capStar_le g hv
  rw [M.energy_smul, h, top_le_iff] at hle
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu hle

/-- `cap* < ∞` (l.399–401): the interior bump `v` has `ℓ(v) = V⁻¹ ∫ v ≠ 0`. -/
theorem capStar_lt_top [IsFiniteMeasure (M.vol g)] (hV : M.vol g ≠ 0) (hI : M.InteriorBump g) :
    M.capStar g < ⊤ := by
  obtain ⟨v, hfin, htr, hint⟩ := hI
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  have hb : M.bdryAvg g v = 0 := by
    unfold bdryAvg
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_congr_ae (htr j)]
    simp
  have hl : M.ell g v ≠ 0 := by
    unfold ell volMean
    rw [hb, sub_zero]
    exact mul_ne_zero (inv_ne_zero hVpos.ne') hint
  rw [lt_top_iff_ne_top]
  intro htop
  exact hl (M.ell_eq_zero_of_capStar_eq_top g htop v hfin)

/-- `cap* ≥ L⁻²` whenever `|ℓ(v)| ≤ L ‖∇v‖_{L²}` (l.399–400). -/
theorem capStar_ge_of_abs_ell_le {L : ℝ} (hL : ∀ v : D, |M.ell g v| ≤ L * Real.sqrt (M.dirichlet g v)) :
    ENNReal.ofReal (L ^ 2)⁻¹ ≤ M.capStar g := by
  refine le_iInf₂ fun v hv => ?_
  by_cases hfin : M.energy g v = ⊤
  · rw [hfin]; exact le_top
  · have h1 : 1 ≤ L * Real.sqrt (M.dirichlet g v) := by
      have := hL v; rwa [hv, abs_one] at this
    have hd0 := M.dirichlet_nonneg g v
    have hsq := Real.sq_sqrt hd0
    have h2 : 1 ≤ L ^ 2 * M.dirichlet g v := by
      have h0 : 0 ≤ L * Real.sqrt (M.dirichlet g v) := by linarith
      nlinarith
    have hL2 : 0 < L ^ 2 := by
      rcases lt_trichotomy (L ^ 2) 0 with h | h | h
      · exact absurd h (not_lt.mpr (sq_nonneg L))
      · rw [h, zero_mul] at h2; linarith
      · exact h
    rw [← ENNReal.ofReal_toReal hfin, ← dirichlet_eq_toReal_energy]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (L ^ 2)⁻¹ = (L ^ 2)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (L ^ 2)⁻¹ * (L ^ 2 * M.dirichlet g v) :=
          mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hL2.le)
      _ = M.dirichlet g v := by rw [← mul_assoc, inv_mul_cancel₀ hL2.ne', one_mul]

/-- The Poincaré step (l.394–398): `|ℓ(v)| = |ℓ(v − v̄)| ≤ Λ ‖v − v̄‖_{W^{1,2}}
≤ Λ (1 + √K) ‖∇v‖_{L²}`. -/
theorem abs_ell_le_of_bounds (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hS : M.bdryS g ≠ 0)
    (hL1 : ∀ u, Integrable (M.val u) (M.vol g)) (hL1' : ∀ u j, Integrable (M.tr u) (M.bvol g j))
    {Λ K : ℝ} (hΛ : 0 ≤ Λ) (hK : 0 ≤ K)
    (hell : ∀ w : D, |M.ell g w| ≤ Λ * Real.sqrt (M.dirichlet g w + normSq (M.vol g) 2 (M.val w)))
    (hP : ∀ v : D, normSq (M.vol g) 2 (M.val v - fun _ => M.volMean g v) ≤ K * M.dirichlet g v)
    (v : D) : |M.ell g v| ≤ Λ * (1 + Real.sqrt K) * Real.sqrt (M.dirichlet g v) := by
  set c := M.volMean g v
  have h1 := hell (v - c • M.one)
  rw [M.ell_sub_smul_one g hN hV hS (hL1 v) (hL1' v) c, M.val_sub_smul_one' c v] at h1
  have hd : M.dirichlet g (v - c • M.one) = M.dirichlet g v := by
    rw [dirichlet_eq_toReal_energy, dirichlet_eq_toReal_energy, M.energy_sub_smul_one]
  rw [hd] at h1
  have hd0 := M.dirichlet_nonneg g v
  have h2 : Real.sqrt (M.dirichlet g v + normSq (M.vol g) 2 (M.val v - fun _ => c)) ≤
      (1 + Real.sqrt K) * Real.sqrt (M.dirichlet g v) := by
    calc Real.sqrt (M.dirichlet g v + normSq (M.vol g) 2 (M.val v - fun _ => c))
        ≤ Real.sqrt ((1 + K) * M.dirichlet g v) := Real.sqrt_le_sqrt (by linarith [hP v])
      _ = Real.sqrt (1 + K) * Real.sqrt (M.dirichlet g v) := Real.sqrt_mul (by linarith) _
      _ ≤ (1 + Real.sqrt K) * Real.sqrt (M.dirichlet g v) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          rw [Real.sqrt_le_left (by positivity)]
          nlinarith [Real.sq_sqrt hK, Real.sqrt_nonneg K]
  calc |M.ell g v| ≤ Λ * Real.sqrt (M.dirichlet g v + normSq (M.vol g) 2 (M.val v - fun _ => c)) := h1
    _ ≤ Λ * ((1 + Real.sqrt K) * Real.sqrt (M.dirichlet g v)) := mul_le_mul_of_nonneg_left h2 hΛ
    _ = _ := by ring

/-- The positivity of `cap*` with the paper's explicit bound (l.394–400): if
`|ℓ(w)| ≤ Λ ‖w‖_{W^{1,2}}` and `‖v − v̄‖²_{L²} ≤ K ‖∇v‖²`, then
`cap* ≥ [Λ (1 + √K)]⁻²` (the paper's `[‖ℓ‖ (1 + λ_1^{-1/2})]⁻²`). -/
theorem capStar_ge (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hS : M.bdryS g ≠ 0)
    (hL1 : ∀ u, Integrable (M.val u) (M.vol g)) (hL1' : ∀ u j, Integrable (M.tr u) (M.bvol g j))
    {Λ K : ℝ} (hΛ : 0 ≤ Λ) (hK : 0 ≤ K)
    (hell : ∀ w : D, |M.ell g w| ≤ Λ * Real.sqrt (M.dirichlet g w + normSq (M.vol g) 2 (M.val w)))
    (hP : ∀ v : D, normSq (M.vol g) 2 (M.val v - fun _ => M.volMean g v) ≤ K * M.dirichlet g v) :
    ENNReal.ofReal ((Λ * (1 + Real.sqrt K)) ^ 2)⁻¹ ≤ M.capStar g :=
  M.capStar_ge_of_abs_ell_le g (M.abs_ell_le_of_bounds g hN hV hS hL1 hL1' hΛ hK hell hP)

lemma integrable_val_of_poincare [IsFiniteMeasure (M.vol g)] (hP : M.MeanPoincare g) (u : D) :
    Integrable (M.val u) (M.vol g) := by
  obtain ⟨K, hK⟩ := hP
  exact (hK u).1.integrable one_le_two

lemma memLp_tr_two (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)] {u : D} {j : Fin n}
    (hu : MemLp (M.tr u) (ENNReal.ofReal (pSharp N)) (M.bvol g j)) :
    MemLp (M.tr u) 2 (M.bvol g j) :=
  hu.mono_exponent (by
    rw [← ENNReal.ofReal_ofNat]; exact ENNReal.ofReal_le_ofReal (two_le_pSharp hN))

lemma integrable_tr_of_traceBound (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hT : M.TraceBound g) (u : D) (j : Fin n) : Integrable (M.tr u) (M.bvol g j) := by
  obtain ⟨C, hC⟩ := hT
  exact (M.memLp_tr_two g hN (hC u j).1).integrable one_le_two

/-- `|ℓ(v)| ≤ L ‖∇v‖_{L²}` under the trace theorem and the Poincaré inequality (l.394–399). -/
theorem abs_ell_le (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hS : M.bdryS g ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ v : D, |M.ell g v| ≤ L * Real.sqrt (M.dirichlet g v) := by
  obtain ⟨Λ, hΛ, hell⟩ := M.ell_bounded g hN (fun u => (hP.choose_spec u).1) hT
  obtain ⟨K, hK⟩ := hP
  have hK' : ∀ v : D, normSq (M.vol g) 2 (M.val v - fun _ => M.volMean g v) ≤
      max K 0 * M.dirichlet g v := fun v =>
    (hK v).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (M.dirichlet_nonneg g v))
  refine ⟨Λ * (1 + Real.sqrt (max K 0)), by positivity, ?_⟩
  exact M.abs_ell_le_of_bounds g hN hV hS (M.integrable_val_of_poincare g ⟨K, hK⟩)
    (M.integrable_tr_of_traceBound g hN hT) hΛ (le_max_right _ _) hell hK'

/-- `0 < cap*` (l.394–400). -/
theorem capStar_pos (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hS : M.bdryS g ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g) :
    0 < M.capStar g := by
  obtain ⟨L, hL0, hL⟩ := M.abs_ell_le g hN hV hS hP hT
  have hL' : ∀ v : D, |M.ell g v| ≤ (L + 1) * Real.sqrt (M.dirichlet g v) := fun v =>
    (hL v).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
  refine lt_of_lt_of_le ?_ (M.capStar_ge_of_abs_ell_le g hL')
  rw [ENNReal.ofReal_pos]
  positivity

/-- eq:capineq (l.383–384) for every `u ∈ D`. -/
theorem capineq (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hS : M.bdryS g ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (u : D) :
    M.volMean g u - M.bdryAvg g u ≤ Real.sqrt (M.dirichlet g u) / Real.sqrt (M.capStar g).toReal := by
  change M.ell g u ≤ _
  by_cases hfin : M.energy g u = ⊤
  · -- infinite energy: `dirichlet u = 0`, and the bound `|ℓ u| ≤ L ‖∇u‖` gives `ℓ u = 0`
    obtain ⟨L, _, hL⟩ := M.abs_ell_le g hN hV hS hP hT
    have hd : M.dirichlet g u = 0 := by rw [dirichlet_eq_toReal_energy, hfin, ENNReal.toReal_top]
    have h := hL u
    rw [hd, Real.sqrt_zero, mul_zero] at h
    rw [hd, Real.sqrt_zero, zero_div]
    exact (le_abs_self _).trans h
  · by_cases htop : M.capStar g = ⊤
    · rw [M.ell_eq_zero_of_capStar_eq_top g htop u hfin, htop, ENNReal.toReal_top, Real.sqrt_zero,
        div_zero]
    · have hpos : 0 < (M.capStar g).toReal :=
        ENNReal.toReal_pos (M.capStar_pos g hN hV hS hP hT).ne' htop
      rw [le_div_iff₀ (Real.sqrt_pos.mpr hpos), mul_comm]
      exact M.sqrt_capStar_mul_ell_le g u hfin

/-- `|ℓ(z)|` against the `L²` norms of the values and of the traces. -/
lemma abs_ell_le_L2 [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)] (z : D)
    (hz : MemLp (M.val z) 2 (M.vol g)) (hz' : ∀ j, MemLp (M.tr z) 2 (M.bvol g j)) :
    |M.ell g z| ≤ (M.vol g Set.univ).toReal⁻¹ * (M.vol g Set.univ).toReal ^ (1 / 2 : ℝ) *
        (eLpNorm (M.val z) 2 (M.vol g)).toReal +
      ∑ j, M.capWeight g j / (M.bvol g j Set.univ).toReal *
        ((M.bvol g j Set.univ).toReal ^ (1 / 2 : ℝ) * (eLpNorm (M.tr z) 2 (M.bvol g j)).toReal) := by
  unfold ell
  refine (abs_sub _ _).trans (add_le_add (M.abs_volMean_le g z hz) ?_)
  unfold bdryAvg
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  have hc : 0 ≤ M.capWeight g j / (M.bvol g j Set.univ).toReal :=
    div_nonneg (M.capWeight_nonneg g j) ENNReal.toReal_nonneg
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (abs_integral_le_mul_eLpNorm_two (hz' j)) hc

/-- The infimum is attained (l.402–404), by the direct method. -/
theorem capStar_attained (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hS : M.bdryS g ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (hI : M.InteriorBump g) (hDM : M.DirectMethod g) :
    ∃ v : D, M.ell g v = 1 ∧ M.energy g v = M.capStar g := by
  have hfin : M.capStar g ≠ ⊤ := (M.capStar_lt_top g hV hI).ne
  set c := (M.capStar g).toReal with hc
  have hL1 := M.integrable_val_of_poincare g hP
  have hL1' := M.integrable_tr_of_traceBound g hN hT
  -- a minimising sequence
  have hex : ∀ k : ℕ, ∃ v : D, M.ell g v = 1 ∧
      M.energy g v < M.capStar g + ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
    intro k
    have hlt : M.capStar g < M.capStar g + ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
      ENNReal.lt_add_right hfin (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity)
    obtain ⟨v, hv⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hv1, hv2⟩ := iInf_lt_iff.mp hv
    exact ⟨v, hv1, hv2⟩
  choose v hv1 hv2 using hex
  set u : ℕ → D := fun k => v k - M.volMean g (v k) • M.one with hu
  have hu1 : ∀ k, M.ell g (u k) = 1 := fun k => by
    simp only [hu]; rw [M.ell_sub_smul_one g hN hV hS (hL1 _) (hL1' _), hv1]
  have huE : ∀ k, M.energy g (u k) = M.energy g (v k) := fun k => M.energy_sub_smul_one g _ _
  have hufin : ∀ k, M.energy g (u k) ≠ ⊤ := fun k => by
    rw [huE]
    exact (lt_of_lt_of_le (hv2 k) le_top).ne
  have hlo : ∀ k, c ≤ M.dirichlet g (u k) := fun k =>
    ENNReal.toReal_mono (hufin k) (M.capStar_le g (hu1 k))
  have hhi : ∀ k, M.dirichlet g (u k) ≤ c + 1 / ((k : ℝ) + 1) := fun k => by
    rw [dirichlet_eq_toReal_energy, huE]
    have hne : M.capStar g + ENNReal.ofReal (1 / ((k : ℝ) + 1)) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hfin, ENNReal.ofReal_ne_top⟩
    have := ENNReal.toReal_mono hne (hv2 k).le
    rwa [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at this
  have hconv : Tendsto (fun k => M.dirichlet g (u k)) atTop (𝓝 c) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hlo hhi
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add c
  obtain ⟨K, hK⟩ := hP
  have hbd : ∃ K' : ℝ, ∀ k, M.dirichlet g (u k) + normSq (M.vol g) 2 (M.val (u k)) ≤ K' := by
    refine ⟨(c + 1) + max K 0 * (c + 1), fun k => ?_⟩
    have h1 : M.dirichlet g (u k) ≤ c + 1 := by
      have : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      linarith [hhi k]
    have h2 : normSq (M.vol g) 2 (M.val (u k)) ≤ max K 0 * (c + 1) := by
      simp only [hu]
      rw [M.val_sub_smul_one']
      calc normSq (M.vol g) 2 (M.val (v k) - fun _ => M.volMean g (v k))
          ≤ K * M.dirichlet g (v k) := (hK (v k)).2
        _ ≤ max K 0 * M.dirichlet g (v k) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (M.dirichlet_nonneg g _)
        _ = max K 0 * M.dirichlet g (u k) := by
            rw [dirichlet_eq_toReal_energy, dirichlet_eq_toReal_energy, huE]
        _ ≤ max K 0 * (c + 1) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
    linarith
  obtain ⟨φ, hφ, w, hwE, hwv, hwt⟩ := hDM u c hufin hbd hconv
  -- `ℓ(w) = 1`, by continuity of `ℓ` along the `L²` convergences
  have hw1 : M.ell g w = 1 := by
    obtain ⟨C, hC⟩ := hT
    have hdiff : ∀ k, |1 - M.ell g w| ≤
        (M.vol g Set.univ).toReal⁻¹ * (M.vol g Set.univ).toReal ^ (1 / 2 : ℝ) *
          (eLpNorm (M.val (u (φ k)) - M.val w) 2 (M.vol g)).toReal +
        ∑ j, M.capWeight g j / (M.bvol g j Set.univ).toReal *
          ((M.bvol g j Set.univ).toReal ^ (1 / 2 : ℝ) *
            (eLpNorm (M.tr (u (φ k)) - M.tr w) 2 (M.bvol g j)).toReal) := by
      intro k
      have e : 1 - M.ell g w = M.ell g (u (φ k) - w) := by
        rw [M.ell_sub g (hL1 _) (hL1 _) (hL1' _) (hL1' _), hu1]
      rw [e]
      have h := M.abs_ell_le_L2 g (u (φ k) - w) ((hK _).1)
        (fun j => M.memLp_tr_two g hN (hC _ j).1)
      simpa only [map_sub] using h
    have hlim : Tendsto (fun k =>
        (M.vol g Set.univ).toReal⁻¹ * (M.vol g Set.univ).toReal ^ (1 / 2 : ℝ) *
          (eLpNorm (M.val (u (φ k)) - M.val w) 2 (M.vol g)).toReal +
        ∑ j, M.capWeight g j / (M.bvol g j Set.univ).toReal *
          ((M.bvol g j Set.univ).toReal ^ (1 / 2 : ℝ) *
            (eLpNorm (M.tr (u (φ k)) - M.tr w) 2 (M.bvol g j)).toReal)) atTop (𝓝 0) := by
      have ht0 : ∀ {f : ℕ → ℝ≥0∞}, Tendsto f atTop (𝓝 0) →
          Tendsto (fun k => (f k).toReal) atTop (𝓝 0) := fun hf => by
        have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hf
        rw [ENNReal.toReal_zero] at h
        exact h
      have h1 := (ht0 hwv).const_mul
        ((M.vol g Set.univ).toReal⁻¹ * (M.vol g Set.univ).toReal ^ (1 / 2 : ℝ))
      have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun j _ =>
        ((ht0 (hwt j)).const_mul ((M.bvol g j Set.univ).toReal ^ (1 / 2 : ℝ))).const_mul
          (M.capWeight g j / (M.bvol g j Set.univ).toReal)
      simpa using h1.add h2
    have h0 : |1 - M.ell g w| ≤ 0 := ge_of_tendsto' hlim hdiff
    have := abs_nonpos_iff.mp h0
    linarith
  refine ⟨w, hw1, le_antisymm ?_ (M.capStar_le g hw1)⟩
  rw [hc, ENNReal.ofReal_toReal hfin] at hwE
  exact hwE

/-! ### The Euler–Lagrange system, in weak form -/

lemma gradInner_comm (u w : D) (x : X) : M.gradInner g u w x = M.gradInner g w u x := by
  unfold gradInner
  have hsym : ((g.G x)⁻¹)ᵀ = (g.G x)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, transpose_eq_of_posDef (g.posDef x)]
  exact dotProduct_mulVec_symm hsym _ _

lemma gradInner_self (u : D) (x : X) : M.gradInner g u u x = M.gradSq g u x := rfl

lemma gradInner_add_right (u w z : D) (x : X) :
    M.gradInner g u (w + z) x = M.gradInner g u w x + M.gradInner g u z x := by
  unfold gradInner
  rw [map_add, Pi.add_apply, Matrix.mulVec_add, dotProduct_add]

lemma gradInner_smul_right (u w : D) (c : ℝ) (x : X) :
    M.gradInner g u (c • w) x = c * M.gradInner g u w x := by
  unfold gradInner
  rw [map_smul, Pi.smul_apply, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/-- `|∇(u + t w)|² = |∇u|² + 2t ⟨∇u, ∇w⟩ + t² |∇w|²`. -/
lemma gradSq_add_smul (u w : D) (t : ℝ) (x : X) :
    M.gradSq g (u + t • w) x =
      M.gradSq g u x + 2 * t * M.gradInner g u w x + t ^ 2 * M.gradSq g w x := by
  have hc := M.gradInner_comm g w u x
  unfold gradInner at hc
  unfold gradSq gradInner
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, Matrix.mulVec_add, Matrix.mulVec_smul,
    add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [hc]
  ring

/-- `|∇(u + t w)|² ≤ 2 |∇u|² + 2 t² |∇w|²`. -/
lemma gradSq_add_smul_le (u w : D) (t : ℝ) (x : X) :
    M.gradSq g (u + t • w) x ≤ 2 * M.gradSq g u x + 2 * t ^ 2 * M.gradSq g w x := by
  have h1 := M.gradSq_add_smul g u w t x
  have h2 := M.gradSq_add_smul g u w (-t) x
  have h3 := M.gradSq_nonneg g (u + (-t) • w) x
  nlinarith

variable {M g}

lemma integrable_gradSq (hG : M.GradMeasurable g) {u : D} (hu : M.energy g u ≠ ⊤) :
    Integrable (M.gradSq g u) (M.vol g) :=
  ⟨hG u, (hasFiniteIntegral_iff_ofReal (ae_of_all _ (M.gradSq_nonneg g u))).mpr
    (lt_top_iff_ne_top.mpr hu)⟩

lemma dirichlet_eq_integral (hG : M.GradMeasurable g) (u : D) :
    M.dirichlet g u = ∫ x, M.gradSq g u x ∂(M.vol g) :=
  (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (M.gradSq_nonneg g u)) (hG u)).symm

lemma integrable_gradSq_add_smul (hG : M.GradMeasurable g) {u w : D}
    (hu : Integrable (M.gradSq g u) (M.vol g)) (hw : Integrable (M.gradSq g w) (M.vol g)) (t : ℝ) :
    Integrable (M.gradSq g (u + t • w)) (M.vol g) := by
  refine Integrable.mono' ((hu.const_mul 2).add (hw.const_mul (2 * t ^ 2))) (hG _)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (M.gradSq_nonneg g _ x)]
  exact M.gradSq_add_smul_le g u w t x

lemma energy_ne_top_of_integrable {u : D} (hu : Integrable (M.gradSq g u) (M.vol g)) :
    M.energy g u ≠ ⊤ := by
  unfold energy
  rw [← ofReal_integral_eq_lintegral_ofReal hu (ae_of_all _ (M.gradSq_nonneg g u))]
  exact ENNReal.ofReal_ne_top

lemma integrable_gradInner (hG : M.GradMeasurable g) {u w : D}
    (hu : Integrable (M.gradSq g u) (M.vol g)) (hw : Integrable (M.gradSq g w) (M.vol g)) :
    Integrable (M.gradInner g u w) (M.vol g) := by
  have e : M.gradInner g u w =
      fun x => (M.gradSq g (u + (1 : ℝ) • w) x - M.gradSq g u x - M.gradSq g w x) / 2 := by
    funext x
    rw [M.gradSq_add_smul g u w 1 x]
    ring
  rw [e]
  exact (((integrable_gradSq_add_smul hG hu hw 1).sub hu).sub hw).div_const 2

lemma integral_gradSq_add_smul (hG : M.GradMeasurable g) {u w : D}
    (hu : Integrable (M.gradSq g u) (M.vol g)) (hw : Integrable (M.gradSq g w) (M.vol g)) (t : ℝ) :
    ∫ x, M.gradSq g (u + t • w) x ∂(M.vol g) =
      ∫ x, M.gradSq g u x ∂(M.vol g) + 2 * t * ∫ x, M.gradInner g u w x ∂(M.vol g) +
        t ^ 2 * ∫ x, M.gradSq g w x ∂(M.vol g) := by
  simp only [M.gradSq_add_smul g u w t]
  have hi := integrable_gradInner hG hu hw
  have h1 : Integrable (fun x => M.gradSq g u x + 2 * t * M.gradInner g u w x) (M.vol g) :=
    hu.add (hi.const_mul _)
  have h2 : Integrable (fun x => t ^ 2 * M.gradSq g w x) (M.vol g) := hw.const_mul _
  have h3 : Integrable (fun x => 2 * t * M.gradInner g u w x) (M.vol g) := hi.const_mul _
  rw [integral_add h1 h2, integral_add hu h3, integral_const_mul, integral_const_mul]

variable (M g)

/-- The Euler–Lagrange system of a minimiser, in weak form (l.386–388, l.405–406): with
`μ = 2 cap*`, `∫ ⟨∇v, ∇φ⟩ = (μ/2) ℓ(φ)` for every `φ` of finite energy, and pairing with `v`,
`‖∇v‖² = (μ/2) ℓ(v) = μ/2`. -/
theorem euler_lagrange
    (hL1 : ∀ u, Integrable (M.val u) (M.vol g)) (hL1' : ∀ u j, Integrable (M.tr u) (M.bvol g j))
    (hG : M.GradMeasurable g) (hfin : M.capStar g ≠ ⊤)
    {v : D} (hv : M.ell g v = 1) (hmin : M.energy g v = M.capStar g) :
    (∀ φ : D, M.energy g φ ≠ ⊤ →
      ∫ x, M.gradInner g v φ x ∂(M.vol g) = (2 * (M.capStar g).toReal) / 2 * M.ell g φ) ∧
    M.dirichlet g v = (2 * (M.capStar g).toReal) / 2 * M.ell g v ∧
    M.dirichlet g v = (2 * (M.capStar g).toReal) / 2 := by
  set c := (M.capStar g).toReal with hc
  have hvfin : M.energy g v ≠ ⊤ := by rw [hmin]; exact hfin
  have hvI := integrable_gradSq hG hvfin
  have hdv : M.dirichlet g v = c := by rw [dirichlet_eq_toReal_energy, hmin]
  have hc2 : 2 * c / 2 = c := by ring
  rw [hc2]
  refine ⟨fun φ hφ => ?_, by rw [hv, mul_one, hdv], hdv⟩
  set a := M.ell g φ with ha
  set ψ : D := φ + (-a) • v with hψ
  have hφI := integrable_gradSq hG hφ
  have hψI : Integrable (M.gradSq g ψ) (M.vol g) := integrable_gradSq_add_smul hG hφI hvI (-a)
  have hψ0 : M.ell g ψ = 0 := by
    rw [hψ, M.ell_add g (hL1 _) (hL1 _) (hL1' _) (hL1' _), M.ell_smul, hv, ← ha]
    ring
  -- the quadratic `t ↦ ‖∇(v + tψ)‖²` is minimal at `t = 0`
  set B := ∫ x, M.gradInner g v ψ x ∂(M.vol g) with hB
  set E := ∫ x, M.gradSq g ψ x ∂(M.vol g) with hE
  have hE0 : 0 ≤ E := integral_nonneg fun x => M.gradSq_nonneg g ψ x
  have hquad : ∀ t : ℝ, 0 ≤ 2 * t * B + t ^ 2 * E := by
    intro t
    have hl : M.ell g (v + t • ψ) = 1 := by
      rw [M.ell_add g (hL1 _) (hL1 _) (hL1' _) (hL1' _), M.ell_smul, hψ0, hv]
      ring
    have hI := integrable_gradSq_add_smul hG hvI hψI t
    have hle := M.capStar_le g hl
    unfold energy at hle
    rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ (M.gradSq_nonneg g _))] at hle
    have h1 := ENNReal.toReal_le_of_le_ofReal (integral_nonneg fun x => M.gradSq_nonneg g _ x) hle
    rw [integral_gradSq_add_smul hG hvI hψI t, ← dirichlet_eq_integral hG, hdv] at h1
    linarith
  have hB0 : B = 0 := by
    have h := hquad (-B / (E + 1))
    have hE1 : 0 < E + 1 := by linarith
    have h' : 0 ≤ -(B ^ 2) * (E + 2) := by
      have e : 2 * (-B / (E + 1)) * B + (-B / (E + 1)) ^ 2 * E =
          -(B ^ 2) * (E + 2) / (E + 1) ^ 2 := by
        field_simp; ring
      rw [e] at h
      exact (div_nonneg_iff.mp h).elim (fun h => h.1) fun h => absurd h.2 (not_le.mpr (by positivity))
    have hB2 : B ^ 2 ≤ 0 := by nlinarith
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (le_antisymm hB2 (sq_nonneg B))
  -- `φ = ψ + a v`, so `∫ ⟨∇v, ∇φ⟩ = B + a ‖∇v‖² = a c`
  have hφeq : φ = ψ + a • v := by rw [hψ, neg_smul]; abel
  have hpt : ∀ x, M.gradInner g v φ x = M.gradInner g v ψ x + a * M.gradSq g v x := by
    intro x
    conv_lhs => rw [hφeq]
    rw [M.gradInner_add_right, M.gradInner_smul_right, M.gradInner_self]
  simp only [hpt]
  rw [integral_add (integrable_gradInner hG hvI hψI) (hvI.const_mul a), integral_const_mul,
    ← hB, hB0, ← dirichlet_eq_integral hG, hdv]
  ring

/-! ### lem:capstar and lem:capacitary -/

/-- lem:capstar (l.376–390) over the model, its first three assertions: `0 < cap* < ∞` and
eq:capineq for every `u`. -/
theorem lem_capstar (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (hI : M.InteriorBump g) :
    0 < M.capStar g ∧ M.capStar g < ⊤ ∧ ∀ u : D,
      M.volMean g u - M.bdryAvg g u ≤ Real.sqrt (M.dirichlet g u) / Real.sqrt (M.capStar g).toReal := by
  have hS := (M.bdryS_pos g hB).ne'
  exact ⟨M.capStar_pos g hN hV hS hP hT, M.capStar_lt_top g hV hI, M.capineq g hN hV hS hP hT⟩

/-- lem:capstar (l.376–390) over the model, the minimiser: under the direct method the infimum is
attained, and the minimiser satisfies the Euler–Lagrange system in weak form. -/
theorem lem_capstar_minimiser (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (hI : M.InteriorBump g) (hDM : M.DirectMethod g) (hG : M.GradMeasurable g) :
    ∃ v : D, M.ell g v = 1 ∧ M.energy g v = M.capStar g ∧
      (∀ φ : D, M.energy g φ ≠ ⊤ →
        ∫ x, M.gradInner g v φ x ∂(M.vol g) = (2 * (M.capStar g).toReal) / 2 * M.ell g φ) ∧
      M.dirichlet g v = (2 * (M.capStar g).toReal) / 2 := by
  have hS := (M.bdryS_pos g hB).ne'
  obtain ⟨v, hv1, hvE⟩ := M.capStar_attained g hN hV hS hP hT hI hDM
  obtain ⟨h1, _, h3⟩ := M.euler_lagrange g (M.integrable_val_of_poincare g hP)
    (M.integrable_tr_of_traceBound g hN hT) hG (M.capStar_lt_top g hV hI).ne hv1 hvE
  exact ⟨v, hv1, hvE, h1, h3⟩

/-- lem:capacitary (l.468–472), for every `u ∈ D` (no sign condition). -/
theorem lem_capacitary (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (u : D) :
    M.volMean g u ≤ M.bdryAvg g u + Real.sqrt (M.dirichlet g u) / Real.sqrt (M.capStar g).toReal := by
  have h := M.capineq g hN hV (M.bdryS_pos g hB).ne' hP hT u
  linarith

/-! ### lem:holder -/

/-- lem:holder (l.480), the inequality, for every `u` whose traces are in `L^{p♯}` (no sign
condition), in absolute value: `|Σ_j (w_j/|B_j|) ∫_{B_j} u| ≤ Y/√S`. -/
theorem abs_bdryAvg_le (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)] (u : D)
    (hu : ∀ j, MemLp (M.tr u) (ENNReal.ofReal (pSharp N)) (M.bvol g j)) :
    |M.bdryAvg g u| ≤ M.bdryY g u / Real.sqrt (M.bdryS g) := by
  have hp := pSharp_pos hN
  set y : Fin n → ℝ := fun j => (eLpNorm (M.tr u) (ENNReal.ofReal (pSharp N)) (M.bvol g j)).toReal
    with hy
  set β : Fin n → ℝ := fun j => (M.bvol g j Set.univ).toReal ^ (1 / pSharp N) with hβ
  have hβsq : ∑ j, β j ^ 2 = M.bdryS g := by
    rw [M.bdryS_eq g hN]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hβ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
    congr 1; push_cast; ring
  have hysq : ∑ j, y j ^ 2 = ∑ j, normSq (M.bvol g j) (pSharp N) (M.tr u) := rfl
  calc |M.bdryAvg g u| ≤ ∑ j, M.bdryCoef g j * y j := M.abs_bdryAvg_le_sum g hN u hu
    _ = (∑ j, β j * y j) / M.bdryS g := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [M.bdryCoef_eq g hN]
        ring
    _ ≤ (Real.sqrt (∑ j, β j ^ 2) * Real.sqrt (∑ j, y j ^ 2)) / M.bdryS g :=
        div_le_div_of_nonneg_right (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) (M.bdryS_nonneg g)
    _ = Real.sqrt (M.bdryS g) * M.bdryY g u / M.bdryS g := by rw [hβsq, hysq]; rfl
    _ = M.bdryY g u / Real.sqrt (M.bdryS g) := by
        rcases eq_or_lt_of_le (M.bdryS_nonneg g) with h0 | h0
        · rw [← h0]; simp
        · have hs := Real.sqrt_pos.mpr h0
          rw [div_eq_div_iff h0.ne' hs.ne']
          have := Real.mul_self_sqrt h0.le
          calc Real.sqrt (M.bdryS g) * M.bdryY g u * Real.sqrt (M.bdryS g)
              = M.bdryY g u * (Real.sqrt (M.bdryS g) * Real.sqrt (M.bdryS g)) := by ring
            _ = M.bdryY g u * M.bdryS g := by rw [this]

/-- The objective `Σ_j w_j² |B_j|^{-2/p♯}` of lem:holder (l.482). -/
def holderObj (w : Fin n → ℝ) : ℝ :=
  ∑ j, w j ^ 2 * (M.bvol g j Set.univ).toReal ^ (-(2 / pSharp N))

/-- The identity behind the minimisation (l.493–494): on `Σ_j w_j = 1`,
`Σ_j w_j² |B_j|^{-2/p♯} = 1/S + Σ_j (w_j − w*_j)² |B_j|^{-2/p♯}`. -/
theorem holderObj_eq (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)] (hB : ∀ j, M.bvol g j ≠ 0)
    (hn : 0 < n) {w : Fin n → ℝ} (hw : ∑ j, w j = 1) :
    M.holderObj g w = 1 / M.bdryS g + ∑ j, (w j - M.capWeight g j) ^ 2 *
      (M.bvol g j Set.univ).toReal ^ (-(2 / pSharp N)) := by
  have hS : 0 < M.bdryS g := M.bdryS_pos g ⟨⟨0, hn⟩, hB _⟩
  have hb : ∀ j, 0 < (M.bvol g j Set.univ).toReal ^ (2 / pSharp N) := fun j =>
    Real.rpow_pos_of_pos
      (ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr (hB j)) (measure_ne_top _ _)) _
  unfold holderObj capWeight
  simp only [Real.rpow_neg ENNReal.toReal_nonneg]
  set β : Fin n → ℝ := fun j => (M.bvol g j Set.univ).toReal ^ (2 / pSharp N) with hβ
  have hSβ : M.bdryS g = ∑ j, β j := M.bdryS_eq g hN
  have key : ∀ j, (w j - β j / M.bdryS g) ^ 2 * (β j)⁻¹ =
      w j ^ 2 * (β j)⁻¹ - 2 * w j / M.bdryS g + β j / M.bdryS g ^ 2 := by
    intro j
    have hβj : β j ≠ 0 := (hb j).ne'
    field_simp
    ring
  change ∑ j, w j ^ 2 * (β j)⁻¹ = 1 / M.bdryS g + ∑ j, (w j - β j / M.bdryS g) ^ 2 * (β j)⁻¹
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : ∑ j, 2 * w j / M.bdryS g = 2 / M.bdryS g := by
    rw [← Finset.sum_div, ← Finset.mul_sum, hw, mul_one]
  have h2 : ∑ j, β j / M.bdryS g ^ 2 = 1 / M.bdryS g := by
    rw [← Finset.sum_div, ← hSβ]
    field_simp
  rw [h1, h2]
  ring

/-- **lem:holder** (l.478–483) over the model: the inequality, for every `u` whose traces are in
`L^{p♯}`, and the weights `w_j = |B_j|^{2/p♯}/S` as the unique minimisers of
`Σ_j w_j² |B_j|^{-2/p♯}` on the simplex, with minimum value `1/S` (l.494). -/
theorem lem_holder (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)] :
    (∀ u : D, (∀ j, MemLp (M.tr u) (ENNReal.ofReal (pSharp N)) (M.bvol g j)) →
      M.bdryAvg g u ≤ M.bdryY g u / Real.sqrt (M.bdryS g)) ∧
    ((∀ j, M.bvol g j ≠ 0) → 0 < n →
      ((∀ j, 0 ≤ M.capWeight g j) ∧ ∑ j, M.capWeight g j = 1) ∧
      M.holderObj g (M.capWeight g) = 1 / M.bdryS g ∧
      (∀ w : Fin n → ℝ, (∀ j, 0 ≤ w j) → ∑ j, w j = 1 →
        M.holderObj g (M.capWeight g) ≤ M.holderObj g w ∧
        (M.holderObj g w = M.holderObj g (M.capWeight g) → w = M.capWeight g))) := by
  refine ⟨fun u hu => (le_abs_self _).trans (M.abs_bdryAvg_le g hN u hu), fun hB hn => ?_⟩
  have hS : 0 < M.bdryS g := M.bdryS_pos g ⟨⟨0, hn⟩, hB _⟩
  have hsum := M.sum_capWeight g hN hS.ne'
  have hpos : ∀ j, 0 < (M.bvol g j Set.univ).toReal ^ (-(2 / pSharp N)) := fun j =>
    Real.rpow_pos_of_pos
      (ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr (hB j)) (measure_ne_top _ _)) _
  have hmin : M.holderObj g (M.capWeight g) = 1 / M.bdryS g := by
    rw [M.holderObj_eq g hN hB hn hsum]
    simp
  refine ⟨⟨M.capWeight_nonneg g, hsum⟩, hmin, fun w _ hw => ?_⟩
  have hid := M.holderObj_eq g hN hB hn hw
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ (w j - M.capWeight g j) ^ 2 *
      (M.bvol g j Set.univ).toReal ^ (-(2 / pSharp N)) := fun j _ =>
    mul_nonneg (sq_nonneg _) (hpos j).le
  refine ⟨by rw [hmin, hid]; linarith [Finset.sum_nonneg hnn], fun heq => ?_⟩
  rw [hmin, hid, add_eq_left] at heq
  funext j
  have h := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp heq j (Finset.mem_univ j)
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
  · exact absurd h (hpos j).ne'

/-- On `n` components of equal area the optimal weights are uniform, `w_j = 1/n` (the remark
l.497–500). -/
theorem capWeight_of_equal (hN : 3 ≤ N) {b : ℝ} (hb0 : 0 < b)
    (hb : ∀ j, (M.bvol g j Set.univ).toReal = b) (hn : 0 < n) (j : Fin n) :
    M.capWeight g j = 1 / n := by
  have hS : M.bdryS g = n * b ^ (2 / pSharp N) := by
    rw [M.bdryS_eq g hN]
    simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbp : 0 < b ^ (2 / pSharp N) := Real.rpow_pos_of_pos hb0 _
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold capWeight
  rw [hS, hb]
  field_simp

/-- On `n` components of equal area, `S = n^{1/(N-1)} (Σ_j |B_j|)^{(N-2)/(N-1)}` (the factor of
the remark l.497–500). -/
theorem bdryS_of_equal (hN : 3 ≤ N) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ j, (M.bvol g j Set.univ).toReal = b) (hn : 0 < n) :
    M.bdryS g = (n : ℝ) ^ (1 / ((N : ℝ) - 1)) *
      (∑ j, (M.bvol g j Set.univ).toReal) ^ (((N : ℝ) - 2) / ((N : ℝ) - 1)) := by
  have hN' := three_le_cast hN
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold bdryS
  simp only [hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Real.mul_rpow hn'.le hb0, ← mul_assoc, ← Real.rpow_add hn']
  have e : 1 / ((N : ℝ) - 1) + ((N : ℝ) - 2) / ((N : ℝ) - 1) = 1 := by
    have : (N : ℝ) - 1 ≠ 0 := by linarith
    field_simp; ring
  rw [e, Real.rpow_one]

/-! ### eq:linear and eq:calib (l.502–516), the bridge to thm:main -/

lemma volMean_neg (u : D) : M.volMean g (-u) = -M.volMean g u := by
  rw [← neg_one_smul ℝ u, M.volMean_smul]; ring

lemma bdryAvg_neg (u : D) : M.bdryAvg g (-u) = -M.bdryAvg g u := by
  rw [← neg_one_smul ℝ u, M.bdryAvg_smul]; ring

lemma dirichlet_neg (u : D) : M.dirichlet g (-u) = M.dirichlet g u := by
  rw [dirichlet_eq_toReal_energy, dirichlet_eq_toReal_energy, ← neg_one_smul ℝ u, M.energy_smul]
  norm_num

lemma bdryY_neg (u : D) : M.bdryY g (-u) = M.bdryY g u := by
  unfold bdryY normSq
  simp only [map_neg, eLpNorm_neg]

/-- eq:linear (l.504–509), in absolute value, for every `u ∈ D`:
`V^{1/p*} |ū| ≤ C_1 X + C_2 Y` with `C_1 = V^{1/p*}/√cap*`, `C_2 = V^{1/p*}/√S`. Applying
lem:capacitary and lem:holder to `u` and `−u` gives the absolute value, with no sign condition. -/
theorem eq_linear (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (u : D) :
    (M.vol g Set.univ).toReal ^ (1 / pStar N) * |M.volMean g u| ≤
      (M.vol g Set.univ).toReal ^ (1 / pStar N) / Real.sqrt (M.capStar g).toReal *
          Real.sqrt (M.dirichlet g u) +
        (M.vol g Set.univ).toReal ^ (1 / pStar N) / Real.sqrt (M.bdryS g) * M.bdryY g u := by
  obtain ⟨C, hC⟩ := hT
  have h1 := M.lem_capacitary g hN hV hB hP ⟨C, hC⟩ u
  have h2 := M.lem_capacitary g hN hV hB hP ⟨C, hC⟩ (-u)
  rw [M.volMean_neg, M.bdryAvg_neg, M.dirichlet_neg] at h2
  have h3 := abs_le.mp (M.abs_bdryAvg_le g hN u fun j => (hC u j).1)
  have habs : |M.volMean g u| ≤ Real.sqrt (M.dirichlet g u) / Real.sqrt (M.capStar g).toReal +
      M.bdryY g u / Real.sqrt (M.bdryS g) :=
    abs_le.mpr ⟨by linarith [h3.2], by linarith [h3.1]⟩
  have ha : 0 ≤ (M.vol g Set.univ).toReal ^ (1 / pStar N) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  calc (M.vol g Set.univ).toReal ^ (1 / pStar N) * |M.volMean g u|
      ≤ (M.vol g Set.univ).toReal ^ (1 / pStar N) *
          (Real.sqrt (M.dirichlet g u) / Real.sqrt (M.capStar g).toReal +
            M.bdryY g u / Real.sqrt (M.bdryS g)) := mul_le_mul_of_nonneg_left habs ha
    _ = _ := by ring

/-- `F_g(1) = c_N S / V^{(N-2)/N}` (eq:F1, l.146). -/
theorem Fq_one_eq (hN : 3 ≤ N) :
    M.Fq g M.one = cN N * M.bdryS g / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) := by
  unfold Fq
  rw [M.F_one g hN, bdryS, Finset.mul_sum]

/-- eq:calib (l.511–516): `a_N/C_1² = a_N cap*/V^{2/p*} = θ F_g(1)` and
`c_N/C_2² = c_N S/V^{2/p*} = F_g(1)`. -/
theorem eq_calib (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] (hV : M.vol g ≠ 0)
    (hS : 0 < M.bdryS g) :
    aN N / ((M.vol g Set.univ).toReal ^ (1 / pStar N) / Real.sqrt (M.capStar g).toReal) ^ 2 =
        aN N * (M.capStar g).toReal / (M.vol g Set.univ).toReal ^ (2 / pStar N) ∧
      aN N * (M.capStar g).toReal / (M.vol g Set.univ).toReal ^ (2 / pStar N) =
        M.theta g * M.Fq g M.one ∧
      cN N / ((M.vol g Set.univ).toReal ^ (1 / pStar N) / Real.sqrt (M.bdryS g)) ^ 2 =
        cN N * M.bdryS g / (M.vol g Set.univ).toReal ^ (2 / pStar N) ∧
      cN N * M.bdryS g / (M.vol g Set.univ).toReal ^ (2 / pStar N) = M.Fq g M.one := by
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  have hsq : ((M.vol g Set.univ).toReal ^ (1 / pStar N)) ^ 2 =
      (M.vol g Set.univ).toReal ^ (2 / pStar N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hVpos.le]
    congr 1; push_cast; ring
  have hVp : 0 < (M.vol g Set.univ).toReal ^ (2 / pStar N) := Real.rpow_pos_of_pos hVpos _
  have hcN := cN_pos (N := N) (by omega)
  have hF : M.Fq g M.one = cN N * M.bdryS g / (M.vol g Set.univ).toReal ^ (2 / pStar N) := by
    rw [M.Fq_one_eq g hN, two_div_pStar hN]
  refine ⟨?_, ?_, ?_, hF.symm⟩
  · rw [div_pow, hsq, Real.sq_sqrt ENNReal.toReal_nonneg, div_div_eq_mul_div]
  · rw [hF, theta]
    field_simp
  · rw [div_pow, hsq, Real.sq_sqrt hS.le, div_div_eq_mul_div]

end MeasuredModel

/-! ## A witness: the two-point toy model -/

section Toy

lemma toy_volMean (u : Bool → ℝ) : toyModel.volMean toyMetric u = (u true + u false) / 2 := by
  unfold MeasuredModel.volMean
  rw [toy_vol, toy_count_univ, integral_fintype .of_finite]
  simp [toyModel]
  ring

lemma toy_bdryS : toyModel.bdryS toyMetric = 1 := by
  unfold MeasuredModel.bdryS
  rw [Fin.sum_univ_one, toy_bvol_univ, Real.one_rpow]

lemma toy_capWeight (j : Fin 1) : toyModel.capWeight toyMetric j = 1 := by
  unfold MeasuredModel.capWeight
  rw [toy_bvol_univ, toy_bdryS]
  simp

lemma toy_bdryAvg (u : Bool → ℝ) : toyModel.bdryAvg toyMetric u = u false := by
  unfold MeasuredModel.bdryAvg
  simp only [toy_capWeight, toy_bvol, integral_dirac, Fin.sum_univ_one]
  simp [toyModel]

lemma toy_ell (u : Bool → ℝ) : toyModel.ell toyMetric u = (u true - u false) / 2 := by
  unfold MeasuredModel.ell
  rw [toy_volMean, toy_bdryAvg]
  ring

lemma toy_energy (u : Bool → ℝ) :
    toyModel.energy toyMetric u = ENNReal.ofReal (2 * (u true - u false) ^ 2) := by
  unfold MeasuredModel.energy
  simp only [toy_gradSq]
  rw [toy_vol, lintegral_const, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
  congr 1
  rw [Measure.count_apply_finite _ Set.finite_univ]
  simp

/-- `cap* = 8` on the toy model, attained at `v = (true ↦ 1, false ↦ −1)`. -/
theorem toy_capStar : toyModel.capStar toyMetric = 8 := by
  refine le_antisymm ?_ (le_iInf₂ fun v hv => ?_)
  · have hv : toyModel.ell toyMetric (fun b => if b then 1 else -1) = 1 := by
      rw [toy_ell]; norm_num
    refine (toyModel.capStar_le toyMetric hv).trans (le_of_eq ?_)
    rw [toy_energy]
    norm_num
  · rw [toy_ell] at hv
    have h2 : v true - v false = 2 := by linarith
    rw [toy_energy, h2]
    norm_num

/-- `θ = a_3 · 8 / c_3 = 64/c_3` on the toy model. -/
theorem toy_theta : toyModel.theta toyMetric = 64 / cN 3 := by
  unfold MeasuredModel.theta
  rw [toy_capStar, toy_bdryS]
  norm_num [aN]

lemma toy_normSq_two_vol (f : Bool → ℝ) :
    normSq (toyModel.vol toyMetric) 2 f = f true ^ 2 + f false ^ 2 := by
  have hne : ∀ t : ℝ, ‖t‖ₑ ^ (2 : ℝ) ≠ ⊤ := fun _ =>
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top
  rw [normSq_eq_lintegral two_pos, toy_vol, lintegral_count, tsum_fintype, Fintype.sum_bool,
    ENNReal.toReal_add (hne _) (hne _), ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, toReal_enorm,
    toReal_enorm, Real.rpow_two, Real.rpow_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    div_self two_ne_zero, Real.rpow_one]

theorem toy_meanPoincare : toyModel.MeanPoincare toyMetric := by
  haveI := toy_isFiniteMeasure_vol
  refine ⟨1, fun v => ⟨MemLp.of_discrete, ?_⟩⟩
  have e : toyModel.val v = v := rfl
  rw [e, toy_normSq_two_vol, toy_volMean, toy_dirichlet]
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (v true - v false)]

theorem toy_traceBound : toyModel.TraceBound toyMetric := by
  refine ⟨1, fun u j => ?_⟩
  haveI := toy_isFiniteMeasure_bvol j
  refine ⟨MemLp.of_discrete, ?_⟩
  have e1 : toyModel.tr u = u := rfl
  have e2 : toyModel.val u = u := rfl
  rw [e1, e2, toy_normSq_bvol u j (pSharp_pos le_rfl), toy_dirichlet, toy_normSq_two_vol]
  nlinarith [sq_nonneg (u true - u false), sq_nonneg (u true)]

theorem toy_interiorBump : toyModel.InteriorBump toyMetric := by
  refine ⟨fun b => if b then 1 else 0, ?_, fun j => ?_, ?_⟩
  · rw [toy_energy]; exact ENNReal.ofReal_ne_top
  · rw [toy_bvol, Filter.EventuallyEq, ae_dirac_iff (MeasurableSet.of_discrete)]
    simp [toyModel]
  · rw [toy_vol, integral_fintype .of_finite]
    simp [toyModel]

theorem toy_gradMeasurable : toyModel.GradMeasurable toyMetric := fun _ =>
  (Measurable.of_discrete).aestronglyMeasurable

/-- `L^2` convergence on the two points from pointwise convergence, for any finite measure. -/
lemma toy_tendsto_eLpNorm {μ : Measure Bool} [IsFiniteMeasure μ] {f : ℕ → Bool → ℝ}
    {a : Bool → ℝ} (h : Tendsto f atTop (𝓝 a)) :
    Tendsto (fun k => eLpNorm (f k - a) 2 μ) atTop (𝓝 0) := by
  have hb : ∀ k, eLpNorm (f k - a) 2 μ ≤
      μ Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal ‖f k - a‖ := fun k =>
    eLpNorm_le_of_ae_bound (ae_of_all _ fun x => norm_le_pi_norm (f k - a) x)
  have hu : Tendsto (fun k => μ Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal ‖f k - a‖) atTop
      (𝓝 0) := by
    have h0 : Tendsto (fun k => ENNReal.ofReal ‖f k - a‖) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.mp h)
      simpa using this
    have := ENNReal.Tendsto.const_mul h0
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (y := (2 : ℝ≥0∞).toReal⁻¹) (by positivity)
        (measure_ne_top μ Set.univ)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun _ => zero_le) hb

theorem toy_directMethod : toyModel.DirectMethod toyMetric := by
  intro u e _ hK hconv
  obtain ⟨K, hK⟩ := hK
  have hbd : ∀ k, u k ∈ Metric.closedBall (0 : Bool → ℝ) (Real.sqrt (max K 0)) := by
    intro k
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro b
    have h := hK k
    have e : toyModel.val (u k) = u k := rfl
    rw [e, toy_normSq_two_vol, toy_dirichlet] at h
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    have h1 : u k b ^ 2 ≤ u k true ^ 2 + u k false ^ 2 := by
      cases b <;> nlinarith [sq_nonneg (u k true), sq_nonneg (u k false)]
    have h2 : 0 ≤ 2 * (u k true - u k false) ^ 2 := by positivity
    exact h1.trans ((by linarith : u k true ^ 2 + u k false ^ 2 ≤ K).trans (le_max_left _ _))
  obtain ⟨a, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
  refine ⟨φ, hφ, a, ?_, ?_, fun j => ?_⟩
  · have h1 : Tendsto (fun k => toyModel.dirichlet toyMetric (u (φ k))) atTop (𝓝 e) :=
      hconv.comp hφ.tendsto_atTop
    have h2 : Tendsto (fun k => toyModel.dirichlet toyMetric (u (φ k))) atTop
        (𝓝 (2 * (a true - a false) ^ 2)) := by
      simp only [toy_dirichlet]
      have hc : Continuous (fun f : Bool → ℝ => 2 * (f true - f false) ^ 2) := by fun_prop
      exact (hc.tendsto a).comp hlim
    rw [toy_energy, tendsto_nhds_unique h1 h2]
  · haveI := toy_isFiniteMeasure_vol
    exact toy_tendsto_eLpNorm hlim
  · haveI := toy_isFiniteMeasure_bvol j
    exact toy_tendsto_eLpNorm hlim

/-- Every hypothesis of `lem_capstar_minimiser` holds on the toy model. -/
theorem toy_lem_capstar_hyps :
    IsFiniteMeasure (toyModel.vol toyMetric) ∧ (∀ j, IsFiniteMeasure (toyModel.bvol toyMetric j)) ∧
    toyModel.vol toyMetric ≠ 0 ∧ (∃ j, toyModel.bvol toyMetric j ≠ 0) ∧
    toyModel.MeanPoincare toyMetric ∧ toyModel.TraceBound toyMetric ∧
    toyModel.InteriorBump toyMetric ∧ toyModel.DirectMethod toyMetric ∧
    toyModel.GradMeasurable toyMetric :=
  ⟨toy_isFiniteMeasure_vol, toy_isFiniteMeasure_bvol, toy_vol_ne_zero,
    ⟨0, by rw [toy_bvol]; exact Measure.dirac_ne_zero⟩, toy_meanPoincare, toy_traceBound,
    toy_interiorBump, toy_directMethod, toy_gradMeasurable⟩

end Toy

end Yamabe
