import Yamabe.Perforated.Capacity

/-!
# Perforated § 6, the upper half of the sandwich: thm:upper, `cap* ≤ cap_D`, and rem:notF1, over the measured model

Labels (the companion BrunswicPerforated, `papers/perforated`; lines of
`papers/perforated/legacy/labeled/perforated.tex`):

* **`thm:upper`** — `perforated.tex:871` (statement l.871–879, proof l.881–895), with the
  definitions of `ψ`, `cap_D`, `θ_D` and the comparison `cap* ≤ cap_D`, `θ ≤ θ_D` (l.862–869):
  `thm_upper` (as printed), `thm_upper_strong` (Jensen form, no `ρ`), `thm_upper_capD` (the
  infimum `cap_D`), `upperTest_sStar` (the honest test function), `capStar_le_capD`,
  `theta_le_thetaDOf`;
* **`rem:notF1`** — `perforated.tex:359` (l.359–371), yamabe's rem:sign in the companion's
  notation: `rem_notF1`, with `rem_notF1_of_cutoff` (under the strict rem:sign's hypotheses).

> Let $\psi\in W^{1,2}(\Sigma)$ be the classical equilibrium potential, i.e.\ the
> minimiser of $\|\nabla\psi\|^2$ subject to $\psi=1$ on $\partial\Sigma$ and
> $\int_\Sigma\psi\dd V=0$, and let
> $\operatorname{cap}_{\mathrm D}:=\|\nabla\psi\|^2_{L^2}$ be the corresponding
> capacity, $\theta_{\mathrm D}:=\aN\operatorname{cap}_{\mathrm D}/(\cN S)$. Since
> the constraint $\psi\equiv1$ on $\partial\Sigma$ is stronger than
> $\ell(\psi)=-1$, one has $\cpstar\le\operatorname{cap}_{\mathrm D}$ and
> $\theta\le\theta_{\mathrm D}$. (l.862–869)

> With $\rho:=\|\psi\|_{L^{\pstar}(\Sigma)}/V^{1/\pstar}$,
> $\lambda_\partial\;\le\;\frac{\theta_{\mathrm D}}{1+\theta_{\mathrm D}}\,
>      \frac{\Fq_g(1)}{(1-\rho)^{2}}$,
> provided $\rho<1$. (l.873–878)

> Take $u_s:=1-s\psi$ for $s\in[0,1]$. [...] and
> $\|u_s\|_{\pstar}\ge V^{1/\pstar}-s\|\psi\|_{\pstar}\ge V^{1/\pstar}(1-\rho)$. (l.882–885)

> $\lambda_\partial<\Fq_g(1)$ strictly. Indeed for $u_\epsilon=1+\epsilon\varphi$
> with $\int_\Sigma\varphi\dd V=0$ the gradient term is $O(\epsilon^2)$ while
> $\frac{d}{d\epsilon}\Big|_{0}\Fq_g(1+\epsilon\varphi)
> =\frac{2\cN}{V^{(N-2)/N}}\sum_j|B_j|^{-1/(N-1)}\int_{B_j}\varphi\dd\sigma$,
> which is $<0$ for any $\varphi$ that is $\le0$ and $\not\equiv0$ on
> $\partial\Sigma$ with zero mean on $\Sigma$. So the constant function is never
> optimal, and any lower bound of the form $\lambda_\partial\ge\kappa\Fq_g(1)$ must
> have $\kappa<1$. (l.361–370)

## The model

Yamabe's `MeasuredModel` (strict `Yamabe.Quotient`, the model of record by DEC-186), with the
companion's `ℓ`, `cap*`, `θ`, `S` of strict `Yamabe.Perforated.Capacity`. `λ_∂ = infF g (c_N)`,
`F_g = Fq`, `V = (vol g univ).toReal`, `|B_j| = (bvol g j univ).toReal`. A competitor of the
classical capacity (`IsCapDCompetitor`) is `ψ ∈ D` with `tr ψ = 1` `bvol_j`-a.e. on every `B_j`
and `∫_Σ ψ dV = 0`; `cap_D` of a competitor is `‖∇ψ‖² = dirichlet ψ` (`thetaDOf`), and the
infimum `capD ∈ [0, ∞]` runs over competitors with values in `L^{p*}` (`thetaD`). `u_s` is
`upperTest ψ s = 1 + (−s)ψ`; `ρ` is `rhoOf ψ`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `N ≥ 3` (l.106) | ✓ carried |
| `Σ` compact (l.117) | ✓ carried as `IsFiniteMeasure (vol g)`, `IsFiniteMeasure (bvol g j)` |
| `Σ` connected (l.117) | ⚠ weakened: not used |
| `∂Σ ≠ ∅` (l.117) | ⚠ weakened in thm:upper: not used; ✓ carried in rem:notF1 and `cap* ≤ cap_D` (`∃ j, bvol g j ≠ 0`, resp. `S ≠ 0`) |
| `ψ` the minimiser of `‖∇ψ‖²` (l.862–864) | ⚠ weakened: every competitor `ψ` (`thm_upper`), and the infimum without a minimiser (`thm_upper_capD`) |
| `ψ ∈ W^{1,2}(Σ)` (l.862) | ⚠ read: `ψ ∈ D` with `val ψ ∈ L^{p*}(Σ)`, the junk guard for `ρ` (`‖ψ‖_{p*} = ∞` would give the junk `ρ = 0`) |
| `ψ = 1` on `∂Σ`, `∫_Σ ψ = 0` (l.863–864) | ✓ carried (`IsCapDCompetitor`) |
| `ρ < 1` (l.878) | ✓ carried in `thm_upper`; ⚠ weakened: not used by `thm_upper_strong` |
| `s ∈ [0, 1]` (l.882) | ⚠ weakened: every real `s` (`Fq_upperTest_le`) |
| `φ ∈ W^{1,2}(Σ)` in rem:notF1 (l.361) | ⚠ read: `val φ ∈ L^{p*}`, `tr φ ∈ L^{p♯}(B_j)`, per direction (no bound, no smoothness) |
| such `φ` exist (implicit, l.367) | ⚠ read: from a competitor `ψ` of `cap_D` (`φ = −ψ`, `neg_isDirection`), which the strict rem:sign's cutoff `χ` provides (`exists_isCapDCompetitor_of_cutoff`) |

## SCOPE (disclosed)

* **Proved in full.** thm:upper as printed for every competitor `ψ` (`thm_upper`), and the
  proof's display (`Fq_upperTest_le_printed`); `cap* ≤ ‖∇ψ‖²` for every competitor
  (`capStar_le_energy_of_isCapDCompetitor`), `cap* ≤ cap_D` (`capStar_le_capD`), `θ ≤ θ_D`
  (`theta_le_thetaDOf`, `theta_le_thetaD`), `ℓ(ψ) = −1` (`ell_of_isCapDCompetitor`); the
  minimisation in `s` (`sandwich_quadratic`, `sandwich_quadratic_le`). rem:notF1 in full
  (`rem_notF1`, given one competitor `ψ`, which the strict rem:sign's cutoff `χ` supplies,
  `rem_notF1_of_cutoff`; the existence of a direction (iii) is `φ = −ψ` from that `ψ`): `F_g(1) = c_N S/V^{(N-2)/N}`, the gradient term `ε² ‖∇φ‖²`, the first
  variation for every direction with `L^{p*}` values and `L^{p♯}` traces
  (`hasDerivAt_F_one_add_of_memLp`, from `hasDerivAt_normSq_one_add_of_memLp`, which needs no
  bound on `φ`), its sign, the existence of a direction, `λ_∂ < F_g(1)` at an explicit
  competitor, and `κ < 1`.
* **Finding (thm:upper, l.885 and l.878).** The triangle-inequality step
  `‖u_s‖_{p*} ≥ V^{1/p*}(1 − ρ)` is lossy: since `∫_Σ ψ = 0`, `∫_Σ u_s = V`, and Hölder against
  `1` gives `‖u_s‖_{p*} ≥ V^{1/p*}` for every real `s` (`le_normSq_of_integral_eq`). Hence
  `λ_∂ ≤ θ_D/(1 + θ_D) F_g(1)` with no factor `(1 − ρ)^{-2}` and no proviso
  (`thm_upper_strong`); the printed form follows. On the two-point toy model `ρ = 1`
  (`toy_rho`): the printed proviso excludes it, the Jensen form applies (`toy_thm_upper_strong`).
  The right side of eq:sandwich (l.903) is therefore `θ_D/(1 + θ_D)`, and `ρ → 0` (l.905) is not
  needed for thm:sharp.
* **Junk values.** `dirichlet` is `0` at infinite energy, so Lean's `inf F` may lie below the
  paper's `λ_∂` (kb 0002), which would weaken an upper bound on it. `upperTest_sStar` closes this:
  the bound is attained by `u_{s*} = 1 − s*ψ`, a competitor of energy `s*² ‖∇ψ‖²`, so it holds for
  the infimum over finite-energy competitors whenever `ψ` has finite energy, as the paper's `ψ`
  does. For a competitor of infinite energy `θ_D(ψ)` is the junk `0`.
* `capD` reads `W^{1,2}` as `ψ ∈ D` with `L^{p*}` values; the model's `SobolevIneq` bounds the junk
  `normSq` and does not give `MemLp`, so the guard is explicit. `θ_D` uses `cap_D.toReal` (`0` if
  `cap_D = ∞`, excluded where used).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Matrix

noncomputable section

namespace Yamabe

/-! ## Squared norms of constants, and the Jensen step -/

section Norms

variable {X : Type*} [MeasurableSpace X]

/-- `‖c‖²_{L^q(ν)} = c² ν(X)^{2/q}`. -/
lemma normSq_fun_const (ν : Measure X) {q : ℝ} (hq : 0 < q) (c : ℝ) :
    normSq ν q (fun _ => c) = c ^ 2 * (ν Set.univ).toReal ^ (2 / q) := by
  have h : (fun _ : X => c) = c • (fun _ : X => (1 : ℝ)) := by funext x; simp
  rw [← normSq_one ν hq]
  unfold normSq
  rw [h, eLpNorm_const_smul, ENNReal.toReal_mul, mul_pow, toReal_enorm, Real.norm_eq_abs, sq_abs]

/-- `normSq` only sees the a.e. class. -/
lemma normSq_ae_congr {ν : Measure X} {q : ℝ} {f f' : X → ℝ} (h : f =ᵐ[ν] f') :
    normSq ν q f = normSq ν q f' := by
  unfold normSq; rw [eLpNorm_congr_ae h]

/-- The Jensen step: on a finite measure, a function of `L^q`, `q ≥ 1`, whose integral is the
mass `ν(X)` has `‖f‖²_{L^q} ≥ ν(X)^{2/q}` (Hölder against `1`). -/
theorem le_normSq_of_integral_eq {ν : Measure X} [IsFiniteMeasure ν] {q : ℝ} (hq : 1 ≤ q)
    {f : X → ℝ} (hf : MemLp f (ENNReal.ofReal q) ν) (hint : ∫ x, f x ∂ν = (ν Set.univ).toReal) :
    (ν Set.univ).toReal ^ (2 / q) ≤ normSq ν q f := by
  have hq0 : 0 < q := by linarith
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg : 0 ≤ (ν Set.univ).toReal) with h0 | h0
  · rw [← h0, Real.zero_rpow (by positivity)]; exact normSq_nonneg _ _ _
  · have hH := abs_integral_le_mul_eLpNorm hq hf
    rw [hint, abs_of_pos h0] at hH
    set V := (ν Set.univ).toReal with hVdef
    set A := (eLpNorm f (ENNReal.ofReal q) ν).toReal with hAdef
    have e : V ^ (1 - 1 / q) * V ^ (1 / q) = V := by
      rw [← Real.rpow_add h0, sub_add_cancel, Real.rpow_one]
    have hA : V ^ (1 / q) ≤ A :=
      le_of_mul_le_mul_left (by rw [e]; exact hH) (Real.rpow_pos_of_pos h0 _)
    unfold normSq
    rw [← hAdef]
    calc V ^ (2 / q) = (V ^ (1 / q)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le]; congr 1; push_cast; ring
      _ ≤ A ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg h0.le _) hA 2

lemma abs_rpow_sub_two_mul_self (y : ℝ) {q : ℝ} (hq : 1 < q) :
    |(|y| ^ (q - 2) * y)| = |y| ^ (q - 1) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [Real.zero_rpow (by linarith : q - 1 ≠ 0)]
  · have hy' : 0 < |y| := abs_pos.mpr hy
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    calc |y| ^ (q - 2) * |y| = |y| ^ (q - 2) * |y| ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = |y| ^ (q - 1) := by rw [← Real.rpow_add hy']; ring_nf

/-- The first variation of a squared norm at `1`, for `f ∈ L^q` (`q > 1`), with no bound on `f`:
`d/dε|₀ ‖1 + εf‖²_{L^q(ν)} = 2 ν(X)^{2/q-1} ∫ f dν`. -/
theorem hasDerivAt_normSq_one_add_of_memLp {ν : Measure X} [IsFiniteMeasure ν] {q : ℝ}
    (hq : 1 < q) {f : X → ℝ} (hf : MemLp f (ENNReal.ofReal q) ν) :
    HasDerivAt (fun ε : ℝ => normSq ν q (fun x => 1 + ε * f x))
      (2 * (ν Set.univ).toReal ^ (2 / q - 1) * ∫ x, f x ∂ν) 0 := by
  have hq0 : 0 < q := by linarith
  rcases eq_or_ne ν 0 with rfl | hν
  · simp only [normSq, eLpNorm_measure_zero, ENNReal.toReal_zero, integral_zero_measure, mul_zero]
    simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have hfm := hf.aestronglyMeasurable
  have hmem : ∀ ε : ℝ, MemLp (fun x => 1 + ε * f x) (ENNReal.ofReal q) ν := fun ε =>
    (memLp_const (μ := ν) (p := ENNReal.ofReal q) (1 : ℝ)).add (hf.const_mul ε)
  have hform : ∀ ε : ℝ, normSq ν q (fun x => 1 + ε * f x) =
      (∫ x, |1 + ε * f x| ^ q ∂ν) ^ (2 / q) := by
    intro ε
    unfold normSq
    rw [(hmem ε).eLpNorm_eq_integral_rpow_norm (by simpa using hq0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le]
    have h0 : 0 ≤ ∫ x, |1 + ε * f x| ^ q ∂ν :=
      integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _
    simp only [Real.norm_eq_abs]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h0 _), ← Real.rpow_natCast, ← Real.rpow_mul h0]
    congr 1; push_cast; field_simp
  set B : X → ℝ := fun x => q * (1 + |f x|) ^ q with hB
  have hBint : Integrable B ν := by
    have h1 : MemLp (fun x => 1 + |f x|) (ENNReal.ofReal q) ν := by
      have := (memLp_const (μ := ν) (p := ENNReal.ofReal q) (1 : ℝ)).add hf.norm
      exact this
    have h2 := h1.integrable_norm_rpow'
    rw [ENNReal.toReal_ofReal hq0.le] at h2
    refine (h2.const_mul q).congr (ae_of_all _ fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
  have hI : HasDerivAt (fun ε : ℝ => ∫ x, |1 + ε * f x| ^ q ∂ν)
      (∫ x, q * (|1 + 0 * f x| ^ (q - 2) * (1 + 0 * f x)) * f x ∂ν) 0 := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (bound := B)
      (F := fun (ε : ℝ) (x : X) => |1 + ε * f x| ^ q)
      (F' := fun (ε : ℝ) (x : X) => q * (|1 + ε * f x| ^ (q - 2) * (1 + ε * f x)) * f x)
      (Metric.ball_mem_nhds 0 one_pos) ?_ ?_ ?_ ?_ hBint ?_).2
    · exact Eventually.of_forall fun ε =>
        ((continuous_abs.rpow_const fun _ => Or.inr hq0.le).comp_aestronglyMeasurable
          (aestronglyMeasurable_const.add (hfm.const_mul ε)))
    · simp only [zero_mul, add_zero, abs_one, Real.one_rpow]; exact integrable_const _
    · simp only [zero_mul, add_zero, abs_one, Real.one_rpow, mul_one]
      exact hfm.const_mul q
    · refine ae_of_all _ fun x ε hε => ?_
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
      have hy : |1 + ε * f x| ≤ 1 + |f x| := by
        calc |1 + ε * f x| ≤ |1| + |ε * f x| := abs_add_le _ _
          _ = 1 + |ε| * |f x| := by rw [abs_one, abs_mul]
          _ ≤ 1 + 1 * |f x| := by gcongr
          _ = 1 + |f x| := by ring
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hq0, abs_rpow_sub_two_mul_self _ hq]
      have h1 : |1 + ε * f x| ^ (q - 1) ≤ (1 + |f x|) ^ (q - 1) :=
        Real.rpow_le_rpow (abs_nonneg _) hy (by linarith)
      have h2 : (1 + |f x|) ^ (q - 1) * |f x| ≤ (1 + |f x|) ^ q := by
        have hpos : 0 < 1 + |f x| := by positivity
        calc (1 + |f x|) ^ (q - 1) * |f x| ≤ (1 + |f x|) ^ (q - 1) * (1 + |f x|) := by
              gcongr; linarith
          _ = (1 + |f x|) ^ q := by
              rw [← Real.rpow_add_one hpos.ne', sub_add_cancel]
      calc q * |1 + ε * f x| ^ (q - 1) * |f x| ≤ q * (1 + |f x|) ^ (q - 1) * |f x| := by
            gcongr
        _ = q * ((1 + |f x|) ^ (q - 1) * |f x|) := by ring
        _ ≤ q * (1 + |f x|) ^ q := by gcongr
    · refine ae_of_all _ fun x ε _ => ?_
      have hd : HasDerivAt (fun ε : ℝ => 1 + ε * f x) (f x) ε := by
        simpa using ((hasDerivAt_id ε).mul_const (f x)).const_add 1
      have := (hasDerivAt_abs_rpow (1 + ε * f x) hq).comp ε hd
      exact this.congr_deriv (by ring)
  have hI0 : ∫ x, |1 + 0 * f x| ^ q ∂ν = (ν Set.univ).toReal := by
    simp [measureReal_def]
  have hVpos : 0 < (ν Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hν) (measure_ne_top _ _)
  have hJ := hI.rpow_const (p := 2 / q) (Or.inl (by rw [hI0]; exact hVpos.ne'))
  rw [hI0] at hJ
  have hval : (∫ x, q * (|1 + 0 * f x| ^ (q - 2) * (1 + 0 * f x)) * f x ∂ν) * (2 / q) *
      (ν Set.univ).toReal ^ (2 / q - 1) = 2 * (ν Set.univ).toReal ^ (2 / q - 1) * ∫ x, f x ∂ν := by
    simp only [zero_mul, add_zero, abs_one, Real.one_rpow, mul_one]
    rw [integral_const_mul]
    field_simp
  rw [hval] at hJ
  exact hJ.congr_of_eventuallyEq (Eventually.of_forall fun ε => hform ε)

end Norms

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : FrameMetric X N)

/-! ## The classical capacity `cap_D` (l.862–869) -/

/-- `ψ = 1` on `∂Σ` and `∫_Σ ψ dV = 0` (l.863–864): the constraint of the classical capacity. -/
def IsCapDCompetitor (ψ : D) : Prop :=
  (∀ j, M.tr ψ =ᵐ[M.bvol g j] fun _ => (1 : ℝ)) ∧ ∫ x, M.val ψ x ∂(M.vol g) = 0

/-- The classical capacity `cap_D = inf {‖∇ψ‖²_{L²} : ψ ∈ W^{1,2}(Σ), ψ = 1 on ∂Σ, ∫_Σ ψ = 0}`
(l.862–866), in `[0, ∞]`, with `W^{1,2}(Σ)` read as `ψ ∈ D` with values in `L^{p*}(Σ)`. -/
def capD : ℝ≥0∞ :=
  ⨅ (ψ : D) (_ : M.IsCapDCompetitor g ψ ∧ MemLp (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g)),
    M.energy g ψ

/-- `θ_D = a_N cap_D / (c_N S)` (l.866) for the capacity `cap_D = ‖∇ψ‖²` of a competitor `ψ`. -/
def thetaDOf (ψ : D) : ℝ := aN N * M.dirichlet g ψ / (cN N * M.bdryS g)

/-- `θ_D = a_N cap_D / (c_N S)` (l.866) for the infimum `cap_D`. -/
def thetaD : ℝ := aN N * (M.capD g).toReal / (cN N * M.bdryS g)

/-- `ρ = ‖ψ‖_{L^{p*}(Σ)} / V^{1/p*}` (l.873). -/
def rhoOf (ψ : D) : ℝ :=
  (eLpNorm (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal /
    (M.vol g Set.univ).toReal ^ (1 / pStar N)

/-- The test function `u_s = 1 − sψ` of the proof (l.882). -/
def upperTest (ψ : D) (s : ℝ) : D := M.one + (-s) • ψ

/-- A competitor has `ℓ(ψ) = −1` (l.867–868), once `S ≠ 0`. -/
theorem ell_of_isCapDCompetitor (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hS : M.bdryS g ≠ 0) {ψ : D} (hψ : M.IsCapDCompetitor g ψ) : M.ell g ψ = -1 := by
  have hb : M.bdryAvg g ψ = M.bdryAvg g M.one := by
    unfold bdryAvg
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_congr_ae (hψ.1 j), M.tr_one]
  have hm : M.volMean g ψ = 0 := by unfold volMean; rw [hψ.2, mul_zero]
  unfold ell
  rw [hm, hb, M.bdryAvg_one g hN hS]
  ring

/-- `cap* ≤ ‖∇ψ‖²` for every competitor `ψ` (l.866–868): `−ψ` competes for `cap*`. -/
theorem capStar_le_energy_of_isCapDCompetitor (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hS : M.bdryS g ≠ 0) {ψ : D} (hψ : M.IsCapDCompetitor g ψ) :
    M.capStar g ≤ M.energy g ψ := by
  have h : M.ell g ((-1 : ℝ) • ψ) = 1 := by
    rw [M.ell_smul, M.ell_of_isCapDCompetitor g hN hS hψ]; norm_num
  calc M.capStar g ≤ M.energy g ((-1 : ℝ) • ψ) := M.capStar_le g h
    _ = M.energy g ψ := by rw [M.energy_smul]; norm_num

/-- `cap* ≤ cap_D` (l.868). -/
theorem capStar_le_capD (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)] (hS : M.bdryS g ≠ 0) :
    M.capStar g ≤ M.capD g :=
  le_iInf₂ fun _ hψ => M.capStar_le_energy_of_isCapDCompetitor g hN hS hψ.1

/-- `θ ≤ θ_D` (l.868–869) for every competitor of finite energy. -/
theorem theta_le_thetaDOf (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)] (hS : M.bdryS g ≠ 0)
    {ψ : D} (hψ : M.IsCapDCompetitor g ψ) (hfin : M.energy g ψ ≠ ⊤) :
    M.theta g ≤ M.thetaDOf g ψ := by
  unfold theta thetaDOf
  have hc : 0 ≤ cN N * M.bdryS g := mul_nonneg (cN_pos (by omega)).le (M.bdryS_nonneg g)
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (aN_pos hN).le) hc
  rw [dirichlet_eq_toReal_energy]
  exact ENNReal.toReal_mono hfin (M.capStar_le_energy_of_isCapDCompetitor g hN hS hψ)

/-- `θ ≤ θ_D` (l.868–869) for the infimum `cap_D`, once it is finite. -/
theorem theta_le_thetaD (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)] (hS : M.bdryS g ≠ 0)
    (hfin : M.capD g ≠ ⊤) : M.theta g ≤ M.thetaD g := by
  unfold theta thetaD
  have hc : 0 ≤ cN N * M.bdryS g := mul_nonneg (cN_pos (by omega)).le (M.bdryS_nonneg g)
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (aN_pos hN).le) hc
  exact ENNReal.toReal_mono hfin (M.capStar_le_capD g hN hS)

/-! ## The test functions `u_s = 1 − sψ` (l.882–891) -/

lemma val_upperTest (ψ : D) (s : ℝ) :
    M.val (M.upperTest ψ s) = fun x => 1 + (-s) * M.val ψ x :=
  M.val_one_add_smul (-s) ψ

lemma tr_upperTest (ψ : D) (s : ℝ) :
    M.tr (M.upperTest ψ s) = fun x => 1 + (-s) * M.tr ψ x :=
  M.tr_one_add_smul (-s) ψ

/-- `‖∇u_s‖² = s² ‖∇ψ‖²` (l.883). -/
lemma dirichlet_upperTest (ψ : D) (s : ℝ) :
    M.dirichlet g (M.upperTest ψ s) = s ^ 2 * M.dirichlet g ψ := by
  unfold upperTest; rw [M.dirichlet_one_add_smul, neg_sq]

/-- `u_s` has finite energy when `ψ` has. -/
lemma energy_upperTest (ψ : D) (s : ℝ) :
    M.energy g (M.upperTest ψ s) = ENNReal.ofReal (s ^ 2) * M.energy g ψ := by
  have h : ∀ x, M.gradSq g (M.upperTest ψ s) x = M.gradSq g ((-s) • ψ) x := by
    intro x; simp [upperTest, gradSq, map_add, M.d_one]
  have e : M.energy g (M.upperTest ψ s) = M.energy g ((-s) • ψ) := by
    unfold energy; simp only [h]
  rw [e, M.energy_smul, neg_sq]

/-- The proof's display (l.888–891), with the Jensen bound `‖u_s‖_{p*} ≥ V^{1/p*}` in place of
`V^{1/p*}(1 − ρ)`: for every real `s`, `u_s` is a competitor and
`F_g(u_s) ≤ (a_N s² ‖∇ψ‖² + c_N (1 − s)² S) / V^{2/p*}`. -/
theorem Fq_upperTest_le_raw (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0)
    {ψ : D} (hψ : M.IsCapDCompetitor g ψ)
    (hψp : MemLp (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g)) (s : ℝ) :
    M.Adm g (M.upperTest ψ s) ∧
      M.Fq g (M.upperTest ψ s) ≤
        (aN N * (s ^ 2 * M.dirichlet g ψ) + cN N * ((1 - s) ^ 2 * M.bdryS g)) /
          (M.vol g Set.univ).toReal ^ (2 / pStar N) := by
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  have hmem : MemLp (M.val (M.upperTest ψ s)) (ENNReal.ofReal (pStar N)) (M.vol g) := by
    have h2 : MemLp (fun x => (-s) * M.val ψ x) (ENNReal.ofReal (pStar N)) (M.vol g) :=
      hψp.const_mul (-s)
    have h3 := (memLp_const (μ := M.vol g) (p := ENNReal.ofReal (pStar N)) (1 : ℝ)).add h2
    rw [val_upperTest]
    exact h3
  have hint : ∫ x, M.val (M.upperTest ψ s) x ∂(M.vol g) = (M.vol g Set.univ).toReal := by
    have hψi : Integrable (M.val ψ) (M.vol g) := hψp.integrable (by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith [two_le_pStar hN]))
    rw [val_upperTest, integral_add (integrable_const 1) (hψi.const_mul (-s)), integral_const,
      integral_const_mul, hψ.2]
    simp [measureReal_def]
  have hJ := le_normSq_of_integral_eq (by linarith [two_le_pStar hN]) hmem hint
  have hD0 : 0 < (M.vol g Set.univ).toReal ^ (2 / pStar N) := Real.rpow_pos_of_pos hVpos _
  refine ⟨lt_of_lt_of_le hD0 hJ, ?_⟩
  have htr : ∀ j, normSq (M.bvol g j) (pSharp N) (M.tr (M.upperTest ψ s)) =
      (1 - s) ^ 2 * (M.bvol g j Set.univ).toReal ^ (2 / pSharp N) := by
    intro j
    rw [normSq_ae_congr (q := pSharp N) (f' := fun _ => 1 - s), normSq_fun_const _ (pSharp_pos hN)]
    filter_upwards [hψ.1 j] with x hx
    rw [tr_upperTest]; simp only [hx]; ring
  have hsum : ∑ j, cN N * normSq (M.bvol g j) (pSharp N) (M.tr (M.upperTest ψ s)) =
      cN N * ((1 - s) ^ 2 * M.bdryS g) := by
    simp only [htr]; rw [M.bdryS_eq g hN, Finset.mul_sum, Finset.mul_sum]
  simp only [Fq, F, traceSobolevQuot]
  rw [hsum, dirichlet_upperTest]
  have hnum : 0 ≤ aN N * (s ^ 2 * M.dirichlet g ψ) + cN N * ((1 - s) ^ 2 * M.bdryS g) := by
    have := M.dirichlet_nonneg g ψ; have := M.bdryS_nonneg g
    have := aN_pos hN; have := cN_pos (N := N) (by omega); positivity
  exact div_le_div_of_nonneg_left hnum hD0 hJ

/-- The proof's display (l.891), Jensen form: `F_g(u_s) ≤ F_g(1) [θ_D s² + (1 − s)²]` for every
real `s`, once some `B_j` has positive area. -/
theorem Fq_upperTest_le (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    {ψ : D} (hψ : M.IsCapDCompetitor g ψ)
    (hψp : MemLp (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g)) (s : ℝ) :
    M.Fq g (M.upperTest ψ s) ≤
      M.Fq g M.one * (M.thetaDOf g ψ * s ^ 2 + (1 - s) ^ 2) := by
  have hS := M.bdryS_pos g hB
  have hc := cN_pos (N := N) (by omega)
  refine (M.Fq_upperTest_le_raw g hN hV hψ hψp s).2.trans (le_of_eq ?_)
  rw [M.Fq_one_eq g hN, ← two_div_pStar hN, thetaDOf]
  field_simp

/-- `inf F ≤ F(u)` at a competitor. -/
lemma infF_le_F_of_adm (hN : 3 ≤ N) {β : Fin n → ℝ} (hβ : ∀ j, 0 ≤ β j) {u : D}
    (hu : M.Adm g u) : M.infF g β ≤ M.F g β u :=
  csInf_le ⟨0, by rintro _ ⟨v, _, rfl⟩; exact M.F_nonneg g hN hβ v⟩ ⟨u, hu, rfl⟩

/-- With `Vol(Σ) = 0` there is no competitor, and Lean's `inf` is `0`. -/
lemma infF_eq_zero_of_vol_eq_zero {β : Fin n → ℝ} (hV : M.vol g = 0) : M.infF g β = 0 := by
  have hempty : {u | M.Adm g u} = ∅ := by
    ext u; simp [Adm, normSq, hV]
  unfold infF; rw [hempty, Set.image_empty, Real.sInf_empty]

/-- The constant `1` is a competitor. -/
lemma adm_one_of_vol_ne_zero (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] (hV : M.vol g ≠ 0) : M.Adm g M.one := by
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  unfold Adm; rw [M.val_one, normSq_one _ (pStar_pos hN)]
  exact Real.rpow_pos_of_pos hVpos _

/-- `S = 0` when every `B_j` is null. -/
lemma bdryS_eq_zero_of_not (hN : 3 ≤ N) (hB : ¬ ∃ j, M.bvol g j ≠ 0) : M.bdryS g = 0 := by
  push Not at hB
  unfold bdryS
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hB j]
  have hN' := three_le_cast hN
  simp only [Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero]
  exact Real.zero_rpow (div_pos (by linarith) (by linarith)).ne'

/-- With every `B_j` null, `λ_∂ ≤ F_g(1) = 0`. -/
lemma infF_le_zero_of_not (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] (hV : M.vol g ≠ 0)
    (hB : ¬ ∃ j, M.bvol g j ≠ 0) :
    M.Fq g M.one = 0 ∧ M.infF g (fun _ => cN N) ≤ 0 := by
  have hF1 : M.Fq g M.one = 0 := by
    rw [M.Fq_one_eq g hN, M.bdryS_eq_zero_of_not g hN hB, mul_zero, zero_div]
  exact ⟨hF1, (M.infF_le_F_of_adm g hN (fun _ => (cN_pos (by omega)).le)
    (M.adm_one_of_vol_ne_zero g hN hV)).trans (le_of_eq hF1)⟩

lemma thetaDOf_nonneg (hN : 3 ≤ N) (ψ : D) : 0 ≤ M.thetaDOf g ψ :=
  div_nonneg (mul_nonneg (aN_pos hN).le (M.dirichlet_nonneg g ψ))
    (mul_nonneg (cN_pos (by omega)).le (M.bdryS_nonneg g))

lemma thetaD_nonneg (hN : 3 ≤ N) : 0 ≤ M.thetaD g :=
  div_nonneg (mul_nonneg (aN_pos hN).le ENNReal.toReal_nonneg)
    (mul_nonneg (cN_pos (by omega)).le (M.bdryS_nonneg g))

lemma zero_le_Fq_one (hN : 3 ≤ N) : 0 ≤ M.Fq g M.one :=
  M.F_nonneg g hN (fun _ => (cN_pos (by omega)).le) _

/-- `min_s [θ s² + (1 − s)²] = θ/(1 + θ)`, attained at `s* = 1/(1 + θ)` (l.893–894). -/
lemma sandwich_quadratic {θ : ℝ} (hθ : 0 ≤ θ) :
    θ * (1 / (1 + θ)) ^ 2 + (1 - 1 / (1 + θ)) ^ 2 = θ / (1 + θ) := by
  have : 1 + θ ≠ 0 := by linarith
  field_simp
  ring

/-- `θ s² + (1 − s)² ≥ θ/(1 + θ)` for every real `s`: `s*` is the minimiser (l.893). -/
lemma sandwich_quadratic_le {θ : ℝ} (hθ : 0 ≤ θ) (s : ℝ) :
    θ / (1 + θ) ≤ θ * s ^ 2 + (1 - s) ^ 2 := by
  have h1 : 0 < 1 + θ := by linarith
  rw [div_le_iff₀ h1]
  nlinarith [sq_nonneg ((1 + θ) * s - 1)]

/-- `x ↦ x/(1 + x)` is monotone and `1`-Lipschitz on `[0, ∞)`. -/
lemma frac_le_frac_add {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) (h : a ≤ b + t) :
    a / (1 + a) ≤ b / (1 + b) + t := by
  rw [div_add' _ _ _ (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_nonneg ht (mul_nonneg ha hb), mul_nonneg ht ha, mul_nonneg ht hb]

/-! ## thm:upper -/

/-- thm:upper in the Jensen form (no `ρ`, no proviso): for every competitor `ψ` with values in
`L^{p*}`, the test function `u_{s*}`, `s* = 1/(1 + θ_D)`, is a competitor with
`F_g(u_{s*}) ≤ θ_D/(1 + θ_D) F_g(1)`, hence `λ_∂ ≤ θ_D/(1 + θ_D) F_g(1)`. -/
theorem thm_upper_strong (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)]
    {ψ : D} (hψ : M.IsCapDCompetitor g ψ)
    (hψp : MemLp (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g)) :
    M.infF g (fun _ => cN N) ≤ M.thetaDOf g ψ / (1 + M.thetaDOf g ψ) * M.Fq g M.one := by
  have hθ0 := M.thetaDOf_nonneg g hN ψ
  have hF0 := M.zero_le_Fq_one g hN
  by_cases hV : M.vol g = 0
  · rw [M.infF_eq_zero_of_vol_eq_zero g hV]
    exact mul_nonneg (div_nonneg hθ0 (by linarith)) hF0
  by_cases hB : ∃ j, M.bvol g j ≠ 0
  · have hadm := (M.Fq_upperTest_le_raw g hN hV hψ hψp (1 / (1 + M.thetaDOf g ψ))).1
    refine (M.infF_le_F_of_adm g hN (fun _ => (cN_pos (by omega)).le) hadm).trans
      ((M.Fq_upperTest_le g hN hV hB hψ hψp _).trans (le_of_eq ?_))
    rw [sandwich_quadratic hθ0, mul_comm]
  · obtain ⟨hF1, h⟩ := M.infF_le_zero_of_not g hN hV hB
    rw [hF1, mul_zero]; exact h

/-- The bound is attained by an honest test function (l.893): `u_{s*} = 1 − s*ψ`,
`s* = 1/(1 + θ_D) ∈ (0, 1]`, is a competitor of energy `s*² ‖∇ψ‖²` (finite when `ψ`'s is) with
`F_g(u_{s*}) ≤ θ_D/(1 + θ_D) F_g(1)`. The bound therefore holds for the infimum over
finite-energy competitors, independently of the junk values of `dirichlet`. -/
theorem upperTest_sStar (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    {ψ : D} (hψ : M.IsCapDCompetitor g ψ)
    (hψp : MemLp (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g)) :
    0 < 1 / (1 + M.thetaDOf g ψ) ∧ 1 / (1 + M.thetaDOf g ψ) ≤ 1 ∧
      M.Adm g (M.upperTest ψ (1 / (1 + M.thetaDOf g ψ))) ∧
      M.energy g (M.upperTest ψ (1 / (1 + M.thetaDOf g ψ))) =
        ENNReal.ofReal ((1 / (1 + M.thetaDOf g ψ)) ^ 2) * M.energy g ψ ∧
      M.Fq g (M.upperTest ψ (1 / (1 + M.thetaDOf g ψ))) ≤
        M.thetaDOf g ψ / (1 + M.thetaDOf g ψ) * M.Fq g M.one := by
  have hθ0 := M.thetaDOf_nonneg g hN ψ
  refine ⟨by positivity, by rw [div_le_one (by linarith)]; linarith,
    (M.Fq_upperTest_le_raw g hN hV hψ hψp _).1, M.energy_upperTest g ψ _,
    (M.Fq_upperTest_le g hN hV hB hψ hψp _).trans (le_of_eq ?_)⟩
  rw [sandwich_quadratic hθ0, mul_comm]

/-- The proof's display as printed (l.888–891): for `s ∈ [0, 1]` and `ρ < 1`,
`F_g(u_s) ≤ F_g(1)/(1 − ρ)² [θ_D s² + (1 − s)²]`. -/
theorem Fq_upperTest_le_printed (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    {ψ : D} (hψ : M.IsCapDCompetitor g ψ)
    (hψp : MemLp (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g)) (hρ : M.rhoOf g ψ < 1)
    {s : ℝ} (_hs0 : 0 ≤ s) (_hs1 : s ≤ 1) :
    M.Fq g (M.upperTest ψ s) ≤
      M.Fq g M.one / (1 - M.rhoOf g ψ) ^ 2 * (M.thetaDOf g ψ * s ^ 2 + (1 - s) ^ 2) := by
  have hρ0 : 0 ≤ M.rhoOf g ψ :=
    div_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hθ0 := M.thetaDOf_nonneg g hN ψ
  have hx : 0 ≤ M.Fq g M.one * (M.thetaDOf g ψ * s ^ 2 + (1 - s) ^ 2) :=
    mul_nonneg (M.zero_le_Fq_one g hN) (by positivity)
  have h1 : 0 < (1 - M.rhoOf g ψ) ^ 2 := by
    have : 0 < 1 - M.rhoOf g ψ := by linarith
    positivity
  have h2 : (1 - M.rhoOf g ψ) ^ 2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  refine (M.Fq_upperTest_le g hN hV hB hψ hψp s).trans ?_
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  calc M.Fq g M.one * (M.thetaDOf g ψ * s ^ 2 + (1 - s) ^ 2) * (1 - M.rhoOf g ψ) ^ 2
      ≤ M.Fq g M.one * (M.thetaDOf g ψ * s ^ 2 + (1 - s) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left h2 hx
    _ = _ := mul_one _

/-- **thm:upper** (l.871–879), as printed, for every competitor `ψ` (the paper's minimiser among
them): with `ρ = ‖ψ‖_{L^{p*}}/V^{1/p*} < 1`, `λ_∂ ≤ θ_D/(1 + θ_D) · F_g(1)/(1 − ρ)²`. -/
theorem thm_upper (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    {ψ : D} (hψ : M.IsCapDCompetitor g ψ)
    (hψp : MemLp (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g)) (hρ : M.rhoOf g ψ < 1) :
    M.infF g (fun _ => cN N) ≤
      M.thetaDOf g ψ / (1 + M.thetaDOf g ψ) * M.Fq g M.one / (1 - M.rhoOf g ψ) ^ 2 := by
  have hρ0 : 0 ≤ M.rhoOf g ψ :=
    div_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  have hx : 0 ≤ M.thetaDOf g ψ / (1 + M.thetaDOf g ψ) * M.Fq g M.one :=
    mul_nonneg (div_nonneg (M.thetaDOf_nonneg g hN ψ) (by linarith [M.thetaDOf_nonneg g hN ψ]))
      (M.zero_le_Fq_one g hN)
  have h1 : 0 < (1 - M.rhoOf g ψ) ^ 2 := by
    have : 0 < 1 - M.rhoOf g ψ := by linarith
    positivity
  have h2 : (1 - M.rhoOf g ψ) ^ 2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  refine (M.thm_upper_strong g hN hψ hψp).trans ?_
  rw [le_div_iff₀ h1]
  calc M.thetaDOf g ψ / (1 + M.thetaDOf g ψ) * M.Fq g M.one * (1 - M.rhoOf g ψ) ^ 2
      ≤ M.thetaDOf g ψ / (1 + M.thetaDOf g ψ) * M.Fq g M.one * 1 :=
        mul_le_mul_of_nonneg_left h2 hx
    _ = _ := mul_one _

/-- thm:upper for the infimum `cap_D` (no minimiser needed), Jensen form:
`λ_∂ ≤ θ_D/(1 + θ_D) F_g(1)` once `cap_D < ∞`. -/
theorem thm_upper_capD (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hfin : M.capD g ≠ ⊤) :
    M.infF g (fun _ => cN N) ≤ M.thetaD g / (1 + M.thetaD g) * M.Fq g M.one := by
  have hc0 := cN_pos (N := N) (by omega)
  have hF0 := M.zero_le_Fq_one g hN
  have hθ0 := M.thetaD_nonneg g hN
  by_cases hV : M.vol g = 0
  · rw [M.infF_eq_zero_of_vol_eq_zero g hV]
    exact mul_nonneg (div_nonneg hθ0 (by linarith)) hF0
  by_cases hB : ∃ j, M.bvol g j ≠ 0
  swap
  · obtain ⟨hF1, h⟩ := M.infF_le_zero_of_not g hN hV hB
    rw [hF1, mul_zero]; exact h
  have hS := M.bdryS_pos g hB
  have hF1 : 0 < M.Fq g M.one := M.Fq_one_pos g hN hV hB
  set c := (M.capD g).toReal with hc
  set K := aN N / (cN N * M.bdryS g) with hK
  have hK0 : 0 < K := div_pos (aN_pos hN) (mul_pos hc0 hS)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / (K * M.Fq g M.one) with hδdef
  have hδ : 0 < δ := div_pos hε (mul_pos hK0 hF1)
  have hlt : M.capD g < ENNReal.ofReal (c + δ) := by
    calc M.capD g = ENNReal.ofReal c := (ENNReal.ofReal_toReal hfin).symm
      _ < ENNReal.ofReal (c + δ) :=
          (ENNReal.ofReal_lt_ofReal_iff (by linarith [ENNReal.toReal_nonneg (a := M.capD g)])).mpr
            (by linarith)
  obtain ⟨ψ, hψ⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hP, hψlt⟩ := iInf_lt_iff.mp hψ
  have hd : M.dirichlet g ψ < c + δ := ENNReal.toReal_lt_of_lt_ofReal hψlt
  have hθψ : M.thetaDOf g ψ ≤ M.thetaD g + K * δ := by
    have e1 : M.thetaDOf g ψ = K * M.dirichlet g ψ := by unfold thetaDOf; rw [hK]; ring
    have e2 : M.thetaD g = K * c := by unfold thetaD; rw [hK]; ring
    rw [e1, e2, ← mul_add]
    exact mul_le_mul_of_nonneg_left hd.le hK0.le
  have key := frac_le_frac_add (M.thetaDOf_nonneg g hN ψ) hθ0 (by positivity) hθψ
  calc M.infF g (fun _ => cN N) ≤ M.thetaDOf g ψ / (1 + M.thetaDOf g ψ) * M.Fq g M.one :=
        M.thm_upper_strong g hN hP.1 hP.2
    _ ≤ (M.thetaD g / (1 + M.thetaD g) + K * δ) * M.Fq g M.one :=
        mul_le_mul_of_nonneg_right key hF0
    _ = M.thetaD g / (1 + M.thetaD g) * M.Fq g M.one + ε := by
        rw [add_mul, hδdef]
        congr 1
        field_simp

/-! ## rem:notF1 -/

/-- The first-variation formula of rem:notF1 (l.364–365) for `F^(β)`, in every direction `φ`
with values in `L^{p*}(Σ)`, traces in `L^{p♯}(B_j)` and `∫_Σ φ = 0` (no bound on `φ`). -/
theorem hasDerivAt_F_one_add_of_memLp (hN : 3 ≤ N) (β : Fin n → ℝ)
    [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0)
    (φ : D) (hφv : MemLp (M.val φ) (ENNReal.ofReal (pStar N)) (M.vol g))
    (hφt : ∀ j, MemLp (M.tr φ) (ENNReal.ofReal (pSharp N)) (M.bvol g j))
    (hmean : ∫ x, M.val φ x ∂(M.vol g) = 0) :
    HasDerivAt (fun ε : ℝ => M.F g β (M.one + ε • φ))
      (2 / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) *
        ∑ j, β j * (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
          ∫ x, M.tr φ x ∂(M.bvol g j)) 0 := by
  have hN' := three_le_cast hN
  have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hfun : (fun ε : ℝ => M.F g β (M.one + ε • φ)) = fun ε : ℝ =>
      (aN N * (ε ^ 2 * M.dirichlet g φ) +
          ∑ j, β j * normSq (M.bvol g j) (pSharp N) (fun x => 1 + ε * M.tr φ x)) /
        normSq (M.vol g) (pStar N) (fun x => 1 + ε * M.val φ x) :=
    funext fun ε => M.F_one_add_smul g β φ ε
  rw [hfun]
  have hE : HasDerivAt (fun ε : ℝ => aN N * (ε ^ 2 * M.dirichlet g φ)) 0 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (M.dirichlet g φ)).const_mul (aN N)
  have hS : HasDerivAt (fun ε : ℝ =>
      ∑ j, β j * normSq (M.bvol g j) (pSharp N) (fun x => 1 + ε * M.tr φ x))
      (∑ j, β j * (2 * (M.bvol g j Set.univ).toReal ^ (2 / pSharp N - 1) *
        ∫ x, M.tr φ x ∂(M.bvol g j))) 0 :=
    HasDerivAt.fun_sum fun j _ =>
      (hasDerivAt_normSq_one_add_of_memLp (by linarith [two_le_pSharp hN]) (hφt j)).const_mul (β j)
  have hD := hasDerivAt_normSq_one_add_of_memLp (by linarith [two_le_pStar hN]) hφv
  rw [hmean, mul_zero] at hD
  have hD0 : normSq (M.vol g) (pStar N) (fun x => 1 + 0 * M.val φ x) =
      (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) := by
    simp only [zero_mul, add_zero]
    rw [normSq_one _ (pStar_pos hN), two_div_pStar hN]
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  have hD0pos : 0 < (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) :=
    Real.rpow_pos_of_pos hVpos _
  have hQ := (hE.add hS).div hD (by rw [hD0]; exact hD0pos.ne')
  refine hQ.congr_deriv ?_
  rw [hD0, two_div_pSharp hN]
  have e : ((N : ℝ) - 2) / ((N : ℝ) - 1) - 1 = -(1 / ((N : ℝ) - 1)) := by field_simp; ring
  rw [e, Finset.mul_sum, mul_zero, sub_zero, zero_add]
  field_simp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- The sign of the first variation (l.367–368), for integrable traces: strictly negative when
`β_j > 0`, `φ ≤ 0` on `∂Σ` and `φ ≢ 0` on `∂Σ`. -/
theorem firstVariation_neg_of_integrable {β : Fin n → ℝ} (hβ : ∀ j, 0 < β j)
    [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0)
    (φ : D) (hint : ∀ j, Integrable (M.tr φ) (M.bvol g j))
    (hle : ∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr φ x ≤ 0)
    (hne : ∃ j, ¬ (M.tr φ =ᵐ[M.bvol g j] 0)) :
    2 / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) *
        ∑ j, β j * (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
          ∫ x, M.tr φ x ∂(M.bvol g j) < 0 := by
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  refine mul_neg_of_pos_of_neg (div_pos two_pos (Real.rpow_pos_of_pos hVpos _)) ?_
  have hterm : ∀ j, β j * (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
      ∫ x, M.tr φ x ∂(M.bvol g j) ≤ 0 := fun j =>
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (hβ j).le (Real.rpow_nonneg ENNReal.toReal_nonneg _))
      (integral_nonpos_of_ae (hle j))
  obtain ⟨j₀, hj₀⟩ := hne
  have hB0 : M.bvol g j₀ ≠ 0 := by
    rintro h0; apply hj₀; rw [h0]; exact ae_zero.le (by simp)
  have hVj : 0 < (M.bvol g j₀ Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hB0) (measure_ne_top _ _)
  have hneg : ∫ x, M.tr φ x ∂(M.bvol g j₀) < 0 := by
    have hpos : 0 < ∫ x, (-M.tr φ) x ∂(M.bvol g j₀) := by
      rw [integral_pos_iff_support_of_nonneg_ae
        ((hle j₀).mono fun x hx => by simpa using hx) (hint j₀).neg]
      have hsupp : Function.support (-M.tr φ) = {x | ¬ M.tr φ x = (0 : X → ℝ) x} := by
        ext x; simp [Function.mem_support]
      rw [hsupp]
      rw [Filter.EventuallyEq, ae_iff] at hj₀
      exact pos_iff_ne_zero.mpr hj₀
    simp only [Pi.neg_apply, integral_neg] at hpos
    linarith
  have hlt : β j₀ * (M.bvol g j₀ Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
      ∫ x, M.tr φ x ∂(M.bvol g j₀) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos (hβ j₀) (Real.rpow_pos_of_pos hVj _)) hneg
  calc ∑ j, β j * (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
        ∫ x, M.tr φ x ∂(M.bvol g j) < ∑ _j : Fin n, (0 : ℝ) :=
        Finset.sum_lt_sum (fun j _ => hterm j) ⟨j₀, Finset.mem_univ _, hlt⟩
    _ = 0 := by simp

/-- Such directions exist (l.367–368): `φ = −ψ`, for a competitor `ψ` of `cap_D`, has values in
`L^{p*}`, traces in `L^{p♯}`, zero mean, and is `≤ 0` and `≢ 0` on `∂Σ`. -/
theorem neg_isDirection [∀ j, IsFiniteMeasure (M.bvol g j)] (hB : ∃ j, M.bvol g j ≠ 0)
    {ψ : D} (hψ : M.IsCapDCompetitor g ψ)
    (hψp : MemLp (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g)) :
    MemLp (M.val (-ψ)) (ENNReal.ofReal (pStar N)) (M.vol g) ∧
      (∀ j, MemLp (M.tr (-ψ)) (ENNReal.ofReal (pSharp N)) (M.bvol g j)) ∧
      ∫ x, M.val (-ψ) x ∂(M.vol g) = 0 ∧
      (∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr (-ψ) x ≤ 0) ∧
      ∃ j, ¬ (M.tr (-ψ) =ᵐ[M.bvol g j] 0) := by
  have htr : ∀ j, M.tr (-ψ) =ᵐ[M.bvol g j] fun _ => (-1 : ℝ) := fun j => by
    filter_upwards [hψ.1 j] with x hx
    simp [map_neg, hx]
  refine ⟨?_, fun j => (memLp_const (-1 : ℝ)).ae_eq (htr j).symm, ?_, fun j => ?_, ?_⟩
  · rw [map_neg]; exact hψp.neg
  · rw [map_neg]; simp only [Pi.neg_apply, integral_neg, hψ.2, neg_zero]
  · filter_upwards [htr j] with x hx; rw [hx]; norm_num
  · obtain ⟨j, hj⟩ := hB
    refine ⟨j, fun h0 => hj ?_⟩
    have hfalse : ∀ᵐ x ∂(M.bvol g j), False := by
      filter_upwards [htr j, h0] with x h1 h2
      rw [h1] at h2; norm_num at h2
    simpa using hfalse

/-- rem:notF1 from a competitor of the classical capacity (no boundedness): there is a
test function `u` of energy `s² ‖∇ψ‖²`, a competitor, with `F_g(u) < F_g(1)`; hence
`λ_∂ < F_g(1)`. -/
theorem exists_Fq_lt_Fq_one_of_isCapDCompetitor (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    {ψ : D} (hψ : M.IsCapDCompetitor g ψ)
    (hψp : MemLp (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g)) :
    ∃ s : ℝ, M.Adm g (M.upperTest ψ s) ∧ M.Fq g (M.upperTest ψ s) < M.Fq g M.one := by
  have hF1 := M.Fq_one_pos g hN hV hB
  have hθ0 := M.thetaDOf_nonneg g hN ψ
  refine ⟨1 / (1 + M.thetaDOf g ψ), (M.Fq_upperTest_le_raw g hN hV hψ hψp _).1,
    lt_of_le_of_lt (M.Fq_upperTest_le g hN hV hB hψ hψp _) ?_⟩
  rw [sandwich_quadratic hθ0]
  have h : M.thetaDOf g ψ / (1 + M.thetaDOf g ψ) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  calc M.Fq g M.one * (M.thetaDOf g ψ / (1 + M.thetaDOf g ψ)) < M.Fq g M.one * 1 :=
        mul_lt_mul_of_pos_left h hF1
    _ = M.Fq g M.one := mul_one _

/-- rem:notF1 (l.361): `λ_∂ < F_g(1)`, from a competitor of the classical capacity. -/
theorem infF_lt_Fq_one_of_isCapDCompetitor (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    {ψ : D} (hψ : M.IsCapDCompetitor g ψ)
    (hψp : MemLp (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g)) :
    M.infF g (fun _ => cN N) < M.Fq g M.one := by
  obtain ⟨s, hadm, hlt⟩ := M.exists_Fq_lt_Fq_one_of_isCapDCompetitor g hN hV hB hψ hψp
  exact lt_of_le_of_lt (M.infF_le_F_of_adm g hN (fun _ => (cN_pos (by omega)).le) hadm) hlt

/-- rem:notF1 (l.369–370): every `κ` with `λ_∂ ≥ κ F_g(1)` has `κ < 1`. -/
theorem kappa_lt_one_of_isCapDCompetitor (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    {ψ : D} (hψ : M.IsCapDCompetitor g ψ)
    (hψp : MemLp (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g)) {κ : ℝ}
    (hκ : κ * M.Fq g M.one ≤ M.infF g (fun _ => cN N)) : κ < 1 := by
  have hlt := M.infF_lt_Fq_one_of_isCapDCompetitor g hN hV hB hψ hψp
  have hpos := M.Fq_one_pos g hN hV hB
  have : κ * M.Fq g M.one < 1 * M.Fq g M.one := by linarith
  exact lt_of_mul_lt_mul_right this hpos.le

/-- The first variation of rem:notF1 (l.364–365), as printed. -/
def firstVariation (φ : D) : ℝ :=
  2 * cN N / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) *
    ∑ j, (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) * ∫ x, M.tr φ x ∂(M.bvol g j)

lemma firstVariation_eq (φ : D) :
    2 / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) *
        ∑ j, (fun _ => cN N) j * (M.bvol g j Set.univ).toReal ^ (-(1 / ((N : ℝ) - 1))) *
          ∫ x, M.tr φ x ∂(M.bvol g j) = M.firstVariation g φ := by
  unfold firstVariation
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

/-- **rem:notF1** (l.359–371) over the model, from a competitor `ψ` of the classical capacity
(`ψ = 1` on `∂Σ`, `∫_Σ ψ = 0`, values in `L^{p*}`):
(i) `F_g(1) = c_N S / V^{(N-2)/N}` (eq:F1);
(ii) in every direction `φ` with values in `L^{p*}`, traces in `L^{p♯}` and `∫_Σ φ = 0`, the
gradient term of `F_g(1 + εφ)` is `ε² ‖∇φ‖²`, the derivative at `0` exists and is the printed
formula, which is `< 0` when `φ ≤ 0` and `φ ≢ 0` on `∂Σ`;
(iii) such directions exist (`φ = −ψ`);
(iv) `λ_∂ < F_g(1)`, at a competitor `u` of energy `s² ‖∇ψ‖²`: the constant is never optimal;
(v) every `κ` with `λ_∂ ≥ κ F_g(1)` has `κ < 1`. -/
theorem rem_notF1 (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    {ψ : D} (hψ : M.IsCapDCompetitor g ψ)
    (hψp : MemLp (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g)) :
    M.Fq g M.one = cN N * M.bdryS g / (M.vol g Set.univ).toReal ^ (((N : ℝ) - 2) / N) ∧
    (∀ φ : D, MemLp (M.val φ) (ENNReal.ofReal (pStar N)) (M.vol g) →
      (∀ j, MemLp (M.tr φ) (ENNReal.ofReal (pSharp N)) (M.bvol g j)) →
      ∫ x, M.val φ x ∂(M.vol g) = 0 →
      (∀ ε : ℝ, M.dirichlet g (M.one + ε • φ) = ε ^ 2 * M.dirichlet g φ) ∧
      HasDerivAt (fun ε : ℝ => M.Fq g (M.one + ε • φ)) (M.firstVariation g φ) 0 ∧
      ((∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr φ x ≤ 0) → (∃ j, ¬ (M.tr φ =ᵐ[M.bvol g j] 0)) →
        M.firstVariation g φ < 0)) ∧
    (∃ φ : D, MemLp (M.val φ) (ENNReal.ofReal (pStar N)) (M.vol g) ∧
      (∀ j, MemLp (M.tr φ) (ENNReal.ofReal (pSharp N)) (M.bvol g j)) ∧
      ∫ x, M.val φ x ∂(M.vol g) = 0 ∧
      (∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr φ x ≤ 0) ∧ ∃ j, ¬ (M.tr φ =ᵐ[M.bvol g j] 0)) ∧
    (∃ u : D, M.Adm g u ∧ (∃ s : ℝ, M.energy g u = ENNReal.ofReal (s ^ 2) * M.energy g ψ) ∧
      M.Fq g u < M.Fq g M.one) ∧
    M.infF g (fun _ => cN N) < M.Fq g M.one ∧
    ∀ κ : ℝ, κ * M.Fq g M.one ≤ M.infF g (fun _ => cN N) → κ < 1 := by
  have hc : 0 < cN N := cN_pos (by omega)
  refine ⟨M.Fq_one_eq g hN, fun φ hφv hφt hmean => ⟨fun ε => M.dirichlet_one_add_smul g ε φ,
    ?_, fun hle hne => ?_⟩, ⟨-ψ, M.neg_isDirection g hB hψ hψp⟩, ?_,
    M.infF_lt_Fq_one_of_isCapDCompetitor g hN hV hB hψ hψp,
    fun κ hκ => M.kappa_lt_one_of_isCapDCompetitor g hN hV hB hψ hψp hκ⟩
  · rw [← M.firstVariation_eq g φ]
    exact M.hasDerivAt_F_one_add_of_memLp g hN (fun _ => cN N) hV φ hφv hφt hmean
  · rw [← M.firstVariation_eq g φ]
    exact M.firstVariation_neg_of_integrable g (fun _ => hc) hV φ
      (fun j => (M.memLp_tr_two g hN (hφt j)).integrable one_le_two) hle hne
  · obtain ⟨s, hadm, hlt⟩ := M.exists_Fq_lt_Fq_one_of_isCapDCompetitor g hN hV hB hψ hψp
    exact ⟨M.upperTest ψ s, hadm, ⟨s, M.energy_upperTest g ψ s⟩, hlt⟩

/-- The boundary cutoff of the strict rem:sign (`Yamabe.MeasuredModel.infF_lt_Fq_one`) gives a
competitor of `cap_D`: from `χ ∈ D` bounded with `tr χ = 1` on `∂Σ` and `∫_Σ χ < Vol(Σ)`,
`ψ = (χ − t)/(1 − t)`, `t = V⁻¹ ∫_Σ χ`. -/
theorem exists_isCapDCompetitor_of_cutoff [IsFiniteMeasure (M.vol g)] (hV : M.vol g ≠ 0)
    (χ : D) (hχv : AEStronglyMeasurable (M.val χ) (M.vol g)) (K : ℝ)
    (hKv : ∀ x, |M.val χ x| ≤ K) (hχ1 : ∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr χ x = 1)
    (hχint : ∫ x, M.val χ x ∂(M.vol g) < (M.vol g Set.univ).toReal) :
    ∃ ψ : D, M.IsCapDCompetitor g ψ ∧ MemLp (M.val ψ) (ENNReal.ofReal (pStar N)) (M.vol g) := by
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  set t : ℝ := (∫ x, M.val χ x ∂(M.vol g)) / (M.vol g Set.univ).toReal with ht
  have ht1 : t < 1 := by rw [ht, div_lt_one hVpos]; exact hχint
  have h1t : (1 - t) ≠ 0 := by linarith
  have hint : Integrable (M.val χ) (M.vol g) :=
    (integrable_const K).mono' hχv (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hKv x)
  have hval : M.val ((1 - t)⁻¹ • (χ - t • M.one)) = fun x => (1 - t)⁻¹ * (M.val χ x - t) := by
    rw [map_smul, map_sub, map_smul, M.val_one]; funext x; simp
  refine ⟨(1 - t)⁻¹ • (χ - t • M.one), ⟨fun j => ?_, ?_⟩, ?_⟩
  · filter_upwards [hχ1 j] with x hx
    rw [map_smul, map_sub, map_smul, M.tr_one]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hx, mul_one]
    field_simp
  · rw [hval, integral_const_mul, integral_sub hint (integrable_const t), integral_const,
      smul_eq_mul, measureReal_def, ht]
    field_simp
    ring
  · rw [hval]
    refine MemLp.of_bound ((hχv.sub aestronglyMeasurable_const).const_mul _)
      (|(1 - t)⁻¹| * (K + |t|)) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith [hKv x])) (abs_nonneg _)

/-- rem:notF1 under the hypotheses of the strict rem:sign (a bounded boundary cutoff `χ`):
`λ_∂ < F_g(1)`, and every `κ` with `λ_∂ ≥ κ F_g(1)` has `κ < 1`. -/
theorem rem_notF1_of_cutoff (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    (χ : D) (hχv : AEStronglyMeasurable (M.val χ) (M.vol g)) (K : ℝ)
    (hKv : ∀ x, |M.val χ x| ≤ K) (hχ1 : ∀ j, ∀ᵐ x ∂(M.bvol g j), M.tr χ x = 1)
    (hχint : ∫ x, M.val χ x ∂(M.vol g) < (M.vol g Set.univ).toReal) :
    M.infF g (fun _ => cN N) < M.Fq g M.one ∧
      ∀ κ : ℝ, κ * M.Fq g M.one ≤ M.infF g (fun _ => cN N) → κ < 1 := by
  obtain ⟨ψ, hψ, hψp⟩ := M.exists_isCapDCompetitor_of_cutoff g hV χ hχv K hKv hχ1 hχint
  exact ⟨M.infF_lt_Fq_one_of_isCapDCompetitor g hN hV hB hψ hψp,
    fun κ hκ => M.kappa_lt_one_of_isCapDCompetitor g hN hV hB hψ hψp hκ⟩

end MeasuredModel

/-! ## A witness: the two-point toy model -/

section Toy

/-- The toy competitor of `cap_D`: `ψ = (true ↦ −1, false ↦ 1)` (trace `1` at the boundary point,
mean `0`). -/
def toyPsi : Bool → ℝ := fun b => if b then -1 else 1

theorem toy_isCapDCompetitor : toyModel.IsCapDCompetitor toyMetric toyPsi := by
  refine ⟨fun j => ?_, ?_⟩
  · rw [toy_bvol, Filter.EventuallyEq, ae_dirac_iff (MeasurableSet.of_discrete)]
    simp [toyModel, toyPsi]
  · rw [toy_vol, integral_fintype .of_finite]
    simp [toyModel, toyPsi]

theorem toy_memLp_psi :
    MemLp (toyModel.val toyPsi) (ENNReal.ofReal (pStar 3)) (toyModel.vol toyMetric) := by
  haveI := toy_isFiniteMeasure_vol
  exact MemLp.of_discrete

/-- `cap_D = 8 = cap*` on the toy model. -/
theorem toy_capD : toyModel.capD toyMetric = 8 := by
  haveI := toy_isFiniteMeasure_bvol
  refine le_antisymm ((iInf₂_le toyPsi ⟨toy_isCapDCompetitor, toy_memLp_psi⟩).trans
    (le_of_eq ?_)) ?_
  · rw [toy_energy]; norm_num [toyPsi]
  · rw [← toy_capStar]
    exact toyModel.capStar_le_capD toyMetric le_rfl (by rw [toy_bdryS]; norm_num)

/-- `ρ = 1` on the toy model: the proviso `ρ < 1` of thm:upper (l.878) fails there. -/
theorem toy_rho : toyModel.rhoOf toyMetric toyPsi = 1 := by
  unfold MeasuredModel.rhoOf
  have h : eLpNorm (toyModel.val toyPsi) (ENNReal.ofReal (pStar 3)) (toyModel.vol toyMetric) =
      eLpNorm (fun _ => (1 : ℝ)) (ENNReal.ofReal (pStar 3)) (toyModel.vol toyMetric) :=
    eLpNorm_congr_norm_ae (ae_of_all _ fun b => by cases b <;> simp [toyModel, toyPsi])
  have hp : (0 : ℝ) < pStar 3 := pStar_pos le_rfl
  rw [h, eLpNorm_const' _ (by simpa using hp) ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le,
    toy_vol]
  simp only [enorm_one, one_mul]
  rw [← ENNReal.toReal_rpow, toy_count_univ]
  exact div_self (Real.rpow_pos_of_pos two_pos _).ne'

/-- `θ_D = θ = 64/c_3` on the toy model. -/
theorem toy_thetaDOf : toyModel.thetaDOf toyMetric toyPsi = 64 / cN 3 := by
  unfold MeasuredModel.thetaDOf
  rw [toy_dirichlet, toy_bdryS]
  norm_num [aN, toyPsi]

/-- On the toy model thm:upper as printed says nothing (`ρ = 1`), while its Jensen form gives
`λ_∂ ≤ θ_D/(1 + θ_D) F_g(1)` with `θ_D = 64/c_3`. -/
theorem toy_thm_upper_strong :
    ¬ toyModel.rhoOf toyMetric toyPsi < 1 ∧
      toyModel.infF toyMetric (fun _ => cN 3) ≤
        64 / cN 3 / (1 + 64 / cN 3) * toyModel.Fq toyMetric toyModel.one := by
  haveI := toy_isFiniteMeasure_vol
  haveI := toy_isFiniteMeasure_bvol
  refine ⟨by rw [toy_rho]; exact lt_irrefl 1, ?_⟩
  have h := toyModel.thm_upper_strong toyMetric le_rfl toy_isCapDCompetitor toy_memLp_psi
  rwa [toy_thetaDOf] at h

/-- Every hypothesis of `rem_notF1` holds on the toy model: there `λ_∂ < F_g(1)`. -/
theorem toy_rem_notF1 :
    toyModel.infF toyMetric (fun _ => cN 3) < toyModel.Fq toyMetric toyModel.one := by
  haveI := toy_isFiniteMeasure_vol
  haveI := toy_isFiniteMeasure_bvol
  exact (toyModel.rem_notF1 toyMetric le_rfl toy_vol_ne_zero
    ⟨0, by rw [toy_bvol]; exact Measure.dirac_ne_zero⟩ toy_isCapDCompetitor toy_memLp_psi).2.2.2.2.1

end Toy

end Yamabe
