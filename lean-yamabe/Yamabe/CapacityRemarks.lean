import Yamabe.Perforated.Poincare
import Yamabe.Perforated.Upper

/-!
# Perforated, three remarks on the proof of thm:main over the measured model: connectedness, tightness, the dichotomy

Labels (the companion BrunswicPerforated, `papers/perforated`; lines of
`papers/perforated/legacy/labeled/perforated.tex`):

* `rem:connected` — `perforated.tex:409` (l.409–415). NOT marked: partial (a reading of
  « `Σ = Σ₁ ⊔ Σ₂` », SCOPE): `MeasuredModel.rem_connected`, `CapRemarks.disc_rem_connected`,
  and `CapRemarks.bal_witness` for « in general »;
* `rem:tight` — `perforated.tex:563` (l.563–572). NOT marked: partial, its third clause is false
  as printed (SCOPE): `MeasuredModel.bdryAvg_eq_of_tr_const`, `MeasuredModel.capacitary_eq_of_minimiser`,
  `MeasuredModel.exists_capacitary_eq`, `cauchySchwarz_step`, `MeasuredModel.cauchySchwarz_step_eq_iff`,
  `MeasuredModel.ratio_upperTest_thetaD`, `MeasuredModel.ratio_upperTest_theta_iff`,
  `CapRemarks.path_rem_tight_counterexample`, `CapRemarks.path_no_tight_profile`;
* `rem:dichotomy` — `perforated.tex:1019` (l.1019–1034). NOT marked: partial (the carried facts
  of thm:main, and two asymptotic sentences not formalized, SCOPE): `MeasuredModel.rem_dichotomy`,
  `MeasuredModel.rankOne_bound`, `dichotomy_eq`, `dichotomy_lt_rankOne`, `toy_rem_dichotomy`.

No `sorry` in this file.

> If $\Sigma=\Sigma_1\sqcup\Sigma_2$ then $v=\mathbf 1_{\Sigma_1}\in W^{1,2}(\Sigma)$
> has $\nabla v\equiv0$ while $\ell(v)\ne0$ in general; rescaling gives
> $\cpstar=0$ and \eqref{eq:capineq} is false. The Poincaré step above is exactly
> where connectedness enters. (l.411–414)

> Each of the three inequalities used is an equality for the capacitary profile:
> Lemma~\ref{lem:holder} is an equality when $u$ is constant on $\partial\Sigma$;
> Lemma~\ref{lem:capacitary} is an equality when $u$ is the equilibrium potential;
> and the Cauchy--Schwarz step is an equality when
> $X/Y=\cN\sqrt S/(\aN\sqrt{\cpstar})$, which is precisely the ratio realised by
> $u=1-s\psi$ at $s=1/(1+\theta)$. Only \eqref{eq:star} is lossy, and only at order
> $\Fq_g(1)$. (l.565–571)

> An earlier form of Theorem~\ref{thm:main} split on
> $\|u-\bar u\|_{\pstar}\lessgtr\eta\|u\|_{\pstar}$ and, on the branch where $u$ is
> nearly constant, \emph{discarded} $\|u-\bar u\|_{\pstar}\ge0$. Optimising $\eta$
> gives $\lambda_\partial\ge A/(1+\sqrt{A/B})^2$ with
> $A=\theta\Fq_g(1)/(1+\theta)$, $B=\aN/\Csp^2$: a relative loss of order
> $\sqrt{\Fq_g(1)}$ rather than $\Fq_g(1)$. Keeping the discarded term instead gives
> the rank-one bound
> $\lambda_\partial\ge\Fq_g(1)\,\theta/\bigl(\theta+(1+\tau)^2\bigr)$,
> $\tau=\Csp\sqrt{\theta\Fq_g(1)/\aN}$, which strictly dominates it for every
> geometry; and using \eqref{eq:star} instead of the triangle inequality removes the
> half-order loss altogether. (l.1021–1033)

## The model

Yamabe's `MeasuredModel` (DEC-186) with the companion's `ℓ`, `cap*`, `θ`, `S`, `w_j`
(`Yamabe.Perforated.Capacity`), `C_1 = linC1`, `C_2 = linC2` (`Yamabe.Perforated.Main`),
`C_SP = Csp` (`Yamabe.Perforated.Star3`), `ψ` a competitor of `cap_D` and `u_s = upperTest ψ s`
(`Yamabe.Perforated.Upper`). `X = √(dirichlet u)`, `Y = bdryY u`, `λ_∂ = infF (fun _ => c_N)`.
Three finite models, `N = 3`, on `Fin k` with the counting measure and the flat frame:
`discModel` (`Σ = {0, 1} ⊔ {2}`, boundary `{0}`), `balModel` (`Σ = {0, 1} ⊔ {2, 3}`, boundaries
`{0}`, `{2}`), `pathModel` (the path `0 — 1 — 2`, boundaries `{0}` of area `1` and `{2}` of area `4`).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Σ = Σ₁ ⊔ Σ₂` (l.411) | ⚠ read: some `v` with `‖∇v‖ = 0` (`energy v = 0`) and `ℓ(v) ≠ 0` |
| « `ℓ(v) ≠ 0` in general » (l.412) | ✓ carried as `ℓ(v) ≠ 0`; the balanced case `ℓ(v) = 0` is `balModel` |
| the Poincaré step (l.394, l.414) | ✓ `MeanPoincare`, refuted under `TraceBound` |
| `u` constant on `∂Σ` (l.566) | ✓ carried: `tr u = c` a.e. on every `B_j`, `c ≥ 0` (the standing `u ≥ 0`, l.460) |
| `u` the equilibrium potential (l.567) | ✓ carried: `ℓ(v) = 1`, `‖∇v‖² = cap*`, `0 < cap* < ∞` |
| `X, Y ≥ 0` (l.464) | ✓ carried |
| `ψ`, `θ` in `u = 1 − sψ` at `s = 1/(1+θ)` (l.569–570) | ⚠ read: `ψ` the competitor of thm:upper (l.862), `θ` the capacity–area ratio of `cap*` (SCOPE) |
| `C_SP` finite (def:constants, l.322) | ✓ from `SobolevIneq`, `MeanPoincare` (`exists_isSobolevPoincareConst`) |
| `θ > 0`, `F_g(1) > 0`, `C_SP > 0` (« every geometry », l.1030) | ✓ carried in the strict comparison |

## SCOPE (disclosed)

* **rem:connected, proved.** For every `v` with `‖∇v‖ = 0` (`energy v = 0`) and `ℓ(v) ≠ 0`:
  `cap* = 0` (the rescaling `ℓ(v)⁻¹ v`), no `κ > 0` has `ℓ(u) ≤ ‖∇u‖/√κ` for all `u`, eq:capineq
  as stated in `Capacity.capineq` fails, and, under the trace theorem, `MeanPoincare` fails
  (`rem_connected`). `discModel` (`Σ = {0,1} ⊔ {2}`) is a disconnected witness: `v = 1_{{2}}`
  has `ℓ(v) = 1/3`, `TraceBound` holds, `MeanPoincare` and eq:capineq fail (`disc_rem_connected`).
* **rem:connected, the reading.** The model has no topology, so « `Σ = Σ₁ ⊔ Σ₂` ⇒
  `1_{Σ₁} ∈ W^{1,2}` with `∇1_{Σ₁} = 0` » is not formalized: disconnectedness enters as the
  remark's own consequence, an energy-zero `v` with `ℓ(v) ≠ 0`. Hence partial.
* **rem:connected, « in general » is load-bearing.** `balModel` (`Σ = {0,1} ⊔ {2,3}`, one
  boundary point per component, equal areas) is disconnected in the model's sense
  (`1_{{2,3}}` has zero energy, `MeanPoincare` fails) yet `ℓ(1_{{2,3}}) = 0`, `cap* = 32 > 0`
  and eq:capineq holds for every `u` (`bal_witness`). The title « Connectedness is necessary »
  overstates: what eq:capineq needs is that no union of components `Σ₁` is balanced,
  `|Σ₁|/|Σ| = Σ_{B_j ⊂ ∂Σ₁} w_j` (this general criterion is argued, not formalized).
* **rem:tight (1) and (2), proved.** lem:holder is an equality when `tr u = c ≥ 0` a.e. on every
  `B_j` (`bdryAvg_eq_of_tr_const`; `Y = |c| √S`, `bdryY_of_tr_const`); lem:capacitary is an
  equality at every minimiser `v` of eq:capstar and at every `a v`, `a ≥ 0`, once `0 < cap* < ∞`
  (`capacitary_eq_of_minimiser`), and a minimiser exists under lem:capstar's hypotheses
  (`exists_capacitary_eq`).
* **rem:tight (3), proved.** The Cauchy–Schwarz step is
  `(C₁X + C₂Y)² ≤ (C₁²/a_N + C₂²/c_N)(a_N X² + c_N Y²)` (the `Ã = 0` skeleton of l.519–550),
  with equality iff `a_N X C₂ = c_N Y C₁` (`cauchySchwarz_step`), i.e. iff
  `X/Y = c_N √S/(a_N √cap*)` (`cauchySchwarz_step_eq_iff`), as printed.
* **Finding, rem:tight (3), l.569–570: false as printed.** For a competitor `ψ` of `cap_D`
  (the thm:upper `ψ`, l.862), `u_s = 1 − sψ` realises `X/Y = √cap_D/(t √S)` at `s = 1/(1+t)`
  (`ratio_upperTest`). At `s = 1/(1 + θ_D)` this is `c_N √S/(a_N √cap_D)` (`ratio_upperTest_thetaD`):
  the printed ratio with `cap_D` for `cap*`. At `s = 1/(1 + θ)`, as printed, it is the printed
  ratio iff `cap_D = cap*` (`ratio_upperTest_theta_iff`). On `pathModel` (a connected path with
  boundary areas `1` and `4`; `MeanPoincare` and `TraceBound` hold) `cap* = 27 < 54 = cap_D`, so
  neither `s` realises the ratio and the Cauchy–Schwarz step is strict at both
  (`path_rem_tight_counterexample`). Worse, the three equalities hold together only at `u = 0`
  (`path_no_tight_profile`): there is no « capacitary profile » for which all three are
  equalities. The clause holds exactly when `cap* = cap_D`, e.g. on the two-point toy model
  (`cap* = cap_D = 8`): when the minimiser of eq:capstar is constant on `∂Σ`.
* **rem:tight, not formalized.** « Only eq:star is lossy, and only at order `F_g(1)` » (l.570–571)
  is eq:main-asymp (`Main.thm_main`), not restated here.
* **rem:dichotomy, proved.** The rank-one bound `λ_∂ ≥ F θ/(θ + (1 + τ)²)`, `τ = C √(θF/a_N)`,
  for every Sobolev–Poincaré constant `C ≥ 0`, by the triangle inequality
  `‖u‖_{p*} ≤ C ‖∇u‖ + V^{1/p*}|ū|` (`sqrt_normSq_le_triangle`), eq:linear and the
  Cauchy–Schwarz step (`rankOne_bound`). The comparison: `τ² = A(1+θ)/B` and
  `A/(1 + √(A/B))² = θF/(√(1+θ) + τ)²` (`dichotomy_eq`); the denominators differ by
  `2τ(√(1+θ) − 1)`, so the rank-one bound dominates, strictly iff `θ, F, C > 0`
  (`dichotomy_lt_rankOne`; the planner's [r] identity, checked). Assembled at `C = C_SP`
  (`rem_dichotomy`): both lower bounds on `λ_∂`, the domination, and strictness once `C_SP > 0`.
  Its hypotheses hold together on the toy model (`toy_rem_dichotomy`).
* **rem:dichotomy, why partial.** (a) It carries thm:main's model facts `MeanPoincare`,
  `TraceBound`, `InteriorBump` (θ > 0), and `SobolevIneq` (for `C_SP < ∞`, through
  `exists_isSobolevPoincareConst`). (b) The « earlier form » (the split on
  `‖u − ū‖ ≶ η‖u‖` and the optimisation in `η`, l.1021–1024) is not printed: only its resulting
  bound is stated, and it is obtained here from the rank-one bound by the comparison.
  (c) « a relative loss of order `√F_g(1)` » (l.1025–1026) and « using eq:star … removes the
  half-order loss » (l.1031–1032) are not formalized (argued: both bounds lose
  `≈ 2τ/√(1+θ)`, resp. `2τ/(1+θ)`, relatively, with `τ ∝ √F_g(1)`; eq:main-asymp loses `O(F_g(1))`).
* **Finding, rem:dichotomy, l.1030 (minor).** « strictly dominates it for every geometry » needs
  `C_SP > 0` (and `θ > 0`): at `C_SP = 0` the two bounds coincide (`dichotomy_lt_rankOne`).
  On a manifold with non-empty boundary `C_SP ≥ 2^{1/N} K_sob > 0` (lem:csp-lower, l.333), so
  the sentence holds there.
* **Junk values.** `cap*` and `θ` are as in `Capacity`; at `C_SP = 0`, Lean's `B = a_N/0 = 0`
  and `A/B = 0`, so both sides of `dichotomy_eq` are `θF/(1 + θ)`, matching the paper's limit.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Matrix

noncomputable section

namespace Yamabe

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : FrameMetric X N)

/-! ## rem:connected (l.409–415) -/

/-- rem:connected, the rescaling (l.412–413): a `v` of zero energy with `ℓ(v) ≠ 0` forces
`cap* = 0`. -/
theorem capStar_eq_zero_of_energy_eq_zero {v : D} (hE : M.energy g v = 0) (hl : M.ell g v ≠ 0) :
    M.capStar g = 0 := by
  have hw : M.ell g ((M.ell g v)⁻¹ • v) = 1 := by rw [M.ell_smul, inv_mul_cancel₀ hl]
  have h := M.capStar_le g hw
  rw [M.energy_smul, hE, mul_zero] at h
  exact le_antisymm h (zero_le)

/-- The normalised `w = ℓ(v)⁻¹ v`: `ℓ(w) = 1` and `‖∇w‖² = 0`. -/
lemma ell_dirichlet_normalise {v : D} (hE : M.energy g v = 0) (hl : M.ell g v ≠ 0) :
    M.ell g ((M.ell g v)⁻¹ • v) = 1 ∧ M.dirichlet g ((M.ell g v)⁻¹ • v) = 0 := by
  refine ⟨by rw [M.ell_smul, inv_mul_cancel₀ hl], ?_⟩
  rw [dirichlet_eq_toReal_energy, M.energy_smul, hE, mul_zero, ENNReal.toReal_zero]

/-- rem:connected, « eq:capineq is false » (l.413): no positive constant `κ` has
`ℓ(u) ≤ ‖∇u‖/√κ` for every `u`, and eq:capineq at `cap* = 0` fails at `±v`. -/
theorem not_capineq_of_energy_eq_zero {v : D} (hE : M.energy g v = 0) (hl : M.ell g v ≠ 0) :
    (¬ ∃ κ : ℝ, 0 < κ ∧ ∀ u : D, M.ell g u ≤ Real.sqrt (M.dirichlet g u) / Real.sqrt κ) ∧
    ¬ (∀ u : D, M.volMean g u - M.bdryAvg g u ≤
        Real.sqrt (M.dirichlet g u) / Real.sqrt (M.capStar g).toReal) := by
  obtain ⟨h1, h0⟩ := M.ell_dirichlet_normalise g hE hl
  refine ⟨fun ⟨κ, _, hκ⟩ => ?_, fun h => ?_⟩
  · have := hκ ((M.ell g v)⁻¹ • v)
    rw [h1, h0, Real.sqrt_zero, zero_div] at this
    linarith
  · have := h ((M.ell g v)⁻¹ • v)
    change M.ell g _ ≤ _ at this
    rw [h1, h0, Real.sqrt_zero, zero_div] at this
    linarith

/-- rem:connected, « the Poincaré step is exactly where connectedness enters » (l.414): under the
trace theorem, a `v` of zero energy with `ℓ(v) ≠ 0` refutes the Poincaré inequality. -/
theorem not_meanPoincare_of_energy_eq_zero (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    (hT : M.TraceBound g) {v : D} (hE : M.energy g v = 0) (hl : M.ell g v ≠ 0) :
    ¬ M.MeanPoincare g := by
  intro hP
  have h := M.capStar_pos g hN hV (M.bdryS_pos g hB).ne' hP hT
  rw [M.capStar_eq_zero_of_energy_eq_zero g hE hl] at h
  exact lt_irrefl _ h

/-- rem:connected over the model (l.409–415), assembled. -/
theorem rem_connected (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    (hT : M.TraceBound g) {v : D} (hE : M.energy g v = 0) (hl : M.ell g v ≠ 0) :
    M.capStar g = 0 ∧
    (¬ ∃ κ : ℝ, 0 < κ ∧ ∀ u : D, M.ell g u ≤ Real.sqrt (M.dirichlet g u) / Real.sqrt κ) ∧
    ¬ (∀ u : D, M.volMean g u - M.bdryAvg g u ≤
        Real.sqrt (M.dirichlet g u) / Real.sqrt (M.capStar g).toReal) ∧
    ¬ M.MeanPoincare g :=
  ⟨M.capStar_eq_zero_of_energy_eq_zero g hE hl, (M.not_capineq_of_energy_eq_zero g hE hl).1,
    (M.not_capineq_of_energy_eq_zero g hE hl).2,
    M.not_meanPoincare_of_energy_eq_zero g hN hV hB hT hE hl⟩

/-! ## rem:tight (l.563–572) -/

/-- `Y = |c| √S` when `tr u = c` a.e. on every `B_j`. -/
lemma bdryY_of_tr_const (hN : 3 ≤ N) {u : D} {c : ℝ}
    (hu : ∀ j, M.tr u =ᵐ[M.bvol g j] fun _ => c) :
    M.bdryY g u = |c| * Real.sqrt (M.bdryS g) := by
  unfold bdryY
  have h : ∀ j, normSq (M.bvol g j) (pSharp N) (M.tr u) =
      c ^ 2 * (M.bvol g j Set.univ).toReal ^ (2 / pSharp N) := fun j => by
    rw [normSq_ae_congr (hu j), normSq_fun_const _ (pSharp_pos hN)]
  simp only [h]
  rw [← Finset.mul_sum, ← M.bdryS_eq g hN, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- rem:tight (1) (l.566): lem:holder is an equality when `u` is a constant `c ≥ 0` on `∂Σ`. -/
theorem bdryAvg_eq_of_tr_const (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hS : M.bdryS g ≠ 0) {u : D} {c : ℝ} (hc : 0 ≤ c)
    (hu : ∀ j, M.tr u =ᵐ[M.bvol g j] fun _ => c) :
    M.bdryAvg g u = M.bdryY g u / Real.sqrt (M.bdryS g) := by
  have hb : M.bdryAvg g u = c * M.bdryAvg g M.one := by
    unfold bdryAvg
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_congr_ae (hu j), M.tr_one, integral_const, integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hb, M.bdryAvg_one g hN hS, mul_one, M.bdryY_of_tr_const g hN hu, abs_of_nonneg hc]
  have hS0 : 0 < Real.sqrt (M.bdryS g) :=
    Real.sqrt_pos.mpr (lt_of_le_of_ne (M.bdryS_nonneg g) (Ne.symm hS))
  field_simp

/-- rem:tight (2) (l.567): lem:capacitary is an equality at the equilibrium potential `v`
(`ℓ(v) = 1`, `‖∇v‖² = cap*`), and at every `a v`, `a ≥ 0`. -/
theorem capacitary_eq_of_minimiser (hcap : 0 < M.capStar g) (hcap' : M.capStar g < ⊤)
    {v : D} (hv : M.ell g v = 1) (hvE : M.energy g v = M.capStar g) {a : ℝ} (ha : 0 ≤ a) :
    M.volMean g (a • v) = M.bdryAvg g (a • v) +
      Real.sqrt (M.dirichlet g (a • v)) / Real.sqrt (M.capStar g).toReal := by
  have hκ : 0 < (M.capStar g).toReal := ENNReal.toReal_pos hcap.ne' hcap'.ne
  have hd : M.dirichlet g (a • v) = a ^ 2 * (M.capStar g).toReal := by
    rw [dirichlet_eq_toReal_energy, M.energy_smul, hvE, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg a)]
  have hl : M.volMean g v - M.bdryAvg g v = 1 := hv
  rw [M.volMean_smul, M.bdryAvg_smul, hd, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha,
    mul_div_assoc, div_self (Real.sqrt_pos.mpr hκ).ne']
  linear_combination a * hl

/-- rem:tight (2), with the minimiser of lem:capstar: under its hypotheses there is an equilibrium
potential at which lem:capacitary is an equality. -/
theorem exists_capacitary_eq (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (hI : M.InteriorBump g) (hDM : M.DirectMethod g) :
    ∃ v : D, M.ell g v = 1 ∧ M.energy g v = M.capStar g ∧
      M.volMean g v = M.bdryAvg g v +
        Real.sqrt (M.dirichlet g v) / Real.sqrt (M.capStar g).toReal := by
  have hS := (M.bdryS_pos g hB).ne'
  obtain ⟨v, hv1, hvE⟩ := M.capStar_attained g hN hV hS hP hT hI hDM
  have h := M.capacitary_eq_of_minimiser g (M.capStar_pos g hN hV hS hP hT)
    (M.capStar_lt_top g hV hI) hv1 hvE zero_le_one
  rw [one_smul] at h
  exact ⟨v, hv1, hvE, h⟩

end MeasuredModel

/-- rem:tight (3) (l.567–569), the Cauchy–Schwarz step in the abstract: for `a, c > 0`,
`(C₁X + C₂Y)² ≤ (C₁²/a + C₂²/c)(aX² + cY²)`, with equality iff `a X C₂ = c Y C₁`. -/
theorem cauchySchwarz_step {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (C₁ C₂ X Y : ℝ) :
    (C₁ * X + C₂ * Y) ^ 2 ≤ (C₁ ^ 2 / a + C₂ ^ 2 / c) * (a * X ^ 2 + c * Y ^ 2) ∧
    ((C₁ * X + C₂ * Y) ^ 2 = (C₁ ^ 2 / a + C₂ ^ 2 / c) * (a * X ^ 2 + c * Y ^ 2) ↔
      a * X * C₂ = c * Y * C₁) := by
  have key : (C₁ ^ 2 / a + C₂ ^ 2 / c) * (a * X ^ 2 + c * Y ^ 2) - (C₁ * X + C₂ * Y) ^ 2 =
      (a * X * C₂ - c * Y * C₁) ^ 2 / (a * c) := by
    field_simp
    ring
  have hac : 0 < a * c := mul_pos ha hc
  refine ⟨by nlinarith [div_nonneg (sq_nonneg (a * X * C₂ - c * Y * C₁)) hac.le], ?_⟩
  constructor
  · intro h
    have h0 : (a * X * C₂ - c * Y * C₁) ^ 2 / (a * c) = 0 := by linarith
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h0)
    · exact absurd h0 hac.ne'
  · intro h
    have h0 : (a * X * C₂ - c * Y * C₁) ^ 2 / (a * c) = 0 := by rw [h, sub_self]; simp
    linarith

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : FrameMetric X N)

/-- rem:tight (3) over the model (l.567–569): with `C₁ = V^{1/p*}/√cap*`, `C₂ = V^{1/p*}/√S`, the
Cauchy–Schwarz step is an equality at `(X, Y)`, `Y > 0`, iff `X/Y = c_N √S/(a_N √cap*)`. -/
theorem cauchySchwarz_step_eq_iff (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] (hV : M.vol g ≠ 0)
    (hS : 0 < M.bdryS g) (hcap : 0 < (M.capStar g).toReal) {X Y : ℝ} (hY : 0 < Y) :
    (M.linC1 g * X + M.linC2 g * Y) ^ 2 =
        (M.linC1 g ^ 2 / aN N + M.linC2 g ^ 2 / cN N) * (aN N * X ^ 2 + cN N * Y ^ 2) ↔
      X / Y = cN N * Real.sqrt (M.bdryS g) / (aN N * Real.sqrt (M.capStar g).toReal) := by
  have ha := aN_pos hN
  have hc := cN_pos (N := N) (by omega)
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  have hW : 0 < (M.vol g Set.univ).toReal ^ (1 / pStar N) := Real.rpow_pos_of_pos hVpos _
  have hsS := Real.sqrt_pos.mpr hS
  have hsk := Real.sqrt_pos.mpr hcap
  rw [(cauchySchwarz_step ha hc _ _ X Y).2, div_eq_div_iff hY.ne' (by positivity)]
  unfold linC1 linC2
  set W := (M.vol g Set.univ).toReal ^ (1 / pStar N)
  set sS := Real.sqrt (M.bdryS g)
  set sk := Real.sqrt (M.capStar g).toReal
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-- `Y(u_s) = |1 − s| √S` for a competitor `ψ` of `cap_D` (l.884). -/
theorem bdryY_upperTest (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)] {ψ : D}
    (hψ : M.IsCapDCompetitor g ψ) (s : ℝ) :
    M.bdryY g (M.upperTest ψ s) = |1 - s| * Real.sqrt (M.bdryS g) := by
  refine M.bdryY_of_tr_const g hN fun j => ?_
  filter_upwards [hψ.1 j] with x hx
  rw [tr_upperTest]; simp only [hx]; ring

/-- The ratio `X/Y` realised by `u_s`, `s = 1/(1 + t)`, `t > 0`: `√(‖∇ψ‖²)/(t √S)`. -/
theorem ratio_upperTest (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hS : 0 < M.bdryS g) {ψ : D} (hψ : M.IsCapDCompetitor g ψ) {t : ℝ} (ht : 0 < t) :
    Real.sqrt (M.dirichlet g (M.upperTest ψ (1 / (1 + t)))) /
        M.bdryY g (M.upperTest ψ (1 / (1 + t))) =
      Real.sqrt (M.dirichlet g ψ) / (t * Real.sqrt (M.bdryS g)) := by
  have h1t : 0 < 1 + t := by linarith
  have hs : 1 - 1 / (1 + t) = t / (1 + t) := by field_simp; ring
  rw [M.bdryY_upperTest g hN hψ, dirichlet_upperTest, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by positivity), hs, abs_of_pos (by positivity)]
  have hsS := Real.sqrt_pos.mpr hS
  field_simp

/-- rem:tight (3), the ratio realised by `u_s = 1 − sψ` at `s = 1/(1 + θ_D)`:
`X/Y = c_N √S/(a_N √cap_D)`, `cap_D = ‖∇ψ‖²`. -/
theorem ratio_upperTest_thetaD (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hS : 0 < M.bdryS g) {ψ : D} (hψ : M.IsCapDCompetitor g ψ) (hD : 0 < M.dirichlet g ψ) :
    Real.sqrt (M.dirichlet g (M.upperTest ψ (1 / (1 + M.thetaDOf g ψ)))) /
        M.bdryY g (M.upperTest ψ (1 / (1 + M.thetaDOf g ψ))) =
      cN N * Real.sqrt (M.bdryS g) / (aN N * Real.sqrt (M.dirichlet g ψ)) := by
  have ha := aN_pos hN
  have hc := cN_pos (N := N) (by omega)
  have hθ : 0 < M.thetaDOf g ψ := by unfold thetaDOf; positivity
  rw [M.ratio_upperTest g hN hS hψ hθ, thetaDOf]
  have hsS := Real.sqrt_pos.mpr hS
  have hsD := Real.sqrt_pos.mpr hD
  have e1 := Real.sq_sqrt hS.le
  have e2 := Real.sq_sqrt hD.le
  rw [div_eq_div_iff (by positivity) (by positivity)]
  set sS := Real.sqrt (M.bdryS g)
  set sD := Real.sqrt (M.dirichlet g ψ)
  rw [← e1, ← e2]
  field_simp

/-- rem:tight (3) as printed, at `s = 1/(1 + θ)`: the ratio realised by `u_s` is
`c_N √S/(a_N √cap*)` iff `‖∇ψ‖² = cap*`. -/
theorem ratio_upperTest_theta_iff (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hS : 0 < M.bdryS g) (hcap : 0 < (M.capStar g).toReal) {ψ : D} (hψ : M.IsCapDCompetitor g ψ)
    (hD : 0 < M.dirichlet g ψ) :
    Real.sqrt (M.dirichlet g (M.upperTest ψ (1 / (1 + M.theta g)))) /
        M.bdryY g (M.upperTest ψ (1 / (1 + M.theta g))) =
      cN N * Real.sqrt (M.bdryS g) / (aN N * Real.sqrt (M.capStar g).toReal) ↔
      M.dirichlet g ψ = (M.capStar g).toReal := by
  have ha := aN_pos hN
  have hc := cN_pos (N := N) (by omega)
  have hθ : 0 < M.theta g := by unfold theta; positivity
  rw [M.ratio_upperTest g hN hS hψ hθ, theta]
  have hsS := Real.sqrt_pos.mpr hS
  have hsD := Real.sqrt_pos.mpr hD
  have hsk := Real.sqrt_pos.mpr hcap
  have e1 := Real.sq_sqrt hS.le
  have e2 := Real.sq_sqrt hD.le
  have e3 := Real.sq_sqrt hcap.le
  rw [div_eq_div_iff (by positivity) (by positivity)]
  set sS := Real.sqrt (M.bdryS g)
  set sD := Real.sqrt (M.dirichlet g ψ)
  set sk := Real.sqrt (M.capStar g).toReal
  rw [← e1, ← e2, ← e3]
  constructor
  · intro h
    have h' : sD * (aN N * cN N * sS ^ 2 * sk) = sk * (aN N * cN N * sS ^ 2 * sk) := by
      field_simp at h
      rw [h]
    have hne : aN N * cN N * sS ^ 2 * sk ≠ 0 := by positivity
    have := mul_right_cancel₀ hne h'
    rw [this]
  · intro h
    have hsq : sD = sk := by
      have := congrArg Real.sqrt h
      rwa [Real.sqrt_sq hsD.le, Real.sqrt_sq hsk.le] at this
    rw [hsq]
    field_simp

/-! ## rem:dichotomy (l.1019–1034): the rank-one bound on the model -/

/-- The triangle inequality of the rank-one bound (l.1026–1028): for a competitor `u` and a
Sobolev–Poincaré constant `C`, `‖u‖_{p*} ≤ C ‖∇u‖ + V^{1/p*} |ū|`. -/
theorem sqrt_normSq_le_triangle (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] (hV : M.vol g ≠ 0)
    {u : D} (hmeas : AEStronglyMeasurable (M.val u) (M.vol g)) (hu : M.Adm g u) {C : ℝ}
    (hC : M.IsSobolevPoincareConst g C) :
    Real.sqrt (normSq (M.vol g) (pStar N) (M.val u)) ≤
      C * Real.sqrt (M.dirichlet g u) +
        (M.vol g Set.univ).toReal ^ (1 / pStar N) * |M.volMean g u| := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (pStar N) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith [two_le_pStar hN])
  have hp0 : ENNReal.ofReal (pStar N) ≠ 0 := by
    intro h; rw [h] at hp1; exact absurd hp1 (by simp)
  set m := M.mean g u with hm
  set f := M.val u
  have hfin : eLpNorm f (ENNReal.ofReal (pStar N)) (M.vol g) ≠ ⊤ := by
    intro h
    have := hu
    unfold Adm normSq at this
    rw [h, ENNReal.toReal_top] at this
    norm_num at this
  have hcm : AEStronglyMeasurable (fun _ : X => m) (M.vol g) := aestronglyMeasurable_const
  have hdm : AEStronglyMeasurable (fun x => f x - m) (M.vol g) := hmeas.sub hcm
  have hconst : eLpNorm (fun _ : X => m) (ENNReal.ofReal (pStar N)) (M.vol g) =
      ‖m‖ₑ * M.vol g Set.univ ^ (1 / pStar N) := by
    rw [eLpNorm_const _ hp0 hV, ENNReal.toReal_ofReal (by linarith [two_le_pStar hN])]
  have hcfin : eLpNorm (fun _ : X => m) (ENNReal.ofReal (pStar N)) (M.vol g) ≠ ⊤ := by
    rw [hconst]
    exact ENNReal.mul_ne_top enorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by have := pStar_pos hN; positivity) (measure_ne_top _ _))
  have hdfin : eLpNorm (fun x => f x - m) (ENNReal.ofReal (pStar N)) (M.vol g) ≠ ⊤ := by
    have h := eLpNorm_sub_le (f := f) (g := fun _ => m) hmeas hcm hp1
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfin, hcfin⟩) h
  have hsplit : f = (fun x => f x - m) + (fun _ => m) := by funext x; simp
  have htri := eLpNorm_add_le hdm hcm hp1
  rw [← hsplit] at htri
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hdfin, hcfin⟩) htri
  rw [ENNReal.toReal_add hdfin hcfin] at hreal
  rw [sqrt_normSq]
  refine hreal.trans (add_le_add (hC u) (le_of_eq ?_))
  rw [hconst, ENNReal.toReal_mul, toReal_enorm, ENNReal.toReal_rpow, Real.norm_eq_abs, hm,
    mean_eq_volMean, mul_comm]

/-- rem:dichotomy, the rank-one bound (l.1028–1030), for any Sobolev–Poincaré constant `C ≥ 0`:
`λ_∂ ≥ F_g(1) θ/(θ + (1 + τ)²)`, `τ = C √(θ F_g(1)/a_N)`. -/
theorem rankOne_bound (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (hθ : 0 < M.theta g) {C : ℝ} (hC0 : 0 ≤ C) (hC : M.IsSobolevPoincareConst g C) :
    M.Fq g M.one * M.theta g /
        (M.theta g + (1 + C * Real.sqrt (M.theta g * M.Fq g M.one / aN N)) ^ 2) ≤
      M.infF g (fun _ => cN N) := by
  obtain ⟨e1, e2, -, hF1pos⟩ := M.calib_main g hN hV hB
  obtain ⟨K, hK⟩ := hP
  have ha := aN_pos hN
  have hc := cN_pos (N := N) (by omega)
  set F := M.Fq g M.one with hFdef
  set θ := M.theta g with hθdef
  set C1 := M.linC1 g with hC1
  set C2 := M.linC2 g with hC2
  have hC1n : 0 ≤ C1 := M.linC1_nonneg g
  have hC2n : 0 ≤ C2 := M.linC2_nonneg g
  set τ := C * Real.sqrt (θ * F / aN N) with hτ
  have hq : 0 ≤ θ * F / aN N := by positivity
  have hτ2 : τ ^ 2 = θ * F * C ^ 2 / aN N := by
    rw [hτ, mul_pow, Real.sq_sqrt hq]; ring
  have hsq : Real.sqrt (θ * F / aN N) = θ * F * C1 / aN N := by
    have h0 : 0 ≤ θ * F * C1 / aN N := by positivity
    have e1' : θ * (F * C1 ^ 2) = aN N := by rw [e1]; field_simp
    have hsq2 : (θ * F * C1 / aN N) ^ 2 = θ * F / aN N := by
      calc (θ * F * C1 / aN N) ^ 2 = θ * F * (θ * (F * C1 ^ 2)) / aN N ^ 2 := by ring
        _ = θ * F / aN N := by rw [e1']; field_simp
    rw [← hsq2, Real.sqrt_sq h0]
  have hτ1 : τ = θ * F * C * C1 / aN N := by rw [hτ, hsq]; ring
  set Kc := (C + C1) ^ 2 / aN N + C2 ^ 2 / cN N with hKc
  have hKF : F * θ * Kc = θ + (1 + τ) ^ 2 := by
    have e1' : θ * (F * C1 ^ 2) = aN N := by rw [e1]; field_simp
    have hexp : θ + (1 + τ) ^ 2 = θ + 1 + 2 * τ + τ ^ 2 := by ring
    rw [hexp, hKc, hτ2, hτ1]
    field_simp
    linear_combination cN N * e1' + aN N * θ * e2
  have hden : 0 < θ + (1 + τ) ^ 2 := by positivity
  refine M.le_infF_of_forall g hN hV fun u hu => ?_
  have hlin : (M.vol g Set.univ).toReal ^ (1 / pStar N) * |M.volMean g u| ≤
      C1 * Real.sqrt (M.dirichlet g u) + C2 * M.bdryY g u := M.eq_linear g hN hV hB ⟨K, hK⟩ hT u
  have hnorm := M.sqrt_normSq_le_triangle g hN hV ((hK u).1.aestronglyMeasurable) hu hC
  set Xu := Real.sqrt (M.dirichlet g u)
  set Yu := M.bdryY g u
  have hX0 : 0 ≤ Xu := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Yu := Real.sqrt_nonneg _
  have hX2 : Xu ^ 2 = M.dirichlet g u := Real.sq_sqrt (M.dirichlet_nonneg g u)
  have hY2 : Yu ^ 2 = ∑ j, normSq (M.bvol g j) (pSharp N) (M.tr u) := M.bdryY_sq g u
  have hZ : Real.sqrt (normSq (M.vol g) (pStar N) (M.val u)) ≤ (C + C1) * Xu + C2 * Yu := by
    linarith
  have hZ2 : normSq (M.vol g) (pStar N) (M.val u) ≤ ((C + C1) * Xu + C2 * Yu) ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hZ 2
    rwa [Real.sq_sqrt (normSq_nonneg _ _ _)] at h
  have hCS := (cauchySchwarz_step ha hc (C + C1) C2 Xu Yu).1
  have hnum : aN N * M.dirichlet g u + cN N * ∑ j, normSq (M.bvol g j) (pSharp N) (M.tr u) =
      aN N * Xu ^ 2 + cN N * Yu ^ 2 := by rw [hX2, hY2]
  rw [M.Fq_eq g u, hnum, div_le_div_iff₀ hden hu]
  have hb : F * θ * normSq (M.vol g) (pStar N) (M.val u) ≤
      F * θ * (Kc * (aN N * Xu ^ 2 + cN N * Yu ^ 2)) :=
    mul_le_mul_of_nonneg_left (hZ2.trans hCS) (by positivity)
  calc F * θ * normSq (M.vol g) (pStar N) (M.val u)
      ≤ F * θ * (Kc * (aN N * Xu ^ 2 + cN N * Yu ^ 2)) := hb
    _ = (aN N * Xu ^ 2 + cN N * Yu ^ 2) * (θ + (1 + τ) ^ 2) := by rw [← hKF]; ring

end MeasuredModel

/-! ## rem:dichotomy: the comparison (algebra) -/

/-- `τ² = A(1 + θ)/B` and `A/(1 + √(A/B))² = θF/(√(1 + θ) + τ)²`, with `A = θF/(1 + θ)`,
`B = a/C²`, `τ = C √(θF/a)`. -/
theorem dichotomy_eq {θ F a C : ℝ} (hθ : 0 ≤ θ) (hF : 0 ≤ F) (ha : 0 < a) (hC : 0 ≤ C) :
    (C * Real.sqrt (θ * F / a)) ^ 2 = θ * F / (1 + θ) * (1 + θ) / (a / C ^ 2) ∧
    θ * F / (1 + θ) / (1 + Real.sqrt (θ * F / (1 + θ) / (a / C ^ 2))) ^ 2 =
      θ * F / (Real.sqrt (1 + θ) + C * Real.sqrt (θ * F / a)) ^ 2 := by
  have hq : 0 ≤ θ * F / a := div_nonneg (mul_nonneg hθ hF) ha.le
  have hτ2 : (C * Real.sqrt (θ * F / a)) ^ 2 = C ^ 2 * (θ * F / a) := by
    rw [mul_pow, Real.sq_sqrt hq]
  have h1θ : 0 < 1 + θ := by linarith
  have hAB : θ * F / (1 + θ) / (a / C ^ 2) = (C * Real.sqrt (θ * F / a)) ^ 2 / (1 + θ) := by
    rw [hτ2]
    rcases hC.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · field_simp
  refine ⟨?_, ?_⟩
  · rw [hτ2]
    rcases hC.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · field_simp
  · set τ := C * Real.sqrt (θ * F / a) with hτ
    have hτ0 : 0 ≤ τ := mul_nonneg hC (Real.sqrt_nonneg _)
    set r := Real.sqrt (1 + θ) with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr h1θ
    have hr2 : r ^ 2 = 1 + θ := Real.sq_sqrt h1θ.le
    have hs : Real.sqrt (τ ^ 2 / (1 + θ)) = τ / r := by
      rw [Real.sqrt_div' _ h1θ.le, Real.sqrt_sq hτ0]
    rw [hAB, hs]
    have e : (1 + τ / r) ^ 2 = (r + τ) ^ 2 / (1 + θ) := by
      rw [← hr2]; field_simp
    rw [e, div_div_eq_mul_div]
    field_simp

/-- rem:dichotomy, the comparison (l.1030): the rank-one bound dominates the dichotomy's,
`A/(1 + √(A/B))² ≤ θF/(θ + (1 + τ)²)`; the denominators differ by `2τ(√(1 + θ) − 1)`; and the
domination is strict iff `θ, F, C > 0`. -/
theorem dichotomy_lt_rankOne {θ F a C : ℝ} (hθ : 0 ≤ θ) (hF : 0 ≤ F) (ha : 0 < a) (hC : 0 ≤ C) :
    (Real.sqrt (1 + θ) + C * Real.sqrt (θ * F / a)) ^ 2 -
        (θ + (1 + C * Real.sqrt (θ * F / a)) ^ 2) =
      2 * (C * Real.sqrt (θ * F / a)) * (Real.sqrt (1 + θ) - 1) ∧
    θ * F / (1 + θ) / (1 + Real.sqrt (θ * F / (1 + θ) / (a / C ^ 2))) ^ 2 ≤
      F * θ / (θ + (1 + C * Real.sqrt (θ * F / a)) ^ 2) ∧
    (θ * F / (1 + θ) / (1 + Real.sqrt (θ * F / (1 + θ) / (a / C ^ 2))) ^ 2 <
      F * θ / (θ + (1 + C * Real.sqrt (θ * F / a)) ^ 2) ↔ 0 < θ ∧ 0 < F ∧ 0 < C) := by
  rw [(dichotomy_eq hθ hF ha hC).2]
  set τ := C * Real.sqrt (θ * F / a) with hτ
  have hτ0 : 0 ≤ τ := mul_nonneg hC (Real.sqrt_nonneg _)
  have h1θ : 0 < 1 + θ := by linarith
  set r := Real.sqrt (1 + θ) with hr
  have hr2 : r ^ 2 = 1 + θ := Real.sq_sqrt h1θ.le
  have hr1 : 1 ≤ r := by rw [hr, Real.one_le_sqrt]; linarith
  have hdiff : (r + τ) ^ 2 - (θ + (1 + τ) ^ 2) = 2 * τ * (r - 1) := by
    linear_combination hr2
  have hden : 0 < θ + (1 + τ) ^ 2 := by nlinarith
  have hle : θ + (1 + τ) ^ 2 ≤ (r + τ) ^ 2 := by nlinarith
  have hnum : 0 ≤ θ * F := mul_nonneg hθ hF
  refine ⟨hdiff, ?_, ?_⟩
  · rw [mul_comm F θ]
    exact div_le_div_of_nonneg_left hnum hden hle
  · constructor
    · intro hlt
      have hθF : 0 < θ * F := by
        rcases hnum.eq_or_lt with h0 | h0
        · rw [← h0, mul_comm F θ, ← h0] at hlt; simp at hlt
        · exact h0
      have hθ0 : 0 < θ := lt_of_le_of_ne hθ (fun h => by rw [← h] at hθF; simp at hθF)
      have hF0 : 0 < F := lt_of_le_of_ne hF (fun h => by rw [← h] at hθF; simp at hθF)
      refine ⟨hθ0, hF0, lt_of_le_of_ne hC fun hC0 => ?_⟩
      have : τ = 0 := by rw [hτ, ← hC0, zero_mul]
      rw [this] at hlt hdiff
      have heq : (r + 0) ^ 2 = θ + (1 + 0) ^ 2 := by linarith
      rw [heq, mul_comm F θ] at hlt
      exact lt_irrefl _ hlt
    · rintro ⟨hθ0, hF0, hC0⟩
      have hτp : 0 < τ := mul_pos hC0 (Real.sqrt_pos.mpr (by positivity))
      have hr1' : 1 < r := by rw [hr, Real.lt_sqrt zero_le_one]; linarith
      have hlt : θ + (1 + τ) ^ 2 < (r + τ) ^ 2 := by nlinarith
      rw [mul_comm F θ]
      exact div_lt_div_of_pos_left (by positivity) hden hlt

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : FrameMetric X N)

/-- rem:dichotomy over the model (l.1019–1034), assembled at `C = C_SP`: the dichotomy bound
`λ_∂ ≥ A/(1 + √(A/B))²` and the rank-one bound `λ_∂ ≥ F θ/(θ + (1 + τ)²)` both hold, the second
dominates the first, strictly once `C_SP > 0`. -/
theorem rem_dichotomy (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (hI : M.InteriorBump g) (hSob : M.SobolevIneq g) :
    let F := M.Fq g M.one
    let θ := M.theta g
    let A := θ * F / (1 + θ)
    let B := aN N / M.Csp g ^ 2
    let τ := M.Csp g * Real.sqrt (θ * F / aN N)
    A / (1 + Real.sqrt (A / B)) ^ 2 ≤ M.infF g (fun _ => cN N) ∧
    F * θ / (θ + (1 + τ) ^ 2) ≤ M.infF g (fun _ => cN N) ∧
    A / (1 + Real.sqrt (A / B)) ^ 2 ≤ F * θ / (θ + (1 + τ) ^ 2) ∧
    (0 < M.Csp g → A / (1 + Real.sqrt (A / B)) ^ 2 < F * θ / (θ + (1 + τ) ^ 2)) := by
  intro F θ A B τ
  have hθ : 0 < θ := M.theta_pos g hN hV hB hP hT hI
  have hF : 0 < F := (M.calib_main g hN hV hB).2.2.2
  have hC0 := M.Csp_nonneg g
  have hSP := M.isSobolevPoincareConst_Csp g (M.exists_isSobolevPoincareConst g hSob hP)
  have hrank := M.rankOne_bound g hN hV hB hP hT hθ hC0 hSP
  obtain ⟨-, hle, hlt⟩ := dichotomy_lt_rankOne hθ.le hF.le (aN_pos hN) hC0
  exact ⟨hle.trans hrank, hrank, hle, fun hC => hlt.mpr ⟨hθ, hF, hC⟩⟩

end MeasuredModel

/-! ## Three finite models, `N = 3`, on `Fin k` -/

namespace CapRemarks

section FinModels

/-- The flat frame metric `G = 1` on `Fin k`. -/
def finMetric (k : ℕ) : FrameMetric (Fin k) 3 where
  G := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one

/-- A graph-like model on `Fin k`: counting measure, boundary measures `μb`, values and traces the
identity, and the differential the constant (in `x`) vector `e u`. -/
def finModel (k n : ℕ) (μb : Fin n → Measure (Fin k)) (e : (Fin k → ℝ) →ₗ[ℝ] Fin 3 → ℝ)
    (he : e (fun _ => 1) = 0) : MeasuredModel (Fin k) (Fin k → ℝ) 3 n where
  μ := Measure.count
  μb := μb
  P := fun _ => toyP
  P_injective := fun _ => toyP_injective
  val := LinearMap.id
  tr := LinearMap.id
  d := LinearMap.pi fun _ => e
  one := fun _ => 1
  val_one := rfl
  tr_one := rfl
  d_one := by funext x; simp [he]

variable {k n : ℕ} {μb : Fin n → Measure (Fin k)} {e : (Fin k → ℝ) →ₗ[ℝ] Fin 3 → ℝ}
  {he : e (fun _ => 1) = 0}

lemma finModel_val (u : Fin k → ℝ) : (finModel k n μb e he).val u = u := rfl

lemma finModel_tr (u : Fin k → ℝ) : (finModel k n μb e he).tr u = u := rfl

lemma finModel_vol : (finModel k n μb e he).vol (finMetric k) = Measure.count := by
  simp [MeasuredModel.vol, finModel, finMetric]

lemma finModel_bvol (j : Fin n) : (finModel k n μb e he).bvol (finMetric k) j = μb j := by
  simp only [MeasuredModel.bvol, finModel, finMetric, Matrix.mul_one]
  rw [toyP_transpose_mul]
  simp

lemma finModel_gradSq (u : Fin k → ℝ) (x : Fin k) :
    (finModel k n μb e he).gradSq (finMetric k) u x = ∑ a, e u a ^ 2 := by
  simp [MeasuredModel.gradSq, finModel, finMetric, dotProduct, sq]

lemma finModel_energy (u : Fin k → ℝ) :
    (finModel k n μb e he).energy (finMetric k) u = ENNReal.ofReal (k * ∑ a, e u a ^ 2) := by
  unfold MeasuredModel.energy
  simp only [finModel_gradSq]
  rw [finModel_vol, lintegral_const, Measure.count_univ, ENNReal.ofReal_mul (by positivity)]
  simp [mul_comm]

lemma finModel_dirichlet (u : Fin k → ℝ) :
    (finModel k n μb e he).dirichlet (finMetric k) u = k * ∑ a, e u a ^ 2 := by
  rw [MeasuredModel.dirichlet_eq_toReal_energy, finModel_energy,
    ENNReal.toReal_ofReal (by positivity)]

lemma finModel_volMean (u : Fin k → ℝ) :
    (finModel k n μb e he).volMean (finMetric k) u = (∑ x, u x) / k := by
  unfold MeasuredModel.volMean
  rw [finModel_vol, integral_fintype .of_finite, Measure.count_univ]
  simp [finModel, div_eq_inv_mul]

/-- `‖f‖²_{L²(count)} = Σ f²` on `Fin k`. -/
lemma normSq_count_two (f : Fin k → ℝ) :
    normSq (Measure.count : Measure (Fin k)) 2 f = ∑ x, f x ^ 2 := by
  have hne : ∀ t : ℝ, ‖t‖ₑ ^ (2 : ℝ) ≠ ⊤ := fun _ =>
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top
  rw [normSq_eq_lintegral two_pos, lintegral_count, tsum_fintype,
    ENNReal.toReal_sum fun x _ => hne _]
  simp only [← ENNReal.toReal_rpow, toReal_enorm, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  norm_num

lemma eq_ae_smul_dirac (c : ℝ≥0∞) (x : Fin k) (f : Fin k → ℝ) :
    f =ᵐ[c • Measure.dirac x] fun _ => f x :=
  Measure.ae_smul_measure (by rw [ae_dirac_eq]; exact Filter.eventually_pure.mpr rfl) c

/-- `‖f‖²_{L^q(c δ_x)} = f(x)² c^{2/q}`. -/
lemma normSq_smul_dirac {q : ℝ} (hq : 0 < q) (c : ℝ≥0∞) (x : Fin k) (f : Fin k → ℝ) :
    normSq (c • Measure.dirac x) q f = f x ^ 2 * c.toReal ^ (2 / q) := by
  rw [normSq_ae_congr (eq_ae_smul_dirac c x f), normSq_fun_const _ hq]
  simp

lemma integral_smul_dirac (c : ℝ≥0∞) (x : Fin k) (f : Fin k → ℝ) :
    ∫ y, f y ∂(c • Measure.dirac x) = c.toReal * f x := by
  rw [integral_smul_measure, integral_dirac, smul_eq_mul]

lemma finModel_isFiniteMeasure_vol [NeZero k] :
    IsFiniteMeasure ((finModel k n μb e he).vol (finMetric k)) := by
  rw [finModel_vol]; infer_instance

lemma finModel_vol_ne_zero [NeZero k] : (finModel k n μb e he).vol (finMetric k) ≠ 0 := by
  rw [finModel_vol]
  intro h
  have := congrArg (fun μ : Measure (Fin k) => μ {0}) h
  simp at this

lemma normSq_dirac {q : ℝ} (hq : 0 < q) (x : Fin k) (f : Fin k → ℝ) :
    normSq (Measure.dirac x) q f = f x ^ 2 := by
  have h := normSq_smul_dirac hq 1 x f
  rw [one_smul] at h
  rw [h]; simp

/-- The differential with two edges `i → j`, `i' → j'`: `e u = (u j − u i, u j' − u i', 0)`. -/
def edgeMap (i j i' j' : Fin k) : (Fin k → ℝ) →ₗ[ℝ] Fin 3 → ℝ :=
  LinearMap.pi (R := ℝ) (φ := fun _ : Fin 3 => ℝ)
    ![(LinearMap.proj j : (Fin k → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj i,
      (LinearMap.proj j' : (Fin k → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj i', 0]

lemma edgeMap_one (i j i' j' : Fin k) : edgeMap i j i' j' (fun _ => (1 : ℝ)) = 0 := by
  funext a; fin_cases a <;> simp [edgeMap]

lemma edgeMap_sq (i j i' j' : Fin k) (u : Fin k → ℝ) :
    ∑ a, edgeMap i j i' j' u a ^ 2 = (u j - u i) ^ 2 + (u j' - u i') ^ 2 := by
  simp [edgeMap, Fin.sum_univ_three]

lemma rpow_half_four : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
  rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

lemma exp_three : (((3 : ℕ) : ℝ) - 2) / (((3 : ℕ) : ℝ) - 1) = 1 / 2 := by norm_num

lemma two_div_pSharp_three : 2 / pSharp 3 = 1 / 2 := by
  rw [two_div_pSharp le_rfl]; norm_num

/-- The entries of a vector literal of length at most four. -/
theorem vecLit {α : Type*} (a b c d : α) :
    ![a, b, c, d] 0 = a ∧ ![a, b, c, d] 1 = b ∧ ![a, b, c, d] 2 = c ∧ ![a, b, c, d] 3 = d := by
  simp only [Matrix.cons_val_three, Matrix.cons_val_two, Matrix.cons_val_one,
    Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons, and_self]

/-- The entries of a vector literal of length three. -/
theorem vecLit3 {α : Type*} (a b c : α) :
    ![a, b, c] 0 = a ∧ ![a, b, c] 1 = b ∧ ![a, b, c] 2 = c := by
  simp only [Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.tail_cons,
    Matrix.head_cons, and_self]

/-! ### `discModel`: `Σ = {0, 1} ⊔ {2}`, boundary `{0}` (rem:connected) -/

/-- Two components: the edge `0 — 1` with boundary point `0`, and the isolated point `2`. -/
def discModel : MeasuredModel (Fin 3) (Fin 3 → ℝ) 3 1 :=
  finModel 3 1 (fun _ => Measure.dirac 0) (edgeMap 0 1 0 0) (edgeMap_one _ _ _ _)

lemma disc_energy (u : Fin 3 → ℝ) :
    discModel.energy (finMetric 3) u = ENNReal.ofReal (3 * (u 1 - u 0) ^ 2) := by
  rw [discModel, finModel_energy, edgeMap_sq]; simp

lemma disc_dirichlet (u : Fin 3 → ℝ) :
    discModel.dirichlet (finMetric 3) u = 3 * (u 1 - u 0) ^ 2 := by
  rw [discModel, finModel_dirichlet, edgeMap_sq]; simp

lemma disc_bdryS : discModel.bdryS (finMetric 3) = 1 := by
  unfold MeasuredModel.bdryS
  simp only [discModel, finModel_bvol]
  simp

lemma disc_bdryAvg (u : Fin 3 → ℝ) : discModel.bdryAvg (finMetric 3) u = u 0 := by
  unfold MeasuredModel.bdryAvg MeasuredModel.capWeight
  rw [disc_bdryS]
  simp only [discModel, finModel_bvol, finModel_tr]
  simp [integral_dirac]

lemma disc_ell (u : Fin 3 → ℝ) :
    discModel.ell (finMetric 3) u = (u 0 + u 1 + u 2) / 3 - u 0 := by
  unfold MeasuredModel.ell
  rw [disc_bdryAvg]
  simp only [discModel, finModel_volMean, Fin.sum_univ_three]
  norm_num

instance disc_fin_vol : IsFiniteMeasure (discModel.vol (finMetric 3)) :=
  finModel_isFiniteMeasure_vol

instance disc_fin_bvol (j : Fin 1) : IsFiniteMeasure (discModel.bvol (finMetric 3) j) := by
  simp only [discModel, finModel_bvol]; infer_instance

theorem disc_traceBound : discModel.TraceBound (finMetric 3) := by
  refine ⟨1, fun u j => ⟨MemLp.of_discrete, ?_⟩⟩
  have h1 : normSq (discModel.bvol (finMetric 3) j) (pSharp 3) (discModel.tr u) = u 0 ^ 2 := by
    simp only [discModel, finModel_bvol, finModel_tr]
    rw [normSq_dirac (pSharp_pos le_rfl)]
  have h2 : normSq (discModel.vol (finMetric 3)) 2 (discModel.val u) = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
    simp only [discModel, finModel_vol, finModel_val]
    rw [normSq_count_two, Fin.sum_univ_three]
  rw [h1, h2, disc_dirichlet]
  nlinarith [sq_nonneg (u 1 - u 0), sq_nonneg (u 1), sq_nonneg (u 2)]

/-- **rem:connected on `discModel`**: `v = 1_{{2}}` has `‖∇v‖ = 0` and `ℓ(v) = 1/3`; hence
`cap* = 0`, eq:capineq fails, and the Poincaré inequality fails while the trace theorem holds. -/
theorem disc_rem_connected :
    discModel.energy (finMetric 3) ![0, 0, 1] = 0 ∧ discModel.ell (finMetric 3) ![0, 0, 1] = 1 / 3 ∧
    discModel.capStar (finMetric 3) = 0 ∧
    ¬ (∀ u, discModel.volMean (finMetric 3) u - discModel.bdryAvg (finMetric 3) u ≤
        Real.sqrt (discModel.dirichlet (finMetric 3) u) /
          Real.sqrt (discModel.capStar (finMetric 3)).toReal) ∧
    discModel.TraceBound (finMetric 3) ∧ ¬ discModel.MeanPoincare (finMetric 3) := by
  have hE : discModel.energy (finMetric 3) ![0, 0, 1] = 0 := by rw [disc_energy]; simp
  have hl : discModel.ell (finMetric 3) ![0, 0, 1] = 1 / 3 := by rw [disc_ell]; simp
  have hl0 : discModel.ell (finMetric 3) ![0, 0, 1] ≠ 0 := by rw [hl]; norm_num
  have hV : discModel.vol (finMetric 3) ≠ 0 := finModel_vol_ne_zero
  have hB : ∃ j, discModel.bvol (finMetric 3) j ≠ 0 :=
    ⟨0, by simp only [discModel, finModel_bvol]; exact Measure.dirac_ne_zero⟩
  obtain ⟨h1, -, h3, h4⟩ :=
    discModel.rem_connected (finMetric 3) le_rfl hV hB disc_traceBound hE hl0
  exact ⟨hE, hl, h1, h3, disc_traceBound, h4⟩

/-! ### `balModel`: `Σ = {0, 1} ⊔ {2, 3}`, boundaries `{0}`, `{2}` (rem:connected, « in general ») -/

/-- Two balanced components, each an edge with one boundary point. -/
def balModel : MeasuredModel (Fin 4) (Fin 4 → ℝ) 3 2 :=
  finModel 4 2 ![Measure.dirac 0, Measure.dirac 2] (edgeMap 0 1 2 3) (edgeMap_one _ _ _ _)

lemma bal_energy (u : Fin 4 → ℝ) :
    balModel.energy (finMetric 4) u = ENNReal.ofReal (4 * ((u 1 - u 0) ^ 2 + (u 3 - u 2) ^ 2)) := by
  rw [balModel, finModel_energy, edgeMap_sq]; simp

lemma bal_dirichlet (u : Fin 4 → ℝ) :
    balModel.dirichlet (finMetric 4) u = 4 * ((u 1 - u 0) ^ 2 + (u 3 - u 2) ^ 2) := by
  rw [balModel, finModel_dirichlet, edgeMap_sq]; simp

lemma bal_bdryS : balModel.bdryS (finMetric 4) = 2 := by
  unfold MeasuredModel.bdryS
  simp only [balModel, finModel_bvol, Fin.sum_univ_two]
  simp
  norm_num

lemma bal_bdryAvg (u : Fin 4 → ℝ) : balModel.bdryAvg (finMetric 4) u = u 0 / 2 + u 2 / 2 := by
  unfold MeasuredModel.bdryAvg MeasuredModel.capWeight
  rw [bal_bdryS]
  simp only [balModel, finModel_bvol, finModel_tr, Fin.sum_univ_two]
  simp [integral_dirac]
  ring

lemma bal_ell (u : Fin 4 → ℝ) :
    balModel.ell (finMetric 4) u = (u 1 - u 0 + (u 3 - u 2)) / 4 := by
  unfold MeasuredModel.ell
  rw [bal_bdryAvg]
  simp only [balModel, finModel_volMean, Fin.sum_univ_four]
  norm_num
  ring

/-- **The balanced disconnected model**: `v = 1_{{2,3}}` has `‖∇v‖ = 0` but `ℓ(v) = 0`; the
Poincaré inequality fails, yet `cap* = 32 > 0` and eq:capineq holds for every `u`. -/
theorem bal_witness :
    balModel.energy (finMetric 4) ![0, 0, 1, 1] = 0 ∧ balModel.ell (finMetric 4) ![0, 0, 1, 1] = 0 ∧
    ¬ balModel.MeanPoincare (finMetric 4) ∧ balModel.capStar (finMetric 4) = 32 ∧
    ∀ u, balModel.volMean (finMetric 4) u - balModel.bdryAvg (finMetric 4) u ≤
      Real.sqrt (balModel.dirichlet (finMetric 4) u) /
        Real.sqrt (balModel.capStar (finMetric 4)).toReal := by
  have hE : balModel.energy (finMetric 4) ![0, 0, 1, 1] = 0 := by rw [bal_energy]; simp
  have hl : balModel.ell (finMetric 4) ![0, 0, 1, 1] = 0 := by rw [bal_ell]; simp
  have hcap : balModel.capStar (finMetric 4) = 32 := by
    refine le_antisymm ?_ (le_iInf₂ fun v hv => ?_)
    · have hv : balModel.ell (finMetric 4) ![0, 2, 0, 2] = 1 := by
        rw [bal_ell]; simp only [vecLit]; norm_num
      refine (balModel.capStar_le (finMetric 4) hv).trans (le_of_eq ?_)
      rw [bal_energy]; simp only [vecLit]; norm_num
    · rw [bal_ell] at hv
      rw [bal_energy, show (32 : ℝ≥0∞) = ENNReal.ofReal 32 by norm_num]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [sq_nonneg (v 1 - v 0 - (v 3 - v 2))]
  refine ⟨hE, hl, fun ⟨K, hK⟩ => ?_, hcap, fun u => ?_⟩
  · have h := (hK ![0, 0, 1, 1]).2
    have hd : balModel.dirichlet (finMetric 4) ![0, 0, 1, 1] = 0 := by rw [bal_dirichlet]; simp
    have hm : balModel.volMean (finMetric 4) ![0, 0, 1, 1] = 1 / 2 := by
      simp only [balModel, finModel_volMean, Fin.sum_univ_four]; simp only [vecLit]; norm_num
    have hn : normSq (balModel.vol (finMetric 4)) 2
        (balModel.val ![0, 0, 1, 1] - fun _ => balModel.volMean (finMetric 4) ![0, 0, 1, 1]) = 1 := by
      rw [hm]
      simp only [balModel, finModel_vol, finModel_val]
      rw [normSq_count_two, Fin.sum_univ_four]
      simp only [Pi.sub_apply, vecLit]; norm_num
    rw [hd, hn, mul_zero] at h
    norm_num at h
  · have hfin : balModel.energy (finMetric 4) u ≠ ⊤ := by rw [bal_energy]; exact ENNReal.ofReal_ne_top
    have h := balModel.sqrt_capStar_mul_ell_le (finMetric 4) u hfin
    rw [hcap] at h ⊢
    change balModel.ell (finMetric 4) u ≤ _
    have h32 : 0 < Real.sqrt ((32 : ℝ≥0∞).toReal) := Real.sqrt_pos.mpr (by norm_num)
    rw [le_div_iff₀ h32]
    linarith

/-! ### `pathModel`: the path `0 — 1 — 2`, boundaries `{0}` (area 1), `{2}` (area 4) (rem:tight) -/

/-- A connected path with two boundary points of unequal areas. -/
def pathModel : MeasuredModel (Fin 3) (Fin 3 → ℝ) 3 2 :=
  finModel 3 2 ![Measure.dirac 0, (4 : ℝ≥0∞) • Measure.dirac 2] (edgeMap 0 1 1 2)
    (edgeMap_one _ _ _ _)

lemma path_energy (u : Fin 3 → ℝ) :
    pathModel.energy (finMetric 3) u = ENNReal.ofReal (3 * ((u 1 - u 0) ^ 2 + (u 2 - u 1) ^ 2)) := by
  rw [pathModel, finModel_energy, edgeMap_sq]; simp

lemma path_dirichlet (u : Fin 3 → ℝ) :
    pathModel.dirichlet (finMetric 3) u = 3 * ((u 1 - u 0) ^ 2 + (u 2 - u 1) ^ 2) := by
  rw [pathModel, finModel_dirichlet, edgeMap_sq]; simp

lemma path_bvol0 : pathModel.bvol (finMetric 3) 0 = Measure.dirac 0 := by
  simp only [pathModel, finModel_bvol]; rfl

lemma path_bvol1 : pathModel.bvol (finMetric 3) 1 = (4 : ℝ≥0∞) • Measure.dirac 2 := by
  simp only [pathModel, finModel_bvol]; rfl

lemma path_bvol_univ0 : (pathModel.bvol (finMetric 3) 0 Set.univ).toReal = 1 := by
  rw [path_bvol0]; simp

lemma path_bvol_univ1 : (pathModel.bvol (finMetric 3) 1 Set.univ).toReal = 4 := by
  rw [path_bvol1]; simp

instance path_fin_vol : IsFiniteMeasure (pathModel.vol (finMetric 3)) :=
  finModel_isFiniteMeasure_vol

instance path_fin_bvol (j : Fin 2) : IsFiniteMeasure (pathModel.bvol (finMetric 3) j) := by
  fin_cases j
  · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, path_bvol0]; infer_instance
  · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, path_bvol1]; exact ⟨by simp⟩

lemma path_bdryS : pathModel.bdryS (finMetric 3) = 3 := by
  unfold MeasuredModel.bdryS
  rw [Fin.sum_univ_two, path_bvol_univ0, path_bvol_univ1, exp_three, rpow_half_four,
    Real.one_rpow]
  norm_num

lemma path_capWeight0 : pathModel.capWeight (finMetric 3) 0 = 1 / 3 := by
  unfold MeasuredModel.capWeight
  rw [path_bvol_univ0, path_bdryS, Real.one_rpow]

lemma path_capWeight1 : pathModel.capWeight (finMetric 3) 1 = 2 / 3 := by
  unfold MeasuredModel.capWeight
  rw [path_bvol_univ1, path_bdryS, two_div_pSharp_three, rpow_half_four]

lemma path_bdryAvg (u : Fin 3 → ℝ) :
    pathModel.bdryAvg (finMetric 3) u = u 0 / 3 + 2 * u 2 / 3 := by
  unfold MeasuredModel.bdryAvg
  rw [Fin.sum_univ_two, path_capWeight0, path_capWeight1, path_bvol_univ0, path_bvol_univ1,
    path_bvol0, path_bvol1, integral_smul_dirac, integral_dirac]
  simp only [pathModel, finModel_tr]
  norm_num
  ring

lemma path_volMean (u : Fin 3 → ℝ) :
    pathModel.volMean (finMetric 3) u = (u 0 + u 1 + u 2) / 3 := by
  simp only [pathModel, finModel_volMean, Fin.sum_univ_three]; norm_num

lemma path_ell (u : Fin 3 → ℝ) : pathModel.ell (finMetric 3) u = (u 1 - u 2) / 3 := by
  unfold MeasuredModel.ell
  rw [path_bdryAvg, path_volMean]
  ring

theorem path_capStar : pathModel.capStar (finMetric 3) = 27 := by
  refine le_antisymm ?_ (le_iInf₂ fun v hv => ?_)
  · have hv : pathModel.ell (finMetric 3) ![0, 0, -3] = 1 := by
      rw [path_ell]; simp only [vecLit3]; norm_num
    refine (pathModel.capStar_le (finMetric 3) hv).trans (le_of_eq ?_)
    rw [path_energy]; simp only [vecLit3]; norm_num
  · rw [path_ell] at hv
    rw [path_energy, show (27 : ℝ≥0∞) = ENNReal.ofReal 27 by norm_num]
    refine ENNReal.ofReal_le_ofReal ?_
    have h : v 2 - v 1 = -3 := by linarith
    rw [h]
    nlinarith [sq_nonneg (v 1 - v 0)]

/-- The classical equilibrium potential of `pathModel`: `ψ = (1, −2, 1)`, the only competitor. -/
def pathPsi : Fin 3 → ℝ := ![1, -2, 1]

theorem path_psi : pathModel.IsCapDCompetitor (finMetric 3) pathPsi ∧
    pathModel.dirichlet (finMetric 3) pathPsi = 54 := by
  refine ⟨⟨fun j => ?_, ?_⟩, ?_⟩
  · fin_cases j
    · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, path_bvol0, Filter.EventuallyEq,
        ae_dirac_eq]
      exact Filter.eventually_pure.mpr (by simp [pathModel, finModel_tr, pathPsi])
    · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, path_bvol1]
      refine (eq_ae_smul_dirac 4 2 _).trans (ae_of_all _ fun _ => ?_)
      simp [pathModel, finModel_tr, pathPsi]
  · simp only [pathModel, finModel_vol, finModel_val]
    rw [integral_fintype .of_finite]
    simp [pathPsi, Fin.sum_univ_three]
    norm_num
  · rw [path_dirichlet]; simp only [pathPsi, vecLit3]; norm_num

theorem path_meanPoincare : pathModel.MeanPoincare (finMetric 3) := by
  refine ⟨1, fun v => ⟨MemLp.of_discrete, ?_⟩⟩
  rw [path_volMean, path_dirichlet]
  simp only [pathModel, finModel_vol, finModel_val]
  rw [normSq_count_two, Fin.sum_univ_three]
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (v 1 - v 0), sq_nonneg (v 2 - v 1), sq_nonneg (v 2 - v 0)]

theorem path_traceBound : pathModel.TraceBound (finMetric 3) := by
  have hq := pSharp_pos (N := 3) le_rfl
  refine ⟨2, fun u j => ⟨MemLp.of_discrete, ?_⟩⟩
  have h2 : normSq (pathModel.vol (finMetric 3)) 2 (pathModel.val u) =
      u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
    simp only [pathModel, finModel_vol, finModel_val]
    rw [normSq_count_two, Fin.sum_univ_three]
  have hd := path_dirichlet u
  have htr : pathModel.tr u = u := rfl
  rw [h2, hd, htr]
  fin_cases j
  · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, path_bvol0, normSq_dirac hq]
    nlinarith [sq_nonneg (u 1 - u 0), sq_nonneg (u 2 - u 1), sq_nonneg (u 1), sq_nonneg (u 2)]
  · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, path_bvol1, normSq_smul_dirac hq,
      two_div_pSharp_three]
    have : ((4 : ℝ≥0∞).toReal) ^ ((1 : ℝ) / 2) = 2 := by
      rw [show ((4 : ℝ≥0∞).toReal) = 4 by norm_num, rpow_half_four]
    rw [this]
    nlinarith [sq_nonneg (u 1 - u 0), sq_nonneg (u 2 - u 1), sq_nonneg (u 1), sq_nonneg (u 0)]

/-- **rem:tight (3) is false as printed on `pathModel`**: a connected model with the Poincaré
inequality and the trace theorem, `cap* = 27 < 54 = cap_D`. The ratio `X/Y` realised by
`u_s = 1 − sψ` is not `c_3 √S/(a_3 √cap*)`, neither at `s = 1/(1 + θ)` nor at
`s = 1/(1 + θ_D)`, so the Cauchy–Schwarz step is strict at both. -/
theorem path_rem_tight_counterexample :
    pathModel.MeanPoincare (finMetric 3) ∧ pathModel.TraceBound (finMetric 3) ∧
    pathModel.capStar (finMetric 3) = 27 ∧ pathModel.dirichlet (finMetric 3) pathPsi = 54 ∧
    Real.sqrt (pathModel.dirichlet (finMetric 3)
          (pathModel.upperTest pathPsi (1 / (1 + pathModel.theta (finMetric 3))))) /
        pathModel.bdryY (finMetric 3)
          (pathModel.upperTest pathPsi (1 / (1 + pathModel.theta (finMetric 3)))) ≠
      cN 3 * Real.sqrt (pathModel.bdryS (finMetric 3)) /
        (aN 3 * Real.sqrt (pathModel.capStar (finMetric 3)).toReal) ∧
    Real.sqrt (pathModel.dirichlet (finMetric 3)
          (pathModel.upperTest pathPsi (1 / (1 + pathModel.thetaDOf (finMetric 3) pathPsi)))) /
        pathModel.bdryY (finMetric 3)
          (pathModel.upperTest pathPsi (1 / (1 + pathModel.thetaDOf (finMetric 3) pathPsi))) ≠
      cN 3 * Real.sqrt (pathModel.bdryS (finMetric 3)) /
        (aN 3 * Real.sqrt (pathModel.capStar (finMetric 3)).toReal) := by
  obtain ⟨hψ, hD⟩ := path_psi
  have hS : 0 < pathModel.bdryS (finMetric 3) := by rw [path_bdryS]; norm_num
  have hcap : 0 < (pathModel.capStar (finMetric 3)).toReal := by rw [path_capStar]; norm_num
  have hD0 : 0 < pathModel.dirichlet (finMetric 3) pathPsi := by rw [hD]; norm_num
  have hk : (pathModel.capStar (finMetric 3)).toReal = 27 := by rw [path_capStar]; norm_num
  refine ⟨path_meanPoincare, path_traceBound, path_capStar, hD, fun h => ?_, fun h => ?_⟩
  · have := (pathModel.ratio_upperTest_theta_iff (finMetric 3) le_rfl hS hcap hψ hD0).mp h
    rw [hD, hk] at this
    norm_num at this
  · rw [pathModel.ratio_upperTest_thetaD (finMetric 3) le_rfl hS hψ hD0, hD, hk] at h
    have ha := aN_pos (N := 3) le_rfl
    have hc := cN_pos (N := 3) (by norm_num)
    have hsS := Real.sqrt_pos.mpr hS
    rw [div_eq_div_iff (by positivity) (by positivity)] at h
    have h' : Real.sqrt 27 = Real.sqrt 54 := by
      have hne : cN 3 * Real.sqrt (pathModel.bdryS (finMetric 3)) * aN 3 ≠ 0 := by positivity
      have : cN 3 * Real.sqrt (pathModel.bdryS (finMetric 3)) * aN 3 * Real.sqrt 27 =
          cN 3 * Real.sqrt (pathModel.bdryS (finMetric 3)) * aN 3 * Real.sqrt 54 := by
        linear_combination h
      exact mul_left_cancel₀ hne this
    have := congrArg (· ^ 2) h'
    rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)] at this
    norm_num at this

lemma path_bdryY (u : Fin 3 → ℝ) :
    pathModel.bdryY (finMetric 3) u = Real.sqrt (u 0 ^ 2 + 2 * u 2 ^ 2) := by
  have hq := pSharp_pos (N := 3) le_rfl
  unfold MeasuredModel.bdryY
  rw [Fin.sum_univ_two, path_bvol0, path_bvol1, normSq_dirac hq, normSq_smul_dirac hq,
    two_div_pSharp_three, show ((4 : ℝ≥0∞).toReal) = 4 by norm_num, rpow_half_four]
  have htr : pathModel.tr u = u := rfl
  rw [htr, mul_comm (u 2 ^ 2)]

/-- **No capacitary profile on `pathModel`**: the three equalities of rem:tight (lem:holder,
lem:capacitary, the Cauchy–Schwarz step) hold together at `u` only for `u = 0`. -/
theorem path_no_tight_profile (u : Fin 3 → ℝ)
    (h1 : pathModel.bdryAvg (finMetric 3) u =
      pathModel.bdryY (finMetric 3) u / Real.sqrt (pathModel.bdryS (finMetric 3)))
    (h2 : pathModel.volMean (finMetric 3) u = pathModel.bdryAvg (finMetric 3) u +
      Real.sqrt (pathModel.dirichlet (finMetric 3) u) /
        Real.sqrt (pathModel.capStar (finMetric 3)).toReal)
    (h3 : (pathModel.linC1 (finMetric 3) * Real.sqrt (pathModel.dirichlet (finMetric 3) u) +
        pathModel.linC2 (finMetric 3) * pathModel.bdryY (finMetric 3) u) ^ 2 =
      (pathModel.linC1 (finMetric 3) ^ 2 / aN 3 + pathModel.linC2 (finMetric 3) ^ 2 / cN 3) *
        (aN 3 * Real.sqrt (pathModel.dirichlet (finMetric 3) u) ^ 2 +
          cN 3 * pathModel.bdryY (finMetric 3) u ^ 2)) :
    u = 0 := by
  have ha := aN_pos (N := 3) le_rfl
  have hc := cN_pos (N := 3) (by norm_num)
  have hk : (pathModel.capStar (finMetric 3)).toReal = 27 := by rw [path_capStar]; norm_num
  rw [path_bdryAvg, path_bdryY, path_bdryS] at h1
  rw [path_volMean, path_bdryAvg, path_dirichlet, hk] at h2
  -- lem:holder's equality forces `u 0 = u 2`
  have e02 : u 0 = u 2 := by
    have hsq := congrArg (· ^ 2) h1
    rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)] at hsq
    have : (u 0 - u 2) ^ 2 = 0 := by nlinarith
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  -- lem:capacitary's equality forces `u 1 = u 0`
  have e10 : u 1 = u 0 := by
    have h2' : (u 1 - u 2) / 3 =
        Real.sqrt (3 * ((u 1 - u 0) ^ 2 + (u 2 - u 1) ^ 2)) / Real.sqrt 27 := by linarith
    have hsq := congrArg (· ^ 2) h2'
    rw [div_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by norm_num)] at hsq
    have : (u 1 - u 0) ^ 2 = 0 := by nlinarith
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  -- the Cauchy–Schwarz step's equality then forces `Y = 0`
  have hX : Real.sqrt (pathModel.dirichlet (finMetric 3) u) = 0 := by
    rw [path_dirichlet, e10, ← e02]; simp
  rw [(cauchySchwarz_step ha hc _ _ _ _).2, hX, mul_zero, zero_mul] at h3
  have hC1 : 0 < pathModel.linC1 (finMetric 3) := by
    unfold MeasuredModel.linC1
    rw [hk]
    have hV : 0 < (pathModel.vol (finMetric 3) Set.univ).toReal := by
      simp only [pathModel, finModel_vol]; simp
    exact div_pos (Real.rpow_pos_of_pos hV _) (Real.sqrt_pos.mpr (by norm_num))
  have hY : pathModel.bdryY (finMetric 3) u = 0 := by
    rcases mul_eq_zero.mp h3.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hc.ne'
      · exact h
    · exact absurd h hC1.ne'
  rw [path_bdryY, Real.sqrt_eq_zero (by positivity)] at hY
  have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 2)]
  funext i
  fin_cases i
  · exact h0
  · simp only [Pi.zero_apply]; show u 1 = 0; rw [e10, h0]
  · simp only [Pi.zero_apply]; show u 2 = 0; rw [← e02, h0]

end FinModels

end CapRemarks

/-! ## Non-vacuity of `rem_dichotomy`: its hypotheses hold on the two-point toy model -/

/-- Every hypothesis of `rem_dichotomy` holds on the strict two-point toy model, so its four
conclusions hold there. -/
theorem toy_rem_dichotomy :
    let F := toyModel.Fq toyMetric toyModel.one
    let θ := toyModel.theta toyMetric
    let A := θ * F / (1 + θ)
    let B := aN 3 / toyModel.Csp toyMetric ^ 2
    let τ := toyModel.Csp toyMetric * Real.sqrt (θ * F / aN 3)
    A / (1 + Real.sqrt (A / B)) ^ 2 ≤ toyModel.infF toyMetric (fun _ => cN 3) ∧
    F * θ / (θ + (1 + τ) ^ 2) ≤ toyModel.infF toyMetric (fun _ => cN 3) ∧
    A / (1 + Real.sqrt (A / B)) ^ 2 ≤ F * θ / (θ + (1 + τ) ^ 2) ∧
    (0 < toyModel.Csp toyMetric → A / (1 + Real.sqrt (A / B)) ^ 2 < F * θ / (θ + (1 + τ) ^ 2)) := by
  obtain ⟨h1, h2, hV, hB, hP, hT, hI, -⟩ := toy_thm_main_hyps
  haveI := h1
  haveI := h2
  exact toyModel.rem_dichotomy toyMetric le_rfl hV hB hP hT hI toy_sobolevIneq

end Yamabe
