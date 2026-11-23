import Yamabe.Perforated.Capacity
import Yamabe.Perforated.Star3

/-!
# Perforated thm:main over the measured model: `λ_∂ ≥ F_g(1)/Λ_max`, `Λ_max` the larger eigenvalue of the calibrated `2 × 2` matrix, and its expansion

Label (the companion BrunswicPerforated, `papers/perforated`; lines of
`papers/perforated/legacy/labeled/perforated.tex`):

* `thm:main` — `perforated.tex:179` (statement l.179–206; proof l.458–460, l.502–561). NOT
  marked: partial (see SCOPE). `MeasuredModel.thm_main` is the printed form,
  `MeasuredModel.thm_main_signed` has eq:star for every `u`, and `MeasuredModel.thm_main_three`
  is the case `N = 3` at the constant of the corrected thm:star3.

> Let $(\Sigma,g)$ be a compact connected Riemannian $N$-manifold with non-empty
> boundary, $N\ge3$, and suppose that the quadratic Sobolev inequality
> $\|u\|^2_{L^{\pstar}(\Sigma)}\;\le\;\Atil\,\|\nabla u\|^2_{L^2(\Sigma)}
>         +V^{2/\pstar}\Bigl(\frac1V\int_\Sigma u\Bigr)^{\!2},
>   \qquad u\in W^{1,2}(\Sigma),\ u\ge0.$
> holds with a finite constant $\Atil=\Atil(\Sigma,g)$. Then, with
> $\theta=\theta(\Sigma,g)$ and $\Fq_g(1)$ as in \eqref{eq:F1},
> $\lambda_\partial(\Sigma,g)\;\ge\;\frac{\Fq_g(1)}{\Lambda_{\max}},
>   \qquad
>   \Lambda_{\max}=\tfrac12\Bigl[(\alpha+\beta+\delta)
>       +\sqrt{(\alpha+\delta-\beta)^2+4\alpha\beta}\Bigr],$
> where $\alpha=1/\theta$, $\beta=1$ and $\delta=\Atil\,\Fq_g(1)/\aN$. In
> particular
> $\lambda_\partial\;\ge\;\frac{\theta}{1+\theta}\,\Fq_g(1)
>      \left(1-\frac{\Atil\,\theta\,\Fq_g(1)}{\aN(1+\theta)^2}
>             +O\bigl(\Fq_g(1)^2\bigr)\right).$ (l.181–205)

> Replacing $u$ by $|u|$ changes
> nothing: $|\nabla|u||=|\nabla u|$ a.e.\ and the trace of $|u|$ is $|{\rm tr}\,u|$,
> so $\Fq_g(|u|)=\Fq_g(u)$. We may therefore assume $u\ge0$, hence $\bar u\ge0$. (l.458–460)

## The model

`MeasuredModel` (DEC-186), notation of `Yamabe.Perforated.Capacity`: `λ_∂ = infF (fun _ => c_N)`
over `Adm`; `F_g(1) = Fq one`; `θ = theta`; eq:star is `StarIneq Ã` (`u ≥ 0`) or
`StarIneqSigned Ã` (every `u`) of `Yamabe.Perforated.Star3`.

## What is proved (no `sorry` in this file)

`lamMax` (the printed `Λ_max`) is the largest eigenvalue of `mainMatrix`
(`lamMax_largest_eigenvalue`, `quad_le_lamMax`, `quad_lamMax_attained`, `lamMax_unnormalized`).
eq:main: `eq_main_lattice`, `eq_main_signed`, and their `_of_capStar_pos` forms. eq:main-asymp:
`mainRem`, `eq_main_asymp_identity`, `mainRem_isBigO`, `mainRem_le`, `mainRem_le_uniform`,
`hasDerivAt_inv_lamMax`. Assemblies: `thm_main`, `thm_main_signed`, `thm_main_three`. Witness:
`toy_thm_main_hyps`, `toy_capStar_route_hyps`, `toy_thm_main`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `N ≥ 3`; `Σ` compact, `Σ ≠ ∅` | ✓ carried: `hN`, finite `vol g`, `bvol g j`; `vol g ≠ 0` |
| non-empty boundary (l.181) | ⚠ read: `∃ j, bvol g j ≠ 0` |
| connected; the trace theorem (via lem:capstar) | ⚠ carried: `MeanPoincare`, `TraceBound`; or (`_of_capStar_pos`) `0 < cap*`, finite energies, `L^{p♯}` traces |
| `cap* < ∞` (l.399–401) | ⚠ carried: `InteriorBump`, for eq:main-asymp only |
| `u ↦ |u|` (l.458–460) | ⚠ carried: `AbsLatticeApprox` (`thm_main`); not used by `thm_main_signed` |
| eq:star, `u ≥ 0` (l.183–189) | ✓ `StarIneq Ã` (`thm_main`); ⚠ `StarIneqSigned Ã` in `thm_main_signed` |
| `Ã ≥ 0` (follows from eq:star, Hölder) | not needed: every real `Ã` |
| `λ_∂ = inf_{u ≠ 0} F_g` (l.132) | ✓ `infF` over `Adm` (DEC-186) |
| `O(F_g(1)²)` (l.204) | ⚠ read: the fixed function `mainRem N θ Ã` of `F` (SCOPE) |

## SCOPE (disclosed)

* **Why partial.** `thm_main` is the printed statement over the model under four carried
  facts of `(Σ, W^{1,2})` that the model lacks: `MeanPoincare` and `TraceBound` (through
  `eq_linear`), `InteriorBump` (`θ > 0`, eq:main-asymp only) and `AbsLatticeApprox` (l.458–460).
  `thm_main_signed` drops the last but assumes eq:star for every `u`, more than l.187 does.
* **What lem:capstar supplies.** eq:main takes only `0 < cap*` (`eq_linear_of_capStar_pos`); the
  `_of_capStar_pos` forms carry it in place of `MeanPoincare`, `TraceBound`, over finite energies
  and `L^{p♯}` traces (an incomparable set). eq:main-asymp also takes `cap* < ∞` (`θ > 0`).
* **Reading (a), `u ↦ |u|` (l.458–460).** It serves eq:star alone: eq:linear holds with `|ū|` for
  every `u` (`eq_linear`), so l.519 needs no sign. It needs only `AbsLatticeApprox`: `w_k ≥ 0`
  with energy and trace norms at most those of `u` and `‖w_k‖_{p*} → ‖u‖_{p*}`. The exact
  `AbsLattice` (`|u| ∈ W^{1,2}`) gives it (`AbsLattice.approx`); under the `C¹` reading of
  OQ-93 (b), where `|u|` is not `C¹`, `w_ε = √(u² + ε²) − ε` does (argued). So `thm_main` with
  prop:starN (`u ≥ 0`) gives thm:main for every `N ≥ 3` under either reading. `thm_main_three`
  is thm:main at the one constant `star3AtilCorr` (thm:star3 composed with thm:main): a special
  case.
* **Reading (b), `O(F_g(1)²)` (l.204).** For one `(Σ, g)` an existential remainder is vacuous, so
  the remainder is the fixed function `mainRem N θ Ã` and eq:main-asymp is eq:main rewritten
  (`eq_main_asymp_identity`). It is `O(F²)` at fixed `θ`, `Ã` (`mainRem_isBigO`), uniformly in
  `θ`: `|R| ≤ (5/7)(ÃF/a_N)²` for `|ÃF/a_N| ≤ 1/4` (`mainRem_le_uniform`; `mainRem_le` sharper).
* **l.527–559.** Proved: the form bound and its attainment on `X, Y ≥ 0`, for every real `Ã`
  (only `√(α'β') ≥ 0` matters; l.543 holds as printed, eq:star forcing `Ã ≥ 0`), and the
  derivative of l.554–559 (`hasDerivAt_inv_lamMax`). Not formalized: « inf = 1/Λ_max » as an
  equality, and the one-dimensional form of l.556–558.
* **Junk values.** If `cap* = ∞`, Lean's `1/θ = 0` (the limit `θ → ∞`) and eq:main still holds.
  `normSq`, `dirichlet` are `0` when infinite, and the carried hypotheses use the same
  quantities, so `le_Fq_of_star` holds on all of `Adm`.
* **Witness.** All hypotheses hold together on the two-point toy model (`toy_thm_main_hyps`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal NNReal Matrix

noncomputable section

namespace Yamabe

/-! ## 1. The `2 × 2` eigenvalue of eq:main -/

section Eigen

/-- `Λ_max(α, β, δ) = ½[(α + β + δ) + √((α + δ − β)² + 4αβ)]` (eq:main, l.195–196). -/
def lamMax (α β δ : ℝ) : ℝ := ((α + β + δ) + Real.sqrt ((α + δ - β) ^ 2 + 4 * α * β)) / 2

/-- The calibrated matrix `[[α + δ, √(αβ)], [√(αβ), β]]` (l.536–538, normalised as at l.546–550). -/
def mainMatrix (α β δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![α + δ, Real.sqrt (α * β); Real.sqrt (α * β), β]

variable {α β δ : ℝ}

lemma sq_sqrt_disc (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    Real.sqrt ((α + δ - β) ^ 2 + 4 * α * β) ^ 2 = (α + δ - β) ^ 2 + 4 * α * β :=
  Real.sq_sqrt (by have := mul_nonneg hα hβ; nlinarith [sq_nonneg (α + δ - β)])

lemma abs_le_sqrt_disc (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    |α + δ - β| ≤ Real.sqrt ((α + δ - β) ^ 2 + 4 * α * β) :=
  Real.abs_le_sqrt (by have := mul_nonneg hα hβ; nlinarith)

lemma le_lamMax_left (hα : 0 ≤ α) (hβ : 0 ≤ β) : α + δ ≤ lamMax α β δ := by
  have h := (le_abs_self _).trans (abs_le_sqrt_disc (δ := δ) hα hβ)
  unfold lamMax; linarith

lemma le_lamMax_right (hα : 0 ≤ α) (hβ : 0 ≤ β) : β ≤ lamMax α β δ := by
  have h' : -(α + δ - β) ≤ Real.sqrt ((α + δ - β) ^ 2 + 4 * α * β) := by
    have := neg_le_abs (α + δ - β)
    exact this.trans (abs_le_sqrt_disc hα hβ)
  unfold lamMax; linarith

lemma lamMax_sub_mul_sub (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (lamMax α β δ - (α + δ)) * (lamMax α β δ - β) = α * β := by
  have hs := sq_sqrt_disc (δ := δ) hα hβ
  unfold lamMax
  linear_combination (1 / 4 : ℝ) * hs

/-- `Λ_max` is a root of the characteristic polynomial `Λ² − (α + β + δ) Λ + δ β`. -/
lemma lamMax_charpoly (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    lamMax α β δ ^ 2 - (α + β + δ) * lamMax α β δ + δ * β = 0 := by
  have h := lamMax_sub_mul_sub (δ := δ) hα hβ
  linear_combination h

/-- The quadratic form of the calibrated matrix is at most `Λ_max (x² + y²)`. -/
theorem quad_le_lamMax (hα : 0 ≤ α) (hβ : 0 ≤ β) (x y : ℝ) :
    (α + δ) * x ^ 2 + 2 * Real.sqrt (α * β) * x * y + β * y ^ 2 ≤ lamMax α β δ * (x ^ 2 + y ^ 2) := by
  have hP := le_lamMax_left (δ := δ) hα hβ
  have hR := le_lamMax_right (δ := δ) hα hβ
  have hPR := lamMax_sub_mul_sub (δ := δ) hα hβ
  set Λ := lamMax α β δ
  have hq : Real.sqrt (Λ - (α + δ)) * Real.sqrt (Λ - β) = Real.sqrt (α * β) := by
    rw [← Real.sqrt_mul (by linarith), hPR]
  have h1 := Real.sq_sqrt (show 0 ≤ Λ - (α + δ) by linarith)
  have h2 := Real.sq_sqrt (show 0 ≤ Λ - β by linarith)
  have key := sq_nonneg (Real.sqrt (Λ - (α + δ)) * x - Real.sqrt (Λ - β) * y)
  have e : (Real.sqrt (Λ - (α + δ)) * x - Real.sqrt (Λ - β) * y) ^ 2 =
      Real.sqrt (Λ - (α + δ)) ^ 2 * x ^ 2 - 2 * (Real.sqrt (Λ - (α + δ)) * Real.sqrt (Λ - β)) * x * y
        + Real.sqrt (Λ - β) ^ 2 * y ^ 2 := by ring
  rw [e, h1, h2, hq] at key
  nlinarith [key]

/-- Perron–Frobenius (l.543–546): the bound is attained on the closed quadrant `x, y ≥ 0`. -/
theorem quad_lamMax_attained (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ (x ≠ 0 ∨ y ≠ 0) ∧
      (α + δ) * x ^ 2 + 2 * Real.sqrt (α * β) * x * y + β * y ^ 2 =
        lamMax α β δ * (x ^ 2 + y ^ 2) := by
  have hP := le_lamMax_left (δ := δ) hα hβ
  have hPR := lamMax_sub_mul_sub (δ := δ) hα hβ
  have hq2 : Real.sqrt (α * β) ^ 2 = α * β := Real.sq_sqrt (mul_nonneg hα hβ)
  set Λ := lamMax α β δ
  by_cases h : Real.sqrt (α * β) = 0 ∧ Λ - (α + δ) = 0
  · refine ⟨1, 0, zero_le_one, le_rfl, Or.inl one_ne_zero, ?_⟩
    rw [h.1]
    linear_combination (-1 : ℝ) * h.2
  · refine ⟨Real.sqrt (α * β), Λ - (α + δ), Real.sqrt_nonneg _, by linarith,
      (not_and_or.mp h), ?_⟩
    linear_combination (Λ - (α + δ)) * hq2 - (Λ - (α + δ)) * hPR

lemma det_mainMatrix_sub (hα : 0 ≤ α) (hβ : 0 ≤ β) (μ : ℝ) :
    (mainMatrix α β δ - μ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det =
      (α + δ - μ) * (β - μ) - α * β := by
  rw [Matrix.det_fin_two]
  simp only [mainMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, mul_one, mul_zero, sub_zero,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [Real.mul_self_sqrt (mul_nonneg hα hβ)]

/-- `Λ_max` is the largest eigenvalue of the calibrated matrix: a root of
`det(M − Λ) = 0`, and every root is at most `Λ_max`. -/
theorem lamMax_largest_eigenvalue (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (mainMatrix α β δ - lamMax α β δ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 ∧
      ∀ μ : ℝ, (mainMatrix α β δ - μ • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 →
        μ ≤ lamMax α β δ := by
  have hPR := lamMax_sub_mul_sub (δ := δ) hα hβ
  have hc := lamMax_charpoly (δ := δ) hα hβ
  have hs0 := Real.sqrt_nonneg ((α + δ - β) ^ 2 + 4 * α * β)
  refine ⟨?_, fun μ hμ => ?_⟩
  · rw [det_mainMatrix_sub hα hβ]
    linear_combination hPR
  · rw [det_mainMatrix_sub hα hβ] at hμ
    set Λ := lamMax α β δ with hΛ
    -- the other root is `α + β + δ − Λ ≤ Λ`
    have hfac : (μ - Λ) * (μ - (α + β + δ - Λ)) = 0 := by linear_combination hμ - hc
    have hle : α + β + δ - Λ ≤ Λ := by rw [hΛ]; unfold lamMax; linarith
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · linarith

/-- `Ã = 0`: `Λ_max = α + β` (l.552–554). -/
lemma lamMax_zero (hα : 0 ≤ α) (hβ : 0 ≤ β) : lamMax α β 0 = α + β := by
  unfold lamMax
  have e : (α + 0 - β) ^ 2 + 4 * α * β = (α + β) ^ 2 := by ring
  rw [e, Real.sqrt_sq (by linarith)]
  ring

/-- `Λ_max` is 1-homogeneous (the normalisation of l.546–550). -/
lemma lamMax_smul {t : ℝ} (ht : 0 ≤ t) :
    lamMax (t * α) (t * β) (t * δ) = t * lamMax α β δ := by
  unfold lamMax
  have e : (t * α + t * δ - t * β) ^ 2 + 4 * (t * α) * (t * β) =
      t ^ 2 * ((α + δ - β) ^ 2 + 4 * α * β) := by ring
  rw [e, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
  ring

end Eigen

/-! ## 2. The expansion eq:main-asymp -/

section Asymp

/-- The remainder of eq:main-asymp, a function of `(θ, Ã, F)` only. -/
def mainRem (N : ℕ) (θ A F : ℝ) : ℝ :=
  (1 + θ) / θ * (1 / lamMax (1 / θ) 1 (A * F / aN N)) - 1 + A * θ * F / (aN N * (1 + θ) ^ 2)

variable {N : ℕ}

lemma eq_main_asymp_identity {θ : ℝ} (hθ : 0 < θ) (A F : ℝ) :
    F / lamMax (1 / θ) 1 (A * F / aN N) =
      θ / (1 + θ) * F * (1 - A * θ * F / (aN N * (1 + θ) ^ 2) + mainRem N θ A F) := by
  have e : 1 - A * θ * F / (aN N * (1 + θ) ^ 2) + mainRem N θ A F =
      (1 + θ) / θ * (1 / lamMax (1 / θ) 1 (A * F / aN N)) := by
    unfold mainRem; ring
  rw [e]
  have hθ' : θ ≠ 0 := hθ.ne'
  have h1θ : 1 + θ ≠ 0 := by linarith
  field_simp

/-- The expansion of `1/Λ_max(α, 1, δ)` at `δ = 0`, with an explicit remainder: for
`|δ| ≤ (1 + α)/4`, `|1/Λ_max − (f − α f³ δ)| ≤ (20/7) α f³ δ²`, `f = 1/(1 + α)`. -/
theorem inv_lamMax_sub_le {α δ : ℝ} (hα : 0 < α) (hδ : |δ| ≤ (1 + α) / 4) :
    |1 / lamMax α 1 δ - (1 / (1 + α) - α * (1 / (1 + α)) ^ 3 * δ)| ≤
      20 / 7 * α * (1 / (1 + α)) ^ 3 * δ ^ 2 := by
  have hα0 := hα.le
  have h1α : 0 < 1 + α := by linarith
  have hΛ1 : 1 ≤ lamMax α 1 δ := le_lamMax_right hα0 zero_le_one
  have hc : lamMax α 1 δ ^ 2 - (α + 1 + δ) * lamMax α 1 δ + δ * 1 = 0 :=
    lamMax_charpoly hα0 zero_le_one
  -- the lower bound `Λ ≥ (1 + α) + α f δ`
  have hs : (1 + α) + δ * ((α - 1) / (α + 1)) ≤ Real.sqrt ((α + δ - 1) ^ 2 + 4 * α * 1) := by
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    have e : ((1 + α) + δ * ((α - 1) / (α + 1))) ^ 2 =
        (α + δ - 1) ^ 2 + 4 * α * 1 - δ ^ 2 * (4 * α / (α + 1) ^ 2) := by
      have : α + 1 ≠ 0 := by linarith
      field_simp; ring
    rw [e]
    have : 0 ≤ δ ^ 2 * (4 * α / (α + 1) ^ 2) := by positivity
    linarith
  have hΛlow : (1 + α) + α * (1 / (1 + α)) * δ ≤ lamMax α 1 δ := by
    have e3 : (1 + α) + α * (1 / (1 + α)) * δ =
        ((α + 1 + δ) + ((1 + α) + δ * ((α - 1) / (α + 1)))) / 2 := by
      have : α + 1 ≠ 0 := by linarith
      field_simp; ring
    rw [e3]; unfold lamMax; linarith
  set f := 1 / (1 + α) with hf
  set Λ := lamMax α 1 δ with hΛ
  have hf0 : 0 < f := by positivity
  have hff : f * (1 + α) = 1 := by rw [hf]; field_simp
  have hαf' : α * f = 1 - f := by linear_combination hff
  have hαf : α * f ≤ 1 := by linarith
  have hf1 : f ≤ 1 := by nlinarith
  have hΛpos : 0 < Λ := by linarith
  have hδf : |α * f * δ| ≤ |δ| := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ α * f)]
    exact mul_le_of_le_one_left (abs_nonneg _) hαf
  have hΛ3 : 3 * (1 + α) / 4 ≤ Λ := by
    have := neg_abs_le (α * f * δ)
    linarith
  have hαf3 : |α * f ^ 3 * δ| ≤ f / 4 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ α * f ^ 3)]
    calc α * f ^ 3 * |δ| ≤ α * f ^ 3 * ((1 + α) / 4) :=
          mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = (α * f) * f * (f * (1 + α)) / 4 := by ring
      _ = (α * f) * f / 4 := by rw [hff]; ring
      _ ≤ 1 * f / 4 := by gcongr
      _ = f / 4 := by ring
  set g := f - α * f ^ 3 * δ with hg
  have hg_abs : |g| ≤ 5 / 4 * f := by
    have := abs_sub f (α * f ^ 3 * δ)
    rw [abs_of_pos hf0] at this
    linarith
  have hδg : |δ * g| ≤ 5 / 16 := by
    rw [abs_mul]
    calc |δ| * |g| ≤ ((1 + α) / 4) * (5 / 4 * f) :=
          mul_le_mul hδ hg_abs (abs_nonneg _) (by positivity)
      _ = 5 / 16 * (f * (1 + α)) := by ring
      _ = 5 / 16 := by rw [hff]; ring
  have hden : 7 / 16 ≤ Λ - δ * g := by
    have := le_abs_self (δ * g)
    linarith
  have hDpos : 0 < Λ - δ * g := by linarith
  -- `P(g) = δ g² − (α + 1 + δ) g + 1` in closed form
  have hPg : δ * g ^ 2 - (α + 1 + δ) * g + 1 = α * f ^ 3 * δ ^ 2 * (1 - 2 * f + α * f ^ 3 * δ) := by
    rw [hg, hf]
    have : 1 + α ≠ 0 := by linarith
    field_simp; ring
  -- `(1/Λ − g)(Λ − δ g) = P(g)`
  have hδΛ : δ / Λ = (α + 1 + δ) - Λ := by
    rw [div_eq_iff hΛpos.ne']
    linear_combination hc
  have hid : (1 / Λ - g) * (Λ - δ * g) = δ * g ^ 2 - (α + 1 + δ) * g + 1 := by
    have e : (1 / Λ - g) * (Λ - δ * g) = 1 / Λ * Λ - δ / Λ * g - g * Λ + δ * g ^ 2 := by ring
    rw [e, one_div_mul_cancel hΛpos.ne', hδΛ]
    ring
  have hPb : |α * f ^ 3 * δ ^ 2 * (1 - 2 * f + α * f ^ 3 * δ)| ≤ 5 / 4 * (α * f ^ 3 * δ ^ 2) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ α * f ^ 3 * δ ^ 2), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h12 : |1 - 2 * f| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have := abs_add_le (1 - 2 * f) (α * f ^ 3 * δ)
    linarith
  have key : |1 / Λ - g| = |δ * g ^ 2 - (α + 1 + δ) * g + 1| / (Λ - δ * g) := by
    rw [← hid, abs_mul, abs_of_pos hDpos, mul_div_assoc, div_self hDpos.ne', mul_one]
  rw [key, div_le_iff₀ hDpos, hPg]
  have hX : 0 ≤ α * f ^ 3 * δ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hden hX
  nlinarith

/-- eq:main-asymp's remainder, quantitatively: `|R(θ, Ã, F)| ≤ (20/7) θ/(1+θ)² (ÃF/a_N)²`
whenever `|ÃF/a_N| ≤ (1 + θ)/(4θ)`. -/
theorem mainRem_le (hN : 3 ≤ N) {θ : ℝ} (hθ : 0 < θ) {A F : ℝ}
    (hF : |A * F / aN N| ≤ (1 + θ) / (4 * θ)) :
    |mainRem N θ A F| ≤ 20 / 7 * θ / (1 + θ) ^ 2 * (A * F / aN N) ^ 2 := by
  have ha := (aN_pos hN).ne'
  have hθ' : θ ≠ 0 := hθ.ne'
  have h1θ : 1 + θ ≠ 0 := by linarith
  have h1θ' : θ + 1 ≠ 0 := by linarith
  have hα : 0 < 1 / θ := by positivity
  have hδ' : |A * F / aN N| ≤ (1 + 1 / θ) / 4 := by
    rw [show (1 + 1 / θ) / 4 = (1 + θ) / (4 * θ) by field_simp; ring]; exact hF
  have hb := inv_lamMax_sub_le hα hδ'
  have eg : (1 + θ) / θ * (1 / (1 + 1 / θ) - 1 / θ * (1 / (1 + 1 / θ)) ^ 3 * (A * F / aN N)) =
      1 - A * θ * F / (aN N * (1 + θ) ^ 2) := by
    field_simp; ring
  have e : mainRem N θ A F = (1 + θ) / θ * (1 / lamMax (1 / θ) 1 (A * F / aN N) -
      (1 / (1 + 1 / θ) - 1 / θ * (1 / (1 + 1 / θ)) ^ 3 * (A * F / aN N))) := by
    unfold mainRem; rw [mul_sub, eg]; ring
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < (1 + θ) / θ)]
  calc (1 + θ) / θ * |1 / lamMax (1 / θ) 1 (A * F / aN N) -
        (1 / (1 + 1 / θ) - 1 / θ * (1 / (1 + 1 / θ)) ^ 3 * (A * F / aN N))|
      ≤ (1 + θ) / θ * (20 / 7 * (1 / θ) * (1 / (1 + 1 / θ)) ^ 3 * (A * F / aN N) ^ 2) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 20 / 7 * θ / (1 + θ) ^ 2 * (A * F / aN N) ^ 2 := by field_simp; ring

/-- The remainder is uniform in `θ`: `|R(θ, Ã, F)| ≤ (5/7) (ÃF/a_N)²` whenever
`|ÃF/a_N| ≤ 1/4`, for every `θ > 0`. -/
theorem mainRem_le_uniform (hN : 3 ≤ N) {θ : ℝ} (hθ : 0 < θ) {A F : ℝ}
    (hF : |A * F / aN N| ≤ 1 / 4) :
    |mainRem N θ A F| ≤ 5 / 7 * (A * F / aN N) ^ 2 := by
  have h1 : 1 / 4 ≤ (1 + θ) / (4 * θ) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  refine (mainRem_le hN hθ (hF.trans h1)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [mul_div_assoc, show (5 / 7 : ℝ) = 20 / 7 * (1 / 4) by norm_num]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg (θ - 1)]

/-- eq:main-asymp's `O(F_g(1)²)`, read at fixed `θ` and `Ã`: the remainder is `O(F²)` as `F → 0`. -/
theorem mainRem_isBigO (hN : 3 ≤ N) {θ : ℝ} (hθ : 0 < θ) (A : ℝ) :
    (fun F => mainRem N θ A F) =O[𝓝 0] (fun F => F ^ 2) := by
  have ha := (aN_pos hN).ne'
  refine IsBigO.of_bound (20 / 7 * θ / (1 + θ) ^ 2 * (A / aN N) ^ 2) ?_
  have hc : Tendsto (fun F : ℝ => |A * F / aN N|) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun F : ℝ => |A * F / aN N|) := by fun_prop
    simpa using this.tendsto 0
  have hpos : (0 : ℝ) < (1 + θ) / (4 * θ) := by positivity
  filter_upwards [hc.eventually_le_const hpos] with F hF
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg F)]
  refine (mainRem_le hN hθ hF).trans (le_of_eq ?_)
  field_simp

/-- The envelope computation (l.554–560): `d/dδ (1/Λ_max(α, 1, δ))|_{δ=0} = −α/(1+α)³`; at
`α = 1/θ` this is the relative loss `θδ/(1+θ)² = ε/(1+θ)²`, `ε = Ãθ F_g(1)/a_N`. -/
theorem hasDerivAt_inv_lamMax {α : ℝ} (hα : 0 < α) :
    HasDerivAt (fun δ => 1 / lamMax α 1 δ) (-(α * (1 / (1 + α)) ^ 3)) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  have h0 : 1 / lamMax α 1 0 = 1 / (1 + α) := by rw [lamMax_zero hα.le zero_le_one, add_comm]
  have hO : (fun δ => 1 / lamMax α 1 δ - (1 / (1 + α) - α * (1 / (1 + α)) ^ 3 * δ)) =O[𝓝 0]
      (fun δ => δ ^ 2) := by
    refine IsBigO.of_bound (20 / 7 * α * (1 / (1 + α)) ^ 3) ?_
    have hc : Tendsto (fun δ : ℝ => |δ|) (𝓝 0) (𝓝 0) := by
      simpa using continuous_abs.tendsto (0 : ℝ)
    have hpos : (0 : ℝ) < (1 + α) / 4 := by positivity
    filter_upwards [hc.eventually_le_const hpos] with δ hδ
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg δ)]
    exact inv_lamMax_sub_le hα hδ
  refine (hO.trans_isLittleO (isLittleO_pow_id one_lt_two)).congr' ?_ ?_
  · filter_upwards with δ
    rw [h0, smul_eq_mul]
    ring
  · filter_upwards with δ
    ring

end Asymp

/-! ## 3. thm:main on the model -/

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : FrameMetric X N)

lemma mean_eq_volMean (u : D) : M.mean g u = M.volMean g u := by
  unfold mean volMean; rw [div_eq_inv_mul]

/-- `Λ_max` of eq:main for the model: `α = 1/θ`, `β = 1`, `δ = Ã F_g(1)/a_N` (l.195–198). -/
def mainLamMax (A : ℝ) : ℝ := lamMax (1 / M.theta g) 1 (A * M.Fq g M.one / aN N)

/-- The lattice property used at l.458–460, in a weak form: for every `u` some `w ∈ D` has
`w ≥ 0`, `w = |u|` a.e., trace `|tr u|` a.e. on each `B_j`, and `‖∇w‖² ≤ ‖∇u‖²` (the paper has
`|∇|u|| = |∇u|` a.e.). -/
def AbsLattice : Prop :=
  ∀ u : D, ∃ w : D, (∀ x, 0 ≤ M.val w x) ∧ M.val w =ᵐ[M.vol g] (fun x => |M.val u x|) ∧
    (∀ j, M.tr w =ᵐ[M.bvol g j] (fun x => |M.tr u x|)) ∧ M.dirichlet g w ≤ M.dirichlet g u

/-- The constant `C_1 = V^{1/p*}/√cap*` of eq:linear (l.507). -/
def linC1 : ℝ := (M.vol g Set.univ).toReal ^ (1 / pStar N) / Real.sqrt (M.capStar g).toReal

/-- The constant `C_2 = V^{1/p*}/√S` of eq:linear (l.508). -/
def linC2 : ℝ := (M.vol g Set.univ).toReal ^ (1 / pStar N) / Real.sqrt (M.bdryS g)

lemma linC1_nonneg : 0 ≤ M.linC1 g :=
  div_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (Real.sqrt_nonneg _)

lemma linC2_nonneg : 0 ≤ M.linC2 g :=
  div_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (Real.sqrt_nonneg _)

lemma theta_nonneg (hN : 3 ≤ N) : 0 ≤ M.theta g :=
  div_nonneg (mul_nonneg (aN_pos hN).le ENNReal.toReal_nonneg)
    (mul_nonneg (cN_pos (by omega)).le (M.bdryS_nonneg g))

/-- The calibration eq:calib (l.511–516) in the form the proof of thm:main uses:
`F_g(1) C_1² = a_N/θ`, `F_g(1) C_2² = c_N`, `F_g(1) C_1 C_2 = √(1/θ) √a_N √c_N`, `F_g(1) > 0`. -/
theorem calib_main (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] (hV : M.vol g ≠ 0)
    (hB : ∃ j, M.bvol g j ≠ 0) [∀ j, IsFiniteMeasure (M.bvol g j)] :
    M.Fq g M.one * M.linC1 g ^ 2 = 1 / M.theta g * aN N ∧
      M.Fq g M.one * M.linC2 g ^ 2 = cN N ∧
      M.Fq g M.one * (M.linC1 g * M.linC2 g) =
        Real.sqrt (1 / M.theta g * 1) * (Real.sqrt (aN N) * Real.sqrt (cN N)) ∧
      0 < M.Fq g M.one := by
  have hS := M.bdryS_pos g hB
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  have ha := aN_pos hN
  have hc := cN_pos (N := N) (by omega)
  have hW : ((M.vol g Set.univ).toReal ^ (1 / pStar N)) ^ 2 =
      (M.vol g Set.univ).toReal ^ (2 / pStar N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hVpos.le]
    congr 1; push_cast; ring
  have hVp : 0 < (M.vol g Set.univ).toReal ^ (2 / pStar N) := Real.rpow_pos_of_pos hVpos _
  have hF1 : M.Fq g M.one = cN N * M.bdryS g / (M.vol g Set.univ).toReal ^ (2 / pStar N) :=
    (M.eq_calib g hN hV hS).2.2.2.symm
  have hF1pos : 0 < M.Fq g M.one := by rw [hF1]; positivity
  have e1 : M.Fq g M.one * M.linC1 g ^ 2 = 1 / M.theta g * aN N := by
    unfold linC1 theta
    rw [div_pow, hW, Real.sq_sqrt ENNReal.toReal_nonneg, hF1]
    rcases (ENNReal.toReal_nonneg : 0 ≤ (M.capStar g).toReal).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · field_simp
  have e2 : M.Fq g M.one * M.linC2 g ^ 2 = cN N := by
    unfold linC2
    rw [div_pow, hW, Real.sq_sqrt hS.le, hF1]
    field_simp
  refine ⟨e1, e2, ?_, hF1pos⟩
  have hθ := M.theta_nonneg g hN
  have h1 : 0 ≤ M.Fq g M.one * (M.linC1 g * M.linC2 g) :=
    mul_nonneg hF1pos.le (mul_nonneg (M.linC1_nonneg g) (M.linC2_nonneg g))
  have h2 : 0 ≤ Real.sqrt (1 / M.theta g * 1) * (Real.sqrt (aN N) * Real.sqrt (cN N)) := by
    positivity
  refine (sq_eq_sq₀ h1 h2).mp ?_
  have hθ' : 0 ≤ 1 / M.theta g * 1 := by positivity
  calc (M.Fq g M.one * (M.linC1 g * M.linC2 g)) ^ 2 =
        (M.Fq g M.one * M.linC1 g ^ 2) * (M.Fq g M.one * M.linC2 g ^ 2) := by ring
    _ = (1 / M.theta g * aN N) * cN N := by rw [e1, e2]
    _ = Real.sqrt (1 / M.theta g * 1) ^ 2 * (Real.sqrt (aN N) ^ 2 * Real.sqrt (cN N) ^ 2) := by
        rw [Real.sq_sqrt hθ', Real.sq_sqrt ha.le, Real.sq_sqrt hc.le]; ring
    _ = _ := by ring

lemma Fq_eq (u : D) : M.Fq g u = (aN N * M.dirichlet g u +
    cN N * ∑ j, normSq (M.bvol g j) (pSharp N) (M.tr u)) / normSq (M.vol g) (pStar N) (M.val u) := by
  unfold Fq F traceSobolevQuot
  rw [Finset.mul_sum]

lemma bdryY_sq (u : D) : M.bdryY g u ^ 2 = ∑ j, normSq (M.bvol g j) (pSharp N) (M.tr u) :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => normSq_nonneg _ _ _)

/-- The core of the proof of thm:main (l.519–550), for one `u`: from eq:linear at `u` (with
`|ū|`) and eq:star at `u`, `F_g(u) ≥ F_g(1)/Λ_max`. -/
theorem le_Fq_of_linear_of_star (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    {A : ℝ} {u : D} (hu : M.Adm g u)
    (hlin : (M.vol g Set.univ).toReal ^ (1 / pStar N) * |M.volMean g u| ≤
      M.linC1 g * Real.sqrt (M.dirichlet g u) + M.linC2 g * M.bdryY g u)
    (hstar : normSq (M.vol g) (pStar N) (M.val u) ≤
      A * M.dirichlet g u + (M.vol g Set.univ).toReal ^ (2 / pStar N) * M.mean g u ^ 2) :
    M.Fq g M.one / M.mainLamMax g A ≤ M.Fq g u := by
  obtain ⟨e1, e2, e3, hF1pos⟩ := M.calib_main g hN hV hB
  have ha := aN_pos hN
  have hc := cN_pos (N := N) (by omega)
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  have hW : ((M.vol g Set.univ).toReal ^ (1 / pStar N)) ^ 2 =
      (M.vol g Set.univ).toReal ^ (2 / pStar N) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hVpos.le]
    congr 1; push_cast; ring
  -- eq:linear, squared
  have hsq : (M.vol g Set.univ).toReal ^ (2 / pStar N) * M.mean g u ^ 2 ≤
      (M.linC1 g * Real.sqrt (M.dirichlet g u) + M.linC2 g * M.bdryY g u) ^ 2 := by
    rw [mean_eq_volMean, ← hW, ← sq_abs (M.volMean g u), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hlin 2
  set X := Real.sqrt (M.dirichlet g u) with hXdef
  set Y := M.bdryY g u with hYdef
  have hX2 : X ^ 2 = M.dirichlet g u := Real.sq_sqrt (M.dirichlet_nonneg g u)
  have hY2 : Y ^ 2 = ∑ j, normSq (M.bvol g j) (pSharp N) (M.tr u) := M.bdryY_sq g u
  set F1 := M.Fq g M.one with hF1def
  set α := 1 / M.theta g with hα
  set δ := A * F1 / aN N with hδ
  have hα0 : 0 ≤ α := by rw [hα]; exact one_div_nonneg.mpr (M.theta_nonneg g hN)
  have hΛ : M.mainLamMax g A = lamMax α 1 δ := rfl
  have hΛpos : 0 < lamMax α 1 δ := lt_of_lt_of_le one_pos (le_lamMax_right hα0 zero_le_one)
  have hquad := quad_le_lamMax (δ := δ) hα0 zero_le_one (Real.sqrt (aN N) * X) (Real.sqrt (cN N) * Y)
  have hδa : δ * aN N = A * F1 := by rw [hδ]; field_simp
  have hsa := Real.sq_sqrt ha.le
  have hsc := Real.sq_sqrt hc.le
  have key : F1 * normSq (M.vol g) (pStar N) (M.val u) ≤
      lamMax α 1 δ * (aN N * M.dirichlet g u + cN N * ∑ j, normSq (M.bvol g j) (pSharp N) (M.tr u)) := by
    calc F1 * normSq (M.vol g) (pStar N) (M.val u)
        ≤ F1 * (A * X ^ 2 + (M.linC1 g * X + M.linC2 g * Y) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hF1pos.le
          rw [hX2]; linarith
      _ = (α + δ) * (Real.sqrt (aN N) * X) ^ 2 +
            2 * Real.sqrt (α * 1) * (Real.sqrt (aN N) * X) * (Real.sqrt (cN N) * Y) +
            1 * (Real.sqrt (cN N) * Y) ^ 2 := by
          rw [mul_pow, mul_pow, hsa, hsc]
          linear_combination X ^ 2 * e1 + 2 * X * Y * e3 + Y ^ 2 * e2 - X ^ 2 * hδa
      _ ≤ lamMax α 1 δ * ((Real.sqrt (aN N) * X) ^ 2 + (Real.sqrt (cN N) * Y) ^ 2) := hquad
      _ = _ := by rw [mul_pow, mul_pow, hsa, hsc, hX2, hY2]
  rw [M.Fq_eq g u, hΛ, div_le_div_iff₀ hΛpos hu]
  linarith [key]

/-- The core of the proof of thm:main (l.519–550): if eq:star holds at `u`, then
`F_g(u) ≥ F_g(1)/Λ_max`. The squaring of eq:linear uses `|ū|` (`eq_linear`), not `ū ≥ 0`. -/
theorem le_Fq_of_star (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    {A : ℝ} {u : D} (hu : M.Adm g u)
    (hstar : normSq (M.vol g) (pStar N) (M.val u) ≤
      A * M.dirichlet g u + (M.vol g Set.univ).toReal ^ (2 / pStar N) * M.mean g u ^ 2) :
    M.Fq g M.one / M.mainLamMax g A ≤ M.Fq g u :=
  M.le_Fq_of_linear_of_star g hN hV hB hu (M.eq_linear g hN hV hB hP hT u) hstar

/-- eq:linear with `|ū|` from `0 < cap*` alone, for `u` of finite energy whose traces lie in
`L^{p♯}`: the only input thm:main takes from lem:capstar. -/
theorem eq_linear_of_capStar_pos (hN : 3 ≤ N) [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hcap : 0 < M.capStar g) {u : D} (hE : M.energy g u ≠ ⊤)
    (htr : ∀ j, MemLp (M.tr u) (ENNReal.ofReal (pSharp N)) (M.bvol g j)) :
    (M.vol g Set.univ).toReal ^ (1 / pStar N) * |M.volMean g u| ≤
      M.linC1 g * Real.sqrt (M.dirichlet g u) + M.linC2 g * M.bdryY g u := by
  have hW : 0 ≤ (M.vol g Set.univ).toReal ^ (1 / pStar N) := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hb := M.abs_bdryAvg_le g hN u htr
  have hsplit : M.volMean g u = M.ell g u + M.bdryAvg g u := by unfold ell; ring
  have hX0 := Real.sqrt_nonneg (M.dirichlet g u)
  -- `|ℓ(u)| ≤ X/√cap*`
  have hell : |M.ell g u| ≤ Real.sqrt (M.dirichlet g u) / Real.sqrt (M.capStar g).toReal := by
    by_cases htop : M.capStar g = ⊤
    · rw [M.ell_eq_zero_of_capStar_eq_top g htop u hE, abs_zero, htop, ENNReal.toReal_top,
        Real.sqrt_zero, div_zero]
    · have hκ : 0 < Real.sqrt (M.capStar g).toReal :=
        Real.sqrt_pos.mpr (ENNReal.toReal_pos hcap.ne' htop)
      have h1 := M.sqrt_capStar_mul_ell_le g u hE
      have hE' : M.energy g (-u) ≠ ⊤ := by
        rw [← neg_one_smul ℝ u, M.energy_smul]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE
      have h2 := M.sqrt_capStar_mul_ell_le g (-u) hE'
      rw [M.dirichlet_neg, ← neg_one_smul ℝ u, M.ell_smul] at h2
      rw [le_div_iff₀ hκ]
      rcases abs_cases (M.ell g u) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nlinarith
  calc (M.vol g Set.univ).toReal ^ (1 / pStar N) * |M.volMean g u|
      ≤ (M.vol g Set.univ).toReal ^ (1 / pStar N) *
          (Real.sqrt (M.dirichlet g u) / Real.sqrt (M.capStar g).toReal +
            M.bdryY g u / Real.sqrt (M.bdryS g)) := by
        refine mul_le_mul_of_nonneg_left ?_ hW
        rw [hsplit]
        exact (abs_add_le _ _).trans (add_le_add hell hb)
    _ = _ := by unfold linC1 linC2; ring

/-- The core of thm:main with `0 < cap*` in place of the Poincaré and trace hypotheses. -/
theorem le_Fq_of_star_of_capStar_pos (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    (hcap : 0 < M.capStar g) {A : ℝ} {u : D} (hu : M.Adm g u) (hE : M.energy g u ≠ ⊤)
    (htr : ∀ j, MemLp (M.tr u) (ENNReal.ofReal (pSharp N)) (M.bvol g j))
    (hstar : normSq (M.vol g) (pStar N) (M.val u) ≤
      A * M.dirichlet g u + (M.vol g Set.univ).toReal ^ (2 / pStar N) * M.mean g u ^ 2) :
    M.Fq g M.one / M.mainLamMax g A ≤ M.Fq g u :=
  M.le_Fq_of_linear_of_star g hN hV hB hu (M.eq_linear_of_capStar_pos g hN hcap hE htr) hstar

lemma adm_one (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] (hV : M.vol g ≠ 0) : M.Adm g M.one := by
  have hVpos : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hV) (measure_ne_top _ _)
  unfold Adm
  rw [M.val_one, normSq_one _ (pStar_pos hN)]
  exact Real.rpow_pos_of_pos hVpos _

/-- eq:main from a pointwise bound on every competitor. -/
lemma le_infF_of_forall (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] (hV : M.vol g ≠ 0) {b : ℝ}
    (h : ∀ u, M.Adm g u → b ≤ M.Fq g u) : b ≤ M.infF g (fun _ => cN N) := by
  unfold infF
  refine le_csInf ⟨_, ⟨M.one, M.adm_one g hN hV, rfl⟩⟩ ?_
  rintro _ ⟨u, hu, rfl⟩
  exact h u hu

/-- **eq:main with eq:star for every `u`** (the signed form): no lattice property of `D` is used. -/
theorem eq_main_signed (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    {A : ℝ} (hstar : M.StarIneqSigned g A) :
    M.Fq g M.one / M.mainLamMax g A ≤ M.infF g (fun _ => cN N) :=
  M.le_infF_of_forall g hN hV fun u hu => M.le_Fq_of_star g hN hV hB hP hT hu (hstar u)

lemma normSq_congr_abs {ν : Measure X} {q : ℝ} {f h : X → ℝ} (hfh : f =ᵐ[ν] fun x => |h x|) :
    normSq ν q f = normSq ν q h := by
  unfold normSq
  rw [eLpNorm_congr_ae hfh]
  have : (fun x => |h x|) = fun x => ‖h x‖ := funext fun x => (Real.norm_eq_abs _).symm
  rw [this, eLpNorm_norm]

/-- The approximate lattice property, all that l.458–460 needs: for every `u`, a sequence
`w_k ∈ D` with `w_k ≥ 0`, `‖∇w_k‖² ≤ ‖∇u‖²`, `‖tr w_k‖²_{L^{p♯}(B_j)} ≤ ‖tr u‖²_{L^{p♯}(B_j)}` and
`‖w_k‖²_{L^{p*}} → ‖u‖²_{L^{p*}}`. `AbsLattice` gives it (`AbsLattice.approx`); under the `C¹`
reading `w_ε = √(u² + ε²) − ε` gives it (argued, not formalized). -/
def AbsLatticeApprox : Prop :=
  ∀ u : D, ∃ w : ℕ → D, (∀ k x, 0 ≤ M.val (w k) x) ∧ (∀ k, M.dirichlet g (w k) ≤ M.dirichlet g u) ∧
    (∀ k j, normSq (M.bvol g j) (pSharp N) (M.tr (w k)) ≤ normSq (M.bvol g j) (pSharp N) (M.tr u)) ∧
    Tendsto (fun k => normSq (M.vol g) (pStar N) (M.val (w k))) atTop
      (𝓝 (normSq (M.vol g) (pStar N) (M.val u)))

/-- The exact lattice property gives the approximate one (the constant sequence). -/
theorem AbsLattice.approx (hL : M.AbsLattice g) : M.AbsLatticeApprox g := by
  intro u
  obtain ⟨w, hw0, hwv, hwt, hwd⟩ := hL u
  refine ⟨fun _ => w, fun _ => hw0, fun _ => hwd, fun _ j => (normSq_congr_abs (hwt j)).le, ?_⟩
  simp only [normSq_congr_abs hwv]
  exact tendsto_const_nhds

/-- The reduction `u ↦ |u|` of l.458–460: under `AbsLatticeApprox`, a lower bound on `F_g` over
the nonnegative competitors is a lower bound over all of them. -/
theorem le_Fq_of_lattice (hN : 3 ≤ N) (hL : M.AbsLatticeApprox g) {b : ℝ}
    (h : ∀ w, M.Adm g w → (∀ x, 0 ≤ M.val w x) → b ≤ M.Fq g w) {u : D} (hu : M.Adm g u) :
    b ≤ M.Fq g u := by
  obtain ⟨w, hw0, hwd, hwt, hlim⟩ := hL u
  unfold Adm at hu
  rw [M.Fq_eq g u]
  have hlim' := (tendsto_const_nhds (x := aN N * M.dirichlet g u +
    cN N * ∑ j, normSq (M.bvol g j) (pSharp N) (M.tr u))).div hlim hu.ne'
  refine ge_of_tendsto hlim' ?_
  filter_upwards [hlim.eventually (eventually_gt_nhds hu)] with k hk
  refine (h (w k) hk (hw0 k)).trans ?_
  rw [M.Fq_eq g (w k)]
  refine div_le_div_of_nonneg_right ?_ hk.le
  have h1 := mul_le_mul_of_nonneg_left (hwd k) (aN_pos hN).le
  have h2 := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hwt k j)
    (cN_pos (N := N) (by omega)).le
  linarith

/-- eq:main with eq:star for `u ≥ 0`, as printed, under the approximate lattice property of l.458–460. -/
theorem eq_main_lattice (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (hL : M.AbsLatticeApprox g) {A : ℝ} (hstar : M.StarIneq g A) :
    M.Fq g M.one / M.mainLamMax g A ≤ M.infF g (fun _ => cN N) :=
  M.le_infF_of_forall g hN hV fun _ hu => M.le_Fq_of_lattice g hN hL
    (fun w hw hw0 => M.le_Fq_of_star g hN hV hB hP hT hw (hstar w hw0)) hu

/-- eq:main with eq:star for every `u`, from `0 < cap*` (the conclusion of lem:capstar that the
proof uses) in place of `MeanPoincare` and `TraceBound`, over a model whose functions have finite
energy and traces in `L^{p♯}` (`D ⊂ W^{1,2}`). -/
theorem eq_main_signed_of_capStar_pos (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    (hE : ∀ u, M.energy g u ≠ ⊤) (htr : ∀ u j, MemLp (M.tr u) (ENNReal.ofReal (pSharp N)) (M.bvol g j))
    (hcap : 0 < M.capStar g) {A : ℝ} (hstar : M.StarIneqSigned g A) :
    M.Fq g M.one / M.mainLamMax g A ≤ M.infF g (fun _ => cN N) :=
  M.le_infF_of_forall g hN hV fun u hu =>
    M.le_Fq_of_star_of_capStar_pos g hN hV hB hcap hu (hE u) (htr u) (hstar u)

/-- eq:main as printed (eq:star for `u ≥ 0`, `AbsLatticeApprox`), from `0 < cap*` over a model whose
functions have finite energy and traces in `L^{p♯}`. -/
theorem eq_main_lattice_of_capStar_pos (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    (hE : ∀ u, M.energy g u ≠ ⊤) (htr : ∀ u j, MemLp (M.tr u) (ENNReal.ofReal (pSharp N)) (M.bvol g j))
    (hcap : 0 < M.capStar g) (hL : M.AbsLatticeApprox g) {A : ℝ} (hstar : M.StarIneq g A) :
    M.Fq g M.one / M.mainLamMax g A ≤ M.infF g (fun _ => cN N) :=
  M.le_infF_of_forall g hN hV fun _ hu => M.le_Fq_of_lattice g hN hL
    (fun w hw hw0 => M.le_Fq_of_star_of_capStar_pos g hN hV hB hcap hw (hE w) (htr w)
      (hstar w hw0)) hu

/-- The unnormalised matrix of l.531–541, `α' = C_1²/a_N`, `β' = C_2²/c_N`, `δ' = Ã/a_N`:
`Λ_max(M) = Λ_max^norm / F_g(1)` (l.546–550). -/
theorem lamMax_unnormalized (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (A : ℝ) :
    lamMax (M.linC1 g ^ 2 / aN N) (M.linC2 g ^ 2 / cN N) (A / aN N) =
      M.mainLamMax g A / M.Fq g M.one := by
  obtain ⟨e1, e2, -, hF1⟩ := M.calib_main g hN hV hB
  have ha := (aN_pos hN).ne'
  have hc := (cN_pos (N := N) (by omega)).ne'
  have hF := hF1.ne'
  have h1 : M.linC1 g ^ 2 / aN N = 1 / M.Fq g M.one * (1 / M.theta g) := by
    have : M.linC1 g ^ 2 = 1 / M.theta g * aN N / M.Fq g M.one := by
      rw [← e1]; field_simp
    rw [this]; field_simp
  have h2 : M.linC2 g ^ 2 / cN N = 1 / M.Fq g M.one * 1 := by
    have : M.linC2 g ^ 2 = cN N / M.Fq g M.one := by
      rw [← e2]; field_simp
    rw [this]; field_simp
  have h3 : A / aN N = 1 / M.Fq g M.one * (A * M.Fq g M.one / aN N) := by
    field_simp
  rw [h1, h2, h3, lamMax_smul (by positivity)]
  unfold mainLamMax
  ring

/-- `θ > 0` under the hypotheses of lem:capstar (`lem_capstar`). -/
lemma theta_pos (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (hI : M.InteriorBump g) : 0 < M.theta g := by
  obtain ⟨h0, h1, -⟩ := M.lem_capstar g hN hV hB hP hT hI
  have hκ : 0 < (M.capStar g).toReal := ENNReal.toReal_pos h0.ne' h1.ne
  have hS := M.bdryS_pos g hB
  have ha := aN_pos hN
  have hc := cN_pos (N := N) (by omega)
  unfold theta
  positivity

/-- eq:main-asymp from eq:main: the exact rewriting with the remainder `mainRem`, which depends on
`(θ, Ã, F_g(1))` only. -/
theorem eq_main_asymp_of_main (hθ : 0 < M.theta g) {A b : ℝ}
    (h : M.Fq g M.one / M.mainLamMax g A ≤ b) :
    M.theta g / (1 + M.theta g) * M.Fq g M.one *
        (1 - A * M.theta g * M.Fq g M.one / (aN N * (1 + M.theta g) ^ 2) +
          mainRem N (M.theta g) A (M.Fq g M.one)) ≤ b := by
  rw [← eq_main_asymp_identity hθ]
  exact h

/-- thm:main (l.179–206) over the model, in the printed form (eq:star for `u ≥ 0`), under the
approximate lattice property that l.458–460 needs: eq:main; eq:main-asymp with the explicit
remainder `mainRem N θ Ã`; the remainder is `O(F²)` at fixed `θ`, `Ã`, with the explicit bound. -/
theorem thm_main (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (hI : M.InteriorBump g) (hL : M.AbsLatticeApprox g) {A : ℝ} (hstar : M.StarIneq g A) :
    M.Fq g M.one / lamMax (1 / M.theta g) 1 (A * M.Fq g M.one / aN N) ≤
        M.infF g (fun _ => cN N) ∧
      M.theta g / (1 + M.theta g) * M.Fq g M.one *
          (1 - A * M.theta g * M.Fq g M.one / (aN N * (1 + M.theta g) ^ 2) +
            mainRem N (M.theta g) A (M.Fq g M.one)) ≤ M.infF g (fun _ => cN N) ∧
      (fun F => mainRem N (M.theta g) A F) =O[𝓝 0] (fun F => F ^ 2) ∧
      (∀ F : ℝ, |A * F / aN N| ≤ (1 + M.theta g) / (4 * M.theta g) →
        |mainRem N (M.theta g) A F| ≤ 20 / 7 * M.theta g / (1 + M.theta g) ^ 2 * (A * F / aN N) ^ 2) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 → |mainRem N (M.theta g) A F| ≤ 5 / 7 * (A * F / aN N) ^ 2 := by
  have hθ := M.theta_pos g hN hV hB hP hT hI
  have hmain := M.eq_main_lattice g hN hV hB hP hT hL hstar
  exact ⟨hmain, M.eq_main_asymp_of_main g hθ hmain, mainRem_isBigO hN hθ A,
    fun F hF => mainRem_le hN hθ hF, fun F hF => mainRem_le_uniform hN hθ hF⟩

/-- **thm:main with eq:star for every `u`** (the signed form): the same conclusions, with no
lattice property of `D`. -/
theorem thm_main_signed (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (hI : M.InteriorBump g) {A : ℝ} (hstar : M.StarIneqSigned g A) :
    M.Fq g M.one / lamMax (1 / M.theta g) 1 (A * M.Fq g M.one / aN N) ≤
        M.infF g (fun _ => cN N) ∧
      M.theta g / (1 + M.theta g) * M.Fq g M.one *
          (1 - A * M.theta g * M.Fq g M.one / (aN N * (1 + M.theta g) ^ 2) +
            mainRem N (M.theta g) A (M.Fq g M.one)) ≤ M.infF g (fun _ => cN N) ∧
      (fun F => mainRem N (M.theta g) A F) =O[𝓝 0] (fun F => F ^ 2) ∧
      (∀ F : ℝ, |A * F / aN N| ≤ (1 + M.theta g) / (4 * M.theta g) →
        |mainRem N (M.theta g) A F| ≤ 20 / 7 * M.theta g / (1 + M.theta g) ^ 2 * (A * F / aN N) ^ 2) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 → |mainRem N (M.theta g) A F| ≤ 5 / 7 * (A * F / aN N) ^ 2 := by
  have hθ := M.theta_pos g hN hV hB hP hT hI
  have hmain := M.eq_main_signed g hN hV hB hP hT hstar
  exact ⟨hmain, M.eq_main_asymp_of_main g hθ hmain, mainRem_isBigO hN hθ A,
    fun F hF => mainRem_le hN hθ hF, fun F hF => mainRem_le_uniform hN hθ hF⟩

/-- thm:main for `N = 3` at the single constant `Ã = star3AtilCorr V λ C` of the corrected
thm:star3 (`star3_of_consts`), for any valid Poincaré and Sobolev–Poincaré constants `λ`, `C`: the
composite of thm:star3 and thm:main, a special case of thm:main. -/
theorem thm_main_three (M : MeasuredModel X D 3 n) (g : FrameMetric X 3)
    [IsFiniteMeasure (M.vol g)] [∀ j, IsFiniteMeasure (M.bvol g j)]
    (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0) (hP : M.MeanPoincare g) (hT : M.TraceBound g)
    (hI : M.InteriorBump g) {lam C : ℝ} (hlam : 0 < lam) (hC : 0 ≤ C)
    (hPl : M.IsPoincareConst g lam) (hS : M.IsSobolevPoincareConst g C) :
    let A := star3AtilCorr (M.vol g Set.univ).toReal lam C
    M.Fq g M.one / lamMax (1 / M.theta g) 1 (A * M.Fq g M.one / aN 3) ≤
        M.infF g (fun _ => cN 3) ∧
      M.theta g / (1 + M.theta g) * M.Fq g M.one *
          (1 - A * M.theta g * M.Fq g M.one / (aN 3 * (1 + M.theta g) ^ 2) +
            mainRem 3 (M.theta g) A (M.Fq g M.one)) ≤ M.infF g (fun _ => cN 3) ∧
      (fun F => mainRem 3 (M.theta g) A F) =O[𝓝 0] (fun F => F ^ 2) ∧
      (∀ F : ℝ, |A * F / aN 3| ≤ (1 + M.theta g) / (4 * M.theta g) →
        |mainRem 3 (M.theta g) A F| ≤ 20 / 7 * M.theta g / (1 + M.theta g) ^ 2 * (A * F / aN 3) ^ 2) ∧
      ∀ F : ℝ, |A * F / aN 3| ≤ 1 / 4 → |mainRem 3 (M.theta g) A F| ≤ 5 / 7 * (A * F / aN 3) ^ 2 := by
  intro A
  have hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g) := by
    obtain ⟨K, hK⟩ := hP
    exact fun u => (hK u).1.aestronglyMeasurable
  exact M.thm_main_signed g le_rfl hV hB hP hT hI (star3_of_consts M g hD hlam hC hPl hS)

end MeasuredModel

/-! ## 4. A witness: the hypotheses of `thm_main` hold together on the two-point toy model -/

section Toy

lemma toy_mean (u : Bool → ℝ) : toyModel.mean toyMetric u = (u true + u false) / 2 := by
  rw [MeasuredModel.mean_eq_volMean, toy_volMean]

/-- The toy model has the lattice property: `|u| ∈ D` with `‖∇|u|‖ ≤ ‖∇u‖`. -/
theorem toy_absLattice : toyModel.AbsLattice toyMetric := by
  intro u
  refine ⟨fun b => |u b|, fun x => abs_nonneg _, ae_of_all _ fun x => rfl,
    fun j => ae_of_all _ fun x => rfl, ?_⟩
  rw [toy_dirichlet, toy_dirichlet]
  have h : (|u true| - |u false|) ^ 2 ≤ (u true - u false) ^ 2 :=
    sq_le_sq.mpr (abs_abs_sub_abs_le_abs_sub _ _)
  linarith

theorem toy_isPoincareConst : toyModel.IsPoincareConst toyMetric 4 := by
  intro v
  have e : toyModel.val v = v := rfl
  rw [toy_normSq_two_vol, toy_dirichlet]
  simp only [e, toy_mean]
  nlinarith [sq_nonneg (v true - v false)]

theorem toy_lambda1_pos : 0 < toyModel.lambda1 toyMetric := by
  refine toyModel.lambda1_pos toyMetric four_pos toy_isPoincareConst ⟨4, ?_⟩
  rintro lam ⟨-, hl⟩
  have h := hl (fun b => if b then 1 else 0)
  have e : toyModel.val (fun b : Bool => if b then (1 : ℝ) else 0) = fun b => if b then 1 else 0 := rfl
  rw [toy_normSq_two_vol, toy_dirichlet] at h
  simp only [e, toy_mean] at h
  norm_num at h
  linarith

theorem toy_isSobolevPoincareConst : toyModel.IsSobolevPoincareConst toyMetric 1 := by
  intro v
  rw [← sqrt_normSq]
  refine (Real.sqrt_le_sqrt (toy_normSq_vol_le _)).trans ?_
  rw [one_mul, toy_dirichlet]
  apply Real.sqrt_le_sqrt
  have e : toyModel.val v = v := rfl
  simp only [e, toy_mean]
  nlinarith [sq_nonneg (v true - v false)]

/-- Every hypothesis of `thm_main` and `thm_main_three` holds on the toy model. -/
theorem toy_thm_main_hyps :
    IsFiniteMeasure (toyModel.vol toyMetric) ∧ (∀ j, IsFiniteMeasure (toyModel.bvol toyMetric j)) ∧
    toyModel.vol toyMetric ≠ 0 ∧ (∃ j, toyModel.bvol toyMetric j ≠ 0) ∧
    toyModel.MeanPoincare toyMetric ∧ toyModel.TraceBound toyMetric ∧
    toyModel.InteriorBump toyMetric ∧ toyModel.AbsLattice toyMetric ∧
    toyModel.IsPoincareConst toyMetric 4 ∧ 0 < toyModel.lambda1 toyMetric ∧
    toyModel.IsSobolevPoincareConst toyMetric 1 ∧
    toyModel.StarIneqSigned toyMetric (star3AtilCorr (toyModel.vol toyMetric Set.univ).toReal 4 1) := by
  haveI := toy_isFiniteMeasure_vol
  have hD : ∀ u, AEStronglyMeasurable (toyModel.val u) (toyModel.vol toyMetric) := fun _ =>
    (Measurable.of_discrete).aestronglyMeasurable
  exact ⟨toy_isFiniteMeasure_vol, toy_isFiniteMeasure_bvol, toy_vol_ne_zero,
    ⟨0, by rw [toy_bvol]; exact Measure.dirac_ne_zero⟩, toy_meanPoincare, toy_traceBound,
    toy_interiorBump, toy_absLattice, toy_isPoincareConst, toy_lambda1_pos,
    toy_isSobolevPoincareConst,
    MeasuredModel.star3_of_consts toyModel toyMetric hD four_pos zero_le_one toy_isPoincareConst
      toy_isSobolevPoincareConst⟩

/-- The hypotheses of `eq_main_signed_of_capStar_pos` hold on the toy model (`cap* = 8`). -/
theorem toy_capStar_route_hyps :
    (∀ u, toyModel.energy toyMetric u ≠ ⊤) ∧
      (∀ u j, MemLp (toyModel.tr u) (ENNReal.ofReal (pSharp 3)) (toyModel.bvol toyMetric j)) ∧
      0 < toyModel.capStar toyMetric := by
  refine ⟨fun u => by rw [toy_energy]; exact ENNReal.ofReal_ne_top, fun u j => ?_, ?_⟩
  · haveI := toy_isFiniteMeasure_bvol j
    exact MemLp.of_discrete
  · rw [toy_capStar]; norm_num

/-- thm:main on the toy model, in the printed form (eq:star for `u ≥ 0` with the corrected
constant of thm:star3 at `λ = 4`, `C = 1`). -/
theorem toy_thm_main :
    let A := star3AtilCorr (toyModel.vol toyMetric Set.univ).toReal 4 1
    toyModel.Fq toyMetric toyModel.one /
        lamMax (1 / toyModel.theta toyMetric) 1 (A * toyModel.Fq toyMetric toyModel.one / aN 3) ≤
      toyModel.infF toyMetric (fun _ => cN 3) := by
  intro A
  obtain ⟨h1, h2, hV, hB, hP, hT, hI, hL, -, -, -, hstar⟩ := toy_thm_main_hyps
  haveI := h1
  haveI := h2
  exact (toyModel.thm_main toyMetric le_rfl hV hB hP hT hI
    (MeasuredModel.AbsLattice.approx _ _ hL) hstar.starIneq).1

end Toy

end Yamabe
