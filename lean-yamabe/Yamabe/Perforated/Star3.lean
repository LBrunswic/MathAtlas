import Yamabe.Negative

/-!
# Perforated § 5, `N = 3`: the Poincaré and Sobolev–Poincaré constants, and eq:star with the explicit `Ã` of eq:Atil, over the measured model

Labels (NOT marked: partial, see SCOPE and the findings):

* `def:constants` — `perforated.tex:316` (l.316–326): `λ₁` read as the best Poincaré constant
  (`MeasuredModel.lambda1`; its Rayleigh form is proved, the eigenvalue of an operator is not
  formalized), `C_SP` the least Sobolev–Poincaré constant (`MeasuredModel.Csp`); both attained.
* `thm:star3` — `perforated.tex:601` (statement l.601–618, proof l.620–655): its proof is wrong at l.635 and in case (ii)
  (proved against the paper), and the printed constant is invalid on the model of record
  (`thm_star3_printed_false`; a two-point model, which violates the paper's lem:csp-lower, so
  against a Riemannian Σ this is argued, not proved: a dumbbell with a thin neck, every
  constant scaling like 1/κ); the minimum of eq:Atil restricted to `C_SP X₀ ≤ 2` is a valid
  constant, for every `u`, signed or not (`thm_star3_corrected`, `thm_star3_corrected_nonneg`).

> \item $\lambda_1=\lambda_1(\Sigma,g)>0$ is the first non-zero Neumann eigenvalue,
>       equivalently the best constant in the Poincaré inequality
>       $\|v-\bar v\|^2_{L^2}\le\lambda_1^{-1}\|\nabla v\|^2_{L^2}$;
> \item $\Csp=\Csp(\Sigma,g)$ is the Sobolev--Poincaré constant, the least $C$ with
>       $\|v-\bar v\|_{L^{\pstar}(\Sigma)}\le C\|\nabla v\|_{L^2(\Sigma)}$ for all
>       $v\in W^{1,2}(\Sigma)$. (l.318–325)

> Let $N=3$ and let $(\Sigma,g)$ be compact, connected, with Lipschitz boundary.
> Then \eqref{eq:star} holds with
> $\Atil=\min_{X_0>0,\ t_0\in[0,1)}\ \max\left\{\frac1{X_0^2},\quad
>      \frac{G(X_0)}{1+t_0^2+t_0^4},\quad\frac{\Csp^2}{(1-t_0)^2}\right\}$,
> where, with $n_2=X_0/\sqrt{\lambda_1}$ and $n_6=\min\{\Csp X_0,2\}$,
> $G(X_0):=\frac1{X_0^2}\Bigl[15V^{-2/3}n_2^2+20V^{-1/2}n_2^{3/2}n_6^{3/2}
>      +15V^{-1/3}n_2n_6^{3}+6V^{-1/6}n_2^{1/2}n_6^{9/2}+n_6^{6}\Bigr]$. (l.603–617)

> $\|u\|^2_{L^{\pstar}(\Sigma)}\;\le\;\Atil\,\|\nabla u\|^2_{L^2(\Sigma)}
>        +V^{2/\pstar}\Bigl(\frac1V\int_\Sigma u\Bigr)^{\!2},
>  \qquad u\in W^{1,2}(\Sigma),\ u\ge0.$ (eq:star, l.184–187)

> [...] so the right-hand side of \eqref{eq:binom} is at most $X^2\,G(X)$ with $G$ as above
> evaluated at $X$; note $G$ is non-decreasing in its argument. (l.634–635)

## What is proved (no `sorry` in this file)

* def:constants: `MeasuredModel.isPoincareConst_lambda1`, `le_lambda1`, `lambda1_pos`,
  `lambda1_eq_sInf_rayleigh`; `MeasuredModel.isSobolevPoincareConst_Csp`, `Csp_le`, `Csp_nonneg`.
* The proof of thm:star3, step by step: `star3_binom` (eq:binom), `star3_interp` (l.629–633),
  `star3_core` (`|t| ≤ 1`; eq:binom bounded after the interpolations; `1 − |t| ≤ ‖v‖₆ ≤ 1 + |t|`),
  `star3_Dbound` (eq:Dbound, as printed), `star3_normalized` (cases (i)–(iii) at `C X₀ ≤ 2`),
  `star3_integral` (2-homogeneity), `MeasuredModel.star3_point`, `MeasuredModel.star3_of_consts`
  (any valid constants `λ`, `C`), and the assembly `MeasuredModel.thm_star3_corrected`.
* The findings: `star3G_not_monotone`; the two-point model `star3CexModel` with `star3Cex_hyps`
  (`λ₁ ≥ 100 > 0`, `C_SP ≤ 100^{-1/6}`), `star3Cex_not_star`, and `thm_star3_printed_false`.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `N = 3` | ✓ carried (`MeasuredModel X D 3 n`) |
| `(Σ, g)` compact | ✓ carried as `IsFiniteMeasure (M.vol g)` |
| connected, Lipschitz, through `λ₁ > 0`, `C_SP < ∞` (l.319, l.328) | ✓ carried as `0 < M.lambda1 g` (`sSup` is `0` on an empty or unbounded set, so this says `λ₁ ∈ (0, ∞)`) and `∃ C, M.IsSobolevPoincareConst g C`; their proof is T-perf-poincare's |
| `u ∈ W^{1,2}(Σ)` | ⚠ read: `u ∈ D` with `M.val u` a.e.-strongly measurable (`hD`) |
| `u ≥ 0` (eq:star, l.187) | ⚠ weakened: not used; eq:star is proved for every `u` (`StarIneqSigned`) |
| `Σ ≠ ∅`, `∂Σ ≠ ∅` | ⚠ weakened: not used (`vol = 0` is handled; no boundary term enters) |
| the constant `Ã` of eq:Atil | ⚠ changed: the min is taken over `C_SP X₀ ≤ 2` (`star3AtilCorr`, a larger constant); the printed one is refuted |

## SCOPE (disclosed)

* **Finding (l.635).** "`G` is non-decreasing" is false: with the cap `n₆ = min{C_SP X₀, 2}`, `G`
  decreases on `[2/C_SP, ∞)` (`star3G_not_monotone`: `G(4) < G(2)` at `V = λ₁ = C_SP = 1`).
  Case (ii) (l.645–647) uses it, and fails: `G(X) ≤ G(X₀)` fails for some `X < 2/C_SP < X₀` (e.g. `X = 2/C_SP`).
* **Finding (l.607).** The printed `Ã` is not a valid constant. On the two-point model of masses
  `1/100`, `99/100` (every hypothesis holds), `Ã ≤` the coefficient at `(X₀, t₀) = (10⁵, 0)`,
  `≤ 0.22`, while `u = (1, 1/5) ≥ 0` needs `Ã ≥ 0.27` (`star3Cex_not_star`). The model is the
  model of record (DEC-186); a Riemannian dumbbell is expected to behave alike (not formalized).
* **Correction.** Every other step holds as printed (eq:binom, the interpolations, eq:Dbound,
  cases (i) and (iii)); for `C_SP X₀ ≤ 2` one has `n₆ = C_SP X₀`, `X²G(X₀)` bounds the right side
  of eq:binom for `X < X₀`, and eq:star holds with the restricted minimum (`thm_star3_corrected`).
* **Signed form.** The proof uses `u ≥ 0` only for `t ∈ [0,1]`; with `|t|` for `t` every step
  holds, so eq:star holds for every `u` with the same constant (`StarIneqSigned`).
* `λ₁` is formalized as the best Poincaré constant `sup{λ > 0 : λ‖v − v̄‖² ≤ ‖∇v‖² ∀ v}`, equal
  to `inf ‖∇v‖²/‖v − v̄‖²` (`lambda1_eq_sInf_rayleigh`); the model carries no Laplacian, so the
  spectral reading "first non-zero Neumann eigenvalue" is not formalized.
* "min" in eq:Atil is read as an infimum (`sInf`), equal to the min whenever it exists.
* `|t| ≤ 1` (eq:t, "by Hölder") is proved from eq:binom and the convexity of `x ↦ x⁶`.
* The numerics of l.657–664 are not formalized.
* Junk values of the model (`normSq`, `dirichlet` are `0` when infinite, `Yamabe.Quotient`) enter
  only through `IsPoincareConst`, `IsSobolevPoincareConst`: an instance must take `D` among
  finite-energy functions (kb 0002), as the paper's `W^{1,2}(Σ)` is.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Matrix

noncomputable section

namespace Yamabe

/-! ## 1. The constants of eq:Atil -/

section Constants

/-- `n₂ = X₀ / √λ₁` (l.612). -/
def star3N2 (lam X0 : ℝ) : ℝ := X0 / Real.sqrt lam

/-- `n₆ = min {C_SP X₀, 2}` (l.612). -/
def star3N6 (C X0 : ℝ) : ℝ := min (C * X0) 2

/-- `G(X₀)` (l.613–617), as printed. -/
def star3G (V lam C X0 : ℝ) : ℝ :=
  1 / X0 ^ 2 * (15 * V ^ (-(2 / 3 : ℝ)) * star3N2 lam X0 ^ 2
    + 20 * V ^ (-(1 / 2 : ℝ)) * star3N2 lam X0 ^ (3 / 2 : ℝ) * star3N6 C X0 ^ (3 / 2 : ℝ)
    + 15 * V ^ (-(1 / 3 : ℝ)) * star3N2 lam X0 * star3N6 C X0 ^ 3
    + 6 * V ^ (-(1 / 6 : ℝ)) * star3N2 lam X0 ^ (1 / 2 : ℝ) * star3N6 C X0 ^ (9 / 2 : ℝ)
    + star3N6 C X0 ^ 6)

/-- The coefficient of eq:Atil at `(X₀, t₀)` (l.607–610). -/
def star3Coeff (V lam C X0 t0 : ℝ) : ℝ :=
  max (1 / X0 ^ 2) (max (star3G V lam C X0 / (1 + t0 ^ 2 + t0 ^ 4)) (C ^ 2 / (1 - t0) ^ 2))

/-- eq:Atil as printed (l.607): the min over `X₀ > 0`, `t₀ ∈ [0,1)`, read as an infimum. -/
def star3Atil (V lam C : ℝ) : ℝ :=
  sInf {A | ∃ X0 t0 : ℝ, 0 < X0 ∧ 0 ≤ t0 ∧ t0 < 1 ∧ star3Coeff V lam C X0 t0 = A}

/-- eq:Atil corrected: the same min over `X₀ ∈ (0, 2/C_SP]`, read as an infimum. -/
def star3AtilCorr (V lam C : ℝ) : ℝ :=
  sInf {A | ∃ X0 t0 : ℝ, 0 < X0 ∧ C * X0 ≤ 2 ∧ 0 ≤ t0 ∧ t0 < 1 ∧ star3Coeff V lam C X0 t0 = A}

/-- The right-hand side of eq:binom after the interpolations, in `ω = V^{-1/6}`,
`α = ‖v‖₂^{1/2}`, `β = ‖v‖₆^{1/2}`: `X₀² G(X₀) = Φ(ω, √n₂, √n₆)` (`star3G_eq`). -/
def star3Phi (ω α β : ℝ) : ℝ :=
  15 * ω ^ 4 * α ^ 4 + 20 * ω ^ 3 * α ^ 3 * β ^ 3 + 15 * ω ^ 2 * α ^ 2 * β ^ 6
    + 6 * ω * α * β ^ 9 + β ^ 12

lemma star3Coeff_nonneg (V lam C X0 t0 : ℝ) : 0 ≤ star3Coeff V lam C X0 t0 :=
  le_trans (by positivity) (le_max_left _ _)

lemma star3Phi_mono {ω α β ω' α' β' : ℝ} (hω : 0 ≤ ω) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (h1 : ω ≤ ω') (h2 : α ≤ α') (h3 : β ≤ β') : star3Phi ω α β ≤ star3Phi ω' α' β' := by
  have hω' : 0 ≤ ω' := hω.trans h1
  have hα' : 0 ≤ α' := hα.trans h2
  have hβ' : 0 ≤ β' := hβ.trans h3
  unfold star3Phi
  gcongr

lemma star3Phi_scale {ω α β s : ℝ} (hω : 0 ≤ ω) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : star3Phi ω (s * α) (s * β) ≤ s ^ 4 * star3Phi ω α β := by
  have T2 : 0 ≤ 20 * ω ^ 3 * α ^ 3 * β ^ 3 := by positivity
  have T3 : 0 ≤ 15 * ω ^ 2 * α ^ 2 * β ^ 6 := by positivity
  have T4 : 0 ≤ 6 * ω * α * β ^ 9 := by positivity
  have T5 : 0 ≤ β ^ 12 := by positivity
  have k2 := mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0 hs1 (by norm_num : 4 ≤ 6)) T2
  have k3 := mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0 hs1 (by norm_num : 4 ≤ 8)) T3
  have k4 := mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0 hs1 (by norm_num : 4 ≤ 10)) T4
  have k5 := mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0 hs1 (by norm_num : 4 ≤ 12)) T5
  have e1 : star3Phi ω (s * α) (s * β) = s ^ 4 * (15 * ω ^ 4 * α ^ 4) + s ^ 6 * (20 * ω ^ 3 * α ^ 3 * β ^ 3)
      + s ^ 8 * (15 * ω ^ 2 * α ^ 2 * β ^ 6) + s ^ 10 * (6 * ω * α * β ^ 9) + s ^ 12 * β ^ 12 := by
    unfold star3Phi; ring
  have e2 : s ^ 4 * star3Phi ω α β = s ^ 4 * (15 * ω ^ 4 * α ^ 4) + s ^ 4 * (20 * ω ^ 3 * α ^ 3 * β ^ 3)
      + s ^ 4 * (15 * ω ^ 2 * α ^ 2 * β ^ 6) + s ^ 4 * (6 * ω * α * β ^ 9) + s ^ 4 * β ^ 12 := by
    unfold star3Phi; ring
  rw [e1, e2]; linarith

lemma rpow_div_two_eq_sqrt_pow {y : ℝ} (hy : 0 ≤ y) (k : ℕ) : y ^ ((k : ℝ) / 2) = Real.sqrt y ^ k := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy]
  congr 1; ring

lemma inv_rpow_sixth_pow {V : ℝ} (hV : 0 < V) (k : ℕ) :
    ((V ^ (1 / 6 : ℝ))⁻¹) ^ k = V ^ (-((k : ℝ) / 6)) := by
  rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hV.le, ← Real.rpow_neg hV.le]
  congr 1; ring

/-- `X₀² G(X₀) = Φ(V^{-1/6}, √n₂, √n₆)`. -/
lemma star3G_eq {V lam C X0 : ℝ} (hV : 0 < V) (hC : 0 ≤ C) (hX0 : 0 < X0) :
    star3G V lam C X0 = 1 / X0 ^ 2 *
      star3Phi (V ^ (1 / 6 : ℝ))⁻¹ (Real.sqrt (star3N2 lam X0)) (Real.sqrt (star3N6 C X0)) := by
  have h2 : 0 ≤ star3N2 lam X0 := div_nonneg hX0.le (Real.sqrt_nonneg _)
  have h6 : 0 ≤ star3N6 C X0 := le_min (mul_nonneg hC hX0.le) (by norm_num)
  have a1 : V ^ (-(2 / 3 : ℝ)) = ((V ^ (1 / 6 : ℝ))⁻¹) ^ 4 := by rw [inv_rpow_sixth_pow hV]; norm_num
  have a2 : V ^ (-(1 / 2 : ℝ)) = ((V ^ (1 / 6 : ℝ))⁻¹) ^ 3 := by rw [inv_rpow_sixth_pow hV]; norm_num
  have a3 : V ^ (-(1 / 3 : ℝ)) = ((V ^ (1 / 6 : ℝ))⁻¹) ^ 2 := by rw [inv_rpow_sixth_pow hV]; norm_num
  have a4 : V ^ (-(1 / 6 : ℝ)) = ((V ^ (1 / 6 : ℝ))⁻¹) ^ 1 := by rw [inv_rpow_sixth_pow hV]; norm_num
  have b1 : star3N2 lam X0 ^ (3 / 2 : ℝ) = Real.sqrt (star3N2 lam X0) ^ 3 := by
    rw [← rpow_div_two_eq_sqrt_pow h2]; norm_num
  have b2 : star3N6 C X0 ^ (3 / 2 : ℝ) = Real.sqrt (star3N6 C X0) ^ 3 := by
    rw [← rpow_div_two_eq_sqrt_pow h6]; norm_num
  have b3 : star3N2 lam X0 ^ (1 / 2 : ℝ) = Real.sqrt (star3N2 lam X0) ^ 1 := by
    rw [← rpow_div_two_eq_sqrt_pow h2]; norm_num
  have b4 : star3N6 C X0 ^ (9 / 2 : ℝ) = Real.sqrt (star3N6 C X0) ^ 9 := by
    rw [← rpow_div_two_eq_sqrt_pow h6]; norm_num
  have c2 : star3N2 lam X0 = Real.sqrt (star3N2 lam X0) ^ 2 := (Real.sq_sqrt h2).symm
  have c6 : star3N6 C X0 = Real.sqrt (star3N6 C X0) ^ 2 := (Real.sq_sqrt h6).symm
  unfold star3G star3Phi
  rw [a1, a2, a3, a4, b1, b2, b3, b4]
  set p := Real.sqrt (star3N2 lam X0)
  set q := Real.sqrt (star3N6 C X0)
  rw [c2, c6]
  ring

/-- **Finding (l.635).** `G` is not non-decreasing: `G(4) < G(2)` at `V = λ₁ = C_SP = 1`. -/
theorem star3G_not_monotone : star3G 1 1 1 4 < star3G 1 1 1 2 := by
  rw [star3G_eq one_pos zero_le_one (by norm_num), star3G_eq one_pos zero_le_one (by norm_num)]
  have e4 : star3N2 1 4 = 4 := by norm_num [star3N2]
  have e2 : star3N2 1 2 = 2 := by norm_num [star3N2]
  have f4 : star3N6 1 4 = 2 := by norm_num [star3N6]
  have f2 : star3N6 1 2 = 2 := by norm_num [star3N6]
  have s4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [e4, e2, f4, f2, s4]
  simp only [Real.one_rpow, inv_one]
  set s := Real.sqrt 2 with hs
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 2
  have hslt : s < 2 := by nlinarith
  unfold star3Phi
  have e3 : s ^ 3 = 2 * s := by rw [pow_succ, hs2]
  have e6 : s ^ 6 = 8 := by rw [show s ^ 6 = (s ^ 2) ^ 3 by ring, hs2]; norm_num
  have e9 : s ^ 9 = 16 * s := by rw [show s ^ 9 = (s ^ 2) ^ 4 * s by ring, hs2]; norm_num
  have e10 : s ^ 10 = 32 := by rw [show s ^ 10 = (s ^ 2) ^ 5 by ring, hs2]; norm_num
  have e12 : s ^ 12 = 64 := by rw [show s ^ 12 = (s ^ 2) ^ 6 by ring, hs2]; norm_num
  have e4' : s ^ 4 = 4 := by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]; norm_num
  rw [e3, e6, e9, e12, e4', hs2]
  nlinarith

end Constants

/-! ## 2. The analytic steps on a finite measure: eq:binom, the interpolations, the three cases -/

section Analysis

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma integrable_pow_of_memLp_six [IsFiniteMeasure ν] {v : X → ℝ} (hv : MemLp v 6 ν) {k : ℕ}
    (hk : k ≤ 6) : Integrable (fun x => v x ^ k) ν := by
  have hk' : MemLp v (k : ℝ≥0∞) ν := hv.mono_exponent (by exact_mod_cast hk)
  refine hk'.integrable_norm_pow'.mono' (hv.1.pow k) (ae_of_all _ fun x => ?_)
  simp [norm_pow]

/-- `‖f‖_{L⁶}` through the integral. -/
lemma toReal_eLpNorm_six {f : X → ℝ} (hf : MemLp f 6 ν) :
    (eLpNorm f 6 ν).toReal = (∫ x, f x ^ 6 ∂ν) ^ (1 / 6 : ℝ) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h6 : (6 : ℝ≥0∞).toReal = 6 := by norm_num
  have hpt : ∀ x, ‖f x‖ ^ (6 : ℝ) = f x ^ 6 := fun x => by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.norm_eq_abs,
      Even.pow_abs ⟨3, rfl⟩]
  rw [h6]
  simp_rw [hpt]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _)]
  norm_num

lemma normSq_six {f : X → ℝ} (hf : MemLp f 6 ν) :
    normSq ν 6 f = (∫ x, f x ^ 6 ∂ν) ^ (1 / 3 : ℝ) := by
  unfold normSq
  rw [ENNReal.ofReal_ofNat, toReal_eLpNorm_six hf, ← Real.rpow_natCast,
    ← Real.rpow_mul (integral_nonneg fun x => by positivity)]
  norm_num

/-- Linearity for a polynomial in `v`. -/
lemma integral_poly {v : X → ℝ} (c : ℕ → ℝ) (n : ℕ)
    (hint : ∀ k ≤ n, Integrable (fun x => v x ^ k) ν) :
    ∫ x, ∑ k ∈ Finset.range (n + 1), c k * v x ^ k ∂ν =
      ∑ k ∈ Finset.range (n + 1), c k * ∫ x, v x ^ k ∂ν := by
  rw [integral_finsetSum _ (fun k hk => (hint k (by
    have := Finset.mem_range.mp hk; omega)).const_mul (c k))]
  simp only [integral_const_mul]

/-- eq:binom (l.623–627): `∫u⁶ − V ū⁶ = 15ū⁴∫v² + 20ū³∫v³ + 15ū²∫v⁴ + 6ū∫v⁵ + ∫v⁶`,
`v = u − ū`, `∫ v = 0`; and the right-hand side is `∫` of a nonnegative function. -/
theorem star3_binom [IsFiniteMeasure ν] (hV : 0 < (ν Set.univ).toReal) {w : X → ℝ}
    (hw : MemLp w 6 ν) {m : ℝ} (hm : m = (∫ y, w y ∂ν) / (ν Set.univ).toReal) :
    ∫ x, w x ^ 6 ∂ν - (ν Set.univ).toReal * m ^ 6 =
      15 * m ^ 4 * ∫ x, (w x - m) ^ 2 ∂ν + 20 * m ^ 3 * ∫ x, (w x - m) ^ 3 ∂ν
        + 15 * m ^ 2 * ∫ x, (w x - m) ^ 4 ∂ν + 6 * m * ∫ x, (w x - m) ^ 5 ∂ν
        + ∫ x, (w x - m) ^ 6 ∂ν := by
  have hvL : MemLp (fun x => w x - m) 6 ν := hw.sub (memLp_const m)
  have hint : ∀ k ≤ 6, Integrable (fun x => (w x - m) ^ k) ν :=
    fun k hk => integrable_pow_of_memLp_six hvL hk
  have hwi : Integrable w ν := by simpa using integrable_pow_of_memLp_six hw (k := 1) (by norm_num)
  have hv0 : ∫ x, (w x - m) ∂ν = 0 := by
    rw [integral_sub hwi (integrable_const m), integral_const, smul_eq_mul, measureReal_def, hm]
    field_simp
    ring
  have hpt : (fun x => w x ^ 6) = fun x => ∑ k ∈ Finset.range (6 + 1),
      ((Nat.choose 6 k : ℝ) * m ^ (6 - k)) * (w x - m) ^ k := by
    funext x
    have : w x = (w x - m) + m := by ring
    rw [this, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring_nf
  rw [hpt, integral_poly _ 6 hint]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, hv0,
    integral_const, smul_eq_mul, measureReal_def]
  norm_num [Nat.choose]
  ring


/-- Cauchy–Schwarz for nonnegative real functions. -/
lemma integral_mul_le_sqrt_mul_sqrt {f h : X → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hh0 : ∀ x, 0 ≤ h x)
    (hf : MemLp f 2 ν) (hh : MemLp h 2 ν) :
    ∫ x, f x * h x ∂ν ≤ Real.sqrt (∫ x, f x ^ 2 ∂ν) * Real.sqrt (∫ x, h x ^ 2 ∂ν) := by
  have := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := ν) Real.HolderConjugate.two_two
    (ae_of_all _ hf0) (ae_of_all _ hh0) (by simpa using hf) (by simpa using hh)
  simpa [Real.sqrt_eq_rpow, Real.rpow_two] using this

/-- The interpolations in the variables `α = (∫v²)^{1/4}`, `β = (∫v⁶)^{1/12}`. -/
lemma star3_interp_ab [IsFiniteMeasure ν] {v : X → ℝ} (hv : MemLp v 6 ν) :
    ∫ x, |v x| ^ 3 ∂ν ≤ ((∫ x, v x ^ 2 ∂ν) ^ (1 / 4 : ℝ)) ^ 3 * ((∫ x, v x ^ 6 ∂ν) ^ (1 / 12 : ℝ)) ^ 3 ∧
    ∫ x, v x ^ 4 ∂ν ≤ ((∫ x, v x ^ 2 ∂ν) ^ (1 / 4 : ℝ)) ^ 2 * ((∫ x, v x ^ 6 ∂ν) ^ (1 / 12 : ℝ)) ^ 6 ∧
    ∫ x, |v x| ^ 5 ∂ν ≤ ((∫ x, v x ^ 2 ∂ν) ^ (1 / 4 : ℝ)) * ((∫ x, v x ^ 6 ∂ν) ^ (1 / 12 : ℝ)) ^ 9 := by
  set I2 := ∫ x, v x ^ 2 ∂ν with hI2
  set I4 := ∫ x, v x ^ 4 ∂ν with hI4
  set I6 := ∫ x, v x ^ 6 ∂ν with hI6
  have hI2n : 0 ≤ I2 := integral_nonneg fun x => by positivity
  have hI4n : 0 ≤ I4 := integral_nonneg fun x => by positivity
  have hI6n : 0 ≤ I6 := integral_nonneg fun x => by positivity
  set α := I2 ^ (1 / 4 : ℝ) with hα
  set β := I6 ^ (1 / 12 : ℝ) with hβ
  have hα0 : 0 ≤ α := Real.rpow_nonneg hI2n _
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hI6n _
  have hαs : Real.sqrt I2 = α ^ 2 := by
    rw [hα, ← Real.rpow_natCast, ← Real.rpow_mul hI2n, Real.sqrt_eq_rpow]; norm_num
  have hβs : Real.sqrt I6 = β ^ 6 := by
    rw [hβ, ← Real.rpow_natCast, ← Real.rpow_mul hI6n, Real.sqrt_eq_rpow]; norm_num
  have hm : AEStronglyMeasurable (fun x => |v x|) ν := continuous_abs.comp_aestronglyMeasurable hv.1
  have hint : ∀ k ≤ 6, Integrable (fun x => v x ^ k) ν :=
    fun k hk => integrable_pow_of_memLp_six hv hk
  have L1 : MemLp (fun x => |v x|) 2 ν := (memLp_two_iff_integrable_sq hm).2 (by simpa using hint 2 (by norm_num))
  have L3 : MemLp (fun x => |v x| ^ 3) 2 ν := (memLp_two_iff_integrable_sq (hm.pow 3)).2 (by
    refine (hint 6 le_rfl).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.pow_apply]
    rw [← pow_mul, Even.pow_abs ⟨3, rfl⟩])
  have L2 : MemLp (fun x => v x ^ 2) 2 ν := (memLp_two_iff_integrable_sq (hv.1.pow 2)).2 (by
    refine (hint 4 (by norm_num)).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.pow_apply]
    rw [← pow_mul])
  -- I4 ≤ √I2 √I6
  have k4 : I4 ≤ Real.sqrt I2 * Real.sqrt I6 := by
    have h := integral_mul_le_sqrt_mul_sqrt (fun x => abs_nonneg (v x)) (fun x => by positivity) L1 L3
    have e1 : (fun x => |v x| * |v x| ^ 3) = fun x => v x ^ 4 := by
      funext x; rw [← pow_succ', Even.pow_abs ⟨2, rfl⟩]
    have e2 : (fun x => |v x| ^ 2) = fun x => v x ^ 2 := by funext x; rw [sq_abs]
    have e3 : (fun x => (|v x| ^ 3) ^ 2) = fun x => v x ^ 6 := by
      funext x; rw [← pow_mul, Even.pow_abs ⟨3, rfl⟩]
    simp only [e1, e2, e3] at h
    exact h
  have k4' : I4 ≤ α ^ 2 * β ^ 6 := by rw [← hαs, ← hβs]; exact k4
  have hs4 : Real.sqrt I4 ≤ α * β ^ 3 := by
    rw [show α * β ^ 3 = Real.sqrt ((α * β ^ 3) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith [k4'])
  refine ⟨?_, k4', ?_⟩
  · have h := integral_mul_le_sqrt_mul_sqrt (fun x => abs_nonneg (v x)) (fun x => by positivity) L1 L2
    have e1 : (fun x => |v x| * v x ^ 2) = fun x => |v x| ^ 3 := by
      funext x; rw [← sq_abs (v x)]; ring
    have e2 : (fun x => |v x| ^ 2) = fun x => v x ^ 2 := by funext x; rw [sq_abs]
    have e3 : (fun x => (v x ^ 2) ^ 2) = fun x => v x ^ 4 := by funext x; rw [← pow_mul]
    simp only [e1, e2, e3] at h
    calc ∫ x, |v x| ^ 3 ∂ν ≤ Real.sqrt I2 * Real.sqrt I4 := h
      _ ≤ α ^ 2 * (α * β ^ 3) := by rw [hαs]; gcongr
      _ = α ^ 3 * β ^ 3 := by ring
  · have h := integral_mul_le_sqrt_mul_sqrt (fun x => by positivity) (fun x => by positivity) L2 L3
    have e1 : (fun x => v x ^ 2 * |v x| ^ 3) = fun x => |v x| ^ 5 := by
      funext x; rw [← sq_abs (v x)]; ring
    have e3 : (fun x => (v x ^ 2) ^ 2) = fun x => v x ^ 4 := by funext x; rw [← pow_mul]
    have e4 : (fun x => (|v x| ^ 3) ^ 2) = fun x => v x ^ 6 := by
      funext x; rw [← pow_mul, Even.pow_abs ⟨3, rfl⟩]
    simp only [e1, e3, e4] at h
    calc ∫ x, |v x| ^ 5 ∂ν ≤ Real.sqrt I4 * Real.sqrt I6 := h
      _ ≤ (α * β ^ 3) * β ^ 6 := by rw [hβs]; gcongr
      _ = α * β ^ 9 := by ring

/-- The interpolations between `L²` and `L⁶` (l.629–633), as integrals:
`‖v‖₃³ ≤ ‖v‖₂^{3/2}‖v‖₆^{3/2}`, `‖v‖₄⁴ ≤ ‖v‖₂‖v‖₆³`, `‖v‖₅⁵ ≤ ‖v‖₂^{1/2}‖v‖₆^{9/2}`. -/
theorem star3_interp [IsFiniteMeasure ν] {v : X → ℝ} (hv : MemLp v 6 ν) :
    ∫ x, |v x| ^ 3 ∂ν ≤ (∫ x, v x ^ 2 ∂ν) ^ (3 / 4 : ℝ) * (∫ x, v x ^ 6 ∂ν) ^ (1 / 4 : ℝ) ∧
    ∫ x, v x ^ 4 ∂ν ≤ (∫ x, v x ^ 2 ∂ν) ^ (1 / 2 : ℝ) * (∫ x, v x ^ 6 ∂ν) ^ (1 / 2 : ℝ) ∧
    ∫ x, |v x| ^ 5 ∂ν ≤ (∫ x, v x ^ 2 ∂ν) ^ (1 / 4 : ℝ) * (∫ x, v x ^ 6 ∂ν) ^ (3 / 4 : ℝ) := by
  obtain ⟨h3, h4, h5⟩ := star3_interp_ab hv
  have hI2n : 0 ≤ ∫ x, v x ^ 2 ∂ν := integral_nonneg fun x => by positivity
  have hI6n : 0 ≤ ∫ x, v x ^ 6 ∂ν := integral_nonneg fun x => by positivity
  have r : ∀ {y : ℝ}, 0 ≤ y → ∀ (a : ℝ) (k : ℕ), (y ^ a) ^ k = y ^ (a * k) := by
    intro y hy a k; rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  rw [r hI2n, r hI6n] at h3
  rw [r hI2n, r hI6n] at h4
  rw [r hI6n] at h5
  norm_num at h3 h4 h5
  exact ⟨h3, h4, h5⟩

end Analysis

section Core

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- The pointwise convexity behind `t ∈ [-1, 1]`: `(m+v)⁶ − m⁶ − 6m⁵v ≥ 0`. -/
lemma star3_convex (m v : ℝ) :
    0 ≤ 15 * m ^ 4 * v ^ 2 + 20 * m ^ 3 * v ^ 3 + 15 * m ^ 2 * v ^ 4 + 6 * m * v ^ 5 + v ^ 6 := by
  have e : 15 * m ^ 4 * v ^ 2 + 20 * m ^ 3 * v ^ 3 + 15 * m ^ 2 * v ^ 4 + 6 * m * v ^ 5 + v ^ 6 =
      v ^ 2 * ((v ^ 2 + 3 * m * v + 2 * m ^ 2) ^ 2 + 2 * (m * (v + 2 * m)) ^ 2 + 3 * (m ^ 2) ^ 2) := by
    ring
  rw [e]; positivity

/-- The common core of the proof of thm:star3 (l.620–655) for `‖w‖₆ = 1`, `t = V^{1/6} w̄`:
`|t| ≤ 1` (eq:t, Hölder, here from the convexity of `x ↦ x⁶`), eq:binom with the interpolations
(`1 − t⁶ ≤ Φ(V^{-1/6}, ‖v‖₂^{1/2}, ‖v‖₆^{1/2})`), and `1 − |t| ≤ ‖v‖₆ ≤ 1 + |t|` (l.596, l.650). -/
theorem star3_core [IsFiniteMeasure ν] (hV : 0 < (ν Set.univ).toReal)
    {w : X → ℝ} (hw : MemLp w 6 ν) (hw1 : ∫ x, w x ^ 6 ∂ν = 1) {m : ℝ}
    (hm : m = (∫ y, w y ∂ν) / (ν Set.univ).toReal) :
    |(ν Set.univ).toReal ^ (1 / 6 : ℝ) * m| ≤ 1 ∧
    1 - ((ν Set.univ).toReal ^ (1 / 6 : ℝ) * m) ^ 6 ≤
      star3Phi ((ν Set.univ).toReal ^ (1 / 6 : ℝ))⁻¹ ((∫ x, (w x - m) ^ 2 ∂ν) ^ (1 / 4 : ℝ))
        ((∫ x, (w x - m) ^ 6 ∂ν) ^ (1 / 12 : ℝ)) ∧
    1 ≤ |(ν Set.univ).toReal ^ (1 / 6 : ℝ) * m| + (∫ x, (w x - m) ^ 6 ∂ν) ^ (1 / 6 : ℝ) ∧
    (∫ x, (w x - m) ^ 6 ∂ν) ^ (1 / 6 : ℝ) ≤ 1 + |(ν Set.univ).toReal ^ (1 / 6 : ℝ) * m| := by
  set V := (ν Set.univ).toReal with hVdef
  have hvL : MemLp (fun x => w x - m) 6 ν := hw.sub (memLp_const m)
  have hint : ∀ k ≤ 6, Integrable (fun x => (w x - m) ^ k) ν :=
    fun k hk => integrable_pow_of_memLp_six hvL hk
  set I2 := ∫ x, (w x - m) ^ 2 ∂ν with hI2
  set I3 := ∫ x, (w x - m) ^ 3 ∂ν with hI3
  set I4 := ∫ x, (w x - m) ^ 4 ∂ν with hI4
  set I5 := ∫ x, (w x - m) ^ 5 ∂ν with hI5
  set I6 := ∫ x, (w x - m) ^ 6 ∂ν with hI6
  have hbin : 1 - V * m ^ 6 = 15 * m ^ 4 * I2 + 20 * m ^ 3 * I3 + 15 * m ^ 2 * I4
      + 6 * m * I5 + I6 := by
    rw [← hw1]; exact star3_binom hV hw hm
  -- the right-hand side of eq:binom is nonnegative (convexity of `x ↦ x⁶`)
  have hQ : 0 ≤ 15 * m ^ 4 * I2 + 20 * m ^ 3 * I3 + 15 * m ^ 2 * I4 + 6 * m * I5 + I6 := by
    have hlin := integral_poly (ν := ν) (v := fun x => w x - m)
      (fun k => if k = 2 then 15 * m ^ 4 else if k = 3 then 20 * m ^ 3 else if k = 4 then
        15 * m ^ 2 else if k = 5 then 6 * m else if k = 6 then 1 else 0) 6 hint
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hlin
    norm_num at hlin
    rw [← hI2, ← hI3, ← hI4, ← hI5, ← hI6] at hlin
    rw [← hlin]
    exact integral_nonneg fun x => by
      simp only [Pi.zero_apply]; exact star3_convex m (w x - m)
  -- the interpolations
  obtain ⟨h3, h4, h5⟩ := star3_interp_ab hvL
  have hI2n : 0 ≤ I2 := integral_nonneg fun x => by positivity
  have hI4n : 0 ≤ I4 := integral_nonneg fun x => by positivity
  have hI6n : 0 ≤ I6 := integral_nonneg fun x => by positivity
  set α := I2 ^ (1 / 4 : ℝ) with hα
  set β := I6 ^ (1 / 12 : ℝ) with hβ
  have hα0 : 0 ≤ α := Real.rpow_nonneg hI2n _
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hI6n _
  have hα4 : α ^ 4 = I2 := by
    rw [hα, ← Real.rpow_natCast, ← Real.rpow_mul hI2n]; norm_num
  have hβ12 : β ^ 12 = I6 := by
    rw [hβ, ← Real.rpow_natCast, ← Real.rpow_mul hI6n]; norm_num
  have hβ2 : β ^ 2 = I6 ^ (1 / 6 : ℝ) := by
    rw [hβ, ← Real.rpow_natCast, ← Real.rpow_mul hI6n]; norm_num
  have hI3a : |I3| ≤ α ^ 3 * β ^ 3 :=
    (abs_integral_le_integral_abs).trans (by simpa [abs_pow] using h3)
  have hI5a : |I5| ≤ α * β ^ 9 :=
    (abs_integral_le_integral_abs).trans (by simpa [abs_pow] using h5)
  -- t
  have hV6 : 0 < V ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hV _
  have hV6pow : (V ^ (1 / 6 : ℝ)) ^ 6 = V := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV.le]; norm_num
  set t := V ^ (1 / 6 : ℝ) * m with ht
  have ht6 : t ^ 6 = V * m ^ 6 := by rw [ht, mul_pow, hV6pow]
  have htabs : |t| ≤ 1 := by
    have h6 : |t| ^ 6 ≤ 1 := by rw [Even.pow_abs ⟨3, rfl⟩, ht6]; linarith
    exact (pow_le_one_iff_of_nonneg (abs_nonneg t) (by norm_num)).mp h6
  set ω := (V ^ (1 / 6 : ℝ))⁻¹ with hω
  have hω0 : 0 ≤ ω := inv_nonneg.mpr hV6.le
  have hmω : |m| ≤ ω := by
    have e : |m| = |t| / V ^ (1 / 6 : ℝ) := by
      rw [ht, abs_mul, abs_of_pos hV6]; field_simp
    rw [e, hω, ← one_div]
    exact div_le_div_of_nonneg_right htabs hV6.le
  -- 1 − t⁶ ≤ Φ(ω, α, β)
  have hPhi : 1 - t ^ 6 ≤ star3Phi ω α β := by
    rw [ht6, hbin]
    have hm2 : m ^ 2 ≤ ω ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg m) hmω 2
    have hm4 : m ^ 4 ≤ ω ^ 4 := by
      rw [← Even.pow_abs ⟨2, rfl⟩]; exact pow_le_pow_left₀ (abs_nonneg m) hmω 4
    have hm3 : |m| ^ 3 ≤ ω ^ 3 := pow_le_pow_left₀ (abs_nonneg m) hmω 3
    have A2 : 15 * m ^ 4 * I2 ≤ 15 * ω ^ 4 * α ^ 4 := by
      rw [← hα4]; have := mul_le_mul_of_nonneg_right hm4 (by positivity : (0:ℝ) ≤ α ^ 4); linarith
    have A3 : 20 * m ^ 3 * I3 ≤ 20 * ω ^ 3 * α ^ 3 * β ^ 3 := by
      calc 20 * m ^ 3 * I3 ≤ |20 * m ^ 3 * I3| := le_abs_self _
        _ = 20 * |m| ^ 3 * |I3| := by rw [abs_mul, abs_mul, abs_pow]; norm_num
        _ ≤ 20 * ω ^ 3 * (α ^ 3 * β ^ 3) := by gcongr
        _ = 20 * ω ^ 3 * α ^ 3 * β ^ 3 := by ring
    have A4 : 15 * m ^ 2 * I4 ≤ 15 * ω ^ 2 * α ^ 2 * β ^ 6 := by
      calc 15 * m ^ 2 * I4 ≤ 15 * ω ^ 2 * (α ^ 2 * β ^ 6) := by gcongr
        _ = 15 * ω ^ 2 * α ^ 2 * β ^ 6 := by ring
    have A5 : 6 * m * I5 ≤ 6 * ω * α * β ^ 9 := by
      calc 6 * m * I5 ≤ |6 * m * I5| := le_abs_self _
        _ = 6 * |m| * |I5| := by rw [abs_mul, abs_mul]; norm_num
        _ ≤ 6 * ω * (α * β ^ 9) := by gcongr
        _ = 6 * ω * α * β ^ 9 := by ring
    unfold star3Phi
    rw [← hβ12] at *
    linarith
  -- Minkowski: `1 = ‖w‖₆ ≤ ‖v‖₆ + ‖ū‖₆ = β² + |t|`
  have hmink : 1 ≤ |t| + β ^ 2 := by
    have hsplit : w = (fun x => w x - m) + (fun _ => m) := by funext x; simp
    have h := eLpNorm_add_le (p := 6) hvL.1 (aestronglyMeasurable_const (b := m)) (by norm_num)
    rw [← hsplit] at h
    have hfin1 : eLpNorm (fun x => w x - m) 6 ν ≠ ∞ := hvL.eLpNorm_ne_top
    have hfin2 : eLpNorm (fun _ : X => m) 6 ν ≠ ∞ := (memLp_const m).eLpNorm_ne_top
    have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩) h
    rw [ENNReal.toReal_add hfin1 hfin2, toReal_eLpNorm_six hw, hw1, toReal_eLpNorm_six hvL,
      toReal_eLpNorm_six (memLp_const m), Real.one_rpow] at h'
    have hc : ∫ _ : X, m ^ 6 ∂ν = |t| ^ 6 := by
      rw [integral_const, smul_eq_mul, measureReal_def, Even.pow_abs ⟨3, rfl⟩, ht6]
    rw [hc, show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (abs_nonneg t) (by norm_num)] at h'
    rw [hβ2]
    rw [show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
    linarith
  -- the reverse bound `‖v‖₆ ≤ ‖w‖₆ + ‖w̄‖₆ = 1 + |t|` (l.596)
  have hrev : β ^ 2 ≤ 1 + |t| := by
    have h := eLpNorm_sub_le (p := 6) hw.1 (aestronglyMeasurable_const (b := m)) (by norm_num)
    have hsplit : (fun x => w x - m) = w - fun _ => m := by funext x; simp
    rw [← hsplit] at h
    have hfin1 : eLpNorm w 6 ν ≠ ∞ := hw.eLpNorm_ne_top
    have hfin2 : eLpNorm (fun _ : X => m) 6 ν ≠ ∞ := (memLp_const m).eLpNorm_ne_top
    have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩) h
    rw [ENNReal.toReal_add hfin1 hfin2, toReal_eLpNorm_six hw, hw1, toReal_eLpNorm_six hvL,
      toReal_eLpNorm_six (memLp_const m), Real.one_rpow] at h'
    have hc : ∫ _ : X, m ^ 6 ∂ν = |t| ^ 6 := by
      rw [integral_const, smul_eq_mul, measureReal_def, Even.pow_abs ⟨3, rfl⟩, ht6]
    rw [hc, show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.pow_rpow_inv_natCast (abs_nonneg t) (by norm_num)] at h'
    rw [hβ2, show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
    linarith
  exact ⟨htabs, hPhi, by rw [← hβ2]; exact hmink, by rw [← hβ2]; exact hrev⟩

/-- eq:Dbound (l.637–640), as printed: `D = 1 − t² ≤ G(X) X² / (1 + t² + t⁴)` for `‖w‖₆ = 1`,
with `G` evaluated at `X = ‖∇w‖₂ = √E` itself, the cap `n₆ = min{C_SP X, 2}` included. -/
theorem star3_Dbound [IsFiniteMeasure ν] (hV : 0 < (ν Set.univ).toReal)
    {w : X → ℝ} (hw : MemLp w 6 ν) (hw1 : ∫ x, w x ^ 6 ∂ν = 1)
    {E lam C : ℝ} (hE : 0 < E) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hP : lam * ∫ x, (w x - (∫ y, w y ∂ν) / (ν Set.univ).toReal) ^ 2 ∂ν ≤ E)
    (hS : (∫ x, (w x - (∫ y, w y ∂ν) / (ν Set.univ).toReal) ^ 6 ∂ν) ^ (1 / 6 : ℝ) ≤
      C * Real.sqrt E) :
    1 - ((ν Set.univ).toReal ^ (1 / 6 : ℝ) * ((∫ x, w x ∂ν) / (ν Set.univ).toReal)) ^ 2 ≤
      star3G (ν Set.univ).toReal lam C (Real.sqrt E) * Real.sqrt E ^ 2 /
        (1 + ((ν Set.univ).toReal ^ (1 / 6 : ℝ) * ((∫ x, w x ∂ν) / (ν Set.univ).toReal)) ^ 2 +
          ((ν Set.univ).toReal ^ (1 / 6 : ℝ) * ((∫ x, w x ∂ν) / (ν Set.univ).toReal)) ^ 4) := by
  obtain ⟨htabs, hPhi, -, hrev⟩ := star3_core hV hw hw1 rfl
  set V := (ν Set.univ).toReal with hVdef
  set m := (∫ y, w y ∂ν) / V with hm
  set I2 := ∫ x, (w x - m) ^ 2 ∂ν with hI2
  set I6 := ∫ x, (w x - m) ^ 6 ∂ν with hI6
  have hI2n : 0 ≤ I2 := integral_nonneg fun x => by positivity
  have hI6n : 0 ≤ I6 := integral_nonneg fun x => by positivity
  set α := I2 ^ (1 / 4 : ℝ) with hα
  set β := I6 ^ (1 / 12 : ℝ) with hβ
  have hα0 : 0 ≤ α := Real.rpow_nonneg hI2n _
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hI6n _
  have hα4 : α ^ 4 = I2 := by
    rw [hα, ← Real.rpow_natCast, ← Real.rpow_mul hI2n]; norm_num
  have hβ2 : β ^ 2 = I6 ^ (1 / 6 : ℝ) := by
    rw [hβ, ← Real.rpow_natCast, ← Real.rpow_mul hI6n]; norm_num
  rw [← hβ2] at hrev
  have hV6 : 0 < V ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hV _
  set t := V ^ (1 / 6 : ℝ) * m with ht
  set ω := (V ^ (1 / 6 : ℝ))⁻¹ with hω
  have hω0 : 0 ≤ ω := inv_nonneg.mpr hV6.le
  set Xn := Real.sqrt E with hXdef
  have hXpos : 0 < Xn := Real.sqrt_pos.mpr hE
  have hXE : Xn ^ 2 = E := Real.sq_sqrt hE.le
  set n2 := star3N2 lam Xn with hn2
  set n6 := star3N6 C Xn with hn6
  have hn2pos : 0 ≤ n2 := div_nonneg hXpos.le (Real.sqrt_nonneg _)
  have hn6pos : 0 ≤ n6 := le_min (mul_nonneg hC hXpos.le) (by norm_num)
  -- `‖v‖₂ ≤ n₂ = X/√λ₁`, `‖v‖₆ ≤ n₆ = min{C_SP X, 1 + t}` (l.592–596)
  have hα' : α ≤ Real.sqrt n2 := by
    have h : (α ^ 2) ^ 2 ≤ n2 ^ 2 := by
      rw [hn2, star3N2, div_pow, Real.sq_sqrt hlam.le, hXE, ← pow_mul, hα4,
        le_div_iff₀ hlam]
      linarith
    have h' := (pow_le_pow_iff_left₀ (by positivity) hn2pos two_ne_zero).mp h
    rw [← Real.sq_sqrt hn2pos] at h'
    exact (pow_le_pow_iff_left₀ hα0 (Real.sqrt_nonneg _) two_ne_zero).mp h'
  have hβ' : β ≤ Real.sqrt n6 := by
    have h : β ^ 2 ≤ n6 := le_min (by rw [hβ2]; exact hS) (by linarith)
    rw [← Real.sq_sqrt hn6pos] at h
    exact (pow_le_pow_iff_left₀ hβ0 (Real.sqrt_nonneg _) two_ne_zero).mp h
  have hG := star3G_eq (lam := lam) hV hC hXpos
  rw [← hω, ← hn2, ← hn6] at hG
  have hXG : star3Phi ω (Real.sqrt n2) (Real.sqrt n6) = star3G V lam C Xn * Xn ^ 2 := by
    rw [hG]; field_simp
  have k := star3Phi_mono hω0 hα0 hβ0 le_rfl hα' hβ'
  have hP0 : 0 < 1 + t ^ 2 + t ^ 4 := by positivity
  rw [le_div_iff₀ hP0]
  calc (1 - t ^ 2) * (1 + t ^ 2 + t ^ 4) = 1 - t ^ 6 := by ring
    _ ≤ star3G V lam C Xn * Xn ^ 2 := by linarith

/-- The normalized form of the proof of thm:star3 (l.620–655), at one `(X₀, t₀)` with
`C X₀ ≤ 2`: `‖w‖₆ = 1`, `λ ‖w − w̄‖₂² ≤ E`, `‖w − w̄‖₆ ≤ C √E` give `1 ≤ A E + V^{1/3} w̄²`:
the three cases (i)–(iii) of l.641–651. -/
theorem star3_normalized [IsFiniteMeasure ν] (hV : 0 < (ν Set.univ).toReal)
    {w : X → ℝ} (hw : MemLp w 6 ν) (hw1 : ∫ x, w x ^ 6 ∂ν = 1)
    {E lam C X0 t0 : ℝ} (hE : 0 ≤ E) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hX0 : 0 < X0) (hCX0 : C * X0 ≤ 2) (ht0 : 0 ≤ t0) (ht1 : t0 < 1)
    (hP : lam * ∫ x, (w x - (∫ y, w y ∂ν) / (ν Set.univ).toReal) ^ 2 ∂ν ≤ E)
    (hS : (∫ x, (w x - (∫ y, w y ∂ν) / (ν Set.univ).toReal) ^ 6 ∂ν) ^ (1 / 6 : ℝ) ≤
      C * Real.sqrt E) :
    1 ≤ star3Coeff (ν Set.univ).toReal lam C X0 t0 * E +
      (ν Set.univ).toReal ^ (1 / 3 : ℝ) * ((∫ x, w x ∂ν) / (ν Set.univ).toReal) ^ 2 := by
  obtain ⟨htabs, hPhi, hmink, -⟩ := star3_core hV hw hw1 rfl
  set V := (ν Set.univ).toReal with hVdef
  set m := (∫ y, w y ∂ν) / V with hm
  set I2 := ∫ x, (w x - m) ^ 2 ∂ν with hI2
  set I6 := ∫ x, (w x - m) ^ 6 ∂ν with hI6
  have hI2n : 0 ≤ I2 := integral_nonneg fun x => by positivity
  have hI6n : 0 ≤ I6 := integral_nonneg fun x => by positivity
  set α := I2 ^ (1 / 4 : ℝ) with hα
  set β := I6 ^ (1 / 12 : ℝ) with hβ
  have hα0 : 0 ≤ α := Real.rpow_nonneg hI2n _
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hI6n _
  have hα4 : α ^ 4 = I2 := by
    rw [hα, ← Real.rpow_natCast, ← Real.rpow_mul hI2n]; norm_num
  have hβ2 : β ^ 2 = I6 ^ (1 / 6 : ℝ) := by
    rw [hβ, ← Real.rpow_natCast, ← Real.rpow_mul hI6n]; norm_num
  rw [← hβ2] at hmink
  have hV6 : 0 < V ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hV _
  set t := V ^ (1 / 6 : ℝ) * m with ht
  set ω := (V ^ (1 / 6 : ℝ))⁻¹ with hω
  have hω0 : 0 ≤ ω := inv_nonneg.mpr hV6.le
  -- the three cases
  set Xn := Real.sqrt E with hXdef
  have hX : 0 ≤ Xn := Real.sqrt_nonneg E
  have hXE : Xn ^ 2 = E := Real.sq_sqrt hE
  have hSb : β ^ 2 ≤ C * Xn := by rw [hβ2]; exact hS
  set A := star3Coeff V lam C X0 t0 with hA
  have hA1 : 1 / X0 ^ 2 ≤ A := le_max_left _ _
  have hA2 : star3G V lam C X0 / (1 + t0 ^ 2 + t0 ^ 4) ≤ A :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hA3 : C ^ 2 / (1 - t0) ^ 2 ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hT : V ^ (1 / 3 : ℝ) * m ^ 2 = t ^ 2 := by
    rw [ht, mul_pow]; congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV.le]; norm_num
  rw [hT]
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  by_cases hc3 : |t| < t0
  · -- (iii) `t < t₀`: `1 − t₀ < 1 − t ≤ ‖v‖₆ ≤ C_SP X`
    have h1 : 1 - t0 < C * Xn := by linarith
    have h1pos : 0 < 1 - t0 := by linarith
    have h2 : (1 - t0) ^ 2 ≤ C ^ 2 * E := by
      rw [← hXE, ← mul_pow]; exact pow_le_pow_left₀ h1pos.le h1.le 2
    have h3' : 1 ≤ C ^ 2 / (1 - t0) ^ 2 * E := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
    linarith [mul_le_mul_of_nonneg_right hA3 hE]
  · push Not at hc3
    by_cases hc1 : X0 ≤ Xn
    · -- (i) `X ≥ X₀`: `D ≤ 1 ≤ X²/X₀²`
      have h1 : 1 ≤ 1 / X0 ^ 2 * E := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity), one_mul, ← hXE]
        exact pow_le_pow_left₀ hX0.le hc1 2
      linarith [mul_le_mul_of_nonneg_right hA1 hE]
    · -- (ii) `X < X₀`, `t ≥ t₀`
      push Not at hc1
      set n2 := star3N2 lam X0 with hn2
      set n6 := star3N6 C X0 with hn6
      have hn6e : n6 = C * X0 := min_eq_left hCX0
      have hn2pos : 0 ≤ n2 := div_nonneg hX0.le (Real.sqrt_nonneg _)
      have hn6pos : 0 ≤ n6 := by rw [hn6e]; positivity
      set s := Real.sqrt (Xn / X0) with hs
      have hs0 : 0 ≤ s := Real.sqrt_nonneg _
      have hs2 : s ^ 2 = Xn / X0 := Real.sq_sqrt (div_nonneg hX hX0.le)
      have hs1 : s ≤ 1 := Real.sqrt_le_one.mpr ((div_le_one hX0).mpr hc1.le)
      have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
      -- `‖v‖₂ ≤ X/√λ₁ = s² n₂` and `‖v‖₆ ≤ C_SP X = s² n₆`
      have hα2 : (α ^ 2) ^ 2 ≤ (s ^ 2 * n2) ^ 2 := by
        have e : s ^ 2 * n2 = Xn / Real.sqrt lam := by
          rw [hs2, hn2, star3N2]; field_simp
        rw [e, div_pow, Real.sq_sqrt hlam.le, hXE, ← pow_mul, hα4]
        rw [le_div_iff₀ hlam]; linarith
      have hα' : α ≤ s * Real.sqrt n2 := by
        have h := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hα2
        have e : s ^ 2 * n2 = (s * Real.sqrt n2) ^ 2 := by rw [mul_pow, Real.sq_sqrt hn2pos]
        rw [e] at h
        exact (pow_le_pow_iff_left₀ hα0 (by positivity) two_ne_zero).mp h
      have hβ' : β ≤ s * Real.sqrt n6 := by
        have h : β ^ 2 ≤ (s * Real.sqrt n6) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hn6pos, hs2, hn6e]
          calc β ^ 2 ≤ C * Xn := hSb
            _ = Xn / X0 * (C * X0) := by field_simp
        exact (pow_le_pow_iff_left₀ hβ0 (by positivity) two_ne_zero).mp h
      -- `1 − t⁶ ≤ X² G(X₀)`
      have hG := star3G_eq (lam := lam) hV hC hX0
      rw [← hω, ← hn2, ← hn6] at hG
      have hEG : 1 - t ^ 6 ≤ E * star3G V lam C X0 := by
        have k1 := star3Phi_mono hω0 hα0 hβ0 le_rfl hα' hβ'
        have k2 := star3Phi_scale hω0 (Real.sqrt_nonneg n2) (Real.sqrt_nonneg n6) hs0 hs1
        have e : s ^ 4 * star3Phi ω (Real.sqrt n2) (Real.sqrt n6) = E * star3G V lam C X0 := by
          rw [hG, show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2, ← hXE]
          field_simp
        linarith
      -- `D = (1 − t⁶)/(1 + t² + t⁴) ≤ G(X₀) X²/(1 + t₀² + t₀⁴)`
      have hq2 : t0 ^ 2 ≤ t ^ 2 := by
        rw [← sq_abs t]; exact pow_le_pow_left₀ ht0 hc3 2
      have hq4 : t0 ^ 4 ≤ t ^ 4 := by
        rw [← Even.pow_abs ⟨2, rfl⟩ t]; exact pow_le_pow_left₀ ht0 hc3 4
      have ht21 : t ^ 2 ≤ 1 := by
        rw [← sq_abs t]; exact pow_le_one₀ (abs_nonneg t) htabs
      have hP0 : 0 < 1 + t0 ^ 2 + t0 ^ 4 := by positivity
      have hfac : (1 - t ^ 2) * (1 + t ^ 2 + t ^ 4) = 1 - t ^ 6 := by ring
      have hD : 1 - t ^ 2 ≤ star3G V lam C X0 / (1 + t0 ^ 2 + t0 ^ 4) * E := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hP0]
        calc (1 - t ^ 2) * (1 + t0 ^ 2 + t0 ^ 4) ≤ (1 - t ^ 2) * (1 + t ^ 2 + t ^ 4) :=
              mul_le_mul_of_nonneg_left (add_le_add (by linarith : 1 + t0 ^ 2 ≤ 1 + t ^ 2) hq4)
                (sub_nonneg.mpr ht21)
          _ = 1 - t ^ 6 := hfac
          _ ≤ E * star3G V lam C X0 := hEG
          _ = star3G V lam C X0 * E := mul_comm _ _
      linarith [mul_le_mul_of_nonneg_right hA2 hE]

end Core

section Homogeneous

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- The homogeneous form (both sides of eq:star are 2-homogeneous, l.578). -/
theorem star3_integral [IsFiniteMeasure ν] (hV : 0 < (ν Set.univ).toReal)
    {f : X → ℝ} (hf : MemLp f 6 ν)
    {E lam C X0 t0 : ℝ} (hE : 0 ≤ E) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hX0 : 0 < X0) (hCX0 : C * X0 ≤ 2) (ht0 : 0 ≤ t0) (ht1 : t0 < 1)
    (hP : lam * ∫ x, (f x - (∫ y, f y ∂ν) / (ν Set.univ).toReal) ^ 2 ∂ν ≤ E)
    (hS : (∫ x, (f x - (∫ y, f y ∂ν) / (ν Set.univ).toReal) ^ 6 ∂ν) ^ (1 / 6 : ℝ) ≤
      C * Real.sqrt E) :
    (∫ x, f x ^ 6 ∂ν) ^ (1 / 3 : ℝ) ≤ star3Coeff (ν Set.univ).toReal lam C X0 t0 * E +
      (ν Set.univ).toReal ^ (1 / 3 : ℝ) * ((∫ x, f x ∂ν) / (ν Set.univ).toReal) ^ 2 := by
  set V := (ν Set.univ).toReal with hVdef
  set m := (∫ y, f y ∂ν) / V with hm
  set A := star3Coeff V lam C X0 t0 with hA
  set J := ∫ x, f x ^ 6 ∂ν with hJ
  have hA0 : 0 ≤ A := star3Coeff_nonneg _ _ _ _ _
  have hR : 0 ≤ A * E + V ^ (1 / 3 : ℝ) * m ^ 2 :=
    add_nonneg (mul_nonneg hA0 hE) (mul_nonneg (Real.rpow_nonneg hV.le _) (sq_nonneg m))
  have hJ0 : 0 ≤ J := integral_nonneg fun x => by positivity
  rcases hJ0.eq_or_lt with hJz | hJpos
  · rw [← hJz, Real.zero_rpow (by norm_num)]; exact hR
  set c := J ^ (-(1 / 6 : ℝ)) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hJpos _
  have hc6 : c ^ 6 * J = 1 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hJpos.le]
    norm_num
    rw [Real.rpow_neg_one, inv_mul_cancel₀ hJpos.ne']
  have hc2 : c ^ 2 * J ^ (1 / 3 : ℝ) = 1 := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul hJpos.le, ← Real.rpow_add hJpos]
    norm_num
  have hw : MemLp (fun x => c * f x) 6 ν := hf.const_mul c
  have hw1 : ∫ x, (c * f x) ^ 6 ∂ν = 1 := by
    simp_rw [mul_pow]; rw [integral_const_mul, hc6]
  have hmean : (∫ y, c * f y ∂ν) / V = c * m := by rw [integral_const_mul, hm]; ring
  have hP' : lam * ∫ x, (c * f x - (∫ y, c * f y ∂ν) / V) ^ 2 ∂ν ≤ c ^ 2 * E := by
    rw [hmean]
    have e : ∀ x, (c * f x - c * m) ^ 2 = c ^ 2 * (f x - m) ^ 2 := fun x => by ring
    simp_rw [e]; rw [integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left hP (sq_nonneg c)]
  have hS' : (∫ x, (c * f x - (∫ y, c * f y ∂ν) / V) ^ 6 ∂ν) ^ (1 / 6 : ℝ) ≤
      C * Real.sqrt (c ^ 2 * E) := by
    rw [hmean]
    have e : ∀ x, (c * f x - c * m) ^ 6 = c ^ 6 * (f x - m) ^ 6 := fun x => by ring
    simp_rw [e]
    rw [integral_const_mul, Real.mul_rpow (by positivity) (integral_nonneg fun x => by positivity),
      show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num, Real.pow_rpow_inv_natCast hc0.le (by norm_num),
      Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc0.le]
    rw [show (((6 : ℕ) : ℝ))⁻¹ = (1 / 6 : ℝ) by norm_num]
    nlinarith [mul_le_mul_of_nonneg_left hS hc0.le]
  have key := star3_normalized hV hw hw1 (mul_nonneg (sq_nonneg c) hE) hlam hC hX0 hCX0 ht0 ht1
    hP' hS'
  rw [hmean] at key
  have e : A * (c ^ 2 * E) + V ^ (1 / 3 : ℝ) * (c * m) ^ 2 =
      c ^ 2 * (A * E + V ^ (1 / 3 : ℝ) * m ^ 2) := by ring
  rw [e] at key
  have hJ3 : 0 ≤ J ^ (1 / 3 : ℝ) := Real.rpow_nonneg hJ0 _
  calc J ^ (1 / 3 : ℝ) = J ^ (1 / 3 : ℝ) * 1 := (mul_one _).symm
    _ ≤ J ^ (1 / 3 : ℝ) * (c ^ 2 * (A * E + V ^ (1 / 3 : ℝ) * m ^ 2)) :=
        mul_le_mul_of_nonneg_left key hJ3
    _ = (c ^ 2 * J ^ (1 / 3 : ℝ)) * (A * E + V ^ (1 / 3 : ℝ) * m ^ 2) := by ring
    _ = A * E + V ^ (1 / 3 : ℝ) * m ^ 2 := by rw [hc2, one_mul]

end Homogeneous

/-! ## 3. def:constants and eq:star on the model -/

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : FrameMetric X N)

/-- `v̄ = V⁻¹ ∫_Σ v dV` (l.313). -/
def mean (u : D) : ℝ := (∫ x, M.val u x ∂(M.vol g)) / (M.vol g Set.univ).toReal

/-- The Poincaré inequality with constant `λ`: `‖v − v̄‖²_{L²} ≤ λ⁻¹ ‖∇v‖²_{L²}` (l.321), written
`λ ‖v − v̄‖² ≤ ‖∇v‖²`. -/
def IsPoincareConst (lam : ℝ) : Prop :=
  ∀ v : D, lam * normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v) ≤ M.dirichlet g v

/-- def:constants (1): `λ₁`, the best constant in the Poincaré inequality (l.319–321). -/
def lambda1 : ℝ := sSup {lam : ℝ | 0 < lam ∧ M.IsPoincareConst g lam}

/-- The Sobolev–Poincaré inequality with constant `C`:
`‖v − v̄‖_{L^{p*}} ≤ C ‖∇v‖_{L²}` (l.323). -/
def IsSobolevPoincareConst (C : ℝ) : Prop :=
  ∀ v : D, (eLpNorm (fun x => M.val v x - M.mean g v) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal
    ≤ C * Real.sqrt (M.dirichlet g v)

/-- def:constants (2): `C_SP`, the least Sobolev–Poincaré constant (l.322–324). -/
def Csp : ℝ := sInf {C : ℝ | 0 ≤ C ∧ M.IsSobolevPoincareConst g C}

/-- eq:star (l.184–187) with constant `A`, as printed: for `u ≥ 0`. -/
def StarIneq (A : ℝ) : Prop :=
  ∀ u : D, (∀ x, 0 ≤ M.val u x) →
    normSq (M.vol g) (pStar N) (M.val u) ≤
      A * M.dirichlet g u + (M.vol g Set.univ).toReal ^ (2 / pStar N) * M.mean g u ^ 2

/-- eq:star with constant `A`, for every `u` (the signed form). -/
def StarIneqSigned (A : ℝ) : Prop :=
  ∀ u : D, normSq (M.vol g) (pStar N) (M.val u) ≤
      A * M.dirichlet g u + (M.vol g Set.univ).toReal ^ (2 / pStar N) * M.mean g u ^ 2

lemma StarIneqSigned.starIneq {A : ℝ} (h : M.StarIneqSigned g A) : M.StarIneq g A :=
  fun u _ => h u

/-! ### def:constants: the extremal constants are attained -/

/-- `λ₁ > 0` makes the set of Poincaré constants nonempty and bounded, and `λ₁` is one of them. -/
theorem isPoincareConst_lambda1 (h : 0 < M.lambda1 g) : M.IsPoincareConst g (M.lambda1 g) := by
  have hne : {lam : ℝ | 0 < lam ∧ M.IsPoincareConst g lam}.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have : M.lambda1 g = 0 := by rw [lambda1, hne, Real.sSup_empty]
    linarith
  have hbdd : BddAbove {lam : ℝ | 0 < lam ∧ M.IsPoincareConst g lam} := by
    by_contra hb
    have : M.lambda1 g = 0 := Real.sSup_of_not_bddAbove hb
    linarith
  intro v
  have ha : 0 ≤ normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v) := normSq_nonneg _ _ _
  rcases ha.eq_or_lt with ha0 | hapos
  · rw [← ha0, mul_zero]; exact M.dirichlet_nonneg g v
  · have h' : M.lambda1 g ≤ M.dirichlet g v / normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v) :=
      csSup_le hne fun lam hl => by rw [le_div_iff₀ hapos]; exact hl.2 v
    rwa [le_div_iff₀ hapos] at h'

/-- `λ₁` is the best Poincaré constant. -/
theorem le_lambda1 (h : 0 < M.lambda1 g) {lam : ℝ} (hl : 0 < lam) (hP : M.IsPoincareConst g lam) :
    lam ≤ M.lambda1 g := by
  have hbdd : BddAbove {lam : ℝ | 0 < lam ∧ M.IsPoincareConst g lam} := by
    by_contra hb
    have : M.lambda1 g = 0 := Real.sSup_of_not_bddAbove hb
    linarith
  exact le_csSup hbdd ⟨hl, hP⟩

/-- `λ₁ > 0` as soon as some `λ > 0` is a Poincaré constant and they are bounded. -/
theorem lambda1_pos {lam : ℝ} (hl : 0 < lam) (hP : M.IsPoincareConst g lam)
    (hb : BddAbove {lam : ℝ | 0 < lam ∧ M.IsPoincareConst g lam}) : 0 < M.lambda1 g :=
  lt_of_lt_of_le hl (le_csSup hb ⟨hl, hP⟩)

/-- The Rayleigh form of `λ₁` (the variational reading of "first non-zero Neumann eigenvalue",
l.319): `λ₁ = inf {‖∇v‖² / ‖v − v̄‖² : ‖v − v̄‖ > 0}`. -/
theorem lambda1_eq_sInf_rayleigh (h : 0 < M.lambda1 g) :
    M.lambda1 g = sInf {r : ℝ | ∃ v : D, 0 < normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v) ∧
      r = M.dirichlet g v / normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v)} := by
  set R := {r : ℝ | ∃ v : D, 0 < normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v) ∧
      r = M.dirichlet g v / normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v)} with hR
  have hP := M.isPoincareConst_lambda1 g h
  have hRne : R.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hzero : ∀ v : D, normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v) = 0 := by
      intro v
      by_contra hv
      have hmem : M.dirichlet g v / normSq (M.vol g) 2 (fun x => M.val v x - M.mean g v) ∈ R :=
        ⟨v, lt_of_le_of_ne (normSq_nonneg _ _ _) (Ne.symm hv), rfl⟩
      rw [hne] at hmem
      exact hmem
    have hb : ¬ BddAbove {lam : ℝ | 0 < lam ∧ M.IsPoincareConst g lam} := by
      rintro ⟨B, hB⟩
      have hmem : max B 0 + 1 ∈ {lam : ℝ | 0 < lam ∧ M.IsPoincareConst g lam} :=
        ⟨by positivity, fun v => by rw [hzero v, mul_zero]; exact M.dirichlet_nonneg g v⟩
      have := hB hmem
      linarith [le_max_left B 0]
    have : M.lambda1 g = 0 := Real.sSup_of_not_bddAbove hb
    linarith
  have hRb : BddBelow R := ⟨0, by
    rintro _ ⟨v, hv, rfl⟩; exact div_nonneg (M.dirichlet_nonneg g v) hv.le⟩
  apply le_antisymm
  · refine le_csInf hRne ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [le_div_iff₀ hv]; exact hP v
  · rcases le_or_gt (sInf R) 0 with h0 | h0
    · linarith
    · refine M.le_lambda1 g h h0 fun v => ?_
      rcases (normSq_nonneg (M.vol g) 2 (fun x => M.val v x - M.mean g v)).eq_or_lt with ha | ha
      · rw [← ha, mul_zero]; exact M.dirichlet_nonneg g v
      · have := csInf_le hRb ⟨v, ha, rfl⟩
        rwa [le_div_iff₀ ha] at this

lemma Csp_nonneg : 0 ≤ M.Csp g := Real.sInf_nonneg fun _ hC => hC.1

/-- `C_SP` is a Sobolev–Poincaré constant once there is one. -/
theorem isSobolevPoincareConst_Csp (h : ∃ C, M.IsSobolevPoincareConst g C) :
    M.IsSobolevPoincareConst g (M.Csp g) := by
  obtain ⟨C0, hC0⟩ := h
  have hmem : max C0 0 ∈ {C : ℝ | 0 ≤ C ∧ M.IsSobolevPoincareConst g C} :=
    ⟨le_max_right _ _, fun v => (hC0 v).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))⟩
  intro v
  rcases (Real.sqrt_nonneg (M.dirichlet g v)).eq_or_lt with hs0 | hspos
  · have h1 := hmem.2 v
    rw [← hs0, mul_zero] at h1 ⊢
    exact h1
  · have h' : (eLpNorm (fun x => M.val v x - M.mean g v) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal
        / Real.sqrt (M.dirichlet g v) ≤ M.Csp g :=
      le_csInf ⟨_, hmem⟩ fun C hC => by rw [div_le_iff₀ hspos]; exact hC.2 v
    rwa [div_le_iff₀ hspos] at h'

/-- `C_SP` is the least Sobolev–Poincaré constant. -/
theorem Csp_le {C : ℝ} (hC : 0 ≤ C) (h : M.IsSobolevPoincareConst g C) : M.Csp g ≤ C :=
  csInf_le ⟨0, fun _ hC' => hC'.1⟩ ⟨hC, h⟩

/-! ### thm:star3 -/

/-- The proof of thm:star3 at one `(X₀, t₀)` with `C X₀ ≤ 2`, for any valid constants `λ`, `C`,
and every `u` (signed). -/
theorem star3_point (M : MeasuredModel X D 3 n) (g : FrameMetric X 3) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) {lam C : ℝ} (hlam : 0 < lam)
    (hC : 0 ≤ C) (hP : M.IsPoincareConst g lam) (hS : M.IsSobolevPoincareConst g C)
    {X0 t0 : ℝ} (hX0 : 0 < X0) (hCX0 : C * X0 ≤ 2) (ht0 : 0 ≤ t0) (ht1 : t0 < 1) (u : D) :
    normSq (M.vol g) (pStar 3) (M.val u) ≤
      star3Coeff (M.vol g Set.univ).toReal lam C X0 t0 * M.dirichlet g u +
        (M.vol g Set.univ).toReal ^ (2 / pStar 3) * M.mean g u ^ 2 := by
  have hR : 0 ≤ star3Coeff (M.vol g Set.univ).toReal lam C X0 t0 * M.dirichlet g u +
      (M.vol g Set.univ).toReal ^ (2 / pStar 3) * M.mean g u ^ 2 :=
    add_nonneg (mul_nonneg (star3Coeff_nonneg _ _ _ _ _) (M.dirichlet_nonneg g u))
      (mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (sq_nonneg _))
  have h6 : ENNReal.ofReal (pStar 3) = 6 := by rw [pStar_three]; norm_num
  rcases eq_or_ne (M.vol g) 0 with hν0 | hν0
  · have h0 : normSq (M.vol g) (pStar 3) (M.val u) = 0 := by simp [normSq, hν0]
    rw [h0]; exact hR
  have hV : 0 < (M.vol g Set.univ).toReal :=
    ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hν0) (measure_ne_top _ _)
  by_cases hmem : MemLp (M.val u) 6 (M.vol g)
  · have e1 : normSq (M.vol g) (pStar 3) (M.val u) = normSq (M.vol g) 6 (M.val u) := by
      rw [pStar_three]
    have e2 : (2 : ℝ) / pStar 3 = 1 / 3 := by rw [pStar_three]; norm_num
    rw [e1, normSq_six hmem, e2]
    have hvL : MemLp (fun x => M.val u x - M.mean g u) 6 (M.vol g) := hmem.sub (memLp_const _)
    have hv2 : MemLp (fun x => M.val u x - M.mean g u) 2 (M.vol g) :=
      hvL.mono_exponent (by norm_num)
    have hPu := hP u
    rw [← integral_sq_eq_normSq hv2] at hPu
    have hSu := hS u
    rw [h6, toReal_eLpNorm_six hvL] at hSu
    simp only [mean] at hPu hSu ⊢
    exact star3_integral hV hmem (M.dirichlet_nonneg g u) hlam hC hX0 hCX0 ht0 ht1 hPu hSu
  · have htop : eLpNorm (M.val u) 6 (M.vol g) = ∞ := by
      by_contra hne
      exact hmem ⟨hD u, lt_top_iff_ne_top.mpr hne⟩
    have h0 : normSq (M.vol g) (pStar 3) (M.val u) = 0 := by simp [normSq, h6, htop]
    rw [h0]; exact hR

/-- thm:star3, corrected, for any valid constants (the theorem "holds for any finite values"). -/
theorem star3_of_consts (M : MeasuredModel X D 3 n) (g : FrameMetric X 3)
    [IsFiniteMeasure (M.vol g)] (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g))
    {lam C : ℝ} (hlam : 0 < lam) (hC : 0 ≤ C) (hP : M.IsPoincareConst g lam)
    (hS : M.IsSobolevPoincareConst g C) :
    M.StarIneqSigned g (star3AtilCorr (M.vol g Set.univ).toReal lam C) := by
  intro u
  set V := (M.vol g Set.univ).toReal
  set S := {A | ∃ X0 t0 : ℝ, 0 < X0 ∧ C * X0 ≤ 2 ∧ 0 ≤ t0 ∧ t0 < 1 ∧
    star3Coeff V lam C X0 t0 = A} with hSdef
  have hne : S.Nonempty := ⟨_, 1 / (C + 1), 0, by positivity,
    by rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith, le_rfl, one_pos, rfl⟩
  have hall : ∀ A ∈ S, normSq (M.vol g) (pStar 3) (M.val u) ≤
      A * M.dirichlet g u + V ^ (2 / pStar 3) * M.mean g u ^ 2 := by
    rintro _ ⟨X0, t0, h1, h2, h3, h4, rfl⟩
    exact star3_point M g hD hlam hC hP hS h1 h2 h3 h4 u
  show _ ≤ sInf S * M.dirichlet g u + _
  rcases (M.dirichlet_nonneg g u).eq_or_lt with hE0 | hEpos
  · obtain ⟨A, hA⟩ := hne
    have h1 := hall A hA
    rw [← hE0, mul_zero] at h1 ⊢
    exact h1
  · have h' : (normSq (M.vol g) (pStar 3) (M.val u) - V ^ (2 / pStar 3) * M.mean g u ^ 2) /
        M.dirichlet g u ≤ sInf S :=
      le_csInf hne fun A hA => by rw [div_le_iff₀ hEpos]; linarith [hall A hA]
    rw [div_le_iff₀ hEpos] at h'
    linarith

/-- **thm:star3, corrected** (l.601–618): eq:star holds, for every `u`, with the minimum of
eq:Atil over `X₀ ∈ (0, 2/C_SP]`, `λ₁` and `C_SP` those of def:constants. -/
theorem thm_star3_corrected (M : MeasuredModel X D 3 n) (g : FrameMetric X 3)
    [IsFiniteMeasure (M.vol g)] (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g))
    (hl1 : 0 < M.lambda1 g) (hC : ∃ C, M.IsSobolevPoincareConst g C) :
    M.StarIneqSigned g (star3AtilCorr (M.vol g Set.univ).toReal (M.lambda1 g) (M.Csp g)) :=
  star3_of_consts M g hD hl1 (M.Csp_nonneg g) (M.isPoincareConst_lambda1 g hl1)
    (M.isSobolevPoincareConst_Csp g hC)

/-- thm:star3, corrected, in the printed form `u ≥ 0`. -/
theorem thm_star3_corrected_nonneg (M : MeasuredModel X D 3 n) (g : FrameMetric X 3)
    [IsFiniteMeasure (M.vol g)] (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g))
    (hl1 : 0 < M.lambda1 g) (hC : ∃ C, M.IsSobolevPoincareConst g C) :
    M.StarIneq g (star3AtilCorr (M.vol g Set.univ).toReal (M.lambda1 g) (M.Csp g)) :=
  (thm_star3_corrected M g hD hl1 hC).starIneq

end MeasuredModel

/-! ## 4. The counterexample to the printed thm:star3 -/

section Counterexample

/-- A two-point model, `N = 3`: masses `1/100` at `true`, `99/100` at `false`, the edge
differential `du = (u(true) − u(false), 0, 0)`, the boundary at `false`. -/
def star3CexModel : MeasuredModel Bool (Bool → ℝ) 3 1 where
  μ := ENNReal.ofReal (1 / 100) • Measure.dirac true + ENNReal.ofReal (99 / 100) • Measure.dirac false
  μb := fun _ => Measure.dirac false
  P := fun _ => toyP
  P_injective := fun _ => toyP_injective
  val := LinearMap.id
  tr := LinearMap.id
  d := toyD
  one := fun _ => 1
  val_one := rfl
  tr_one := rfl
  d_one := by
    funext x a
    simp [toyD]

lemma star3Cex_vol : star3CexModel.vol toyMetric =
    ENNReal.ofReal (1 / 100) • Measure.dirac true + ENNReal.ofReal (99 / 100) • Measure.dirac false := by
  simp [MeasuredModel.vol, star3CexModel, toyMetric]

instance star3Cex_fin1 : IsFiniteMeasure (ENNReal.ofReal (1 / 100) • Measure.dirac true) :=
  (Measure.dirac true).smul_finite ENNReal.ofReal_ne_top

instance star3Cex_fin2 : IsFiniteMeasure (ENNReal.ofReal (99 / 100) • Measure.dirac false) :=
  (Measure.dirac false).smul_finite ENNReal.ofReal_ne_top

instance star3Cex_fin : IsFiniteMeasure (star3CexModel.vol toyMetric) := by
  rw [star3Cex_vol]; infer_instance

lemma star3Cex_integral (f : Bool → ℝ) :
    ∫ x, f x ∂(star3CexModel.vol toyMetric) = 1 / 100 * f true + 99 / 100 * f false := by
  rw [star3Cex_vol, integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)]
  simp [smul_eq_mul]

lemma star3Cex_univ : (star3CexModel.vol toyMetric Set.univ).toReal = 1 := by
  have h := star3Cex_integral (fun _ => 1)
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def] at h
  rw [h]; norm_num

lemma star3Cex_mean (u : Bool → ℝ) :
    star3CexModel.mean toyMetric u = 1 / 100 * u true + 99 / 100 * u false := by
  rw [MeasuredModel.mean, star3Cex_univ, div_one]
  exact star3Cex_integral u

lemma star3Cex_dirichlet (u : Bool → ℝ) :
    star3CexModel.dirichlet toyMetric u = (u true - u false) ^ 2 := by
  have hg : ∀ x, star3CexModel.gradSq toyMetric u x = (u true - u false) ^ 2 := by
    intro x
    simp [MeasuredModel.gradSq, star3CexModel, toyMetric, toyD, dotProduct]
    ring
  simp only [MeasuredModel.dirichlet, hg, lintegral_const]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), star3Cex_univ, mul_one]

@[simp] lemma star3Cex_val (u : Bool → ℝ) : star3CexModel.val u = u := rfl

lemma star3Cex_normSq_two (h : Bool → ℝ) :
    normSq (star3CexModel.vol toyMetric) 2 h = 1 / 100 * h true ^ 2 + 99 / 100 * h false ^ 2 := by
  rw [← integral_sq_eq_normSq MemLp.of_discrete]
  exact star3Cex_integral _

lemma star3Cex_toReal_eLpNorm (h : Bool → ℝ) :
    (eLpNorm h (ENNReal.ofReal (pStar 3)) (star3CexModel.vol toyMetric)).toReal =
      (1 / 100 * h true ^ 6 + 99 / 100 * h false ^ 6) ^ (1 / 6 : ℝ) := by
  rw [pStar_three, ENNReal.ofReal_ofNat, toReal_eLpNorm_six MemLp.of_discrete]
  congr 1
  exact star3Cex_integral _

/-- `λ = 100` is a Poincaré constant of the two-point model (`λ₁ = 10⁴/99`). -/
lemma star3Cex_poincare : star3CexModel.IsPoincareConst toyMetric 100 := by
  intro v
  rw [star3Cex_normSq_two, star3Cex_dirichlet]
  simp only [star3Cex_mean, star3Cex_val]
  have e : 100 * (1 / 100 * (v true - (1 / 100 * v true + 99 / 100 * v false)) ^ 2 +
      99 / 100 * (v false - (1 / 100 * v true + 99 / 100 * v false)) ^ 2) =
      99 / 100 * (v true - v false) ^ 2 := by ring
  rw [e]
  nlinarith [sq_nonneg (v true - v false)]

lemma star3Cex_bdd :
    BddAbove {lam : ℝ | 0 < lam ∧ star3CexModel.IsPoincareConst toyMetric lam} := by
  refine ⟨10000 / 99, fun lam hl => ?_⟩
  have h := hl.2 (fun b => if b then 1 else 0)
  rw [star3Cex_normSq_two, star3Cex_dirichlet] at h
  simp only [star3Cex_mean, star3Cex_val] at h
  norm_num at h
  show lam ≤ 10000 / 99
  linarith

lemma star3Cex_lambda1_ge : 100 ≤ star3CexModel.lambda1 toyMetric :=
  le_csSup star3Cex_bdd ⟨by norm_num, star3Cex_poincare⟩

/-- `C = (1/100)^{1/6}` is a Sobolev–Poincaré constant of the two-point model. -/
lemma star3Cex_sp : star3CexModel.IsSobolevPoincareConst toyMetric ((1 / 100 : ℝ) ^ (1 / 6 : ℝ)) := by
  intro v
  rw [star3Cex_toReal_eLpNorm, star3Cex_dirichlet, Real.sqrt_sq_eq_abs]
  simp only [star3Cex_mean, star3Cex_val]
  set δ := v true - v false with hδ
  have e : 1 / 100 * (v true - (1 / 100 * v true + 99 / 100 * v false)) ^ 6 +
      99 / 100 * (v false - (1 / 100 * v true + 99 / 100 * v false)) ^ 6 =
      (1 / 100 * (99 / 100) ^ 6 + 99 / 100 * (1 / 100) ^ 6) * δ ^ 6 := by rw [hδ]; ring
  rw [e]
  have hle : (1 / 100 * (99 / 100) ^ 6 + 99 / 100 * (1 / 100) ^ 6) * δ ^ 6 ≤ 1 / 100 * |δ| ^ 6 := by
    rw [Even.pow_abs ⟨3, rfl⟩]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  calc ((1 / 100 * (99 / 100) ^ 6 + 99 / 100 * (1 / 100) ^ 6) * δ ^ 6) ^ (1 / 6 : ℝ)
      ≤ (1 / 100 * |δ| ^ 6) ^ (1 / 6 : ℝ) := Real.rpow_le_rpow (by positivity) hle (by norm_num)
    _ = (1 / 100 : ℝ) ^ (1 / 6 : ℝ) * |δ| := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
        congr 1
        rw [show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num,
          Real.pow_rpow_inv_natCast (abs_nonneg δ) (by norm_num)]

lemma star3Cex_Csp_sq : star3CexModel.Csp toyMetric ^ 2 ≤ 22 / 100 := by
  have h1 := star3CexModel.Csp_le toyMetric (by positivity) star3Cex_sp
  have h0 := star3CexModel.Csp_nonneg toyMetric
  have h2 : ((1 / 100 : ℝ) ^ (1 / 6 : ℝ)) ^ 2 ≤ 22 / 100 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    calc (1 / 100 : ℝ) ^ ((1 / 6 : ℝ) * ((2 : ℕ) : ℝ)) = (1 / 100 : ℝ) ^ ((3 : ℕ) : ℝ)⁻¹ := by
          norm_num
      _ ≤ ((22 / 100 : ℝ) ^ 3) ^ ((3 : ℕ) : ℝ)⁻¹ :=
          Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = 22 / 100 := Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
  calc star3CexModel.Csp toyMetric ^ 2 ≤ ((1 / 100 : ℝ) ^ (1 / 6 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ ≤ 22 / 100 := h2

lemma star3Cex_G :
    star3G 1 (star3CexModel.lambda1 toyMetric) (star3CexModel.Csp toyMetric) 100000 ≤ 22 / 100 := by
  rw [star3G_eq one_pos (star3CexModel.Csp_nonneg toyMetric) (by norm_num)]
  simp only [Real.one_rpow, inv_one]
  have hl := star3Cex_lambda1_ge
  have hs : 10 ≤ Real.sqrt (star3CexModel.lambda1 toyMetric) := by
    rw [show (10 : ℝ) = Real.sqrt 100 by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hl
  have hn2 : Real.sqrt (star3N2 (star3CexModel.lambda1 toyMetric) 100000) ≤ 100 := by
    have h : star3N2 (star3CexModel.lambda1 toyMetric) 100000 ≤ 100 ^ 2 := by
      rw [star3N2, div_le_iff₀ (by linarith)]; nlinarith
    calc Real.sqrt _ ≤ Real.sqrt (100 ^ 2) := Real.sqrt_le_sqrt h
      _ = 100 := Real.sqrt_sq (by norm_num)
  have hn6 : Real.sqrt (star3N6 (star3CexModel.Csp toyMetric) 100000) ≤ 3 / 2 := by
    have h : star3N6 (star3CexModel.Csp toyMetric) 100000 ≤ (3 / 2) ^ 2 :=
      (min_le_right _ _).trans (by norm_num)
    calc Real.sqrt _ ≤ Real.sqrt ((3 / 2) ^ 2) := Real.sqrt_le_sqrt h
      _ = 3 / 2 := Real.sqrt_sq (by norm_num)
  have hP := star3Phi_mono zero_le_one (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) le_rfl hn2 hn6
  calc 1 / (100000 : ℝ) ^ 2 * star3Phi 1 _ _ ≤ 1 / (100000 : ℝ) ^ 2 * star3Phi 1 100 (3 / 2) :=
        mul_le_mul_of_nonneg_left hP (by positivity)
    _ ≤ 22 / 100 := by norm_num [star3Phi]

lemma star3Cex_Atil :
    star3Atil (star3CexModel.vol toyMetric Set.univ).toReal (star3CexModel.lambda1 toyMetric)
      (star3CexModel.Csp toyMetric) ≤ 22 / 100 := by
  rw [star3Cex_univ]
  calc star3Atil 1 (star3CexModel.lambda1 toyMetric) (star3CexModel.Csp toyMetric)
      ≤ star3Coeff 1 (star3CexModel.lambda1 toyMetric) (star3CexModel.Csp toyMetric) 100000 0 :=
        csInf_le ⟨0, by rintro _ ⟨X0, t0, _, _, _, rfl⟩; exact star3Coeff_nonneg _ _ _ _ _⟩
          ⟨100000, 0, by norm_num, le_rfl, by norm_num, rfl⟩
    _ ≤ 22 / 100 := by
        unfold star3Coeff
        refine max_le (by norm_num) (max_le ?_ ?_)
        · norm_num; linarith [star3Cex_G]
        · norm_num; linarith [star3Cex_Csp_sq]

/-- On the two-point model the hypotheses of thm:star3 hold: `λ₁ > 0`, `C_SP < ∞`. -/
theorem star3Cex_hyps :
    0 < star3CexModel.lambda1 toyMetric ∧ (∃ C, star3CexModel.IsSobolevPoincareConst toyMetric C) :=
  ⟨lt_of_lt_of_le (by norm_num) star3Cex_lambda1_ge, ⟨_, star3Cex_sp⟩⟩

/-- **Finding: thm:star3's printed constant is invalid on the model of record.** On the
two-point model (outside the paper's setting by lem:csp-lower; a Riemannian dumbbell is argued,
not proved), eq:star fails with the
printed `Ã` of eq:Atil, at `u = (1, 1/5) ≥ 0`: `‖u‖²₆ > 0.19 > Ã ‖∇u‖² + V^{1/3} ū²`. -/
theorem star3Cex_not_star :
    ¬ star3CexModel.StarIneq toyMetric
      (star3Atil (star3CexModel.vol toyMetric Set.univ).toReal (star3CexModel.lambda1 toyMetric)
        (star3CexModel.Csp toyMetric)) := by
  intro h
  have hu := h (fun b => if b then 1 else 1 / 5) (fun x => by cases x <;> norm_num)
  have hn : normSq (star3CexModel.vol toyMetric) (pStar 3)
      (star3CexModel.val (fun b => if b then (1 : ℝ) else 1 / 5)) =
      (1 / 100 * 1 + 99 / 100 * (1 / 5) ^ 6) ^ (1 / 3 : ℝ) := by
    rw [pStar_three, star3Cex_val, normSq_six MemLp.of_discrete]
    congr 1
    rw [star3Cex_integral]
    norm_num
  rw [hn, star3Cex_dirichlet, star3Cex_mean, star3Cex_univ, Real.one_rpow, one_mul] at hu
  norm_num at hu
  have hA := star3Cex_Atil
  rw [star3Cex_univ] at hA
  have hJ : (19 / 100 : ℝ) < (1 / 100 * 1 + 99 / 100 * (1 / 5) ^ 6) ^ (1 / 3 : ℝ) := by
    calc (19 / 100 : ℝ) = ((19 / 100 : ℝ) ^ 3) ^ ((3 : ℕ) : ℝ)⁻¹ :=
          (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
      _ < (1 / 100 * 1 + 99 / 100 * (1 / 5) ^ 6) ^ ((3 : ℕ) : ℝ)⁻¹ :=
          Real.rpow_lt_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = (1 / 100 * 1 + 99 / 100 * (1 / 5) ^ 6) ^ (1 / 3 : ℝ) := by norm_num
  norm_num at hJ
  nlinarith

/-- **thm:star3 as printed is false** over the model of record: some model satisfies every
hypothesis (finite volume, measurable functions, `λ₁ > 0`, `C_SP < ∞`) and not eq:star with the
printed `Ã`. -/
theorem thm_star3_printed_false :
    ¬ ∀ (X D : Type) [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] (n : ℕ)
        (M : MeasuredModel X D 3 n) (g : FrameMetric X 3), IsFiniteMeasure (M.vol g) →
        (∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) →
        0 < M.lambda1 g → (∃ C, M.IsSobolevPoincareConst g C) →
        M.StarIneq g (star3Atil (M.vol g Set.univ).toReal (M.lambda1 g) (M.Csp g)) := by
  intro h
  exact star3Cex_not_star (h Bool (Bool → ℝ) 1 star3CexModel toyMetric inferInstance
    (fun _ => (Measurable.of_discrete).aestronglyMeasurable) star3Cex_hyps.1 star3Cex_hyps.2)

end Counterexample

end Yamabe
