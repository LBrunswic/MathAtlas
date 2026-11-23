import Yamabe.Perforated.Main

/-!
# Perforated § 5, general `N`: the elementary inequality, the deficit bound of prop:starN, and eq:star with an explicit `Ã` by the three-branch split, over the measured model

Labels (lines of `papers/perforated/legacy/labeled/perforated.tex`):

* **`lem:elem`** — `perforated.tex:673` (l.673–677, printed without proof): `lem_elem`, with
  the explicit constant `c_q = q² 2^q` (`elemC`, `elem_elemC`).
* `prop:starN` — `perforated.tex:679` (statement l.679–689, proof l.691–704). NOT marked:
  partial, since it carries `0 < λ₁` and a finite `C_SP`, the readings of OQ-109 (see SCOPE):
  `MeasuredModel.prop_starN`.

> \begin{lemma}
> \label{lem:elem}
> For $q\ge2$ there is $c_q<\infty$ with
> $(1+x)^q\le1+qx+c_q\bigl(x^2+|x|^q\bigr)$ for all $x\ge-1$.
> \end{lemma} (l.673–677)

> Let $q=\pstar$ and $c_q$ as in Lemma~\ref{lem:elem}. For $u\ge0$ with
> $\|u\|_{q}=1$ and $t=V^{1/q}\bar u$,
> \[
>   D\;\le\;\tfrac{2}{q}c_q\Bigl[V^{2/q-1}\lambda_1^{-1}X^2
>         +t^{2-q}\,\Csp^{\,q}X^{q}\Bigr],
> \]
> and consequently \eqref{eq:star} holds with an explicit $\Atil$ obtained by the
> same three-branch split as in Theorem~\ref{thm:star3}. (l.681–688)

> Apply Lemma~\ref{lem:elem} with $x=v/\bar u$ and integrate:
> $\int u^q\le\bar u^qV+c_q\bigl(\bar u^{q-2}\|v\|_2^2+\|v\|_q^q\bigr)$, the linear
> term vanishing. Since $2/q\le1$, concavity gives
> $(A+B)^{2/q}\le A^{2/q}+\tfrac2qA^{2/q-1}B$ for $A,B\ge0$, and with
> $A=\bar u^qV=t^q$ this yields
> \[
>   1=\|u\|_q^2\le V^{2/q}\bar u^2
>      +\tfrac2qc_qV^{2/q-1}\bigl(\|v\|_2^2+\bar u^{2-q}\|v\|_q^q\bigr).
> \]
> Insert $\|v\|_2\le X/\sqrt{\lambda_1}$, $\|v\|_q\le\Csp X$ and
> $\bar u^{2-q}=t^{2-q}V^{(q-2)/q}$, and use $1-t^2\le1-t^q$ for $t\in[0,1]$,
> $q\ge2$. (l.692–703)

with `D := 1 − t²` (eq:D, l.584–587), `X := ‖∇u‖_{L²}`, `V = Vol(Σ, g)`, `ū = V⁻¹∫u` (l.312–313),
and `λ₁`, `C_SP` those of def:constants (l.316–326).

## What is proved (no `sorry` in this file)

* lem:elem: `lem_elem` (the printed statement), `elem_elemC` (the constant `q² 2^q`, through
  `rpow_le_one_add_tangent`, `two_rpow_ge_four`), `elem_const_nonneg` (every constant of lem:elem
  is `≥ 0`), `elem_signed`, `le_elemC` and `elem_signed_elemC` (the signed form
  `|1 + x|^q ≤ …` for every real `x`).
* The proof of prop:starN, step by step: `elem_scaled` (lem:elem at `x = v/ū`, l.692),
  `rpow_add_le_tangent` (the concavity step, l.694–695, for `A > 0`), `starN_core` (the display
  of l.697–699, at the integral level), `MeasuredModel.normalized_facts`,
  `MeasuredModel.mean_pos_of_nonneg` (`ū > 0`), `MeasuredModel.starN_deficit_of_pointwise` (the
  insertions of l.702–703), `MeasuredModel.starN_deficit` (the bound, `u ≥ 0`, any valid `λ`,
  `C`), `MeasuredModel.starN_deficit_signed` (every `u` with `ū ≠ 0`, with `|t|`).
* The three-branch split: `starNCoeff`, `starNAtil` (the explicit `Ã`), `starNAtil_nonneg`,
  `starNAtil_le` (`Ã ≤` the coefficient at any `(X₀, t₀)`), `starN_split` (cases (i)–(iii)),
  `MeasuredModel.starN_minkowski` (`1 − |t| ≤ ‖v‖_q`, case (iii)),
  `MeasuredModel.star_of_normalized` (2-homogeneity, l.577–578), `MeasuredModel.starN_point`,
  `MeasuredModel.starN_point_signed`, `MeasuredModel.le_starNAtil_of_forall`,
  `MeasuredModel.starN_of_consts` (eq:star, `u ≥ 0`, any valid `λ`, `C`),
  `MeasuredModel.starN_signed_of_consts` (eq:star for every `u`).
* Assemblies: `MeasuredModel.prop_starN` (prop:starN at `λ₁`, `C_SP`: the deficit bound and
  eq:star), `MeasuredModel.prop_starN_signed`, `MeasuredModel.prop_starN_explicit`
  (`c_q = q² 2^q`), and `MeasuredModel.thm_main_starN` (thm:main for every `N ≥ 3` at the
  constant of prop:starN, through `thm_main_signed`; a composite, not a label of this file).
* Witness: `toy_prop_starN` (every hypothesis of `prop_starN` holds on the two-point toy model,
  `N = 3`, and so does its conclusion).

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `q ≥ 2` (lem:elem) | ✓ carried (`hq`) |
| `x ≥ −1` (lem:elem) | ✓ carried; the signed form holds for every `x` with `max c q` |
| `q = p*`, `N ≥ 3` (prop:starN; the standing `N ≥ 3` of thm:main, l.182) | ✓ carried (`hN`) |
| `c_q` as in lem:elem | ✓ any `c` satisfying lem:elem's inequality (`hc`), not only one |
| `(Σ, g)` compact | ✓ carried as `IsFiniteMeasure (M.vol g)` |
| connected, Lipschitz, through `λ₁ > 0`, `C_SP < ∞` (l.319, l.328) | ⚠ carried as `0 < M.lambda1 g` and `∃ C, M.IsSobolevPoincareConst g C`, as `Star3.lean` does; their proof is T-perf-poincare's |
| `u ∈ W^{1,2}(Σ)` | ⚠ read: `u ∈ D` with `M.val u` a.e.-strongly measurable (`hD`), as in `Star3.lean` |
| `u ≥ 0`, `‖u‖_q = 1` | ✓ carried (`∀ x, 0 ≤ M.val u x`, `(eLpNorm …).toReal = 1`); eq:star itself is 2-homogeneous and proved for every `u ≥ 0` |
| `Ã` « explicit », « by the same three-branch split » | ⚠ read: `starNAtil`, the infimum over `X₀ > 0`, `t₀ ∈ (0, 1)` of the three branch coefficients (SCOPE) |

## SCOPE (disclosed)

* **No cap.** OQ-109's failure of thm:star3 is its case (ii), where the cap `n₆ = min{C_SP X₀, 2}`
  makes `G` decrease. prop:starN's bound has no cap: for `X < X₀`, `t ≥ t₀ > 0` one has
  `X^q ≤ X₀^{q−2} X²` and `t^{2−q} ≤ t₀^{2−q}`, so case (ii) is monotone and the split goes
  through (`starN_split`). The printed statement is proved as printed, nothing is corrected.
* **The explicit `Ã`.** The paper does not print it. Here
  `Ã = inf_{X₀ > 0, t₀ ∈ (0,1)} max{1/X₀², (2/q)c_q(V^{2/q−1}λ₁⁻¹ + t₀^{2−q}C_SP^q X₀^{q−2}), C_SP²/(1−t₀)²}`
  (`starNAtil`), the three branches of thm:star3's split with prop:starN's bound in case (ii).
  `t₀ = 0` is excluded: there `t₀^{2−q} = ∞` (Lean's `0^{2−q}` would be the junk `0`).
  `min` is read as an infimum (`sInf`), as for eq:Atil in `Star3.lean`.
* **The concavity step** (l.694–695) is stated « for `A, B ≥ 0` »; for `q > 2` it needs `A > 0`
  (`A^{2/q−1}` is undefined at `0`). Here `A = t^q > 0` because `u ≥ 0` and `‖u‖_q = 1` force
  `ū > 0` (`mean_pos_of_nonneg`), so nothing is lost.
* **l.702.** « use `1 − t² ≤ 1 − t^q` » is true but not used: the display of l.697–699 already
  bounds `1 − t²`, since `V^{2/q} ū² = t²`.
* **Signed form.** With `|t|` for `t` and `max c q` for `c`, every step holds for every `u` with
  `ū ≠ 0`, and case (iii) covers `ū = 0`, so eq:star holds for every `u`
  (`starN_signed_of_consts`), which `thm_main_signed` takes without a lattice property.
* **Junk values** (`normSq`, `dirichlet` are `0` when infinite) enter only through
  `IsPoincareConst`, `IsSobolevPoincareConst`, as in `Star3.lean`: an instance must take `D` among
  finite-energy functions (kb 0002).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal NNReal

noncomputable section

namespace Yamabe

/-! ## 1. lem:elem -/

section Elem

/-- The explicit constant of lem:elem: `c_q = q² 2^q`. -/
def elemC (q : ℝ) : ℝ := q ^ 2 * 2 ^ q

/-- The tangent line of `s ↦ s^p` at `s`, evaluated at `1` (Bernoulli's inequality at `1/s`):
`s^p ≤ 1 + p s^{p−1} (s − 1)` for `s > 0`, `p ≥ 1`. -/
lemma rpow_le_one_add_tangent {s p : ℝ} (hs : 0 < s) (hp : 1 ≤ p) :
    s ^ p ≤ 1 + p * s ^ (p - 1) * (s - 1) := by
  have hs1 : -1 ≤ 1 / s - 1 := by have : 0 < 1 / s := by positivity
                                  linarith
  have h1 := one_add_mul_self_le_rpow_one_add hs1 hp
  rw [show 1 + (1 / s - 1) = s⁻¹ by ring, Real.inv_rpow hs.le] at h1
  have hsp : 0 < s ^ p := Real.rpow_pos_of_pos hs p
  have h2 : (1 + p * (1 / s - 1)) * s ^ p ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h1 hsp.le
    rwa [inv_mul_cancel₀ hsp.ne'] at this
  have e : s ^ p = s ^ (p - 1) * s := by rw [← Real.rpow_add_one hs.ne', sub_add_cancel]
  rw [e] at h2 ⊢
  set a := s ^ (p - 1)
  have key : (1 + p * (1 / s - 1)) * (a * s) = a * s + p * a - p * a * s := by
    field_simp; ring
  rw [key] at h2
  linarith

/-- `2^q ≥ 4` for `q ≥ 2`. -/
lemma two_rpow_ge_four {q : ℝ} (hq : 2 ≤ q) : 4 ≤ (2 : ℝ) ^ q := by
  have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hq
  rw [show ((2 : ℝ) ^ (2 : ℝ)) = 4 by norm_num] at this
  exact this

/-- lem:elem with the explicit constant `c_q = q² 2^q`. -/
theorem elem_elemC {q : ℝ} (hq : 2 ≤ q) (x : ℝ) (hx : -1 ≤ x) :
    (1 + x) ^ q ≤ 1 + q * x + elemC q * (x ^ 2 + |x| ^ q) := by
  have h2q := two_rpow_ge_four hq
  have hq0 : 0 ≤ q := by linarith
  have h2q0 : (0 : ℝ) ≤ 2 ^ q := by positivity
  have hc4 : 4 * 2 ^ q ≤ elemC q := by
    unfold elemC; exact mul_le_mul_of_nonneg_right (by nlinarith) h2q0
  have hcq : q * 2 ^ q ≤ elemC q := by
    unfold elemC; exact mul_le_mul_of_nonneg_right (by nlinarith) h2q0
  have habs : 0 ≤ |x| ^ q := Real.rpow_nonneg (abs_nonneg x) q
  rcases lt_or_ge x 1 with hx1 | hx1
  · rcases hx.eq_or_lt with hxm | hxm
    · -- x = -1
      subst hxm
      rw [show (1 : ℝ) + -1 = 0 by norm_num, Real.zero_rpow (by linarith)]
      nlinarith
    · have hs : 0 < 1 + x := by linarith
      have ht := rpow_le_one_add_tangent hs (show 1 ≤ q by linarith)
      rw [show 1 + x - 1 = x by ring] at ht
      rcases le_or_gt 0 x with hx0 | hx0
      · -- 0 ≤ x < 1
        have ht2 := rpow_le_one_add_tangent hs (show 1 ≤ q - 1 by linarith)
        rw [show 1 + x - 1 = x by ring, show q - 1 - 1 = q - 2 by ring] at ht2
        have hb : (1 + x) ^ (q - 2) ≤ 2 ^ q := by
          calc (1 + x) ^ (q - 2) ≤ 2 ^ (q - 2) :=
                Real.rpow_le_rpow hs.le (by linarith) (by linarith)
            _ ≤ 2 ^ q := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        have h3 : (1 + x) ^ (q - 1) ≤ 1 + (q - 1) * 2 ^ q * x := by
          have : (q - 1) * (1 + x) ^ (q - 2) * x ≤ (q - 1) * 2 ^ q * x := by
            apply mul_le_mul_of_nonneg_right _ hx0
            exact mul_le_mul_of_nonneg_left hb (by linarith)
          linarith
        have h4 : q * (1 + x) ^ (q - 1) * x ≤ q * x + q * (q - 1) * 2 ^ q * x ^ 2 := by
          have := mul_le_mul_of_nonneg_left h3 (mul_nonneg hq0 hx0)
          nlinarith
        have h5 : q * (q - 1) * 2 ^ q * x ^ 2 ≤ elemC q * x ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg x)
          unfold elemC; nlinarith
        nlinarith [mul_nonneg (show 0 ≤ elemC q by linarith) habs]
      · -- -1 < x < 0
        have hB := one_add_mul_self_le_rpow_one_add hx (show 1 ≤ q - 1 by linarith)
        have h4 : q * (1 + x) ^ (q - 1) * x ≤ q * (1 + (q - 1) * x) * x := by
          have := mul_le_mul_of_nonpos_right hB (show q * x ≤ 0 by nlinarith)
          nlinarith
        have h5 : q * (q - 1) ≤ elemC q := by
          unfold elemC; nlinarith
        have h6 : q * (q - 1) * x ^ 2 ≤ elemC q * x ^ 2 := mul_le_mul_of_nonneg_right h5 (sq_nonneg x)
        nlinarith [mul_nonneg (show 0 ≤ elemC q by linarith) habs]
  · -- x ≥ 1
    have hx0 : 0 ≤ x := by linarith
    have h1 : (1 + x) ^ q ≤ 2 ^ q * x ^ q := by
      rw [← Real.mul_rpow (by norm_num) hx0]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hq0
    rw [abs_of_nonneg hx0]
    have hxq : 0 ≤ x ^ q := Real.rpow_nonneg hx0 q
    have h2 : 2 ^ q * x ^ q ≤ elemC q * x ^ q := by
      apply mul_le_mul_of_nonneg_right _ hxq; linarith
    nlinarith [mul_nonneg (show 0 ≤ elemC q by linarith) (sq_nonneg x)]

/-- **lem:elem** (l.673–677): for `q ≥ 2` there is `c_q < ∞` with
`(1 + x)^q ≤ 1 + q x + c_q (x² + |x|^q)` for all `x ≥ −1`. -/
theorem lem_elem {q : ℝ} (hq : 2 ≤ q) :
    ∃ c : ℝ, ∀ x : ℝ, -1 ≤ x → (1 + x) ^ q ≤ 1 + q * x + c * (x ^ 2 + |x| ^ q) :=
  ⟨elemC q, elem_elemC hq⟩

/-- Every constant of lem:elem is nonnegative (at `x = 1`, with Bernoulli's `2^q ≥ 1 + q`). -/
lemma elem_const_nonneg {q c : ℝ} (hq : 1 ≤ q)
    (hc : ∀ x : ℝ, -1 ≤ x → (1 + x) ^ q ≤ 1 + q * x + c * (x ^ 2 + |x| ^ q)) : 0 ≤ c := by
  have h1 := hc 1 (by norm_num)
  have hB := one_add_mul_self_le_rpow_one_add (show (-1 : ℝ) ≤ 1 by norm_num) hq
  rw [abs_one, Real.one_rpow] at h1
  nlinarith

/-- The signed form of lem:elem: a constant of lem:elem, enlarged to `max c q`, serves for every
real `x`, with `|1 + x|^q`. -/
theorem elem_signed {q c : ℝ} (hq : 2 ≤ q)
    (hc : ∀ x : ℝ, -1 ≤ x → (1 + x) ^ q ≤ 1 + q * x + c * (x ^ 2 + |x| ^ q)) (x : ℝ) :
    |1 + x| ^ q ≤ 1 + q * x + max c q * (x ^ 2 + |x| ^ q) := by
  have hq0 : 0 ≤ q := by linarith
  have habs : 0 ≤ |x| ^ q := Real.rpow_nonneg (abs_nonneg x) q
  have hS : 0 ≤ x ^ 2 + |x| ^ q := by positivity
  rcases le_or_gt (-1) x with hx | hx
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + x)]
    have := hc x hx
    have : c * (x ^ 2 + |x| ^ q) ≤ max c q * (x ^ 2 + |x| ^ q) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hS
    linarith
  · have h1 : |1 + x| ^ q ≤ |x| ^ q := by
      apply Real.rpow_le_rpow (abs_nonneg _) _ hq0
      rw [abs_of_neg (by linarith : 1 + x < 0), abs_of_neg (by linarith : x < 0)]
      linarith
    have hm : q ≤ max c q := le_max_right _ _
    have h2 : 0 ≤ 1 + q * x + max c q * x ^ 2 := by
      have : q * x ^ 2 ≤ max c q * x ^ 2 := mul_le_mul_of_nonneg_right hm (sq_nonneg x)
      have hxx : 0 ≤ q * (x * (1 + x)) :=
        mul_nonneg hq0 (mul_pos_of_neg_of_neg (by linarith) (by linarith)).le
      nlinarith
    have h3 : |x| ^ q ≤ max c q * |x| ^ q := by
      have : (1 : ℝ) ≤ max c q := by linarith
      nlinarith
    nlinarith

lemma le_elemC {q : ℝ} (hq : 2 ≤ q) : q ≤ elemC q := by
  have := two_rpow_ge_four hq
  unfold elemC; nlinarith

/-- The signed form at `c_q = q² 2^q`. -/
theorem elem_signed_elemC {q : ℝ} (hq : 2 ≤ q) (x : ℝ) :
    |1 + x| ^ q ≤ 1 + q * x + elemC q * (x ^ 2 + |x| ^ q) := by
  have h := elem_signed hq (fun y hy => elem_elemC hq y hy) x
  rwa [max_eq_left (le_elemC hq)] at h

end Elem

/-! ## 2. The steps of the proof of prop:starN -/

section Steps

/-- The concavity step (l.694–695): `(A + B)^p ≤ A^p + p A^{p−1} B` for `A > 0`, `B ≥ 0`,
`p ∈ [0, 1]` (here `p = 2/q`). -/
lemma rpow_add_le_tangent {A B p : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (A + B) ^ p ≤ A ^ p + p * A ^ (p - 1) * B := by
  have hBA : 0 ≤ B / A := div_nonneg hB hA.le
  have h1 := rpow_one_add_le_one_add_mul_self (show -1 ≤ B / A by linarith) hp0 hp1
  have e : A + B = A * (1 + B / A) := by field_simp
  have hAp : 0 < A ^ p := Real.rpow_pos_of_pos hA p
  rw [e, Real.mul_rpow hA.le (by linarith)]
  calc A ^ p * (1 + B / A) ^ p ≤ A ^ p * (1 + p * (B / A)) := mul_le_mul_of_nonneg_left h1 hAp.le
    _ = A ^ p + p * A ^ (p - 1) * B := by
      rw [Real.rpow_sub_one hA.ne']; field_simp

/-- lem:elem at `x = v/m` (l.692), multiplied by `|m|^q`. -/
lemma elem_scaled {q c m v : ℝ} (hm : m ≠ 0)
    (h : |1 + v / m| ^ q ≤ 1 + q * (v / m) + c * ((v / m) ^ 2 + |v / m| ^ q)) :
    |m + v| ^ q ≤ |m| ^ q + q * (|m| ^ q / m) * v + c * (|m| ^ (q - 2) * v ^ 2 + |v| ^ q) := by
  have hm' : 0 < |m| := abs_pos.mpr hm
  have hmq : 0 < |m| ^ q := Real.rpow_pos_of_pos hm' q
  have e1 : |m + v| = |m| * |1 + v / m| := by
    rw [← abs_mul]; congr 1; field_simp
  have e2 : |m| ^ q * (v / m) ^ 2 = |m| ^ (q - 2) * v ^ 2 := by
    rw [Real.rpow_sub hm', div_pow, ← sq_abs m, Real.rpow_two]
    field_simp
  have e3 : |m| ^ q * |v / m| ^ q = |v| ^ q := by
    rw [abs_div, Real.div_rpow (abs_nonneg v) hm'.le]
    field_simp
  rw [e1, Real.mul_rpow hm'.le (abs_nonneg _)]
  calc |m| ^ q * |1 + v / m| ^ q ≤ |m| ^ q * (1 + q * (v / m) + c * ((v / m) ^ 2 + |v / m| ^ q)) :=
        mul_le_mul_of_nonneg_left h hmq.le
    _ = |m| ^ q + q * (|m| ^ q / m) * v + c * (|m| ^ q * (v / m) ^ 2 + |m| ^ q * |v / m| ^ q) := by
        ring
    _ = _ := by rw [e2, e3]

end Steps

/-! ## 3. The display of l.697–699, at the integral level -/

section Core

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- The proof of prop:starN (l.692–699) for `‖w‖_q = 1`, `m = w̄ ≠ 0`, `t = V^{1/q} m`, from the
pointwise inequality of lem:elem at `x = (w − m)/m`: integrating (the linear term vanishing)
and the concavity step give `1 ≤ t² + (2/q) c (V^{2/q−1} ∫v² + |t|^{2−q} ∫|v|^q)`. -/
theorem starN_core [IsFiniteMeasure ν] (hV : 0 < (ν Set.univ).toReal) {q c : ℝ} (hq : 2 ≤ q)
    (hc : 0 ≤ c) {w : X → ℝ} (hw : MemLp w (ENNReal.ofReal q) ν) (hw1 : ∫ x, |w x| ^ q ∂ν = 1)
    {m : ℝ} (hm : m = (∫ x, w x ∂ν) / (ν Set.univ).toReal) (hm0 : m ≠ 0) {K : ℝ}
    (hpt : ∀ x, |w x| ^ q ≤
      |m| ^ q + K * (w x - m) + c * (|m| ^ (q - 2) * (w x - m) ^ 2 + |w x - m| ^ q)) :
    1 ≤ ((ν Set.univ).toReal ^ (1 / q) * m) ^ 2 + 2 / q * c *
      ((ν Set.univ).toReal ^ (2 / q - 1) * ∫ x, (w x - m) ^ 2 ∂ν +
        |(ν Set.univ).toReal ^ (1 / q) * m| ^ (2 - q) * ∫ x, |w x - m| ^ q ∂ν) := by
  set V := (ν Set.univ).toReal with hVdef
  have hq0 : 0 < q := by linarith
  have hp0 : ENNReal.ofReal q ≠ 0 := by simpa using hq0
  have hptop : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hqr : (ENNReal.ofReal q).toReal = q := ENNReal.toReal_ofReal hq0.le
  have h2q : (2 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_ofNat]; exact ENNReal.ofReal_le_ofReal hq
  have h1q : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := le_trans (by norm_num) h2q
  -- integrability
  have hwq : Integrable (fun x => |w x| ^ q) ν := by
    have := hw.integrable_norm_rpow hp0 hptop
    simpa [Real.norm_eq_abs, hqr] using this
  have hv : MemLp (fun x => w x - m) (ENNReal.ofReal q) ν := hw.sub (memLp_const m)
  have hvq : Integrable (fun x => |w x - m| ^ q) ν := by
    have := hv.integrable_norm_rpow hp0 hptop
    simpa [Real.norm_eq_abs, hqr] using this
  have hv2 : Integrable (fun x => (w x - m) ^ 2) ν := (hv.mono_exponent h2q).integrable_sq
  have hwi : Integrable w ν := hw.integrable h1q
  set I2 := ∫ x, (w x - m) ^ 2 ∂ν with hI2
  set Iq := ∫ x, |w x - m| ^ q ∂ν with hIq
  have hI2n : 0 ≤ I2 := integral_nonneg fun x => by positivity
  have hIqn : 0 ≤ Iq := integral_nonneg fun x => by positivity
  -- integrate the pointwise inequality
  have hlin : ∫ x, (w x - m) ∂ν = 0 := by
    rw [integral_sub hwi (integrable_const m), integral_const, smul_eq_mul, measureReal_def,
      ← hVdef, hm]
    field_simp; ring
  have hint : ∫ x, (|m| ^ q + K * (w x - m) + c * (|m| ^ (q - 2) * (w x - m) ^ 2 + |w x - m| ^ q)) ∂ν
      = |m| ^ q * V + c * (|m| ^ (q - 2) * I2 + Iq) := by
    have i1 : Integrable (fun _ : X => |m| ^ q) ν := integrable_const _
    have i2 : Integrable (fun x => K * (w x - m)) ν := (hwi.sub (integrable_const m)).const_mul K
    have i3 : Integrable (fun x => |m| ^ (q - 2) * (w x - m) ^ 2) ν := hv2.const_mul _
    have i12 : Integrable (fun x => |m| ^ q + K * (w x - m)) ν := i1.add i2
    have i34 : Integrable (fun x => |m| ^ (q - 2) * (w x - m) ^ 2 + |w x - m| ^ q) ν := i3.add hvq
    have i34c : Integrable (fun x => c * (|m| ^ (q - 2) * (w x - m) ^ 2 + |w x - m| ^ q)) ν :=
      i34.const_mul c
    rw [integral_add i12 i34c, integral_add i1 i2, integral_const,
      integral_const_mul, hlin, integral_const_mul, integral_add i3 hvq, integral_const_mul,
      smul_eq_mul, measureReal_def, ← hVdef]
    ring
  have hle : 1 ≤ |m| ^ q * V + c * (|m| ^ (q - 2) * I2 + Iq) := by
    rw [← hw1, ← hint]
    refine integral_mono hwq ?_ hpt
    exact ((integrable_const _).add ((hwi.sub (integrable_const m)).const_mul K)).add
      (((hv2.const_mul _).add hvq).const_mul c)
  -- the concavity step
  have hma : 0 < |m| := abs_pos.mpr hm0
  set A := |m| ^ q * V with hA
  set B := c * (|m| ^ (q - 2) * I2 + Iq) with hB
  have hApos : 0 < A := mul_pos (Real.rpow_pos_of_pos hma q) hV
  have hBn : 0 ≤ B := mul_nonneg hc (add_nonneg (mul_nonneg (Real.rpow_nonneg hma.le _) hI2n) hIqn)
  have hp1 : 2 / q ≤ 1 := by rw [div_le_one hq0]; exact hq
  have hp0' : 0 ≤ 2 / q := by positivity
  have hcon := rpow_add_le_tangent hApos hBn hp0' hp1
  have h1 : 1 ≤ (A + B) ^ (2 / q) := Real.one_le_rpow hle hp0'
  -- simplify A^{2/q} and A^{2/q - 1} B
  have eA : A ^ (2 / q) = (V ^ (1 / q) * m) ^ 2 := by
    rw [hA, Real.mul_rpow (Real.rpow_nonneg hma.le _) hV.le, ← Real.rpow_mul hma.le, mul_pow,
      ← Real.rpow_natCast (V ^ (1 / q)), ← Real.rpow_mul hV.le]
    have e1 : q * (2 / q) = ((2 : ℕ) : ℝ) := by field_simp; norm_num
    have e2 : 1 / q * ((2 : ℕ) : ℝ) = 2 / q := by field_simp; norm_num
    rw [e1, e2, Real.rpow_natCast, sq_abs]; ring
  have eB : A ^ (2 / q - 1) * B =
      c * (V ^ (2 / q - 1) * I2 + |V ^ (1 / q) * m| ^ (2 - q) * Iq) := by
    have e1 : q * (2 / q - 1) = 2 - q := by field_simp
    have e2 : 1 / q * (2 - q) = 2 / q - 1 := by field_simp
    have e3 : |m| ^ (2 - q) * |m| ^ (q - 2) = 1 := by
      rw [← Real.rpow_add hma]; norm_num
    rw [hA, hB, Real.mul_rpow (Real.rpow_nonneg hma.le _) hV.le, ← Real.rpow_mul hma.le, e1,
      abs_mul, abs_of_pos (Real.rpow_pos_of_pos hV _), Real.mul_rpow (Real.rpow_nonneg hV.le _) hma.le,
      ← Real.rpow_mul hV.le, e2]
    linear_combination (c * V ^ (2 / q - 1) * I2) * e3
  have : 1 ≤ A ^ (2 / q) + 2 / q * (A ^ (2 / q - 1) * B) := by
    have := h1.trans hcon; linarith [this]
  rw [eA, eB] at this
  linarith

end Core

/-! ## 4. The explicit `Ã` and the three-branch split -/

section Split

/-- The coefficient of the three-branch split at `(X₀, t₀)`: the branches (i) `1/X₀²`,
(ii) `(2/q) c (V^{2/q−1} λ⁻¹ + t₀^{2−q} C^q X₀^{q−2})` (prop:starN's bound with `X ≤ X₀`,
`t ≥ t₀`), (iii) `C²/(1 − t₀)²`. -/
def starNCoeff (q c V lam C X0 t0 : ℝ) : ℝ :=
  max (1 / X0 ^ 2)
    (max (2 / q * c * (V ^ (2 / q - 1) * lam⁻¹ + t0 ^ (2 - q) * C ^ q * X0 ^ (q - 2)))
      (C ^ 2 / (1 - t0) ^ 2))

/-- The explicit `Ã` of prop:starN (l.687–688): the minimum of `starNCoeff` over `X₀ > 0`,
`t₀ ∈ (0, 1)`, read as an infimum. -/
def starNAtil (q c V lam C : ℝ) : ℝ :=
  sInf {A | ∃ X0 t0 : ℝ, 0 < X0 ∧ 0 < t0 ∧ t0 < 1 ∧ starNCoeff q c V lam C X0 t0 = A}

lemma starNCoeff_nonneg (q c V lam C X0 t0 : ℝ) : 0 ≤ starNCoeff q c V lam C X0 t0 :=
  le_trans (by positivity) (le_max_left _ _)

/-- `Ã ≥ 0`. -/
lemma starNAtil_nonneg (q c V lam C : ℝ) : 0 ≤ starNAtil q c V lam C :=
  Real.sInf_nonneg fun _ ⟨_, _, _, _, _, h⟩ => h ▸ starNCoeff_nonneg _ _ _ _ _ _ _

/-- `Ã` is at most the coefficient at any admissible `(X₀, t₀)`: an explicit numerical bound. -/
lemma starNAtil_le (q c V lam C : ℝ) {X0 t0 : ℝ} (hX0 : 0 < X0) (ht0 : 0 < t0) (ht1 : t0 < 1) :
    starNAtil q c V lam C ≤ starNCoeff q c V lam C X0 t0 :=
  csInf_le ⟨0, fun _ ⟨_, _, _, _, _, h⟩ => h ▸ starNCoeff_nonneg _ _ _ _ _ _ _⟩
    ⟨X0, t0, hX0, ht0, ht1, rfl⟩

/-- The three-branch split (cases (i)–(iii) of l.641–651) for prop:starN's bound: with
`E = X²`, the deficit bound (for `t ≠ 0`) and `1 − |t| ≤ C X` give `1 ≤ Coeff · X² + t²`. -/
theorem starN_split {q c V lam C E t X0 t0 : ℝ} (hq : 2 ≤ q) (hc : 0 ≤ c) (hV : 0 ≤ V)
    (hlam : 0 < lam) (hC : 0 ≤ C) (hE : 0 ≤ E) (hX0 : 0 < X0) (ht0 : 0 < t0) (ht1 : t0 < 1)
    (hdef : t ≠ 0 → 1 - t ^ 2 ≤
      2 / q * c * (V ^ (2 / q - 1) * lam⁻¹ * E + |t| ^ (2 - q) * C ^ q * Real.sqrt E ^ q))
    (hmink : 1 - |t| ≤ C * Real.sqrt E) :
    1 ≤ starNCoeff q c V lam C X0 t0 * E + t ^ 2 := by
  set X := Real.sqrt E with hXdef
  have hX : 0 ≤ X := Real.sqrt_nonneg E
  have hXE : X ^ 2 = E := Real.sq_sqrt hE
  have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
  set K := starNCoeff q c V lam C X0 t0 with hK
  have hb1 : 1 / X0 ^ 2 ≤ K := le_max_left _ _
  have hb2 : 2 / q * c * (V ^ (2 / q - 1) * lam⁻¹ + t0 ^ (2 - q) * C ^ q * X0 ^ (q - 2)) ≤ K :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hb3 : C ^ 2 / (1 - t0) ^ 2 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  rcases le_or_gt X0 X with hXX | hXX
  · -- (i) X ≥ X₀
    have h1 : 1 ≤ 1 / X0 ^ 2 * E := by
      rw [← hXE, one_div, inv_mul_eq_div, le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hX0.le hXX 2
    have := mul_le_mul_of_nonneg_right hb1 hE
    linarith
  · rcases le_or_gt t0 |t| with htt | htt
    · -- (ii) X < X₀, t ≥ t₀
      have htne : t ≠ 0 := by
        intro h; rw [h, abs_zero] at htt; linarith
      have hd := hdef htne
      have hq2 : 0 ≤ q - 2 := by linarith
      have ha : 0 ≤ V ^ (2 / q - 1) * lam⁻¹ :=
        mul_nonneg (Real.rpow_nonneg hV _) (inv_nonneg.mpr hlam.le)
      have hCq : 0 ≤ C ^ q := Real.rpow_nonneg hC q
      have htq : |t| ^ (2 - q) ≤ t0 ^ (2 - q) :=
        Real.rpow_le_rpow_of_nonpos ht0 htt (by linarith)
      have hXq : X ^ q = X ^ (q - 2) * E := by
        rw [← hXE, ← Real.rpow_natCast X 2, ← Real.rpow_add' hX (by norm_num; linarith)]
        norm_num
      have hXq2 : X ^ (q - 2) ≤ X0 ^ (q - 2) := Real.rpow_le_rpow hX hXX.le hq2
      have hmain : |t| ^ (2 - q) * C ^ q * X ^ q ≤ t0 ^ (2 - q) * C ^ q * X0 ^ (q - 2) * E := by
        rw [hXq]
        have h1 : |t| ^ (2 - q) * C ^ q ≤ t0 ^ (2 - q) * C ^ q :=
          mul_le_mul_of_nonneg_right htq hCq
        have h2 : X ^ (q - 2) * E ≤ X0 ^ (q - 2) * E := mul_le_mul_of_nonneg_right hXq2 hE
        have h3 : 0 ≤ X ^ (q - 2) * E := mul_nonneg (Real.rpow_nonneg hX _) hE
        have h4 : 0 ≤ t0 ^ (2 - q) * C ^ q := mul_nonneg (Real.rpow_nonneg ht0.le _) hCq
        calc |t| ^ (2 - q) * C ^ q * (X ^ (q - 2) * E)
            ≤ t0 ^ (2 - q) * C ^ q * (X ^ (q - 2) * E) := mul_le_mul_of_nonneg_right h1 h3
          _ ≤ t0 ^ (2 - q) * C ^ q * (X0 ^ (q - 2) * E) := mul_le_mul_of_nonneg_left h2 h4
          _ = t0 ^ (2 - q) * C ^ q * X0 ^ (q - 2) * E := by ring
      have hK0 : 0 ≤ 2 / q * c := mul_nonneg (by positivity) hc
      have h5 : 2 / q * c * (V ^ (2 / q - 1) * lam⁻¹ * E + |t| ^ (2 - q) * C ^ q * X ^ q) ≤
          2 / q * c * (V ^ (2 / q - 1) * lam⁻¹ + t0 ^ (2 - q) * C ^ q * X0 ^ (q - 2)) * E := by
        have := mul_le_mul_of_nonneg_left
          (add_le_add_right hmain (V ^ (2 / q - 1) * lam⁻¹ * E)) hK0
        calc _ ≤ 2 / q * c * (V ^ (2 / q - 1) * lam⁻¹ * E +
              t0 ^ (2 - q) * C ^ q * X0 ^ (q - 2) * E) := by linarith
          _ = _ := by ring
      have := mul_le_mul_of_nonneg_right hb2 hE
      linarith
    · -- (iii) X < X₀, t < t₀
      have h1 : 0 < 1 - t0 := by linarith
      have h2 : 1 - t0 ≤ C * X := by linarith
      have h3 : (1 - t0) ^ 2 ≤ C ^ 2 * E := by
        rw [← hXE, ← mul_pow]; exact pow_le_pow_left₀ h1.le h2 2
      have h4 : 1 ≤ C ^ 2 / (1 - t0) ^ 2 * E := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul]; exact h3
      have := mul_le_mul_of_nonneg_right hb3 hE
      linarith

end Split

/-! ## 5. prop:starN on the model -/

namespace MeasuredModel

variable {X D : Type*} [MeasurableSpace X] [AddCommGroup D] [Module ℝ D] {N n : ℕ}
variable (M : MeasuredModel X D N n) (g : FrameMetric X N)

/-- `‖u‖_q = 1` makes `u ∈ L^q`, `∫|u|^q = 1` and `V > 0`. -/
lemma normalized_facts (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) {u : D}
    (hu1 : (eLpNorm (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal = 1) :
    MemLp (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g) ∧
      ∫ x, |M.val u x| ^ pStar N ∂(M.vol g) = 1 ∧ 0 < (M.vol g Set.univ).toReal := by
  have hq := two_le_pStar hN
  have hq0 : 0 < pStar N := by linarith
  have hp0 : ENNReal.ofReal (pStar N) ≠ 0 := by simpa using hq0
  have hne : eLpNorm (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g) ≠ ⊤ := by
    intro h; rw [h, ENNReal.toReal_top] at hu1; exact zero_ne_one hu1
  have hw : MemLp (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g) :=
    ⟨hD u, lt_top_iff_ne_top.mpr hne⟩
  refine ⟨hw, ?_, ?_⟩
  · have e := hw.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hq0.le] at e
    have hI0 : 0 ≤ ∫ x, ‖M.val u x‖ ^ pStar N ∂(M.vol g) := integral_nonneg fun x => by positivity
    rw [e, ENNReal.toReal_ofReal (Real.rpow_nonneg hI0 _)] at hu1
    have := congrArg (fun y => y ^ pStar N) hu1
    simp only [Real.rpow_inv_rpow hI0 hq0.ne', Real.one_rpow] at this
    simpa [Real.norm_eq_abs] using this
  · have hν : M.vol g ≠ 0 := by
      intro h; rw [h, eLpNorm_measure_zero, ENNReal.toReal_zero] at hu1; exact zero_ne_one hu1
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.mpr hν) (measure_ne_top _ _)

/-- Case (iii) (l.649–650): `1 − |t| ≤ ‖u‖_q − ‖ū‖_q ≤ ‖v‖_q ≤ C X`. -/
lemma starN_minkowski (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) {C : ℝ}
    (hS : M.IsSobolevPoincareConst g C) {u : D}
    (hu1 : (eLpNorm (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal = 1) :
    1 - |(M.vol g Set.univ).toReal ^ (1 / pStar N) * M.mean g u| ≤
      C * Real.sqrt (M.dirichlet g u) := by
  obtain ⟨hw, -, hV⟩ := M.normalized_facts g hN hD hu1
  have hq := two_le_pStar hN
  have hq0 : 0 < pStar N := by linarith
  have hp0 : ENNReal.ofReal (pStar N) ≠ 0 := by simpa using hq0
  have h1q : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (pStar N) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hν : M.vol g ≠ 0 := by
    intro h; rw [h, eLpNorm_measure_zero, ENNReal.toReal_zero] at hu1; exact zero_ne_one hu1
  set m := M.mean g u with hmdef
  set V := (M.vol g Set.univ).toReal with hVdef
  have hv : MemLp (fun x => M.val u x - m) (ENNReal.ofReal (pStar N)) (M.vol g) :=
    hw.sub (memLp_const m)
  have hsplit : M.val u = (fun x => M.val u x - m) + fun _ => m := by
    funext x; simp
  have htri := eLpNorm_add_le hv.aestronglyMeasurable aestronglyMeasurable_const h1q
    (f := fun x => M.val u x - m) (g := fun _ => m) (μ := M.vol g)
  rw [← hsplit] at htri
  have hk : eLpNorm (fun _ : X => m) (ENNReal.ofReal (pStar N)) (M.vol g) =
      ‖m‖ₑ * M.vol g Set.univ ^ (1 / (ENNReal.ofReal (pStar N)).toReal) :=
    eLpNorm_const m hp0 hν
  have hkfin : eLpNorm (fun _ : X => m) (ENNReal.ofReal (pStar N)) (M.vol g) ≠ ⊤ :=
    (memLp_const m).eLpNorm_ne_top
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hv.eLpNorm_ne_top, hkfin⟩) htri
  rw [ENNReal.toReal_add hv.eLpNorm_ne_top hkfin, hu1, hk, ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs,
    ENNReal.toReal_ofReal (abs_nonneg m), ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hq0.le] at h2
  have hS' := hS u
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
  have : |m| * V ^ (1 / pStar N) = V ^ (1 / pStar N) * |m| := mul_comm _ _
  linarith

/-- The insertions of l.702–703 (`‖v‖₂² ≤ X²/λ`, `‖v‖_q ≤ C X`, `ū^{2−q} = t^{2−q}V^{(q−2)/q}`)
into the display of l.697–699, from the pointwise inequality of lem:elem at `x = v/ū`. -/
lemma starN_deficit_of_pointwise (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) {lam C c : ℝ} (hlam : 0 < lam)
    (hC : 0 ≤ C) (hP : M.IsPoincareConst g lam) (hS : M.IsSobolevPoincareConst g C) (hc : 0 ≤ c)
    {u : D} (hu1 : (eLpNorm (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal = 1)
    (hm0 : M.mean g u ≠ 0) {K : ℝ}
    (hpt : ∀ x, |M.val u x| ^ pStar N ≤ |M.mean g u| ^ pStar N + K * (M.val u x - M.mean g u) +
      c * (|M.mean g u| ^ (pStar N - 2) * (M.val u x - M.mean g u) ^ 2 +
        |M.val u x - M.mean g u| ^ pStar N)) :
    1 - ((M.vol g Set.univ).toReal ^ (1 / pStar N) * M.mean g u) ^ 2 ≤
      2 / pStar N * c * ((M.vol g Set.univ).toReal ^ (2 / pStar N - 1) * lam⁻¹ * M.dirichlet g u +
        |(M.vol g Set.univ).toReal ^ (1 / pStar N) * M.mean g u| ^ (2 - pStar N) * C ^ pStar N *
          Real.sqrt (M.dirichlet g u) ^ pStar N) := by
  obtain ⟨hw, hw1, hV⟩ := M.normalized_facts g hN hD hu1
  have hq := two_le_pStar hN
  have hq0 : 0 < pStar N := by linarith
  have hp0 : ENNReal.ofReal (pStar N) ≠ 0 := by simpa using hq0
  set m := M.mean g u with hmdef
  set V := (M.vol g Set.univ).toReal with hVdef
  have core := starN_core hV hq hc hw hw1 (m := m) rfl hm0 hpt
  have hv : MemLp (fun x => M.val u x - m) (ENNReal.ofReal (pStar N)) (M.vol g) :=
    hw.sub (memLp_const m)
  -- the L² term: λ ∫v² ≤ X²
  have hI2 : ∫ x, (M.val u x - m) ^ 2 ∂(M.vol g) ≤ lam⁻¹ * M.dirichlet g u := by
    rw [integral_sq_eq_normSq (memLp_two_of_pStar hN hv)]
    have := hP u
    rw [← hmdef] at this
    rw [inv_mul_eq_div, le_div_iff₀ hlam]; linarith
  -- the L^q term: ∫|v|^q = ‖v‖_q^q ≤ (C X)^q
  have hIq : ∫ x, |M.val u x - m| ^ pStar N ∂(M.vol g) ≤
      C ^ pStar N * Real.sqrt (M.dirichlet g u) ^ pStar N := by
    have e := hv.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hq0.le] at e
    have hI0 : 0 ≤ ∫ x, ‖M.val u x - m‖ ^ pStar N ∂(M.vol g) :=
      integral_nonneg fun x => by positivity
    have hS' := hS u
    rw [← hmdef, e, ENNReal.toReal_ofReal (Real.rpow_nonneg hI0 _)] at hS'
    have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hI0 _) hS' hq0.le
    rw [Real.rpow_inv_rpow hI0 hq0.ne', Real.mul_rpow hC (Real.sqrt_nonneg _)] at h1
    simpa [Real.norm_eq_abs] using h1
  have hK0 : 0 ≤ 2 / pStar N * c := mul_nonneg (by positivity) hc
  have hVa : 0 ≤ V ^ (2 / pStar N - 1) := Real.rpow_nonneg hV.le _
  have hta : 0 ≤ |V ^ (1 / pStar N) * m| ^ (2 - pStar N) := Real.rpow_nonneg (abs_nonneg _) _
  have h3 := add_le_add (mul_le_mul_of_nonneg_left hI2 hVa) (mul_le_mul_of_nonneg_left hIq hta)
  have h4 := mul_le_mul_of_nonneg_left h3 hK0
  have e5 : V ^ (2 / pStar N - 1) * (lam⁻¹ * M.dirichlet g u) +
      |V ^ (1 / pStar N) * m| ^ (2 - pStar N) * (C ^ pStar N * Real.sqrt (M.dirichlet g u) ^ pStar N) =
      V ^ (2 / pStar N - 1) * lam⁻¹ * M.dirichlet g u +
      |V ^ (1 / pStar N) * m| ^ (2 - pStar N) * C ^ pStar N * Real.sqrt (M.dirichlet g u) ^ pStar N := by
    ring
  rw [e5] at h4
  linarith

/-- `u ≥ 0` and `‖u‖_q = 1` force `ū > 0`. -/
lemma mean_pos_of_nonneg (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) {u : D} (hu0 : ∀ x, 0 ≤ M.val u x)
    (hu1 : (eLpNorm (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal = 1) :
    0 < M.mean g u := by
  obtain ⟨hw, -, hV⟩ := M.normalized_facts g hN hD hu1
  have h1q : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (pStar N) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith [two_le_pStar hN])
  have hwi : Integrable (M.val u) (M.vol g) := hw.integrable h1q
  have hI0 : 0 ≤ ∫ x, M.val u x ∂(M.vol g) := integral_nonneg hu0
  have hIne : ∫ x, M.val u x ∂(M.vol g) ≠ 0 := by
    intro h
    have hae := (integral_eq_zero_iff_of_nonneg hu0 hwi).mp h
    rw [eLpNorm_congr_ae hae, eLpNorm_zero, ENNReal.toReal_zero] at hu1
    exact zero_ne_one hu1
  exact div_pos (lt_of_le_of_ne hI0 (Ne.symm hIne)) hV

/-- The deficit bound of prop:starN (l.683–685) for `u ≥ 0`, `‖u‖_q = 1`, any constant `c` of
lem:elem and any valid Poincaré and Sobolev–Poincaré constants `λ`, `C`. -/
theorem starN_deficit (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) {lam C c : ℝ} (hlam : 0 < lam)
    (hC : 0 ≤ C) (hP : M.IsPoincareConst g lam) (hS : M.IsSobolevPoincareConst g C)
    (hc : ∀ x : ℝ, -1 ≤ x → (1 + x) ^ pStar N ≤ 1 + pStar N * x + c * (x ^ 2 + |x| ^ pStar N))
    {u : D} (hu0 : ∀ x, 0 ≤ M.val u x)
    (hu1 : (eLpNorm (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal = 1) :
    1 - ((M.vol g Set.univ).toReal ^ (1 / pStar N) * M.mean g u) ^ 2 ≤
      2 / pStar N * c * ((M.vol g Set.univ).toReal ^ (2 / pStar N - 1) * lam⁻¹ * M.dirichlet g u +
        ((M.vol g Set.univ).toReal ^ (1 / pStar N) * M.mean g u) ^ (2 - pStar N) * C ^ pStar N *
          Real.sqrt (M.dirichlet g u) ^ pStar N) := by
  have hq := two_le_pStar hN
  have hc0 : 0 ≤ c := elem_const_nonneg (by linarith) hc
  have hm := M.mean_pos_of_nonneg g hN hD hu0 hu1
  obtain ⟨-, -, hV⟩ := M.normalized_facts g hN hD hu1
  have h := M.starN_deficit_of_pointwise g hN hD hlam hC hP hS hc0 hu1 hm.ne'
    (K := pStar N * (|M.mean g u| ^ pStar N / M.mean g u)) (fun x => by
      have hx : -1 ≤ (M.val u x - M.mean g u) / M.mean g u := by
        rw [sub_div, div_self hm.ne']
        have := div_nonneg (hu0 x) hm.le
        linarith
      have h1 := hc _ hx
      rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + (M.val u x - M.mean g u) / M.mean g u)] at h1
      have h2 := elem_scaled hm.ne' h1
      rwa [show M.mean g u + (M.val u x - M.mean g u) = M.val u x by ring] at h2)
  rwa [abs_of_pos (mul_pos (Real.rpow_pos_of_pos hV _) hm)] at h

/-- The deficit bound for every `u` with `ū ≠ 0`, with `|t|` for `t`, for a constant `c` of the
signed form of lem:elem. -/
theorem starN_deficit_signed (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) {lam C c : ℝ} (hlam : 0 < lam)
    (hC : 0 ≤ C) (hP : M.IsPoincareConst g lam) (hS : M.IsSobolevPoincareConst g C)
    (hc : ∀ x : ℝ, |1 + x| ^ pStar N ≤ 1 + pStar N * x + c * (x ^ 2 + |x| ^ pStar N))
    {u : D} (hu1 : (eLpNorm (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal = 1)
    (hm0 : M.mean g u ≠ 0) :
    1 - ((M.vol g Set.univ).toReal ^ (1 / pStar N) * M.mean g u) ^ 2 ≤
      2 / pStar N * c * ((M.vol g Set.univ).toReal ^ (2 / pStar N - 1) * lam⁻¹ * M.dirichlet g u +
        |(M.vol g Set.univ).toReal ^ (1 / pStar N) * M.mean g u| ^ (2 - pStar N) * C ^ pStar N *
          Real.sqrt (M.dirichlet g u) ^ pStar N) := by
  have hq := two_le_pStar hN
  have hc0 : 0 ≤ c := elem_const_nonneg (by linarith) fun x hx => by
    have := hc x; rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + x)] at this
  exact M.starN_deficit_of_pointwise g hN hD hlam hC hP hS hc0 hu1 hm0
    (K := pStar N * (|M.mean g u| ^ pStar N / M.mean g u)) (fun x => by
      have h2 := elem_scaled hm0 (hc ((M.val u x - M.mean g u) / M.mean g u))
      rwa [show M.mean g u + (M.val u x - M.mean g u) = M.val u x by ring] at h2)

/-- 2-homogeneity (l.577–578): eq:star with a constant `A ≥ 0` on a class of `u` closed under
positive scaling follows from its normalized form `1 ≤ A X² + t²` at `‖u‖_q = 1`. -/
lemma star_of_normalized (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)] {A : ℝ} (hA : 0 ≤ A)
    (P : D → Prop) (hPs : ∀ (u : D) (k : ℝ), 0 < k → P u → P (k • u))
    (h : ∀ u : D, P u → (eLpNorm (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal = 1 →
      1 ≤ A * M.dirichlet g u + ((M.vol g Set.univ).toReal ^ (1 / pStar N) * M.mean g u) ^ 2)
    (u : D) (hu : P u) :
    normSq (M.vol g) (pStar N) (M.val u) ≤
      A * M.dirichlet g u + (M.vol g Set.univ).toReal ^ (2 / pStar N) * M.mean g u ^ 2 := by
  have hq := two_le_pStar hN
  have hq0 : 0 < pStar N := by linarith
  set V := (M.vol g Set.univ).toReal with hVdef
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hR : 0 ≤ A * M.dirichlet g u + V ^ (2 / pStar N) * M.mean g u ^ 2 :=
    add_nonneg (mul_nonneg hA (M.dirichlet_nonneg g u))
      (mul_nonneg (Real.rpow_nonneg hV0 _) (sq_nonneg _))
  set s := (eLpNorm (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal with hs
  have hns : normSq (M.vol g) (pStar N) (M.val u) = s ^ 2 := rfl
  rcases (ENNReal.toReal_nonneg : 0 ≤ s).eq_or_lt with hs0 | hspos
  · have h0 : s ^ 2 = 0 := by rw [hs, ← hs0]; norm_num
    rw [hns, h0]; exact hR
  set k := s⁻¹ with hk
  have hk0 : 0 < k := inv_pos.mpr hspos
  have hval : M.val (k • u) = k • M.val u := map_smul _ _ _
  have hnorm : (eLpNorm (M.val (k • u)) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal = 1 := by
    rw [hval, eLpNorm_const_smul, ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs,
      ENNReal.toReal_ofReal (abs_nonneg k), abs_of_pos hk0, ← hs, hk, inv_mul_cancel₀ hspos.ne']
  have hmean : M.mean g (k • u) = k * M.mean g u := by
    unfold mean; simp only [map_smul, Pi.smul_apply, smul_eq_mul, integral_const_mul]; ring
  have h1 := h (k • u) (hPs u k hk0 hu) hnorm
  have hdir : M.dirichlet g (k • u) = k ^ 2 * M.dirichlet g u := by
    rw [M.dirichlet_eq_toReal_energy, M.energy_smul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sq_nonneg k)]; rfl
  rw [hdir, hmean] at h1
  have e : (V ^ (1 / pStar N) * (k * M.mean g u)) ^ 2 =
      k ^ 2 * (V ^ (2 / pStar N) * M.mean g u ^ 2) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (V ^ (1 / pStar N)), ← Real.rpow_mul hV0]
    have : 1 / pStar N * ((2 : ℕ) : ℝ) = 2 / pStar N := by field_simp; norm_num
    rw [this]; ring
  rw [e] at h1
  have hks : k ^ 2 * s ^ 2 = 1 := by rw [hk, ← mul_pow, inv_mul_cancel₀ hspos.ne', one_pow]
  rw [hns]
  have h2 : s ^ 2 * 1 ≤ s ^ 2 * (A * (k ^ 2 * M.dirichlet g u) +
      k ^ 2 * (V ^ (2 / pStar N) * M.mean g u ^ 2)) :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg s)
  have e2 : s ^ 2 * (A * (k ^ 2 * M.dirichlet g u) + k ^ 2 * (V ^ (2 / pStar N) * M.mean g u ^ 2)) =
      (k ^ 2 * s ^ 2) * (A * M.dirichlet g u + V ^ (2 / pStar N) * M.mean g u ^ 2) := by ring
  rw [e2, hks] at h2
  linarith

/-- eq:star at one `(X₀, t₀)`, for `u ≥ 0`, any constant `c` of lem:elem, any valid `λ`, `C`. -/
theorem starN_point (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) {lam C c : ℝ} (hlam : 0 < lam)
    (hC : 0 ≤ C) (hP : M.IsPoincareConst g lam) (hS : M.IsSobolevPoincareConst g C)
    (hc : ∀ x : ℝ, -1 ≤ x → (1 + x) ^ pStar N ≤ 1 + pStar N * x + c * (x ^ 2 + |x| ^ pStar N))
    {X0 t0 : ℝ} (hX0 : 0 < X0) (ht0 : 0 < t0) (ht1 : t0 < 1) (u : D) (hu0 : ∀ x, 0 ≤ M.val u x) :
    normSq (M.vol g) (pStar N) (M.val u) ≤
      starNCoeff (pStar N) c (M.vol g Set.univ).toReal lam C X0 t0 * M.dirichlet g u +
        (M.vol g Set.univ).toReal ^ (2 / pStar N) * M.mean g u ^ 2 := by
  have hq := two_le_pStar hN
  have hc0 : 0 ≤ c := elem_const_nonneg (by linarith) hc
  refine M.star_of_normalized g hN (starNCoeff_nonneg _ _ _ _ _ _ _) (fun u => ∀ x, 0 ≤ M.val u x)
    (fun u k hk hu x => ?_) (fun u hu0 hu1 => ?_) u hu0
  · rw [map_smul, Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hk.le (hu x)
  · have hdef := M.starN_deficit g hN hD hlam hC hP hS hc hu0 hu1
    have hm := M.mean_pos_of_nonneg g hN hD hu0 hu1
    obtain ⟨-, -, hV⟩ := M.normalized_facts g hN hD hu1
    have ht : 0 < (M.vol g Set.univ).toReal ^ (1 / pStar N) * M.mean g u :=
      mul_pos (Real.rpow_pos_of_pos hV _) hm
    exact starN_split hq hc0 hV.le hlam hC (M.dirichlet_nonneg g u) hX0 ht0 ht1
      (fun _ => by rw [abs_of_pos ht]; exact hdef) (M.starN_minkowski g hN hD hS hu1)

/-- eq:star at one `(X₀, t₀)`, for every `u`, a constant `c` of the signed form of lem:elem. -/
theorem starN_point_signed (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) {lam C c : ℝ} (hlam : 0 < lam)
    (hC : 0 ≤ C) (hP : M.IsPoincareConst g lam) (hS : M.IsSobolevPoincareConst g C)
    (hc : ∀ x : ℝ, |1 + x| ^ pStar N ≤ 1 + pStar N * x + c * (x ^ 2 + |x| ^ pStar N))
    {X0 t0 : ℝ} (hX0 : 0 < X0) (ht0 : 0 < t0) (ht1 : t0 < 1) (u : D) :
    normSq (M.vol g) (pStar N) (M.val u) ≤
      starNCoeff (pStar N) c (M.vol g Set.univ).toReal lam C X0 t0 * M.dirichlet g u +
        (M.vol g Set.univ).toReal ^ (2 / pStar N) * M.mean g u ^ 2 := by
  have hq := two_le_pStar hN
  have hc0 : 0 ≤ c := elem_const_nonneg (by linarith) fun x hx => by
    have := hc x; rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + x)] at this
  refine M.star_of_normalized g hN (starNCoeff_nonneg _ _ _ _ _ _ _) (fun _ => True)
    (fun _ _ _ _ => trivial) (fun u _ hu1 => ?_) u trivial
  obtain ⟨-, -, hV⟩ := M.normalized_facts g hN hD hu1
  exact starN_split hq hc0 hV.le hlam hC (M.dirichlet_nonneg g u) hX0 ht0 ht1
    (fun ht => M.starN_deficit_signed g hN hD hlam hC hP hS hc hu1
      (fun hm => ht (by rw [hm, mul_zero])))
    (M.starN_minkowski g hN hD hS hu1)

/-- From every coefficient of the split to their infimum `starNAtil`. -/
lemma le_starNAtil_of_forall (q c V lam C : ℝ) {a b E : ℝ} (hE : 0 ≤ E)
    (h : ∀ X0 t0 : ℝ, 0 < X0 → 0 < t0 → t0 < 1 → a ≤ starNCoeff q c V lam C X0 t0 * E + b) :
    a ≤ starNAtil q c V lam C * E + b := by
  set S := {A | ∃ X0 t0 : ℝ, 0 < X0 ∧ 0 < t0 ∧ t0 < 1 ∧ starNCoeff q c V lam C X0 t0 = A}
    with hSdef
  have hne : S.Nonempty := ⟨_, 1, 1 / 2, one_pos, by norm_num, by norm_num, rfl⟩
  have hall : ∀ A ∈ S, a ≤ A * E + b := by
    rintro _ ⟨X0, t0, h1, h2, h3, rfl⟩; exact h X0 t0 h1 h2 h3
  show a ≤ sInf S * E + b
  rcases hE.eq_or_lt with hE0 | hEpos
  · obtain ⟨A, hA⟩ := hne
    have h1 := hall A hA
    rw [← hE0, mul_zero] at h1 ⊢
    exact h1
  · have h' : (a - b) / E ≤ sInf S :=
      le_csInf hne fun A hA => by rw [div_le_iff₀ hEpos]; linarith [hall A hA]
    rw [div_le_iff₀ hEpos] at h'
    linarith

/-- eq:star (`u ≥ 0`) with the explicit `Ã = starNAtil`, for any constant `c` of lem:elem and
any valid Poincaré and Sobolev–Poincaré constants `λ`, `C`. -/
theorem starN_of_consts (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) {lam C c : ℝ} (hlam : 0 < lam)
    (hC : 0 ≤ C) (hP : M.IsPoincareConst g lam) (hS : M.IsSobolevPoincareConst g C)
    (hc : ∀ x : ℝ, -1 ≤ x → (1 + x) ^ pStar N ≤ 1 + pStar N * x + c * (x ^ 2 + |x| ^ pStar N)) :
    M.StarIneq g (starNAtil (pStar N) c (M.vol g Set.univ).toReal lam C) :=
  fun u hu0 => le_starNAtil_of_forall _ _ _ _ _ (M.dirichlet_nonneg g u)
    fun _ _ hX0 ht0 ht1 => M.starN_point g hN hD hlam hC hP hS hc hX0 ht0 ht1 u hu0

/-- eq:star for every `u` with the explicit `Ã = starNAtil`, for a constant `c` of the signed
form of lem:elem. -/
theorem starN_signed_of_consts (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) {lam C c : ℝ} (hlam : 0 < lam)
    (hC : 0 ≤ C) (hP : M.IsPoincareConst g lam) (hS : M.IsSobolevPoincareConst g C)
    (hc : ∀ x : ℝ, |1 + x| ^ pStar N ≤ 1 + pStar N * x + c * (x ^ 2 + |x| ^ pStar N)) :
    M.StarIneqSigned g (starNAtil (pStar N) c (M.vol g Set.univ).toReal lam C) :=
  fun u => le_starNAtil_of_forall _ _ _ _ _ (M.dirichlet_nonneg g u)
    fun _ _ hX0 ht0 ht1 => M.starN_point_signed g hN hD hlam hC hP hS hc hX0 ht0 ht1 u

/-! ## 6. Assemblies -/

/-- prop:starN (l.679–689) over the model, at `λ₁` and `C_SP` of def:constants: for any constant
`c_q` of lem:elem, the deficit bound `D = 1 − t² ≤ (2/q) c_q [V^{2/q−1} λ₁⁻¹ X² + t^{2−q} C_SP^q X^q]`
for `u ≥ 0` with `‖u‖_q = 1`, and eq:star (`u ≥ 0`) with the explicit `Ã = starNAtil`. -/
theorem prop_starN (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) (hl1 : 0 < M.lambda1 g)
    (hCsp : ∃ C, M.IsSobolevPoincareConst g C) {c : ℝ}
    (hc : ∀ x : ℝ, -1 ≤ x → (1 + x) ^ pStar N ≤ 1 + pStar N * x + c * (x ^ 2 + |x| ^ pStar N)) :
    (∀ u : D, (∀ x, 0 ≤ M.val u x) →
      (eLpNorm (M.val u) (ENNReal.ofReal (pStar N)) (M.vol g)).toReal = 1 →
      1 - ((M.vol g Set.univ).toReal ^ (1 / pStar N) * M.mean g u) ^ 2 ≤
        2 / pStar N * c * ((M.vol g Set.univ).toReal ^ (2 / pStar N - 1) * (M.lambda1 g)⁻¹ *
            Real.sqrt (M.dirichlet g u) ^ 2 +
          ((M.vol g Set.univ).toReal ^ (1 / pStar N) * M.mean g u) ^ (2 - pStar N) *
            M.Csp g ^ pStar N * Real.sqrt (M.dirichlet g u) ^ pStar N)) ∧
    M.StarIneq g (starNAtil (pStar N) c (M.vol g Set.univ).toReal (M.lambda1 g) (M.Csp g)) := by
  have hP := M.isPoincareConst_lambda1 g hl1
  have hS := M.isSobolevPoincareConst_Csp g hCsp
  refine ⟨fun u hu0 hu1 => ?_, M.starN_of_consts g hN hD hl1 (M.Csp_nonneg g) hP hS hc⟩
  rw [Real.sq_sqrt (M.dirichlet_nonneg g u)]
  exact M.starN_deficit g hN hD hl1 (M.Csp_nonneg g) hP hS hc hu0 hu1

/-- prop:starN, the signed form: eq:star for every `u`, at `max c_q q` for a constant `c_q` of
lem:elem. -/
theorem prop_starN_signed (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) (hl1 : 0 < M.lambda1 g)
    (hCsp : ∃ C, M.IsSobolevPoincareConst g C) {c : ℝ}
    (hc : ∀ x : ℝ, -1 ≤ x → (1 + x) ^ pStar N ≤ 1 + pStar N * x + c * (x ^ 2 + |x| ^ pStar N)) :
    M.StarIneqSigned g
      (starNAtil (pStar N) (max c (pStar N)) (M.vol g Set.univ).toReal (M.lambda1 g) (M.Csp g)) :=
  M.starN_signed_of_consts g hN hD hl1 (M.Csp_nonneg g) (M.isPoincareConst_lambda1 g hl1)
    (M.isSobolevPoincareConst_Csp g hCsp) (elem_signed (two_le_pStar hN) hc)

/-- prop:starN with the explicit `c_q = q² 2^q`: eq:star for every `u` (hence for `u ≥ 0`) with
`Ã = starNAtil q (q² 2^q) V λ₁ C_SP`. -/
theorem prop_starN_explicit (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    (hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g)) (hl1 : 0 < M.lambda1 g)
    (hCsp : ∃ C, M.IsSobolevPoincareConst g C) :
    M.StarIneqSigned g
      (starNAtil (pStar N) (elemC (pStar N)) (M.vol g Set.univ).toReal (M.lambda1 g) (M.Csp g)) :=
  M.starN_signed_of_consts g hN hD hl1 (M.Csp_nonneg g) (M.isPoincareConst_lambda1 g hl1)
    (M.isSobolevPoincareConst_Csp g hCsp) (elem_signed_elemC (two_le_pStar hN))

/-- thm:main (l.179–206) for every `N ≥ 3` at the explicit constant of prop:starN: eq:star for
every `u` (`starN_signed_of_consts`, at `max c q`) fed to `thm_main_signed`, for any valid
Poincaré and Sobolev–Poincaré constants `λ`, `C` and any constant `c` of lem:elem. The composite
of prop:starN and thm:main, as `thm_main_three` is for thm:star3; a special case of thm:main. -/
theorem thm_main_starN (hN : 3 ≤ N) [IsFiniteMeasure (M.vol g)]
    [∀ j, IsFiniteMeasure (M.bvol g j)] (hV : M.vol g ≠ 0) (hB : ∃ j, M.bvol g j ≠ 0)
    (hP : M.MeanPoincare g) (hT : M.TraceBound g) (hI : M.InteriorBump g) {lam C c : ℝ}
    (hlam : 0 < lam) (hC : 0 ≤ C) (hPl : M.IsPoincareConst g lam)
    (hS : M.IsSobolevPoincareConst g C)
    (hc : ∀ x : ℝ, -1 ≤ x → (1 + x) ^ pStar N ≤ 1 + pStar N * x + c * (x ^ 2 + |x| ^ pStar N)) :
    let A := starNAtil (pStar N) (max c (pStar N)) (M.vol g Set.univ).toReal lam C
    M.Fq g M.one / lamMax (1 / M.theta g) 1 (A * M.Fq g M.one / aN N) ≤
        M.infF g (fun _ => cN N) ∧
      M.theta g / (1 + M.theta g) * M.Fq g M.one *
          (1 - A * M.theta g * M.Fq g M.one / (aN N * (1 + M.theta g) ^ 2) +
            mainRem N (M.theta g) A (M.Fq g M.one)) ≤ M.infF g (fun _ => cN N) ∧
      (fun F => mainRem N (M.theta g) A F) =O[𝓝 0] (fun F => F ^ 2) ∧
      (∀ F : ℝ, |A * F / aN N| ≤ (1 + M.theta g) / (4 * M.theta g) →
        |mainRem N (M.theta g) A F| ≤ 20 / 7 * M.theta g / (1 + M.theta g) ^ 2 * (A * F / aN N) ^ 2) ∧
      ∀ F : ℝ, |A * F / aN N| ≤ 1 / 4 → |mainRem N (M.theta g) A F| ≤ 5 / 7 * (A * F / aN N) ^ 2 := by
  intro A
  have hD : ∀ u, AEStronglyMeasurable (M.val u) (M.vol g) := by
    obtain ⟨K, hK⟩ := hP
    exact fun u => (hK u).1.aestronglyMeasurable
  exact M.thm_main_signed g hN hV hB hP hT hI
    (M.starN_signed_of_consts g hN hD hlam hC hPl hS (elem_signed (two_le_pStar hN) hc))

end MeasuredModel

/-! ## 7. A witness: the hypotheses of prop:starN hold on the two-point toy model (`N = 3`) -/

section Toy

/-- On the toy model every hypothesis of `prop_starN` holds, and so does its conclusion at the
explicit `c_q = q² 2^q`. -/
theorem toy_prop_starN :
    IsFiniteMeasure (toyModel.vol toyMetric) ∧
    (∀ u, AEStronglyMeasurable (toyModel.val u) (toyModel.vol toyMetric)) ∧
    0 < toyModel.lambda1 toyMetric ∧ (∃ C, toyModel.IsSobolevPoincareConst toyMetric C) ∧
    toyModel.StarIneqSigned toyMetric (starNAtil (pStar 3) (elemC (pStar 3))
      (toyModel.vol toyMetric Set.univ).toReal (toyModel.lambda1 toyMetric) (toyModel.Csp toyMetric)) := by
  haveI := toy_isFiniteMeasure_vol
  have hD : ∀ u, AEStronglyMeasurable (toyModel.val u) (toyModel.vol toyMetric) := fun _ =>
    (Measurable.of_discrete).aestronglyMeasurable
  exact ⟨toy_isFiniteMeasure_vol, hD, toy_lambda1_pos, ⟨1, toy_isSobolevPoincareConst⟩,
    toyModel.prop_starN_explicit toyMetric le_rfl hD toy_lambda1_pos ⟨1, toy_isSobolevPoincareConst⟩⟩

end Toy

end Yamabe
