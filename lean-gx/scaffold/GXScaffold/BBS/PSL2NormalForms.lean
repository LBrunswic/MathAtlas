import GX.BBS.RP1Circles
import GXScaffold.Interaction.FunnelGTilde

/-!
# BBS § 3.3.1: the normal forms of `SL(2,ℝ)`, `PSL(2,ℝ)` and `G̃` behind the classification of `ℝP¹`-circles

Research target `T-bbs-psl2-normal-forms` (`roadmap/roadmap.toml`; BBS layer L2 in lean-gx,
DEC-192). `papers/bbs/legacy/labeled/colI_v1.tex`, the unlabeled prose of l.740–760. No ledger
label, hence no `**` mark. Imports `GXScaffold.Interaction.FunnelGTilde` (sorry-free) for the
rotation lifts `GX.GTilde.rot`, `GX.GTilde.IsRotLift` and `GX.slRot`.

> **The elliptic case:** Elliptic $\R\PP^1$-circles (\textit{i.e.} with elliptic holonomy) are
> uniquely parametrized by a positive real number (the angle).
>
> **The case $k \geq 1$:** Non-elliptic $\R\PP^1$-circles of degree $k \geq 1$ are uniquely
> parametrized by the pair $(k, [g])$, where $[g]$ is a conjugacy class in $G$. Hyperbolic
> conjugacy classes are uniquely parametrized by a positive real number: the absolute value of
> their trace. There are exactly two parabolic conjugacy classes: the \textit{positive parabolic
> class,} comprising the parabolic elements $g$ such that $gx \geq x$ for every $x$ in
> $\widetilde{\R\PP}^1$, and the \textit{negative parabolic class,} comprising the parabolic
> elements $g$ such that $gx \leq x$ for every $x$ in $\widetilde{\R\PP}^1$ (l.742–750)

The circle-level statements (iso ⇔ conjugate lifted holonomies) are `GX.rp1Iso_iff_conj` in
`GXScaffold.BBS.HSSingularities`, which imports this file; this file supplies the group theory
its three tagged `sorry`s wait on.

## Main declarations

* **The method: one conjugacy criterion.** `GX.slQuad A x y = det [v | A v]` (`v = (x, y)`), the
  quadratic form `c x² + (d - a) x y - b y²`; `GX.slQuad_inv` (`q_{A⁻¹} = -q_A`),
  `GX.slQuad_neg`. If `q_A v = 1` then `[v | A v] ∈ SL(2,ℝ)` conjugates `A` to the companion
  matrix `GX.slCompanion (tr A) = [[0, -1], [1, tr A]]` (`GX.exists_conj_slCompanion`). Hence
  **two elements of `SL(2,ℝ)` with the same trace whose forms both take a positive value are
  `SL(2,ℝ)`-conjugate** (`GX.sl_exists_conj_of_trace_eq`).
* **Hyperbolic** (l.747–748). `SL(2,ℝ)`: `GX.sl_exists_conj_slDiag` (`A ~ diag(λ, λ⁻¹)`,
  `|λ| > 1`, `λ + λ⁻¹ = tr A`, `GX.slDiag`). `PSL(2,ℝ)`:
  `GX.PSL2.IsHyperbolic.exists_conj_slDiag` (`λ > 1`, `tr² = (λ + λ⁻¹)²`); **two hyperbolic
  elements with the same `tr²` are conjugate** `GX.PSL2.IsHyperbolic.exists_conj_of_trSq_eq`;
  with the converse (`GX.sl_trace_conj`), `GX.PSL2.IsHyperbolic.isConj_iff_trSq_eq`. Every
  `|tr| > 2` occurs (`GX.PSL2.isHyperbolic_slDiag`) and `λ > 1` is a complete invariant
  (`GX.PSL2.slDiag_conj_iff`).
* **Parabolic** (l.748–750). `SL(2,ℝ)`: `GX.sl_exists_conj_slUpper` (`A ~ ±[[1, ±1], [0, 1]]`).
  `PSL(2,ℝ)`: `GX.PSL2.IsParabolic.exists_conj_slUpper` (`g ~ [[1, σ], [0, 1]]`, `σ = ±1`),
  `GX.PSL2.isParabolic_slUpper`, the two classes are distinct
  `GX.PSL2.not_exists_conj_slUpper_one_neg_one`; the lift with a fixed point of
  `[[1, s], [0, 1]]` is positive iff `s < 0` (`GX.GTilde.forall_le_iff_of_toPSL_conj_slUpper`);
  **two parabolic elements are conjugate iff their lifts with a fixed point are both positive or
  both negative** `GX.PSL2.IsParabolic.isConj_iff_forall_le`.
* **Elliptic** (l.742–744). `SL(2,ℝ)`: `GX.sl_exists_conj_slRot` (`A ~ rot(α)`, `0 < |α| < π`).
  `PSL(2,ℝ)`: `GX.PSL2.IsElliptic.exists_conj_slRot` (`0 < α < π`), `GX.PSL2.isElliptic_slRot`;
  the angle is the invariant `GX.PSL2.slRot_conj_iff`. `G̃`: an elliptic or central element is
  the rotation lift of its real angle, `GX.GTilde.isRotLift_angle` (`f = h R̃(angle f) h⁻¹`);
  **two elliptic or central elements of `G̃` with the same real angle are conjugate in `G̃`**
  `GX.GTilde.exists_conj_of_angle_eq`, and conversely `GX.GTilde.isConj_iff_angle_eq`.
* **Lifting conjugacies to `G̃`.** `GX.GTilde.exists_conj_of_toPSL_conj` (lifts with a fixed
  point of conjugate elements are conjugate in `G̃`), `GX.GTilde.forall_le_iff_of_conj`.

## For `GXScaffold.BBS.HSSingularities` (target `T-bbs-hs-remark-existence`)

* `GX.PSL2.IsHyperbolic.isConj_iff`, the `sorry` of `⇐`: `exact
  PSL2.IsHyperbolic.exists_conj_of_trSq_eq hg hg' htr`.
* `GX.PSL2.IsParabolic.isConj_iff`: `exact PSL2.IsParabolic.isConj_iff_forall_le hg hg' hf hf'
  hfix hfix'` (same signature).
* `GX.rp1Iso_of_angle_eq`: `exact (rp1Iso_iff_conj hf hf').2 (GTilde.exists_conj_of_angle_eq he
  he' hθ)`.

## Hypothesis checklist

| BBS | here |
|---|---|
| elliptic (l.743) | ✓ `GX.PSL2.IsElliptic` (`tr² < 4`), and central (`toPSL f = 1`) as in HSSingularities (OQ-113 (d)) |
| "the angle" (l.744) | ✓ `GX.GTilde.angle` (`2π` × translation number) |
| hyperbolic, "absolute value of their trace" (l.747–748) | ✓ `GX.PSL2.IsHyperbolic`, `GX.PSL2.trSq` (`|tr|` ⇔ `tr²`) |
| parabolic, `g x ≥ x` (l.748–750) | ⚠ read: `GX.PSL2.IsParabolic`; `g x` read on the lift of `g` with a fixed point, as in `GX.PSL2.IsParabolic.isConj_iff` |

## SCOPE (disclosed)

* Group theory only: the circle statements are in HSSingularities.
* The parabolic classes are told apart by the lift with a fixed point (l.749–750 writes `g x`
  for `g ∈ G`); every lift with a fixed point gives the same answer
  (`GX.GTilde.forall_le_iff_of_toPSL_conj_slUpper`).

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

open Set Real
open scoped MatrixGroups

namespace GX

set_option linter.unusedSectionVars false

/-! ### The quadratic form `det [v | A v]` and the companion matrix -/

/-- The companion matrix `[[0, -1], [1, t]] ∈ SL(2,ℝ)` of `X² - t X + 1`. -/
def slCompanion (t : ℝ) : SL(2, ℝ) :=
  ⟨!![0, -1; 1, t], by simp [Matrix.det_fin_two_of]⟩

/-- `diag(λ, λ⁻¹) ∈ SL(2,ℝ)`. -/
def slDiag (l : ℝˣ) : SL(2, ℝ) :=
  ⟨!![(l : ℝ), 0; 0, ((l⁻¹ : ℝˣ) : ℝ)], by simp [Matrix.det_fin_two_of]⟩

/-- The quadratic form `q_A(x, y) = det [v | A v]`, `v = (x, y)`:
`c x² + (d - a) x y - b y²` for `A = [[a, b], [c, d]]`. Its discriminant is `tr(A)² - 4`. -/
def slQuad (A : SL(2, ℝ)) (x y : ℝ) : ℝ :=
  (A : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * x ^ 2 +
    ((A : Matrix (Fin 2) (Fin 2) ℝ) 1 1 - (A : Matrix (Fin 2) (Fin 2) ℝ) 0 0) * x * y -
    (A : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * y ^ 2

theorem slQuad_smul (A : SL(2, ℝ)) (s x y : ℝ) :
    slQuad A (s * x) (s * y) = s ^ 2 * slQuad A x y := by
  unfold slQuad; ring

theorem slQuad_inv (A : SL(2, ℝ)) (x y : ℝ) : slQuad A⁻¹ x y = -slQuad A x y := by
  simp only [slQuad, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  ring

theorem slQuad_neg (A : SL(2, ℝ)) (x y : ℝ) : slQuad (-A) x y = -slQuad A x y := by
  simp only [slQuad, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  ring

theorem sl_trace_inv (A : SL(2, ℝ)) :
    Matrix.trace ((A⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two_of,
    Matrix.trace_fin_two, add_comm]

theorem sl_trace_neg (A : SL(2, ℝ)) :
    Matrix.trace ((-A : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      -Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg]

/-- The trace is a conjugacy invariant of `SL(2,ℝ)`. -/
theorem sl_trace_conj (P A : SL(2, ℝ)) :
    Matrix.trace ((P * A * P⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.trace_mul_cycle, Matrix.adjugate_mul, P.2,
    one_smul, Matrix.one_mul]

/-- **The companion normal form.** If `det [v | A v] = 1`, then `P = [v | A v] ∈ SL(2,ℝ)` and
`A = P C P⁻¹`, `C = [[0, -1], [1, tr A]]` (Cayley–Hamilton: `A² v = tr(A) A v - v`). -/
theorem exists_conj_slCompanion (A : SL(2, ℝ)) {x y : ℝ} (h : slQuad A x y = 1) :
    ∃ P : SL(2, ℝ),
      A = P * slCompanion (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)) * P⁻¹ := by
  induction A using Matrix.SpecialLinearGroup.fin_two_induction with
  | h a b c d hdet =>
  have hq : c * x ^ 2 + (d - a) * x * y - b * y ^ 2 = 1 := by simpa [slQuad] using h
  refine ⟨⟨!![x, a * x + b * y; y, c * x + d * y], by
    rw [Matrix.det_fin_two_of]; linear_combination hq⟩, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slCompanion, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two_of]
  all_goals first
    | ring1
    | linear_combination (-x) * hdet
    | linear_combination (-y) * hdet

theorem exists_conj_slCompanion_of_pos (A : SL(2, ℝ)) {x y : ℝ} (h : 0 < slQuad A x y) :
    ∃ P : SL(2, ℝ),
      A = P * slCompanion (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)) * P⁻¹ := by
  refine exists_conj_slCompanion A (x := (Real.sqrt (slQuad A x y))⁻¹ * x)
    (y := (Real.sqrt (slQuad A x y))⁻¹ * y) ?_
  rw [slQuad_smul, inv_pow, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']

/-- **The conjugacy criterion.** Two elements of `SL(2,ℝ)` with the same trace, whose forms
`q_A`, `q_B` both take a positive value, are `SL(2,ℝ)`-conjugate. -/
theorem sl_exists_conj_of_trace_eq {A B : SL(2, ℝ)}
    (htr : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.trace (B : Matrix (Fin 2) (Fin 2) ℝ))
    (hA : ∃ x y, 0 < slQuad A x y) (hB : ∃ x y, 0 < slQuad B x y) :
    ∃ P : SL(2, ℝ), B = P * A * P⁻¹ := by
  obtain ⟨x, y, hxy⟩ := hA
  obtain ⟨u, v, huv⟩ := hB
  obtain ⟨P, hP⟩ := exists_conj_slCompanion_of_pos A hxy
  obtain ⟨Q, hQ⟩ := exists_conj_slCompanion_of_pos B huv
  rw [← htr] at hQ
  generalize slCompanion (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)) = C at hP hQ
  refine ⟨Q * P⁻¹, ?_⟩
  rw [hQ, hP]
  group

/-- A central element of `SL(2,ℝ)` (`±1`) has `tr² = 4`. -/
theorem trace_sq_eq_four_of_mem_center {A : SL(2, ℝ)} (hA : A ∈ Subgroup.center SL(2, ℝ)) :
    Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 = 4 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr2 : r ^ 2 = 1 := by simpa using hr
  rw [← hrA, Matrix.trace_fin_two]
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
  linear_combination 4 * hr2

/-- The form of a non-central element is not identically zero. -/
theorem exists_slQuad_ne_zero {A : SL(2, ℝ)} (hA : A ∉ Subgroup.center SL(2, ℝ)) :
    ∃ x y, slQuad A x y ≠ 0 := by
  induction A using Matrix.SpecialLinearGroup.fin_two_induction with
  | h a b c d hdet =>
  by_contra hne
  push Not at hne
  apply hA
  have h10 := hne 1 0
  have h01 := hne 0 1
  have h11 := hne 1 1
  simp only [slQuad, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h10 h01 h11
  have hc : c = 0 := by linear_combination h10
  have hb : b = 0 := by linear_combination -h01
  have hd : d = a := by linear_combination h11 - h10 - h01
  subst hc hb hd
  refine Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨d, ?_, ?_⟩
  · simp only [Fintype.card_fin]; linear_combination hdet
  · ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The form of a hyperbolic element is indefinite: it takes a positive value. -/
theorem exists_slQuad_pos_of_four_lt {A : SL(2, ℝ)}
    (h : 4 < Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ^ 2) : ∃ x y, 0 < slQuad A x y := by
  induction A using Matrix.SpecialLinearGroup.fin_two_induction with
  | h a b c d hdet =>
  simp only [Matrix.trace_fin_two_of] at h
  simp only [slQuad, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · refine ⟨a - d, 2 * c, ?_⟩
    have e : c * (a - d) ^ 2 + (d - a) * (a - d) * (2 * c) - b * (2 * c) ^ 2 =
        -c * ((a + d) ^ 2 - 4) := by linear_combination (4 * c) * hdet
    rw [e]
    exact mul_pos (by linarith) (by linarith)
  · refine ⟨b + 1, d - a, ?_⟩
    have e : 0 * (b + 1) ^ 2 + (d - a) * (b + 1) * (d - a) - b * (d - a) ^ 2 =
        (a + d) ^ 2 - 4 := by linear_combination (-4) * hdet
    rw [e]; linarith
  · exact ⟨1, 0, by simpa using hc⟩

/-! ### `PSL(2,ℝ)`: classes of conjugates and of `-A` -/

theorem pslMk_neg (A : SL(2, ℝ)) : pslMk (-A) = pslMk A := by
  have hc : (-1 : SL(2, ℝ)) ∈ Subgroup.center SL(2, ℝ) :=
    Subgroup.mem_center_iff.2 fun B => by rw [mul_neg, neg_mul, mul_one, one_mul]
  show (QuotientGroup.mk (-A) : PSL(2, ℝ)) = QuotientGroup.mk A
  rw [← neg_one_mul A, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hc, one_mul]

theorem pslMk_conj (P A : SL(2, ℝ)) : pslMk (P * A * P⁻¹) = pslMk P * pslMk A * (pslMk P)⁻¹ := by
  simp only [pslMk, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

/-- Every element of `PSL(2,ℝ)` has a representative of non-negative trace. -/
theorem exists_pslMk_eq_trace_nonneg (g : PSL(2, ℝ)) :
    ∃ A : SL(2, ℝ), pslMk A = g ∧ 0 ≤ Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨A, rfl⟩ := pslMk_surjective g
  rcases le_total 0 (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ)) with h | h
  · exact ⟨A, rfl, h⟩
  · exact ⟨-A, pslMk_neg A, by rw [sl_trace_neg]; linarith⟩

/-! ### Hyperbolic elements: `diag(λ, λ⁻¹)` -/

/-- `t² > 4` is `λ + λ⁻¹` for a real `λ` with `|λ| > 1`. -/
theorem exists_abs_gt_one_add_inv_eq {t : ℝ} (h : 4 < t ^ 2) :
    ∃ l : ℝ, 1 < |l| ∧ l + l⁻¹ = t := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ t ^ 2 - 4 by linarith)
  have hs0 := Real.sqrt_nonneg (t ^ 2 - 4)
  set s := Real.sqrt (t ^ 2 - 4)
  rcases le_or_gt 0 t with ht | ht
  · have ht2 : 2 < t := by nlinarith
    refine ⟨(t + s) / 2, ?_, ?_⟩
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [inv_eq_of_mul_eq_one_right (b := (t - s) / 2) (by linear_combination -hs / 4)]; ring
  · have ht2 : t < -2 := by nlinarith
    refine ⟨(t - s) / 2, ?_, ?_⟩
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [inv_eq_of_mul_eq_one_right (b := (t + s) / 2) (by linear_combination -hs / 4)]; ring

/-- **The hyperbolic normal form in `SL(2,ℝ)`**: `A ~ diag(λ, λ⁻¹)` with `|λ| > 1`. -/
theorem sl_exists_conj_slDiag {A : SL(2, ℝ)}
    (h : 4 < Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ^ 2) :
    ∃ l : ℝˣ, 1 < |(l : ℝ)| ∧
      (l : ℝ) + ((l⁻¹ : ℝˣ) : ℝ) = Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ∧
      ∃ P : SL(2, ℝ), A = P * slDiag l * P⁻¹ := by
  obtain ⟨l, hl1, hlt⟩ := exists_abs_gt_one_add_inv_eq h
  have hl0 : l ≠ 0 := by rintro rfl; simp at hl1; linarith
  refine ⟨Units.mk0 l hl0, by simpa using hl1, by simpa using hlt, ?_⟩
  refine sl_exists_conj_of_trace_eq (A := slDiag (Units.mk0 l hl0)) (B := A) ?_ ?_
    (exists_slQuad_pos_of_four_lt h)
  · simpa [slDiag, Matrix.trace_fin_two_of] using hlt
  · have hne : l⁻¹ - l ≠ 0 := by
      intro h0
      have h1 : l * l = 1 := calc
        l * l = l * l⁻¹ := by rw [show l⁻¹ = l by linarith]
        _ = 1 := mul_inv_cancel₀ hl0
      nlinarith [abs_mul_abs_self l, abs_nonneg l]
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact ⟨1, -1, by simp [slQuad, slDiag]; linarith⟩
    · exact ⟨1, 1, by simp [slQuad, slDiag]; linarith⟩

namespace PSL2

theorem trSq_pslMk_slDiag (l : ℝˣ) :
    trSq (pslMk (slDiag l)) = ((l : ℝ) + ((l⁻¹ : ℝˣ) : ℝ)) ^ 2 := by
  rw [trSq_mk]
  simp [slDiag, Matrix.trace_fin_two_of]

/-- **The hyperbolic normal form in `PSL(2,ℝ)`** (l.747–748): `g ~ diag(λ, λ⁻¹)`, `λ > 1`,
`tr² = (λ + λ⁻¹)²`. -/
theorem IsHyperbolic.exists_conj_slDiag {g : PSL(2, ℝ)} (hg : IsHyperbolic g) :
    ∃ l : ℝˣ, 1 < (l : ℝ) ∧ trSq g = ((l : ℝ) + ((l⁻¹ : ℝˣ) : ℝ)) ^ 2 ∧
      ∃ c : PSL(2, ℝ), g = c * pslMk (slDiag l) * c⁻¹ := by
  obtain ⟨A, rfl, hA⟩ := exists_pslMk_eq_trace_nonneg g
  have htr : 4 < Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 := hg
  obtain ⟨l, hl1, hlt, P, hP⟩ := sl_exists_conj_slDiag htr
  have ht2 : 2 < Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) := by nlinarith
  have hlpos : 1 < (l : ℝ) := by
    rcases lt_or_ge (l : ℝ) 0 with hneg | hnn
    · exfalso
      have : ((l⁻¹ : ℝˣ) : ℝ) < 0 := by rw [Units.val_inv_eq_inv_val]; exact inv_lt_zero.2 hneg
      linarith
    · rwa [abs_of_nonneg hnn] at hl1
  refine ⟨l, hlpos, by rw [trSq_mk, ← hlt], pslMk P, by rw [hP, pslMk_conj]⟩

/-- **Two hyperbolic elements of `PSL(2,ℝ)` with the same `tr²` are conjugate** (l.747–748). -/
theorem IsHyperbolic.exists_conj_of_trSq_eq {g g' : PSL(2, ℝ)} (hg : IsHyperbolic g)
    (hg' : IsHyperbolic g') (h : trSq g = trSq g') : ∃ c : PSL(2, ℝ), g' = c * g * c⁻¹ := by
  obtain ⟨A, rfl, hA⟩ := exists_pslMk_eq_trace_nonneg g
  obtain ⟨B, rfl, hB⟩ := exists_pslMk_eq_trace_nonneg g'
  rw [trSq_mk, trSq_mk] at h
  have htr := (pow_left_inj₀ hA hB two_ne_zero).1 h
  obtain ⟨P, hP⟩ := sl_exists_conj_of_trace_eq htr (exists_slQuad_pos_of_four_lt hg)
    (exists_slQuad_pos_of_four_lt hg')
  exact ⟨pslMk P, by rw [hP, pslMk_conj]⟩

/-- **Hyperbolic conjugacy classes are parametrised by `|tr|`** (l.747–748). -/
theorem IsHyperbolic.isConj_iff_trSq_eq {g g' : PSL(2, ℝ)} (hg : IsHyperbolic g)
    (hg' : IsHyperbolic g') : (∃ c : PSL(2, ℝ), g' = c * g * c⁻¹) ↔ trSq g = trSq g' := by
  refine ⟨fun ⟨c, hc⟩ => ?_, fun h => hg.exists_conj_of_trSq_eq hg' h⟩
  obtain ⟨C, rfl⟩ := pslMk_surjective c
  obtain ⟨A, rfl⟩ := pslMk_surjective g
  rw [hc, ← pslMk_conj, trSq_mk, trSq_mk, sl_trace_conj]

/-- `diag(λ, λ⁻¹)`, `|λ| > 1`, is hyperbolic: every value `|tr| > 2` occurs. -/
theorem isHyperbolic_slDiag {l : ℝˣ} (hl : 1 < |(l : ℝ)|) : IsHyperbolic (pslMk (slDiag l)) := by
  show 4 < trSq (pslMk (slDiag l))
  rw [trSq_pslMk_slDiag, Units.val_inv_eq_inv_val]
  have h1 : (l : ℝ) * (l : ℝ)⁻¹ = 1 := mul_inv_cancel₀ l.ne_zero
  have hne : (l : ℝ) - (l : ℝ)⁻¹ ≠ 0 := by
    intro h0
    have : (l : ℝ) * (l : ℝ) = 1 := by rw [show (l : ℝ)⁻¹ = l by linarith] at h1; exact h1
    nlinarith [abs_mul_abs_self (l : ℝ), abs_nonneg (l : ℝ)]
  have e : ((l : ℝ) + (l : ℝ)⁻¹) ^ 2 = ((l : ℝ) - (l : ℝ)⁻¹) ^ 2 + 4 := by
    linear_combination 4 * h1
  rw [e]
  have := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  linarith

/-- **`λ > 1` parametrises the hyperbolic classes**: `diag(λ, λ⁻¹)` and `diag(λ', λ'⁻¹)`,
`λ, λ' > 1`, are conjugate in `PSL(2,ℝ)` iff `λ = λ'`. -/
theorem slDiag_conj_iff {l l' : ℝˣ} (hl : 1 < (l : ℝ)) (hl' : 1 < (l' : ℝ)) :
    (∃ c : PSL(2, ℝ), pslMk (slDiag l') = c * pslMk (slDiag l) * c⁻¹) ↔ l = l' := by
  rw [IsHyperbolic.isConj_iff_trSq_eq (isHyperbolic_slDiag (by rwa [abs_of_pos (by linarith)]))
    (isHyperbolic_slDiag (by rwa [abs_of_pos (by linarith)])), trSq_pslMk_slDiag,
    trSq_pslMk_slDiag, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
  refine ⟨fun h => ?_, by rintro rfl; rfl⟩
  have hp : 0 ≤ (l : ℝ) + (l : ℝ)⁻¹ := by have := inv_pos.2 (by linarith : (0 : ℝ) < l); linarith
  have hp' : 0 ≤ (l' : ℝ) + (l' : ℝ)⁻¹ := by
    have := inv_pos.2 (by linarith : (0 : ℝ) < l'); linarith
  have h2 := (pow_left_inj₀ hp hp' two_ne_zero).1 h
  have ha : (l : ℝ) * (l : ℝ)⁻¹ = 1 := mul_inv_cancel₀ l.ne_zero
  have hb : (l' : ℝ) * (l' : ℝ)⁻¹ = 1 := mul_inv_cancel₀ l'.ne_zero
  have e : ((l : ℝ) - l') * ((l : ℝ) * l' - 1) = 0 := by
    linear_combination ((l : ℝ) * l') * h2 - (l' : ℝ) * ha + (l : ℝ) * hb
  rcases mul_eq_zero.1 e with e | e
  · exact Units.ext (by linarith)
  · nlinarith

end PSL2

/-! ### Parabolic elements: `±[[1, ±1], [0, 1]]` -/

theorem slUpper_inv (s : ℝ) : (slUpper s)⁻¹ = slUpper (-s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slUpper, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- The case `tr A = 2`: `A ~ [[1, -1], [0, 1]]` if `q_A` takes a positive value, and
`A ~ [[1, 1], [0, 1]]` if it takes a negative one. -/
theorem sl_exists_conj_slUpper_of_trace_eq_two {A : SL(2, ℝ)}
    (h : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = 2) (hq : ∃ x y, slQuad A x y ≠ 0) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ P : SL(2, ℝ), A = P * slUpper σ * P⁻¹ := by
  have hU : Matrix.trace ((slUpper (-1) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = 2 := by
    norm_num [slUpper, Matrix.trace_fin_two_of]
  have hUq : ∃ x y, 0 < slQuad (slUpper (-1)) x y := ⟨0, 1, by simp [slQuad, slUpper]⟩
  obtain ⟨x, y, hxy⟩ := hq
  rcases lt_or_gt_of_ne hxy with hneg | hpos
  · obtain ⟨P, hP⟩ := sl_exists_conj_of_trace_eq (A := slUpper (-1)) (B := A⁻¹)
      (by rw [hU, sl_trace_inv, h]) hUq ⟨x, y, by rw [slQuad_inv]; linarith⟩
    refine ⟨1, Or.inl rfl, P, ?_⟩
    rw [show slUpper 1 = (slUpper (-1))⁻¹ by rw [slUpper_inv, neg_neg], ← inv_inv A, hP]
    group
  · obtain ⟨P, hP⟩ := sl_exists_conj_of_trace_eq (A := slUpper (-1)) (B := A) (by rw [hU, h])
      hUq ⟨x, y, hpos⟩
    exact ⟨-1, Or.inr rfl, P, hP⟩

/-- **The parabolic normal form in `SL(2,ℝ)`**: `A ~ ±[[1, σ], [0, 1]]`, `σ = ±1`. -/
theorem sl_exists_conj_slUpper {A : SL(2, ℝ)}
    (h : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 = 4)
    (hA : A ∉ Subgroup.center SL(2, ℝ)) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ P : SL(2, ℝ),
      A = P * slUpper σ * P⁻¹ ∨ A = P * (-slUpper σ) * P⁻¹ := by
  have hq := exists_slQuad_ne_zero hA
  have ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = 2 ∨
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = -2 := by
    have : (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) - 2) *
        (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) + 2) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h1 | h1
    · left; linarith
    · right; linarith
  rcases ht with ht | ht
  · obtain ⟨σ, hσ, P, hP⟩ := sl_exists_conj_slUpper_of_trace_eq_two ht hq
    exact ⟨σ, hσ, P, Or.inl hP⟩
  · obtain ⟨x, y, hxy⟩ := hq
    obtain ⟨σ, hσ, P, hP⟩ := sl_exists_conj_slUpper_of_trace_eq_two (A := -A)
      (by rw [sl_trace_neg, ht]; norm_num) ⟨x, y, by rw [slQuad_neg]; exact neg_ne_zero.2 hxy⟩
    refine ⟨σ, hσ, P, Or.inr ?_⟩
    rw [mul_neg, neg_mul, ← hP, neg_neg]

namespace PSL2

theorem isParabolic_slUpper {s : ℝ} (hs : s ≠ 0) : IsParabolic (pslMk (slUpper s)) := by
  refine ⟨by rw [trSq_mk]; norm_num [slUpper, Matrix.trace_fin_two_of], fun h => hs ?_⟩
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1
    ((QuotientGroup.eq_one_iff (slUpper s)).1 h)
  have := congrFun (congrFun hr 0) 1
  simpa [slUpper] using this.symm

/-- **The parabolic normal form in `PSL(2,ℝ)`** (l.748): `g ~ [[1, σ], [0, 1]]`, `σ = ±1`. -/
theorem IsParabolic.exists_conj_slUpper {g : PSL(2, ℝ)} (hg : IsParabolic g) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ c : PSL(2, ℝ), g = c * pslMk (slUpper σ) * c⁻¹ := by
  obtain ⟨A, rfl, hA⟩ := exists_pslMk_eq_trace_nonneg g
  obtain ⟨htr, hne⟩ := hg
  rw [trSq_mk] at htr
  have ht : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) = 2 :=
    (pow_left_inj₀ hA (by norm_num : (0 : ℝ) ≤ 2) two_ne_zero).1 (by rw [htr]; norm_num)
  have hcen : A ∉ Subgroup.center SL(2, ℝ) := fun h => hne ((QuotientGroup.eq_one_iff A).2 h)
  obtain ⟨σ, hσ, P, hP⟩ := sl_exists_conj_slUpper_of_trace_eq_two ht (exists_slQuad_ne_zero hcen)
  exact ⟨σ, hσ, pslMk P, by rw [hP, pslMk_conj]⟩

end PSL2

namespace GTilde

/-- Two elements of `G̃` over conjugate elements of `PSL(2,ℝ)` are conjugate up to a deck
transformation `δⁿ`, by a lift of the conjugator. -/
theorem exists_delta_zpow_of_toPSL_conj {f f' : GTilde} {c : PSL(2, ℝ)}
    (h : toPSL f' = c * toPSL f * c⁻¹) :
    ∃ (κ : GTilde) (n : ℤ), toPSL κ = c ∧ f' = delta ^ n * (κ * f * κ⁻¹) := by
  obtain ⟨κ, rfl⟩ := toPSL_surjective c
  have hker : f' * (κ * f * κ⁻¹)⁻¹ ∈ toPSL.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, h, mul_inv_cancel]
  rw [ker_toPSL, Subgroup.mem_zpowers_iff] at hker
  obtain ⟨n, hn⟩ := hker
  exact ⟨κ, n, rfl, by rw [hn, inv_mul_cancel_right]⟩

/-- **Lifts with a fixed point of conjugate elements are conjugate in `G̃`**, by a lift of the
conjugator. -/
theorem exists_conj_of_toPSL_conj {f f' : GTilde} {c : PSL(2, ℝ)} (hfix : ∃ x, f x = x)
    (hfix' : ∃ x, f' x = x) (h : toPSL f' = c * toPSL f * c⁻¹) :
    ∃ κ : GTilde, toPSL κ = c ∧ f' = κ * f * κ⁻¹ := by
  obtain ⟨κ, n, hκ, hn⟩ := exists_delta_zpow_of_toPSL_conj h
  obtain ⟨x, hx⟩ := hfix
  have hfix₁ : (κ * f * κ⁻¹) (κ x) = κ x := by
    rw [coe_mul_apply, coe_mul_apply, inv_apply_apply, hx]
  have hn0 : (0 : ℤ) = n :=
    delta_zpow_mul_unique hfix' ⟨κ x, hfix₁⟩ (by rw [zpow_zero, one_mul, ← hn])
  rw [← hn0, zpow_zero, one_mul] at hn
  exact ⟨κ, hκ, hn⟩

/-- Positivity (`x ≤ f x` everywhere) is a conjugacy invariant of `G̃`. -/
theorem forall_le_iff_of_conj {f f' κ : GTilde} (h : f' = κ * f * κ⁻¹) :
    (∀ x, x ≤ f x) ↔ (∀ x, x ≤ f' x) := by
  subst h
  refine ⟨fun h x => le_conj_apply h κ x, fun h x => ?_⟩
  have := le_conj_apply h κ⁻¹ x
  rwa [show κ⁻¹ * (κ * f * κ⁻¹) * κ⁻¹⁻¹ = f by group] at this

/-- **The lift with a fixed point of `[[1, s], [0, 1]]` is positive iff `s < 0`.** -/
theorem forall_le_iff_of_toPSL_slUpper {f : GTilde} {s : ℝ} (hs : s ≠ 0)
    (hf : toPSL f = pslMk (slUpper s)) (hfix : ∃ x, f x = x) : (∀ x, x ≤ f x) ↔ s < 0 := by
  have hp : IsParabolic f := by
    show PSL2.IsParabolic (toPSL f)
    rw [hf]; exact PSL2.isParabolic_slUpper hs
  -- `[[1, s], [0, 1]]` fixes `proj 0 = [1 : 0]`, so `f 0 = 0`
  have hfix0 : toPSL f • RP1.proj 0 = RP1.proj 0 := by
    rw [hf, pslMk_smul, RP1.proj_eq_mk, mul_zero, Circle.exp_zero, Circle.coe_one,
      RP1.sl_smul_mk _ one_ne_zero]
    congr 1
    rw [slLin_apply]
    apply Complex.ext <;> simp [slUpper]
  obtain ⟨x₀, hx₀⟩ := hfix
  have h0 : f 0 = 0 := by
    have h1 : toPSL f • RP1.proj x₀ = RP1.proj x₀ := by rw [← proj_apply, hx₀]
    obtain ⟨n, hn⟩ := RP1.proj_eq_proj_iff.1 (PSL2.IsParabolic.eq_of_smul_eq hp h1 hfix0)
    have e : x₀ + ((-n : ℤ) : ℝ) = 0 := by rw [hn]; push_cast; ring
    have := map_add_int f x₀ (-n)
    rwa [hx₀, e] at this
  have h1 : f 1 = 1 := by
    have := map_add_int f 0 1
    rw [h0] at this
    simpa using this
  have hu0 : 0 < f (1 / 2) := by
    have := GTilde.strictMono f (show (0 : ℝ) < 1 / 2 by norm_num)
    rwa [h0] at this
  have hu1 : f (1 / 2) < 1 := by
    have := GTilde.strictMono f (show (1 / 2 : ℝ) < 1 by norm_num)
    rwa [h1] at this
  -- `proj (f (1/2)) = [s : 1]`
  have hpu : RP1.mk (Circle.exp (π * f (1 / 2)) : ℂ) = RP1.mk ⟨s, 1⟩ := by
    rw [← RP1.proj_eq_mk, proj_apply, hf, pslMk_smul, RP1.proj_eq_mk,
      RP1.sl_smul_mk _ (Circle.coe_ne_zero _), show π * (1 / 2 : ℝ) = π / 2 by ring]
    congr 1
    rw [slLin_apply, Circle.coe_exp]
    apply Complex.ext <;>
      simp [slUpper]
  have hne : (⟨s, 1⟩ : ℂ) ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0
    simp at this
  obtain ⟨c, hc⟩ := (RP1.mk_eq_mk_iff (Circle.coe_ne_zero _) hne).1 hpu
  have hre := congrArg Complex.re hc
  have him := congrArg Complex.im hc
  simp only [Circle.coe_exp, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul,
    sub_zero, add_zero] at hre him
  have hsin : 0 < Real.sin (π * f (1 / 2)) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc0 : 0 < c := by
    by_contra hc0
    push Not at hc0
    nlinarith
  constructor
  · intro hpos
    have hu : 1 / 2 ≤ f (1 / 2) := hpos (1 / 2)
    have hcos : Real.cos (π * f (1 / 2)) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
    have : s ≤ 0 := by
      rw [hre]
      exact mul_nonpos_of_nonneg_of_nonpos hc0.le hcos
    exact lt_of_le_of_ne this hs
  · intro hs0
    have hu : 1 / 2 < f (1 / 2) := by
      by_contra hh
      push Not at hh
      have : 0 ≤ Real.cos (π * f (1 / 2)) :=
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])
      nlinarith
    exact hp.le_apply ⟨0, h0⟩ ⟨1 / 2, hu⟩

/-- The same for every conjugate of `[[1, s], [0, 1]]`. -/
theorem forall_le_iff_of_toPSL_conj_slUpper {f : GTilde} {s : ℝ} {c : PSL(2, ℝ)} (hs : s ≠ 0)
    (hf : toPSL f = c * pslMk (slUpper s) * c⁻¹) (hfix : ∃ x, f x = x) :
    (∀ x, x ≤ f x) ↔ s < 0 := by
  obtain ⟨κ, rfl⟩ := toPSL_surjective c
  obtain ⟨x, hx⟩ := hfix
  have hc : f = κ * (κ⁻¹ * f * κ) * κ⁻¹ := by group
  refine (forall_le_iff_of_conj hc).symm.trans (forall_le_iff_of_toPSL_slUpper hs ?_ ⟨κ⁻¹ x, ?_⟩)
  · rw [map_mul, map_mul, map_inv, hf]; group
  · rw [coe_mul_apply, coe_mul_apply, apply_inv_apply, hx]

end GTilde

namespace PSL2

/-- **The two parabolic classes are distinct** (l.748–750): `[[1, 1], [0, 1]]` and
`[[1, -1], [0, 1]]` are not conjugate in `PSL(2,ℝ)`. -/
theorem not_exists_conj_slUpper_one_neg_one :
    ¬ ∃ c : PSL(2, ℝ), pslMk (slUpper (-1)) = c * pslMk (slUpper 1) * c⁻¹ := by
  rintro ⟨c, hc⟩
  have hp := isParabolic_slUpper (s := -1) (by norm_num)
  obtain ⟨f, hf⟩ := GTilde.toPSL_surjective (pslMk (slUpper (-1)))
  have hne : ¬ GTilde.IsElliptic f := fun he =>
    (show trSq (GTilde.toPSL f) < 4 from he).ne (by rw [hf]; exact hp.1)
  obtain ⟨k, f₀, hfix, rfl⟩ := GTilde.exists_delta_zpow_mul_of_not_isElliptic hne
  have hf₀ : GTilde.toPSL f₀ = pslMk (slUpper (-1)) := by
    rw [← hf, map_mul, map_zpow, GTilde.toPSL_delta, one_zpow, one_mul]
  have h1 := GTilde.forall_le_iff_of_toPSL_slUpper (by norm_num) hf₀ hfix
  have h2 := GTilde.forall_le_iff_of_toPSL_conj_slUpper one_ne_zero (hf₀.trans hc) hfix
  have := h2.1 (h1.2 (by norm_num))
  norm_num at this

/-- **There are exactly two parabolic conjugacy classes** (l.748–750): two parabolic elements of
`PSL(2,ℝ)` are conjugate iff their lifts with a fixed point are both positive or both negative.
The signature of `GX.PSL2.IsParabolic.isConj_iff` (HSSingularities). -/
theorem IsParabolic.isConj_iff_forall_le {g g' : PSL(2, ℝ)} (hg : IsParabolic g)
    (hg' : IsParabolic g') {f f' : GTilde} (hf : GTilde.toPSL f = g) (hf' : GTilde.toPSL f' = g')
    (hfix : ∃ x, f x = x) (hfix' : ∃ x, f' x = x) :
    (∃ c : PSL(2, ℝ), g' = c * g * c⁻¹) ↔ ((∀ x, x ≤ f x) ↔ (∀ x, x ≤ f' x)) := by
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨κ, -, hκ⟩ := GTilde.exists_conj_of_toPSL_conj hfix hfix' (by rw [hf', hf])
    exact GTilde.forall_le_iff_of_conj hκ
  · intro hiff
    obtain ⟨σ, hσ, c, hc⟩ := hg.exists_conj_slUpper
    obtain ⟨σ', hσ', c', hc'⟩ := hg'.exists_conj_slUpper
    have h1 := GTilde.forall_le_iff_of_toPSL_conj_slUpper
      (by rcases hσ with rfl | rfl <;> norm_num) (hf.trans hc) hfix
    have h2 := GTilde.forall_le_iff_of_toPSL_conj_slUpper
      (by rcases hσ' with rfl | rfl <;> norm_num) (hf'.trans hc') hfix'
    have hσσ : σ = σ' := by
      have : σ < 0 ↔ σ' < 0 := h1.symm.trans (hiff.trans h2)
      rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;> first | rfl | norm_num at this
    subst hσσ
    refine ⟨c' * c⁻¹, ?_⟩
    rw [hc', hc]
    group

end PSL2

/-! ### Elliptic elements: rotations -/

theorem slRot_zero : slRot 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slRot]

theorem slRot_inv (α : ℝ) : (slRot α)⁻¹ = slRot (-α) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slRot, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- The case `q_A` positive: `A ~ rot(α)`, `α = arccos(tr A / 2) ∈ (0, π)`. -/
theorem sl_exists_conj_slRot_of_pos {A : SL(2, ℝ)}
    (h : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 < 4) (hq : ∃ x y, 0 < slQuad A x y) :
    ∃ α : ℝ, 0 < α ∧ α < π ∧ ∃ P : SL(2, ℝ), A = P * slRot α * P⁻¹ := by
  have ht1 : -1 < Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) / 2 := by nlinarith
  have ht2 : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) / 2 < 1 := by nlinarith
  refine ⟨Real.arccos (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) / 2), Real.arccos_pos.2 ht2,
    Real.arccos_lt_pi.2 ht1, ?_⟩
  have hsin : 0 < Real.sin (Real.arccos (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) / 2)) :=
    Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.2 ht2) (Real.arccos_lt_pi.2 ht1)
  refine sl_exists_conj_of_trace_eq
    (A := slRot (Real.arccos (Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) / 2))) (B := A) ?_
    ⟨1, 0, ?_⟩ hq
  · simp only [slRot, Matrix.trace_fin_two_of]
    rw [Real.cos_arccos ht1.le ht2.le]
    ring
  · simpa [slQuad, slRot] using hsin

/-- **The elliptic normal form in `SL(2,ℝ)`**: `A ~ rot(α)`, `0 < |α| < π`. -/
theorem sl_exists_conj_slRot {A : SL(2, ℝ)}
    (h : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 < 4) :
    ∃ α : ℝ, 0 < |α| ∧ |α| < π ∧ ∃ P : SL(2, ℝ), A = P * slRot α * P⁻¹ := by
  have hcen : A ∉ Subgroup.center SL(2, ℝ) := fun hc => by
    have := trace_sq_eq_four_of_mem_center hc
    linarith
  obtain ⟨x, y, hxy⟩ := exists_slQuad_ne_zero hcen
  rcases lt_or_gt_of_ne hxy with hneg | hpos
  · obtain ⟨α, h0, hπ, P, hP⟩ := sl_exists_conj_slRot_of_pos (A := A⁻¹) (by rwa [sl_trace_inv])
      ⟨x, y, by rw [slQuad_inv]; linarith⟩
    refine ⟨-α, by rwa [abs_neg, abs_of_pos h0], by rwa [abs_neg, abs_of_pos h0], P, ?_⟩
    rw [← slRot_inv, ← inv_inv A, hP]
    group
  · obtain ⟨α, h0, hπ, P, hP⟩ := sl_exists_conj_slRot_of_pos h ⟨x, y, hpos⟩
    exact ⟨α, by rwa [abs_of_pos h0], by rwa [abs_of_pos h0], P, hP⟩

namespace PSL2

theorem isElliptic_slRot {α : ℝ} (h0 : 0 < α) (hπ : α < π) : IsElliptic (pslMk (slRot α)) := by
  show trSq (pslMk (slRot α)) < 4
  rw [trSq_mk]
  simp only [slRot, Matrix.trace_fin_two_of]
  have hs := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  nlinarith [Real.sin_sq_add_cos_sq α]

/-- **The elliptic normal form in `PSL(2,ℝ)`** (l.742): `g ~ rot(α)`, `0 < α < π`. -/
theorem IsElliptic.exists_conj_slRot {g : PSL(2, ℝ)} (hg : IsElliptic g) :
    ∃ α : ℝ, 0 < α ∧ α < π ∧ ∃ c : PSL(2, ℝ), g = c * pslMk (slRot α) * c⁻¹ := by
  obtain ⟨A, rfl⟩ := pslMk_surjective g
  have htr : Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 < 4 := hg
  have hcen : A ∉ Subgroup.center SL(2, ℝ) := fun hc => by
    have := trace_sq_eq_four_of_mem_center hc
    linarith
  obtain ⟨x, y, hxy⟩ := exists_slQuad_ne_zero hcen
  rcases lt_or_gt_of_ne hxy with hneg | hpos
  · obtain ⟨α, h0, hπ, P, hP⟩ := sl_exists_conj_slRot_of_pos (A := -A)
      (by rw [sl_trace_neg, neg_sq]; exact htr) ⟨x, y, by rw [slQuad_neg]; linarith⟩
    exact ⟨α, h0, hπ, pslMk P, by rw [← pslMk_neg A, hP, pslMk_conj]⟩
  · obtain ⟨α, h0, hπ, P, hP⟩ := sl_exists_conj_slRot_of_pos htr ⟨x, y, hpos⟩
    exact ⟨α, h0, hπ, pslMk P, by rw [hP, pslMk_conj]⟩

end PSL2

namespace GTilde

theorem delta_zpow_eq_rot (n : ℤ) : delta ^ n = rot (2 * π * n) := by
  refine ext' fun x => ?_
  rw [delta_zpow_apply, rot_apply, mul_div_cancel_left₀ _ (by positivity : (2 * π : ℝ) ≠ 0)]

/-- An element of `G̃` over a conjugate of `rot(α)` is the rotation lift of its real angle. -/
theorem isRotLift_of_toPSL_conj {f : GTilde} {c : PSL(2, ℝ)} {α : ℝ}
    (h : toPSL f = c * pslMk (slRot α) * c⁻¹) : IsRotLift (angle f) f := by
  have h' : toPSL f = c * toPSL (rot (2 * α)) * c⁻¹ := by
    rw [toPSL_rot, show 2 * α / 2 = α by ring, h]
  obtain ⟨κ, n, -, hn⟩ := exists_delta_zpow_of_toPSL_conj h'
  have hc : delta ^ n * κ = κ * delta ^ n :=
    (Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ delta_mem_center n) κ).symm
  have hf : f = κ * rot (2 * π * n + 2 * α) * κ⁻¹ := by
    rw [hn, rot_add, ← delta_zpow_eq_rot]
    calc delta ^ n * (κ * rot (2 * α) * κ⁻¹) = (delta ^ n * κ) * rot (2 * α) * κ⁻¹ := by group
      _ = (κ * delta ^ n) * rot (2 * α) * κ⁻¹ := by rw [hc]
      _ = κ * (delta ^ n * rot (2 * α)) * κ⁻¹ := by group
  have hr : IsRotLift (2 * π * n + 2 * α) f := ⟨κ, hf⟩
  rw [hr.angle_eq]
  exact hr

/-- **An elliptic or central element of `G̃` is the rotation lift of its real angle**:
`f = h R̃(angle f) h⁻¹`. -/
theorem isRotLift_angle {f : GTilde} (he : IsElliptic f ∨ toPSL f = 1) :
    IsRotLift (angle f) f := by
  rcases he with he | he
  · obtain ⟨α, -, -, c, hc⟩ := PSL2.IsElliptic.exists_conj_slRot he
    exact isRotLift_of_toPSL_conj hc
  · refine isRotLift_of_toPSL_conj (c := 1) (α := 0) ?_
    rw [he, slRot_zero]
    simp [pslMk]

/-- **Two elliptic or central elements of `G̃` with the same real angle are conjugate in `G̃`**
(l.742–744). -/
theorem exists_conj_of_angle_eq {f f' : GTilde} (he : IsElliptic f ∨ toPSL f = 1)
    (he' : IsElliptic f' ∨ toPSL f' = 1) (hθ : angle f = angle f') :
    ∃ h : GTilde, f' = h * f * h⁻¹ := by
  obtain ⟨h₁, e₁⟩ := isRotLift_angle he
  obtain ⟨h₂, e₂⟩ := isRotLift_angle he'
  rw [← hθ] at e₂
  generalize angle f = θ at e₁ e₂
  subst e₁ e₂
  exact ⟨h₂ * h₁⁻¹, by group⟩

/-- **The real angle parametrises the elliptic and central conjugacy classes of `G̃`**. -/
theorem isConj_iff_angle_eq {f f' : GTilde} (he : IsElliptic f ∨ toPSL f = 1)
    (he' : IsElliptic f' ∨ toPSL f' = 1) :
    (∃ h : GTilde, f' = h * f * h⁻¹) ↔ angle f = angle f' := by
  refine ⟨fun ⟨h, e⟩ => ?_, exists_conj_of_angle_eq he he'⟩
  rw [e, angle_conj]

end GTilde

namespace PSL2

/-- **The rotation angle `α ∈ (0, π)` parametrises the elliptic classes of `PSL(2,ℝ)`.** -/
theorem slRot_conj_iff {α β : ℝ} (hα : 0 < α) (hα' : α < π) (hβ : 0 < β) (hβ' : β < π) :
    (∃ c : PSL(2, ℝ), pslMk (slRot β) = c * pslMk (slRot α) * c⁻¹) ↔ α = β := by
  refine ⟨fun ⟨c, hc⟩ => ?_, fun h => ⟨1, by subst h; group⟩⟩
  have h' : GTilde.toPSL (GTilde.rot (2 * β)) =
      c * GTilde.toPSL (GTilde.rot (2 * α)) * c⁻¹ := by
    rw [GTilde.toPSL_rot, GTilde.toPSL_rot, show 2 * β / 2 = β by ring,
      show 2 * α / 2 = α by ring, hc]
  obtain ⟨κ, n, -, hn⟩ := GTilde.exists_delta_zpow_of_toPSL_conj h'
  have ha := congrArg GTilde.angle hn
  rw [GTilde.angle_delta_zpow_mul, GTilde.angle_conj, GTilde.angle_rot, GTilde.angle_rot] at ha
  have h3 : (n : ℝ) < 1 := by
    by_contra hh
    push Not at hh
    nlinarith [Real.pi_pos]
  have h4 : -1 < (n : ℝ) := by
    by_contra hh
    push Not at hh
    nlinarith [Real.pi_pos]
  have hn0 : n = 0 := by
    have : n < 1 := by exact_mod_cast h3
    have : -1 < n := by exact_mod_cast h4
    omega
  rw [hn0, Int.cast_zero, mul_zero, zero_add] at ha
  linarith

end PSL2

end GX
