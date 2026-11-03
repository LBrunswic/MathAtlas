import Causal.Flat.Isometries
import Mathlib.Topology.Sequences

/-!
# `Causal.Flat.GromovBase` — the hyperboloid model of `ℍᵈ`, seen from `o = timeUnit d`

Shared vocabulary of the proof of Barbot's Prop 9.1 external `BenoistNoLox` by Gromov's
classification (DEC-111), in the hyperboloid model `ℍᵈ = {v future timelike, minkQ v = -1}` with
`SO₀(1, d) = lorentz d` acting linearly. **No ledger label is certified here**: the module is
infrastructure for `Flat/GromovProof`, which discharges the external of `bprop:sanloxo`
(`GHFspace.tex:2573`).

Proposition 9.1:

> If $\Gamma$ does not contain loxodromic elements, it is elementary; i.e., up to finite index,
> its linear part is either contained in $SO(n-1)$ (up to conjugacy), or its linear part
> stabilizes an isotropic vector. (l.2575–2577)

Nothing below needs a hyperbolic distance: the cosine of the displacement of the base point
`o = (1, 0)` is the time component `orbitCosh A = (A o).1 = −⟨A o | o⟩ = cosh d(o, A o)`, and the
visual compactification of `ℍᵈ` seen from `o` is the **slice** `{x | x.1 = 1, ‖x.2‖ ≤ 1}`, a closed
ball, whose boundary sphere is the Penrose sphere of future null directions.

* `orbitCosh A` (`= (A o).1`), `toSlice x = x.1⁻¹ • x`, `orbitPt A = toSlice (A o)` (Gromov's
  `A o` seen from `o`; `orbitPt A⁻¹` is the "repelling" twin), `slice d`.
* `one_le_orbitCosh`, `orbitCosh_inv` (`cosh d(o, A⁻¹o) = cosh d(o, A o)`),
  `norm_orbitPt_snd_sq` (`‖(orbitPt A).2‖² = 1 − (orbitCosh A)⁻²`, so `orbitPt A ∈ slice d`),
  `isCompact_slice`, `orbitCosh_mul`, `orbitPt_mul` (exact composition formulas),
  `fst_apply_eq` (`(A v).1 = orbitCosh A · (−⟨orbitPt A⁻¹ | v⟩)`).
* **The rank-one estimate** `rankOne_fst`, `rankOne_norm`: for every `v`,
  `A v − (A v).1 • orbitPt A` has time component `0` and spatial norm `≤ ‖v.2‖` — so
  `A v = (A v).1 • orbitPt A + O(‖v‖)` uniformly in `A`, the linear form of Gromov's statement
  that a far-moving isometry collapses `ℍᵈ` towards one point at infinity.

## Hypothesis checklist

| paper hypothesis | here |
|---|---|
| `Γ ≤ SO₀(1, n−1)` | ✓ carried: every statement is about `A : lorentz d` |

## SCOPE (disclosed)

* Infrastructure only; nothing of the paper is certified here.
* The base point is `timeUnit d`; nothing depends on that choice.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`. Barbot campaign,
DEC-111 (Gromov route). Line numbers are those of `papers/barbot/legacy/labeled/GHFspace.tex`.
-/

namespace Causal.Flat

open Filter Topology

variable {d : ℕ}

/-- `cosh d(o, A o)`, read in the hyperboloid model: the time component of `A o`. -/
noncomputable def orbitCosh (A : lorentz d) : ℝ :=
  ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d)).1

/-- Radial projection to the affine slice `{x.1 = 1}` (meaningful when `x.1 ≠ 0`). -/
noncomputable def toSlice (x : Minkowski d) : Minkowski d := (x.1)⁻¹ • x

/-- `A o` seen from `o`: the point of the slice on the ray through `A o`. -/
noncomputable def orbitPt (A : lorentz d) : Minkowski d :=
  toSlice ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d))

variable (d) in
/-- The slice of the closed future cone: the closed ball `{x.1 = 1, ‖x.2‖ ≤ 1}`. Its interior
points are the rays of `ℍᵈ`, its boundary sphere the future null directions (`∂ℍᵈ`). -/
def slice : Set (Minkowski d) := {x | x.1 = 1 ∧ ‖x.2‖ ≤ 1}

/-- A Lorentz transformation preserves `minkB` (a wrapper of `minkB_map`). -/
theorem minkB_lorentz_apply (A : lorentz d) (v w : Minkowski d) :
    minkB ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) v) ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) w) =
      minkB v w :=
  minkB_map (A := (A : Minkowski d ≃ₗ[ℝ] Minkowski d)) A.2.1 v w

theorem lorentz_apply_inv_apply (A : lorentz d) (x : Minkowski d) :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) x) =
      x := by
  rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one]; rfl

theorem lorentz_inv_apply_apply (A : lorentz d) (x : Minkowski d) :
    ((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) x) =
      x := by
  rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]; rfl

/-- `x.1 = −⟨x | o⟩`. -/
theorem fst_eq_neg_minkB_timeUnit (x : Minkowski d) : x.1 = -minkB x (timeUnit d) := by
  simp [minkB, timeUnit]

theorem isFutureTimelike_timeUnit : IsFutureTimelike (timeUnit d) :=
  ⟨by simp [timeUnit], by simp⟩

theorem minkQ_apply_timeUnit (A : lorentz d) :
    minkQ ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d)) = -1 := by
  rw [lorentz.minkQ_apply A.2, minkQ_timeUnit]

/-- `cosh d(o, A o) ≥ 1`: `A o` is future timelike with `minkQ = −1`. -/
theorem one_le_orbitCosh (A : lorentz d) : 1 ≤ orbitCosh A := by
  have hq := minkQ_apply_timeUnit A
  have hpos := (lorentz.isFutureTimelike_apply A.2 (isFutureTimelike_timeUnit (d := d))).1
  unfold orbitCosh
  unfold minkQ at hq
  nlinarith [sq_nonneg ‖((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d)).2‖]

theorem orbitCosh_pos (A : lorentz d) : 0 < orbitCosh A :=
  lt_of_lt_of_le one_pos (one_le_orbitCosh A)

/-- `cosh d(o, A⁻¹ o) = cosh d(o, A o)`: `−⟨A⁻¹o | o⟩ = −⟨o | A o⟩`. -/
theorem orbitCosh_inv (A : lorentz d) : orbitCosh A⁻¹ = orbitCosh A := by
  unfold orbitCosh
  rw [fst_eq_neg_minkB_timeUnit, fst_eq_neg_minkB_timeUnit, ← minkB_lorentz_apply A,
    lorentz_apply_inv_apply, minkB_comm]

theorem toSlice_fst {x : Minkowski d} (hx : x.1 ≠ 0) : (toSlice x).1 = 1 := by
  simp [toSlice, inv_mul_cancel₀ hx]

theorem toSlice_smul {c : ℝ} (hc : c ≠ 0) (x : Minkowski d) : toSlice (c • x) = toSlice x := by
  unfold toSlice
  rw [Prod.smul_fst, smul_eq_mul, smul_smul]
  congr 1
  field_simp

theorem continuousAt_toSlice {x : Minkowski d} (hx : x.1 ≠ 0) : ContinuousAt toSlice x :=
  (continuous_fst.continuousAt.inv₀ hx).smul continuousAt_id

/-- `A o = orbitCosh A • orbitPt A`. -/
theorem apply_timeUnit_eq (A : lorentz d) :
    (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d) = orbitCosh A • orbitPt A := by
  exact (smul_inv_smul₀ (orbitCosh_pos A).ne' _).symm

theorem orbitPt_fst (A : lorentz d) : (orbitPt A).1 = 1 :=
  toSlice_fst (orbitCosh_pos A).ne'

/-- `‖(orbitPt A).2‖² = 1 − (orbitCosh A)⁻²`: from `minkQ (A o) = −1`. -/
theorem norm_orbitPt_snd_sq (A : lorentz d) :
    ‖(orbitPt A).2‖ ^ 2 = 1 - (orbitCosh A)⁻¹ ^ 2 := by
  have hq := minkQ_apply_timeUnit A
  have hc := (orbitCosh_pos A).ne'
  unfold minkQ at hq
  have h2 : ‖((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d)).2‖ ^ 2 = orbitCosh A ^ 2 - 1 := by
    unfold orbitCosh; linarith
  show ‖((orbitCosh A)⁻¹ • (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d)).2‖ ^ 2 = _
  rw [Prod.smul_snd, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, h2]
  field_simp

theorem orbitPt_mem_slice (A : lorentz d) : orbitPt A ∈ slice d := by
  refine ⟨orbitPt_fst A, ?_⟩
  have h := norm_orbitPt_snd_sq A
  have h1 : ‖(orbitPt A).2‖ ^ 2 ≤ 1 := by rw [h]; nlinarith [sq_nonneg (orbitCosh A)⁻¹]
  nlinarith [norm_nonneg (orbitPt A).2]

theorem isCompact_slice : IsCompact (slice d) := by
  have : slice d = ({1} : Set ℝ) ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 := by
    ext x; simp [slice, Set.mem_prod]
  rw [this]
  exact isCompact_singleton.prod (isCompact_closedBall _ _)

/-- `(A v).1 = orbitCosh A · (−⟨orbitPt A⁻¹ | v⟩)`: the time component of `A v` is read off the
repelling point. -/
theorem fst_apply_eq (A : lorentz d) (v : Minkowski d) :
    ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) v).1 = orbitCosh A * -minkB (orbitPt A⁻¹) v := by
  have h := minkB_lorentz_apply A v (((A⁻¹ : lorentz d) : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d))
  rw [lorentz_apply_inv_apply, apply_timeUnit_eq, orbitCosh_inv, minkB_smul_right] at h
  rw [fst_eq_neg_minkB_timeUnit, h, minkB_comm]; ring

/-- Composition, exactly: `cosh d(o, A B o) = cosh d(o, B o) · (A (orbitPt B)).1`. -/
theorem orbitCosh_mul (A B : lorentz d) :
    orbitCosh (A * B) =
      orbitCosh B * ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (orbitPt B)).1 := by
  show ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) ((B : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d))).1 = _
  rw [apply_timeUnit_eq B, map_smul, Prod.smul_fst, smul_eq_mul]

theorem orbitPt_mul (A B : lorentz d) :
    orbitPt (A * B) = toSlice ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) (orbitPt B)) := by
  show toSlice ((A : Minkowski d ≃ₗ[ℝ] Minkowski d)
    ((B : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d))) = _
  rw [apply_timeUnit_eq B, map_smul, toSlice_smul (orbitCosh_pos B).ne']

/-- **The rank-one estimate, time part**: `A v − (A v).1 • orbitPt A` is spatial. -/
theorem rankOne_fst (A : lorentz d) (v : Minkowski d) :
    ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) v -
        ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) v).1 • orbitPt A).1 = 0 := by
  simp [orbitPt_fst]

/-- **The rank-one estimate, spatial part**: `‖(A v − (A v).1 • orbitPt A).2‖ ≤ ‖v.2‖`.
Proof (`w = A o`, `c = w.1`): `z = A v − v.1 • w` is `minkB`-orthogonal to `w` with
`minkQ z = ‖v.2‖²`; `A v − (A v).1 • orbitPt A = z − (z.1 / c) • w`, and orthogonality
`z.1 · c = ⟪z.2, w.2⟫` gives `‖(z − (z.1/c) • w).2‖² = minkQ z − z.1² / c² ≤ ‖v.2‖²`. -/
theorem rankOne_norm (A : lorentz d) (v : Minkowski d) :
    ‖((A : Minkowski d ≃ₗ[ℝ] Minkowski d) v -
        ((A : Minkowski d ≃ₗ[ℝ] Minkowski d) v).1 • orbitPt A).2‖ ≤ ‖v.2‖ := by
  set w := (A : Minkowski d ≃ₗ[ℝ] Minkowski d) (timeUnit d) with hw
  set y := (A : Minkowski d ≃ₗ[ℝ] Minkowski d) v with hy
  have hc : 0 < w.1 := orbitCosh_pos A
  have hQw : -w.1 ^ 2 + ‖w.2‖ ^ 2 = -1 := minkQ_apply_timeUnit A
  have hQy : -y.1 ^ 2 + ‖y.2‖ ^ 2 = -v.1 ^ 2 + ‖v.2‖ ^ 2 := lorentz.minkQ_apply A.2 v
  have hB : -(y.1 * w.1) + inner ℝ y.2 w.2 = -v.1 := by
    have h := minkB_lorentz_apply A v (timeUnit d)
    have h' := fst_eq_neg_minkB_timeUnit v
    simp only [minkB] at h h' ⊢
    linarith
  have he : (y - y.1 • orbitPt A).2 = y.2 - (y.1 / w.1) • w.2 := by
    simp only [orbitPt, toSlice, Prod.snd_sub, Prod.smul_snd, smul_smul, div_eq_mul_inv, ← hw]
  rw [he]
  have hw2 : ‖w.2‖ ^ 2 = w.1 ^ 2 - 1 := by linarith
  have hyw : inner ℝ y.2 w.2 = y.1 * w.1 - v.1 := by linarith
  have key : ‖y.2 - (y.1 / w.1) • w.2‖ ^ 2 = ‖v.2‖ ^ 2 - (v.1 - y.1 / w.1) ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hw2,
      hyw]
    field_simp
    nlinarith [hQy]
  have h2 : ‖y.2 - (y.1 / w.1) • w.2‖ ^ 2 ≤ ‖v.2‖ ^ 2 := by
    rw [key]; nlinarith [sq_nonneg (v.1 - y.1 / w.1)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

end Causal.Flat
