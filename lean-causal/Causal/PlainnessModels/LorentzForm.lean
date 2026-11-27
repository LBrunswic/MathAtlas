import Causal.Flat.Form

/-!
# Lorentzian forms on `ℝ^{1+n}`, pointwise: the cones of a time-oriented Lorentzian form

Target `T-ett-plainness-models` (DEC-168), the linear algebra under
`Causal.PlainnessModels.LipschitzModel`. No label is marked: this is the pointwise
vocabulary of « a field $g$ of non-degenerate symmetric $2$-tensors of signature $(1,n-1)$ »
(`ETT.tex:166–167`).

> A Lorentzian manifold $M$ is an orientable differential manifold of dimension $n\in \N^*$ endowed
> with a metric, i.e. with a field $g$ of non-degenerate symmetric $2$-tensors of signature
> $(1,n-1)$. (`ETT.tex:166–167`)

## What is here (no `sorry`)

* `Lorentz.IsLorentzian b`: the continuous bilinear form `b` on `Minkowski n = ℝ × ℝⁿ` is congruent
  to the Minkowski form `minkB` (Sylvester: signature `(1, n)`, i.e. `(1, N−1)` in dimension
  `N = n + 1`).
* `Lorentz.FC b T v`, `Lorentz.FT b T v`: `v` future causal (`b v v ≤ 0`, `b v T ≤ 0`, `0`
  included), future timelike (`b v v < 0`, `b v T < 0`), the time orientation given by a vector
  `T` with `b T T < 0`.
* A future frame (`exists_futureFrame`), and through it: the pairing of two future causal vectors
  is `≤ 0` (`FC.pairing_nonpos`), `< 0` against a future timelike one when `v ≠ 0`
  (`FC.pairing_neg`), the future causal cone is self-dual (`fc_of_forall_pairing_nonpos`),
  causal plus timelike is timelike (`FC.add_ft`), a timelike vector pairing negatively with a future
  timelike one is future (`ft_of_pairing_neg`), scalings.

## SCOPE (disclosed)

* Signature is read as congruence to `minkB` (a linear change of coordinates), which is
  Sylvester's law of inertia for a non-degenerate form of index one; nothing else is used.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.
-/

namespace Causal

open Flat

namespace Lorentz

variable {n : ℕ}

/-! ### Minkowski space: the cones of `minkB` -/

section Mink

theorem fst_pos_of_isFutureCausal {v : Minkowski n} (hv : IsFutureCausal v) (h0 : v ≠ 0) :
    0 < v.1 := by
  rcases hv.1.lt_or_eq with h | h
  · exact h
  · exact absurd (eq_zero_of_fst_eq_zero h.symm hv.2) h0

theorem norm_snd_le_of_isFutureCausal {v : Minkowski n} (hv : IsFutureCausal v) : ‖v.2‖ ≤ v.1 := by
  have h := minkQ_le_zero_iff.1 hv.2
  nlinarith [norm_nonneg v.2, hv.1]

theorem norm_snd_lt_of_isFutureTimelike {v : Minkowski n} (hv : IsFutureTimelike v) :
    ‖v.2‖ < v.1 := by
  have h := minkQ_lt_zero_iff.1 hv.2
  nlinarith [norm_nonneg v.2, hv.1]

theorem isFutureCausal_of_ft {v : Minkowski n} (hv : IsFutureTimelike v) :
    IsFutureCausal v := ⟨hv.1.le, hv.2.le⟩

/-- Two future causal vectors pair non-positively. -/
theorem minkB_nonpos {v w : Minkowski n} (hv : IsFutureCausal v) (hw : IsFutureCausal w) :
    minkB v w ≤ 0 := by
  unfold minkB
  have h1 := real_inner_le_norm v.2 w.2
  have h2 := norm_snd_le_of_isFutureCausal hv
  have h3 := norm_snd_le_of_isFutureCausal hw
  nlinarith [norm_nonneg v.2, norm_nonneg w.2]

/-- A non-zero future causal vector pairs negatively with a future timelike one. -/
theorem minkB_neg {v e : Minkowski n} (hv : IsFutureCausal v) (h0 : v ≠ 0)
    (he : IsFutureTimelike e) : minkB v e < 0 := by
  unfold minkB
  have h1 := real_inner_le_norm v.2 e.2
  have h2 := norm_snd_le_of_isFutureCausal hv
  have h3 := norm_snd_lt_of_isFutureTimelike he
  have h4 := fst_pos_of_isFutureCausal hv h0
  nlinarith [norm_nonneg v.2, norm_nonneg e.2]

/-- The future causal cone is self-dual. -/
theorem isFutureCausal_of_forall {v : Minkowski n}
    (h : ∀ w : Minkowski n, IsFutureCausal w → minkB v w ≤ 0) : IsFutureCausal v := by
  have h1 : 0 ≤ v.1 := by
    have := h (1, 0) ⟨zero_le_one, by simp [minkQ]⟩
    simpa [minkB] using this
  refine ⟨h1, ?_⟩
  have hw : IsFutureCausal ((‖v.2‖, v.2) : Minkowski n) := ⟨norm_nonneg _, by simp [minkQ]⟩
  have h2 := h _ hw
  simp only [minkB, real_inner_self_eq_norm_sq] at h2
  rw [minkQ_le_zero_iff]
  rcases (norm_nonneg v.2).lt_or_eq with hpos | hz
  · have : ‖v.2‖ ≤ v.1 := by nlinarith
    nlinarith [norm_nonneg v.2]
  · rw [← hz]; nlinarith

/-- Future causal plus future timelike is future timelike. -/
theorem add_isFutureTimelike {v w : Minkowski n} (hv : IsFutureCausal v)
    (hw : IsFutureTimelike w) : IsFutureTimelike (v + w) := by
  have h2 := norm_snd_le_of_isFutureCausal hv
  have h3 := norm_snd_lt_of_isFutureTimelike hw
  have h4 := norm_add_le v.2 w.2
  refine ⟨by simp only [Prod.fst_add]; linarith [hv.1, hw.1], ?_⟩
  rw [minkQ_lt_zero_iff]
  simp only [Prod.fst_add, Prod.snd_add]
  nlinarith [norm_nonneg (v.2 + w.2)]

/-- A timelike vector pairing negatively with a future timelike vector is future timelike. -/
theorem isFutureTimelike_of_minkB_neg {w e : Minkowski n} (hw : minkQ w < 0)
    (he : IsFutureTimelike e) (h : minkB w e < 0) : IsFutureTimelike w := by
  rcases isFutureTimelike_or_neg hw with h' | h'
  · exact h'
  · have h0 : -w ≠ 0 := by
      intro h0
      rw [neg_eq_zero] at h0
      subst h0
      simp at hw
    have := minkB_neg (isFutureCausal_of_ft h') h0 he
    have hneg : minkB (-w) e = -minkB w e := by simp [minkB]; ring
    linarith

/-- The time reflection `(t, x) ↦ (−t, x)`. -/
noncomputable def timeReflection : Minkowski n ≃ₗ[ℝ] Minkowski n where
  toFun v := (-v.1, v.2)
  invFun v := (-v.1, v.2)
  map_add' u v := by ext <;> simp; ring
  map_smul' c v := by ext <;> simp
  left_inv v := by simp
  right_inv v := by simp

@[simp] theorem timeReflection_apply (v : Minkowski n) : timeReflection v = (-v.1, v.2) := rfl

theorem minkB_timeReflection (u v : Minkowski n) :
    minkB (timeReflection u) (timeReflection v) = minkB u v := by
  simp [minkB]

end Mink

/-! ### Lorentzian forms -/

/-- **A Lorentzian form** on `Minkowski n`: congruent to `minkB`, signature `(1, n)`. -/
def IsLorentzian (b : Minkowski n →L[ℝ] Minkowski n →L[ℝ] ℝ) : Prop :=
  ∃ A : Minkowski n ≃ₗ[ℝ] Minkowski n, ∀ u v, b (A u) (A v) = minkB u v

/-- `v` is **future causal** for `b`, the time orientation given by `T` (`0` included). -/
def FC (b : Minkowski n →L[ℝ] Minkowski n →L[ℝ] ℝ) (T v : Minkowski n) : Prop :=
  b v v ≤ 0 ∧ b v T ≤ 0

/-- `v` is **future timelike** for `b`, the time orientation given by `T`. -/
def FT (b : Minkowski n →L[ℝ] Minkowski n →L[ℝ] ℝ) (T v : Minkowski n) : Prop :=
  b v v < 0 ∧ b v T < 0

variable {b : Minkowski n →L[ℝ] Minkowski n →L[ℝ] ℝ} {T u v w e : Minkowski n}

theorem IsLorentzian.symm (hb : IsLorentzian b) (u v : Minkowski n) : b u v = b v u := by
  obtain ⟨A, hA⟩ := hb
  have h1 := hA (A.symm u) (A.symm v)
  have h2 := hA (A.symm v) (A.symm u)
  simp only [LinearEquiv.apply_symm_apply] at h1 h2
  rw [h1, h2, minkB_comm]

/-- **A future frame**: a congruence to `minkB` sending the future of `T` to the future cone. -/
theorem exists_futureFrame (hb : IsLorentzian b) (hT : b T T < 0) :
    ∃ A : Minkowski n ≃ₗ[ℝ] Minkowski n, (∀ u v, b (A u) (A v) = minkB u v) ∧
      IsFutureTimelike (A.symm T) := by
  obtain ⟨A, hA⟩ := hb
  have hq : minkQ (A.symm T) < 0 := by
    rw [minkQ_eq_minkB, ← hA]; simpa using hT
  rcases isFutureTimelike_or_neg hq with h | h
  · exact ⟨A, hA, h⟩
  · refine ⟨timeReflection.trans A, fun u v => ?_, ?_⟩
    · simp only [LinearEquiv.trans_apply]
      rw [hA, minkB_timeReflection]
    · have : (timeReflection.trans A).symm T = timeReflection (A.symm T) := by
        rw [LinearEquiv.symm_trans_apply]
        rfl
      rw [this]
      refine ⟨by simpa using h.1, ?_⟩
      have := h.2
      simpa [minkQ] using this

section Frame

variable {A : Minkowski n ≃ₗ[ℝ] Minkowski n}

theorem frame_apply (hA : ∀ u v, b (A u) (A v) = minkB u v) (u v : Minkowski n) :
    b u v = minkB (A.symm u) (A.symm v) := by
  rw [← hA]; simp

theorem fc_iff_frame (hA : ∀ u v, b (A u) (A v) = minkB u v) (hT : IsFutureTimelike (A.symm T)) :
    FC b T v ↔ IsFutureCausal (A.symm v) := by
  rw [FC, frame_apply hA, frame_apply hA, ← minkQ_eq_minkB]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    by_contra hneg
    rw [not_le] at hneg
    have hc : IsFutureCausal (-(A.symm v)) := ⟨by simp; linarith, by simpa using h1⟩
    have h0 : -(A.symm v) ≠ 0 := by
      intro h0; rw [neg_eq_zero] at h0; rw [h0] at hneg; simp at hneg
    have := minkB_neg hc h0 hT
    have hneg' : minkB (-(A.symm v)) (A.symm T) = -minkB (A.symm v) (A.symm T) := by
      simp [minkB]; ring
    linarith
  · intro h
    exact ⟨h.2, minkB_nonpos h (isFutureCausal_of_ft hT)⟩

theorem ft_iff_frame (hA : ∀ u v, b (A u) (A v) = minkB u v) (hT : IsFutureTimelike (A.symm T)) :
    FT b T v ↔ IsFutureTimelike (A.symm v) := by
  rw [FT, frame_apply hA, frame_apply hA, ← minkQ_eq_minkB]
  constructor
  · rintro ⟨h1, h2⟩
    exact isFutureTimelike_of_minkB_neg h1 hT h2
  · intro h
    have h0 : A.symm v ≠ 0 := by
      intro h0; have := h.2; rw [h0] at this; simp at this
    exact ⟨h.2, minkB_neg (isFutureCausal_of_ft h) h0 hT⟩

end Frame

theorem FT.fc (h : FT b T v) : FC b T v := ⟨h.1.le, h.2.le⟩

theorem fc_zero : FC b T 0 := by simp [FC]

theorem FC.smul (h : FC b T v) {c : ℝ} (hc : 0 ≤ c) : FC b T (c • v) := by
  refine ⟨?_, ?_⟩
  · simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    nlinarith [h.1, mul_nonneg hc hc]
  · simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    nlinarith [h.2]

theorem FT.smul (h : FT b T v) {c : ℝ} (hc : 0 < c) : FT b T (c • v) := by
  refine ⟨?_, ?_⟩
  · simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    have := mul_pos hc hc
    nlinarith [h.1]
  · simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    nlinarith [h.2]

section Lorentzian

variable (hb : IsLorentzian b) (hT : b T T < 0)
include hb hT

/-- Two future causal vectors pair non-positively. -/
theorem FC.pairing_nonpos (hv : FC b T v) (hw : FC b T w) : b v w ≤ 0 := by
  obtain ⟨A, hA, hTA⟩ := exists_futureFrame hb hT
  rw [frame_apply hA]
  exact minkB_nonpos ((fc_iff_frame hA hTA).1 hv) ((fc_iff_frame hA hTA).1 hw)

/-- A non-zero future causal vector pairs negatively with a future timelike vector. -/
theorem FC.pairing_neg (hv : FC b T v) (h0 : v ≠ 0) (he : FT b T e) : b v e < 0 := by
  obtain ⟨A, hA, hTA⟩ := exists_futureFrame hb hT
  rw [frame_apply hA]
  refine minkB_neg ((fc_iff_frame hA hTA).1 hv) ?_ ((ft_iff_frame hA hTA).1 he)
  simpa using h0

/-- **Self-duality** of the future causal cone. -/
theorem fc_of_forall_pairing_nonpos (h : ∀ w, FC b T w → b v w ≤ 0) : FC b T v := by
  obtain ⟨A, hA, hTA⟩ := exists_futureFrame hb hT
  rw [fc_iff_frame hA hTA]
  refine isFutureCausal_of_forall fun w hw => ?_
  have := h (A w) ((fc_iff_frame hA hTA).2 (by simpa using hw))
  rw [frame_apply hA] at this
  simpa using this

/-- Future causal plus future timelike is future timelike. -/
theorem FC.add_ft (hv : FC b T v) (hw : FT b T w) : FT b T (v + w) := by
  obtain ⟨A, hA, hTA⟩ := exists_futureFrame hb hT
  rw [ft_iff_frame hA hTA, map_add]
  exact add_isFutureTimelike ((fc_iff_frame hA hTA).1 hv) ((ft_iff_frame hA hTA).1 hw)

/-- A timelike vector pairing negatively with a future timelike one is future timelike. -/
theorem ft_of_pairing_neg (hw : b w w < 0) (he : FT b T e) (h : b w e < 0) : FT b T w := by
  obtain ⟨A, hA, hTA⟩ := exists_futureFrame hb hT
  rw [ft_iff_frame hA hTA]
  rw [frame_apply hA, ← minkQ_eq_minkB] at hw
  rw [frame_apply hA] at h
  exact isFutureTimelike_of_minkB_neg hw ((ft_iff_frame hA hTA).1 he) h

end Lorentzian

end Lorentz

end Causal
