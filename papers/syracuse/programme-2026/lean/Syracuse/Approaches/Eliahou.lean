import Syracuse.Approaches.CycleLength

/-!
# Eliahou's theorem (1993), proved; and its form at Barina's `2^71`

**Eliahou 1993** (S. Eliahou, "The 3x+1 problem: new lower bounds on nontrivial cycle lengths",
Discrete Math. 118 (1993) 45–56) was stated as `CycleLiterature.Eliahou1993`: if every point of a
cycle exceeds `2^40`, its `T`-length is `E = 301994 a + 17087915 b + 85137581 c` with `a, b, c ≥ 0`,
`b ≥ 1`, `ac = 0`. It is now a theorem (`eliahou1993`), with no literature input at all.

**Proof.** On such a cycle `0 < E log 2 − o log 3 < o/(3·2^40)` (`CycleLiterature.cycle_excess_le`), so
`E/o` lies in `(log₂3, log₂3 + 1/(3·2^40 ln 2))`. The three vectors `v₃ = (85137581, 53715833)`,
`v₂ = (17087915, 10781274)`, `v₁ = (301994, 190537)` satisfy

`85137581/53715833 < log₂3 < 17087915/10781274 < log₂3 + 1/(3·2^40 ln 2) < 301994/190537`

(certified from `CycleLength.log_two_three`), and consecutive ones have determinant `1`. A lattice point
of the cone between two vectors of determinant `1` is a nonnegative integer combination of them
(`cone_decomp`). Split the cone `(v₃, v₁)` at `v₂`: `(E, o) = b v₂ + a v₁` or `b v₂ + c v₃`, and `b ≥ 1`
because `E/o` is strictly inside (`eliahou_40`, which also gives `o`).

**At `2^71`.** The same argument with Barina's bound and the vectors `(103768467013, 65470613321)`
(below `log₂3`), `(114208327604, 72057431991)` (inside) and `(124648188195, 78644250661)` (above the
interval) gives (`eliahou_barina`)

`(E, o) = a (103768467013, 65470613321) + b (114208327604, 72057431991) + c (124648188195, 78644250661)`,
`b ≥ 1`, `ac = 0`,

which contains `CycleLength.cycle_length_ge`.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| a lattice point between two vectors of determinant `1` is a nonnegative combination of them | `cone_decomp` | proved |
| `E` and `o` in Eliahou's form for cycles above `2^40` | `eliahou_40` | proved |
| **Eliahou 1993** (the stated `Prop`) | `eliahou1993` | **proved** (no literature input) |
| Eliahou + Barina without assuming Eliahou | `eliahou_of_barina'` | proved (conditional on Barina) |
| **Eliahou's form at `2^71`** | `eliahou_barina` | proved (conditional on Barina) |
-/

namespace Syracuse.Eliahou

open Syracuse

/-- **Unimodular cones.** If `p'q − pq' = 1`, then `(E, o) = α (p, q) + β (p', q')` with
`α = p'o − Eq'` and `β = Eq − po`. Between the two rays both coefficients are nonnegative. -/
lemma cone_decomp {p q p' q' E o : ℤ} (hdet : p' * q - p * q' = 1) :
    E = (p' * o - E * q') * p + (E * q - p * o) * p' ∧
      o = (p' * o - E * q') * q + (E * q - p * o) * q' :=
  ⟨by linear_combination (-E) * hdet, by linear_combination (-o) * hdet⟩

/-- The cycle sandwich in linear form: `o log 3 < E log 2 < o log 3 + o/(3m)`. -/
lemma sandwich {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {m : ℝ} (hm : 0 < m)
    (hmin : ∀ k < o, m ≤ syr^[k] a) :
    (o : ℝ) * Real.log 3 < (gapWord a o).sum * Real.log 2 ∧
      ((gapWord a o).sum : ℝ) * Real.log 2 - o * Real.log 3 < o / (3 * m) := by
  obtain ⟨s1, s3⟩ := CycleLiterature.cycle_excess_le h hm hmin
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [← Real.log_div_log] at s1 s3
  have e : (((gapWord a o).sum : ℝ) - o * (Real.log 3 / Real.log 2)) * Real.log 2 =
      (gapWord a o).sum * Real.log 2 - o * Real.log 3 := by field_simp
  have e' : (o : ℝ) / (3 * m * Real.log 2) * Real.log 2 = o / (3 * m) := by field_simp
  have t1 := mul_lt_mul_of_pos_right s1 hl2
  have t2 := mul_lt_mul_of_pos_right s3 hl2
  rw [zero_mul] at t1
  constructor <;> linarith

/-- **Eliahou's decomposition, with both coordinates.** If every point of a cycle exceeds `2^40`,
then `(E, o) = a (301994, 190537) + b (17087915, 10781274) + c (85137581, 53715833)` with `b ≥ 1` and
`ac = 0`. -/
theorem eliahou_40 {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (hmin : ∀ k, (2 : ℤ) ^ 40 < syr^[k] a) :
    ∃ x y z : ℕ, (gapWord a o).sum = 301994 * x + 17087915 * y + 85137581 * z ∧
      o = 190537 * x + 10781274 * y + 53715833 * z ∧ 1 ≤ y ∧ x * z = 0 := by
  obtain ⟨l2a, l2b, l3a, l3b⟩ := CycleLength.log_two_three
  have hm : ∀ k < o, ((2 : ℝ) ^ 40) ≤ syr^[k] a := fun k _ => by
    have h40 := (hmin k).le
    have : (((2 : ℤ) ^ 40 : ℤ) : ℝ) ≤ syr^[k] a := Int.cast_le.2 h40
    rwa [Int.cast_pow, Int.cast_ofNat] at this
  obtain ⟨t1, t2⟩ := sandwich h (by positivity) hm
  set E := (gapWord a o).sum
  have ho : (0 : ℝ) < o := by exact_mod_cast h.1
  have hl2 : (0 : ℝ) < Real.log 2 := by linarith
  -- `v₃` below: `53715833 log 3 > 85137581 log 2`
  have K3 : (0 : ℝ) < 53715833 * Real.log 3 - 85137581 * Real.log 2 := by linarith
  -- `v₁` above the interval: `301994 log 2 − 190537 log 3 > 190537/(3·2^40)`
  have K1 : (190537 : ℝ) / (3 * 2 ^ 40) < 301994 * Real.log 2 - 190537 * Real.log 3 := by
    norm_num; linarith
  have F3 : (0 : ℤ) < (E : ℤ) * 53715833 - 85137581 * (o : ℤ) := by
    have hr : (0 : ℝ) < (((E : ℤ) * 53715833 - 85137581 * (o : ℤ) : ℤ) : ℝ) * Real.log 2 := by
      push_cast
      linarith [mul_pos ho K3]
    exact Int.cast_pos.mp ((pos_iff_pos_of_mul_pos hr).2 hl2)
  have F1 : (0 : ℤ) < 301994 * (o : ℤ) - (E : ℤ) * 190537 := by
    have hr : (0 : ℝ) < ((301994 * (o : ℤ) - (E : ℤ) * 190537 : ℤ) : ℝ) * Real.log 2 := by
      push_cast
      have := mul_lt_mul_of_pos_left K1 ho
      have e : (o : ℝ) * (190537 / (3 * 2 ^ 40)) = 190537 * (o / (3 * 2 ^ 40)) := by ring
      linarith
    exact Int.cast_pos.mp ((pos_iff_pos_of_mul_pos hr).2 hl2)
  rcases le_or_gt 0 ((E : ℤ) * 10781274 - 17087915 * (o : ℤ)) with ht | ht
  · -- cone `(v₂, v₁)`: `(E, o) = y v₂ + x v₁`
    obtain ⟨hE, ho'⟩ := cone_decomp (p := 17087915) (q := 10781274) (p' := 301994) (q' := 190537)
      (E := (E : ℤ)) (o := (o : ℤ)) (by norm_num)
    obtain ⟨y, hy⟩ := Int.eq_ofNat_of_zero_le F1.le
    obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le ht
    refine ⟨x, y, 0, ?_, ?_, ?_, by simp⟩
    · rw [hy, hx] at hE; omega
    · rw [hy, hx] at ho'; omega
    · omega
  · -- cone `(v₃, v₂)`: `(E, o) = z v₃ + y v₂`
    obtain ⟨hE, ho'⟩ := cone_decomp (p := 85137581) (q := 53715833) (p' := 17087915) (q' := 10781274)
      (E := (E : ℤ)) (o := (o : ℤ)) (by norm_num)
    obtain ⟨z, hz⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ 17087915 * (o : ℤ) - (E : ℤ) * 10781274
      by omega)
    obtain ⟨y, hy⟩ := Int.eq_ofNat_of_zero_le F3.le
    refine ⟨0, y, z, ?_, ?_, ?_, by simp⟩
    · rw [hz, hy] at hE; omega
    · rw [hz, hy] at ho'; omega
    · omega

/-- **Eliahou 1993, proved.** -/
theorem eliahou1993 : CycleLiterature.Eliahou1993 := fun a o h hmin => by
  obtain ⟨x, y, z, hE, -, hy, hxz⟩ := eliahou_40 h.1 hmin
  exact ⟨x, y, z, hE, hy, hxz⟩

/-- **Eliahou + Barina**, with Eliahou's theorem now proved. -/
theorem eliahou_of_barina' (hB : CycleLiterature.Barina2025) {a : ℤ} {o : ℕ}
    (h : CycleLiterature.IsPrimSyrCycle a o) (ha : 0 < a) (h1 : a ≠ 1) :
    ∃ x y z : ℕ, (gapWord a o).sum = 301994 * x + 17087915 * y + 85137581 * z ∧ 1 ≤ y ∧ x * z = 0 :=
  CycleLiterature.eliahou_of_barina eliahou1993 hB h ha h1

/-- **Eliahou's form at Barina's `2^71`.** Every nontrivial positive cycle has
`(E, o) = a (103768467013, 65470613321) + b (114208327604, 72057431991) + c (124648188195, 78644250661)`
with `b ≥ 1` and `ac = 0`. -/
theorem eliahou_barina (hB : CycleLiterature.Barina2025) {a : ℤ} {o : ℕ} (h : IsSyrCycle a o)
    (ha : 0 < a) (h1 : a ≠ 1) :
    ∃ x y z : ℕ,
      (gapWord a o).sum = 103768467013 * x + 114208327604 * y + 124648188195 * z ∧
      o = 65470613321 * x + 72057431991 * y + 78644250661 * z ∧ 1 ≤ y ∧ x * z = 0 := by
  obtain ⟨l2a, l2b, l3a, l3b⟩ := CycleLength.log_two_three
  have hm : ∀ k < o, ((2 : ℝ) ^ 71) ≤ syr^[k] a := fun k _ => by
    exact_mod_cast CycleLiterature.barina_cycle_ge hB h ha h1 k
  obtain ⟨t1, t2⟩ := sandwich h (by positivity) hm
  set E := (gapWord a o).sum
  have ho : (0 : ℝ) < o := by exact_mod_cast h.1
  have hl2 : (0 : ℝ) < Real.log 2 := by linarith
  have Kn : (0 : ℝ) < 65470613321 * Real.log 3 - 103768467013 * Real.log 2 := by linarith
  have Kw : (78644250661 : ℝ) / (3 * 2 ^ 71) <
      124648188195 * Real.log 2 - 78644250661 * Real.log 3 := by
    norm_num; linarith
  have Fn : (0 : ℤ) < (E : ℤ) * 65470613321 - 103768467013 * (o : ℤ) := by
    have hr : (0 : ℝ) <
        (((E : ℤ) * 65470613321 - 103768467013 * (o : ℤ) : ℤ) : ℝ) * Real.log 2 := by
      push_cast
      linarith [mul_pos ho Kn]
    exact Int.cast_pos.mp ((pos_iff_pos_of_mul_pos hr).2 hl2)
  have Fw : (0 : ℤ) < 124648188195 * (o : ℤ) - (E : ℤ) * 78644250661 := by
    have hr : (0 : ℝ) <
        ((124648188195 * (o : ℤ) - (E : ℤ) * 78644250661 : ℤ) : ℝ) * Real.log 2 := by
      push_cast
      have := mul_lt_mul_of_pos_left Kw ho
      have e : (o : ℝ) * (78644250661 / (3 * 2 ^ 71)) = 78644250661 * (o / (3 * 2 ^ 71)) := by ring
      linarith
    exact Int.cast_pos.mp ((pos_iff_pos_of_mul_pos hr).2 hl2)
  rcases le_or_gt 0 ((E : ℤ) * 72057431991 - 114208327604 * (o : ℤ)) with ht | ht
  · obtain ⟨hE, ho'⟩ := cone_decomp (p := 114208327604) (q := 72057431991) (p' := 124648188195)
      (q' := 78644250661) (E := (E : ℤ)) (o := (o : ℤ)) (by norm_num)
    obtain ⟨y, hy⟩ := Int.eq_ofNat_of_zero_le Fw.le
    obtain ⟨z, hz⟩ := Int.eq_ofNat_of_zero_le ht
    refine ⟨0, y, z, ?_, ?_, ?_, by simp⟩
    · rw [hy, hz] at hE; omega
    · rw [hy, hz] at ho'; omega
    · omega
  · obtain ⟨hE, ho'⟩ := cone_decomp (p := 103768467013) (q := 65470613321) (p' := 114208327604)
      (q' := 72057431991) (E := (E : ℤ)) (o := (o : ℤ)) (by norm_num)
    obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le
      (show (0 : ℤ) ≤ 114208327604 * (o : ℤ) - (E : ℤ) * 72057431991 by omega)
    obtain ⟨y, hy⟩ := Int.eq_ofNat_of_zero_le Fn.le
    refine ⟨x, y, 0, ?_, ?_, ?_, by simp⟩
    · rw [hx, hy] at hE; omega
    · rw [hx, hy] at ho'; omega
    · omega

end Syracuse.Eliahou
