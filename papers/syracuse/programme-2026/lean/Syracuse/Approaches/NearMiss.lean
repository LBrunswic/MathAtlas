import Syracuse.Approaches.Limits

/-!
# The near-miss benchmark (review direction D3)

Every positive word `w` is a primitive cycle of `x ↦ (3x + k(w))/2^ν` with `k(w) = D/gcd(S, D)`
(`Limits.every_word_is_a_cycle`). A `3x + 1` cycle with word `w` exists iff `k(w) = 1`
(`Limits.positive_cycle_iff_kOf_eq_one`). The **near-miss words** sit at the critical slope with a
small `k(w) > 1`: genuine cycles of `3x + 5`, `3x + 29` and `3x + 61`. A program lever that would
exclude a word must not exclude these by an argument blind to `k`. A valid ceiling `f(w) ≥ G(w)`
must satisfy `f(w) ≥ |D|/k(w)` on them. These are the binding test cases of the limits section of
the review (`reports/cocycle-review`, §3 and D3); the data are from OEIS A226607–A226672 and
Belaga–Mignotte 2000.

Each certificate below is a closed computation (`decide`), followed by the cycle it yields. Each word
is also shown **not** to be the gap word of a positive `3x + 1` cycle, since `k ≠ 1`.

## Coverage

| Word | `(E, o)` | `k(w)` | `a(w) = S/G` | Lean |
|---|---|---|---|---|
| `11111211212321115` | (27, 17) | 5 | 187 | `w27a_k`, `w27a_cycle`, `w27a_not_syr` |
| `11113111122412122` | (27, 17) | 5 | 347 | `w27b_k`, `w27b_cycle` |
| `11111112311121121111112111311512211116233` | (65, 41), at the convergent 65/41 | 29 | 3811 | `w65a_k`, `w65a_cycle`, `w65a_not_syr` |
| `11221211111111211131222311232111231232132` | (66, 41) | 61 | 235 | `w66_k`, `w66_cycle` |
-/

namespace Syracuse.NearMiss

open Syracuse Syracuse.Limits

/-- The `3x + 5` near-miss with minimum `187`. -/
def w27a : Word := [1,1,1,1,1,2,1,1,2,1,2,3,2,1,1,1,5]
/-- The `3x + 5` near-miss with minimum `347`. -/
def w27b : Word := [1,1,1,1,3,1,1,1,1,2,2,4,1,2,1,2,2]
/-- The `3x + 29` near-miss at the convergent `65/41` of `log₂ 3`. -/
def w65a : Word := [1,1,1,1,1,1,1,2,3,1,1,1,2,1,1,2,1,1,1,1,1,1,2,1,1,1,3,1,1,5,1,2,2,1,1,1,1,6,2,3,3]
/-- The `3x + 61` near-miss at `(E, o) = (66, 41)`. -/
def w66 : Word := [1,1,2,2,1,2,1,1,1,1,1,1,1,1,2,1,1,1,3,1,2,2,2,3,1,1,2,3,2,1,1,1,2,3,1,2,3,2,1,3,2]

/-- `k = 5`, `a = 187` for `w27a`. -/
theorem w27a_k : kOf w27a = 5 ∧ aOf w27a = 187 := by decide
/-- `k = 5`, `a = 347` for `w27b`. -/
theorem w27b_k : kOf w27b = 5 ∧ aOf w27b = 347 := by decide
/-- `k = 29`, `a = 3811` for `w65a`. -/
theorem w65a_k : kOf w65a = 29 ∧ aOf w65a = 3811 := by decide
/-- `k = 61`, `a = 235` for `w66`. -/
theorem w66_k : kOf w66 = 61 ∧ aOf w66 = 235 := by decide

/-- The four words are positive and nonempty. -/
lemma pos_ne {w : Word} (h : w = w27a ∨ w = w27b ∨ w = w65a ∨ w = w66) : w.Pos ∧ w ≠ [] := by
  rcases h with rfl | rfl | rfl | rfl <;>
    exact ⟨fun d hd => by simp [w27a, w27b, w65a, w66] at hd; omega, by simp [w27a, w27b, w65a, w66]⟩

/-- `w27a` is the gap word of the `3x + 5` cycle through `187` (length 17). -/
theorem w27a_cycle : IsCycleK 5 187 17 ∧ gapWordK 5 187 17 = w27a := by
  obtain ⟨hp, hn⟩ := pos_ne (Or.inl rfl)
  have := every_word_is_a_cycle hp hn
  rw [w27a_k.1, w27a_k.2] at this
  exact ⟨this.2.2.2.2.1, this.2.2.2.2.2⟩

/-- `w27b` is the gap word of the `3x + 5` cycle through `347`. -/
theorem w27b_cycle : IsCycleK 5 347 17 ∧ gapWordK 5 347 17 = w27b := by
  obtain ⟨hp, hn⟩ := pos_ne (Or.inr (Or.inl rfl))
  have := every_word_is_a_cycle hp hn
  rw [w27b_k.1, w27b_k.2] at this
  exact ⟨this.2.2.2.2.1, this.2.2.2.2.2⟩

/-- `w65a` is the gap word of the `3x + 29` cycle through `3811` (length 41). -/
theorem w65a_cycle : IsCycleK 29 3811 41 ∧ gapWordK 29 3811 41 = w65a := by
  obtain ⟨hp, hn⟩ := pos_ne (Or.inr (Or.inr (Or.inl rfl)))
  have := every_word_is_a_cycle hp hn
  rw [w65a_k.1, w65a_k.2] at this
  exact ⟨this.2.2.2.2.1, this.2.2.2.2.2⟩

/-- `w66` is the gap word of the `3x + 61` cycle through `235` (length 41). -/
theorem w66_cycle : IsCycleK 61 235 41 ∧ gapWordK 61 235 41 = w66 := by
  obtain ⟨hp, hn⟩ := pos_ne (Or.inr (Or.inr (Or.inr rfl)))
  have := every_word_is_a_cycle hp hn
  rw [w66_k.1, w66_k.2] at this
  exact ⟨this.2.2.2.2.1, this.2.2.2.2.2⟩

/-- `w27a` is **not** the gap word of a positive `3x + 1` cycle (`k = 5 ≠ 1`). -/
theorem w27a_not_syr : ¬ ∃ a, 0 < a ∧ IsSyrCycle a 17 ∧ gapWord a 17 = w27a := by
  obtain ⟨hp, hn⟩ := pos_ne (Or.inl rfl)
  have := positive_cycle_iff_kOf_eq_one hp hn
  simp only [show w27a.length = 17 from rfl] at this
  rw [this, w27a_k.1]; decide

/-- `w65a` is **not** the gap word of a positive `3x + 1` cycle (`k = 29 ≠ 1`). -/
theorem w65a_not_syr : ¬ ∃ a, 0 < a ∧ IsSyrCycle a 41 ∧ gapWord a 41 = w65a := by
  obtain ⟨hp, hn⟩ := pos_ne (Or.inr (Or.inr (Or.inl rfl)))
  have := positive_cycle_iff_kOf_eq_one hp hn
  simp only [show w65a.length = 41 from rfl] at this
  rw [this, w65a_k.1]; decide

/-- **Slack bar.** On a near-miss word, any rotation-ideal ceiling `f ≥ G` satisfies
`f ≥ |D|/k`: for `w65a`, `G = |D|/29 ≈ 1.45·10^16`. -/
theorem w65a_G : gSD w65a = 14499716215459201 := by decide

end Syracuse.NearMiss
