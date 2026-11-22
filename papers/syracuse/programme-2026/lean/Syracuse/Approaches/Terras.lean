import Syracuse.Approaches.CycleLiterature

/-!
# Terras's theorem (1976), proved

`CycleLiterature.Terras1976` stated, without proof: for every `k`, the first `k` parities of the
`T`-orbit of `n` (`T n = n/2` or `(3n+1)/2`) depend only on `n mod 2^k`, and the map from residues
mod `2^k` to parity vectors in `{0,1}^k` is a bijection (R. Terras, Acta Arith. 30 (1976) 241–252;
Lagarias 1985, Thm. B). It is now a theorem (`terras`).

**Proof.** If `n ≡ m (mod 2^{j+1})`, then `n` and `m` have the same parity and `T n ≡ T m (mod 2^j)`
(`T_modEq`), so congruence mod `2^k` fixes the first `k` parities (`parity_eq_of_modEq`). Conversely,
equal first `k` parities force `n ≡ m (mod 2^k)` (`modEq_of_parity_eq`): one step back from
`T n ≡ T m (mod 2^k)` doubles the modulus, cancelling the unit `3` in the odd case. So the parity map is
injective on residues, and both sides have `2^k` elements.

This is the arithmetic behind the report's "2-adic blindness" limit: every finite parity pattern is
realised by exactly one residue class, so no finite amount of parity information excludes a cycle.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `n ≡ m (mod 2^{j+1})` ⇒ same parity and `T n ≡ T m (mod 2^j)` | `T_modEq` | proved |
| congruence mod `2^k` fixes the first `k` parities | `parity_eq_of_modEq` | proved |
| equal first `k` parities ⇒ congruence mod `2^k` | `modEq_of_parity_eq` | proved |
| **Terras 1976** (the stated `Prop`) | `terras` | **proved** |
-/

namespace Syracuse.Terras

open CycleLiterature

/-- One step: congruence mod `2^{j+1}` gives the same parity and congruence of `T` mod `2^j`. -/
lemma T_modEq {n m j : ℕ} (h : n ≡ m [MOD 2 ^ (j + 1)]) :
    n % 2 = m % 2 ∧ T n ≡ T m [MOD 2 ^ j] := by
  have h2 : n % 2 = m % 2 := Nat.ModEq.of_dvd (dvd_pow_self 2 (by omega)) h
  refine ⟨h2, ?_⟩
  rw [pow_succ'] at h
  unfold T
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have hm : m % 2 = 0 := by omega
    rw [if_pos hn, if_pos hm]
    apply Nat.ModEq.mul_left_cancel' (c := 2) (by norm_num)
    rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hn),
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)]
  · have hm : m % 2 = 1 := by omega
    rw [if_neg (by omega), if_neg (by omega)]
    apply Nat.ModEq.mul_left_cancel' (c := 2) (by norm_num)
    rw [Nat.mul_div_cancel' (by omega : 2 ∣ 3 * n + 1), Nat.mul_div_cancel' (by omega : 2 ∣ 3 * m + 1)]
    exact Nat.ModEq.add_right 1 (Nat.ModEq.mul_left 3 h)

/-- Congruence mod `2^k` fixes the first `k` parities of the `T`-orbit. -/
lemma parity_eq_of_modEq {n m k : ℕ} (h : n ≡ m [MOD 2 ^ k]) :
    ∀ i < k, T^[i] n % 2 = T^[i] m % 2 := by
  have key : ∀ i ≤ k, T^[i] n ≡ T^[i] m [MOD 2 ^ (k - i)] := by
    intro i
    induction i with
    | zero => intro _; simpa using h
    | succ i ih =>
      intro hi
      have := ih (by omega)
      rw [show k - i = (k - (i + 1)) + 1 by omega] at this
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (T_modEq this).2
  intro i hi
  have := key i hi.le
  rw [show k - i = (k - i - 1) + 1 by omega] at this
  exact (T_modEq this).1

/-- Equal first `k` parities force congruence mod `2^k`. -/
lemma modEq_of_parity_eq : ∀ (k n m : ℕ), (∀ i < k, T^[i] n % 2 = T^[i] m % 2) →
    n ≡ m [MOD 2 ^ k] := by
  intro k
  induction k with
  | zero => intro n m _; simp [Nat.ModEq, Nat.mod_one]
  | succ k ih =>
    intro n m h
    have h0 : n % 2 = m % 2 := by simpa using h 0 (by omega)
    have hT : T n ≡ T m [MOD 2 ^ k] := ih (T n) (T m) fun i hi => by
      have := h (i + 1) (by omega)
      rwa [Function.iterate_succ_apply, Function.iterate_succ_apply] at this
    rw [pow_succ']
    unfold T at hT
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · have hm : m % 2 = 0 := by omega
      rw [if_pos hn, if_pos hm] at hT
      have := Nat.ModEq.mul_left' 2 hT
      rwa [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hn),
        Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)] at this
    · have hm : m % 2 = 1 := by omega
      rw [if_neg (by omega), if_neg (by omega)] at hT
      have := Nat.ModEq.mul_left' 2 hT
      rw [Nat.mul_div_cancel' (by omega : 2 ∣ 3 * n + 1),
        Nat.mul_div_cancel' (by omega : 2 ∣ 3 * m + 1)] at this
      have h3 : 3 * n ≡ 3 * m [MOD 2 * 2 ^ k] := Nat.ModEq.add_right_cancel' 1 this
      refine Nat.ModEq.cancel_left_of_coprime ?_ h3
      rw [← pow_succ']
      exact Nat.Coprime.pow_left _ (by norm_num)

/-- **Terras 1976, proved.** -/
theorem terras : Terras1976 := by
  intro k
  refine ⟨fun n i hi => parity_eq_of_modEq (Nat.mod_modEq n (2 ^ k)).symm i hi, ?_⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun r r' hrr => ?_, by simp⟩
  have hpar : ∀ i < k, T^[i] r.val % 2 = T^[i] r'.val % 2 := fun i hi => by
    have := congrFun hrr ⟨i, hi⟩
    simp only [decide_eq_decide] at this
    omega
  have := modEq_of_parity_eq k r.val r'.val hpar
  exact Fin.ext (by rwa [Nat.ModEq, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt r'.isLt] at this)

end Syracuse.Terras
