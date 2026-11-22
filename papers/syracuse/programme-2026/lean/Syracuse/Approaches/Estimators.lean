import Syracuse.Approaches.ExplicitF

/-!
# The abelian estimator, normalised (PROGRAM.md §9.4), and cycle words are `C`-balanced

**§9.4.** PROGRAM.md asks to turn the AM–GM estimator `G_*(w) ≤ A(w) ≤ C(w)·G_*(w)`
(`Program.amgm_sandwich`) into a size estimate of the integer `6`-free part. For a positive nonempty word
`S(w)` is odd (`Sz_odd`) and prime to `3` (`Sz_not_three_dvd`), so its `6`-free part is `S(w)` itself
(`sixFree_Sz`). Since `A(w) = S(w)/(n 3^{n-1})`, the estimator is a two-sided estimate of that `6`-free
part (`abelian_estimate`):

`n 3^{n-1} G_*(w) ≤ sixfree(S(w)) = S(w) ≤ C(w)·n 3^{n-1} G_*(w)`.

On a cycle `|x|·|D| = S(w)` (`cycle_abelian`), so the estimator also locates every cycle point to within
the factor `C(w)`, given `D`.

**Cycle words are `C`-balanced.** Along a window `u` of length `ℓ` (`window_identity`),
`2^{E(u)}·x_{i+ℓ} = 3^ℓ·x_i·Π_k (1 + 1/(3x_k))`. Hence two windows of the same length in a positive cycle
whose points lie in `[m, M]` differ in weight by at most `2 log₂(M/m) + ℓ log₂(1 + 1/(3m))`
(`c_balanced`; the proof needs only a positive orbit bounded in `[m, M]`): `2^{E(u)} ≤ (M/m)²·(1 + 1/(3m))^ℓ·2^{E(u')}`. The review had this only as a derivation.
On a cycle the window product is a sub-product of the whole cycle's product `2^E/3^o`
(`window_prod_le`), so the `+1` of the derivation becomes the exact defect (`c_balanced_cycle`):
`E(u) − E(u') ≤ 2 log₂(x_max/x_min) + (E − o log₂3)` for windows of equal length `ℓ ≤ o`.
Balanced words (`C = 1`) are excluded (`BalancedClass`); this bound controls how unbalanced a cycle word
can be.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `S(w)` odd and prime to `3` for positive nonempty `w` | `Sz_odd`, `Sz_not_three_dvd` | proved |
| `sixfree(S(w)) = |S(w)|` | `sixFree_Sz` | proved |
| `n 3^{n-1} G_* ≤ S ≤ C·n 3^{n-1} G_*` | `abelian_estimate` | proved |
| on a cycle `|x|·|D| = S` | `cycle_abelian` | proved |
| window identity `2^{E(u)} x_{i+ℓ} = 3^ℓ x_i Π(1 + 1/(3x_k))` | `window_identity` | proved |
| **cycle words are `C`-balanced** (any positive orbit in `[m, M]`) | `c_balanced` | proved |
| on a cycle the window product is at most `2^E/3^o` | `window_prod_le` | proved |
| **`C`-balance with the exact defect**: `E(u) − E(u') ≤ 2 log₂(M/m) + (E − o log₂3)` | `c_balanced_cycle` | proved |
-/

namespace Syracuse.Estimators

open Finset Syracuse

/-! ## §9.4 -/

lemma Sz_odd {w : Word} (hw : w.Pos) (hne : w ≠ []) : Odd (Sz w) := by
  obtain ⟨d, u, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hd : 1 ≤ d := hw d List.mem_cons_self
  simp only [Sz, S_cons]
  have h3 : Odd ((3 : ℤ) ^ u.length) := Odd.pow (by decide)
  have h2 : Even ((2 : ℤ) ^ d * S 2 3 u) :=
    ((by decide : Even (2 : ℤ)).pow_of_ne_zero (by omega)).mul_right _
  exact h3.add_even h2

lemma Sz_not_three_dvd {w : Word} (hne : w ≠ []) : ¬ (3 : ℤ) ∣ Sz w := by
  rcases List.eq_nil_or_concat w with h | ⟨u, d, rfl⟩
  · exact absurd h hne
  intro h3
  simp only [Sz, List.concat_eq_append, S_append, S_singleton, List.length_singleton, pow_one,
    mul_one] at h3
  have : (3 : ℤ) ∣ 2 ^ u.sum := by
    have := dvd_sub h3 (dvd_mul_right (3 : ℤ) (S 2 3 u))
    simpa using this
  have hp : Prime (3 : ℤ) := Int.prime_three
  have := hp.dvd_of_dvd_pow this
  norm_num at this

/-- The `6`-free part of `S(w)` is `|S(w)|`. -/
lemma sixFree_Sz {w : Word} (hw : w.Pos) (hne : w ≠ []) : sixFree (Sz w) = (Sz w).natAbs := by
  unfold sixFree
  have h2 : ¬ 2 ∣ (Sz w).natAbs := by
    intro h
    have : (2 : ℤ) ∣ Sz w := Int.natAbs_dvd_natAbs.1 (by simpa using h)
    exact (Int.not_even_iff_odd.2 (Sz_odd hw hne)) (even_iff_two_dvd.2 this)
  have h3 : ¬ 3 ∣ (Sz w).natAbs := by
    intro h
    exact Sz_not_three_dvd hne (Int.natAbs_dvd_natAbs.1 (by simpa using h))
  rw [Nat.factorization_eq_zero_of_not_dvd h2, pow_zero, Nat.div_one,
    Nat.factorization_eq_zero_of_not_dvd h3, pow_zero, Nat.div_one]

/-- **The abelian estimator, normalised.** -/
theorem abelian_estimate {w : Word} (hne : w ≠ []) :
    (w.length * 3 ^ (w.length - 1) : ℝ) * Program.gmean w ≤ Sz w ∧
      (Sz w : ℝ) ≤ Program.stark w hne * ((w.length * 3 ^ (w.length - 1) : ℝ) * Program.gmean w) := by
  obtain ⟨h1, h2⟩ := Program.amgm_sandwich hne
  have hN : (0 : ℝ) < w.length * 3 ^ (w.length - 1) := by
    have : 0 < w.length := List.length_pos_of_ne_nil hne
    positivity
  have hA : Program.amean w * (w.length * 3 ^ (w.length - 1)) = Sz w := by
    unfold Program.amean; exact div_mul_cancel₀ _ hN.ne'
  constructor
  · rw [← hA]; nlinarith
  · rw [← hA]; nlinarith

/-- On a cycle, `|x|·|D| = S`. -/
theorem cycle_abelian {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) :
    |x| * |Dz (gapWord x o)| = Sz (gapWord x o) := by
  have hS := CycleLiterature.Sz_pos (CycleLiterature.cycle_gapWord_ne_nil h)
  rw [← abs_mul, mul_comm, h.cycle_equation, abs_of_pos hS]

/-! ## Cycle words are `C`-balanced -/

/-- **Window identity.** Along `ℓ` steps from `y > 0`,
`2^{E}·syr^ℓ y = 3^ℓ·y·Π_{k<ℓ}(1 + 1/(3 syr^k y))`. -/
theorem window_identity {y : ℤ} (hy : 0 < y) (ℓ : ℕ) :
    (2 : ℝ) ^ (gapWord y ℓ).sum * (syr^[ℓ] y : ℝ) =
      3 ^ ℓ * y * ∏ k ∈ range ℓ, (1 + 1 / (3 * (syr^[k] y : ℝ))) := by
  induction ℓ with
  | zero => simp [gapWord]
  | succ ℓ ih =>
    have hsplit := Repeat.gapWord_add y ℓ 1
    have hz : (0 : ℝ) < syr^[ℓ] y := by exact_mod_cast CycleLiterature.syr_iterate_pos hy ℓ
    set z := syr^[ℓ] y
    have hg : gapWord z 1 = [gap z] := by simp [gapWord]
    rw [hsplit, hg, List.sum_append, List.sum_singleton, pow_add, prod_range_succ,
      Function.iterate_succ_apply']
    have hstep : (2 : ℝ) ^ gap z * (syr z : ℝ) = 3 * z + 1 := by exact_mod_cast two_pow_gap_mul_syr z
    calc (2 : ℝ) ^ (gapWord y ℓ).sum * 2 ^ gap z * (syr z : ℝ)
        = (2 : ℝ) ^ (gapWord y ℓ).sum * ((2 : ℝ) ^ gap z * (syr z : ℝ)) := by ring
      _ = (2 : ℝ) ^ (gapWord y ℓ).sum * (3 * z + 1) := by rw [hstep]
      _ = ((2 : ℝ) ^ (gapWord y ℓ).sum * z) * 3 * (1 + 1 / (3 * z)) := by field_simp
      _ = _ := by rw [ih]; ring

/-- **Cycle words are `C`-balanced.** For a positive orbit whose points lie in `[m, M]` (`m > 0`), any two
windows of length `ℓ` satisfy `2^{E(u)} ≤ (M/m)²·(1 + 1/(3m))^ℓ·2^{E(u')}`. No cycle is assumed; a
positive cycle has finitely many points, so it always has such `m` and `M`. -/
theorem c_balanced {x : ℤ} (hx : 0 < x) {m M : ℝ} (hm0 : 0 < m)
    (hm : ∀ k, m ≤ (syr^[k] x : ℝ)) (hM : ∀ k, (syr^[k] x : ℝ) ≤ M) (i j ℓ : ℕ) :
    (2 : ℝ) ^ (gapWord (syr^[i] x) ℓ).sum ≤
      (M / m) ^ 2 * (1 + 1 / (3 * m)) ^ ℓ * (2 : ℝ) ^ (gapWord (syr^[j] x) ℓ).sum := by
  have hyi := CycleLiterature.syr_iterate_pos hx i
  have hyj := CycleLiterature.syr_iterate_pos hx j
  have wi := window_identity hyi ℓ
  have wj := window_identity hyj ℓ
  simp only [← Function.iterate_add_apply] at wi wj
  have pos : ∀ k, (0 : ℝ) < syr^[k] x := fun k => lt_of_lt_of_le hm0 (hm k)
  set Q := (1 + 1 / (3 * m)) ^ ℓ
  -- `Π_i ≤ (1 + 1/(3m))^ℓ` and `1 ≤ Π_j`
  have fac_le : ∀ k, 1 + 1 / (3 * (syr^[k] x : ℝ)) ≤ 1 + 1 / (3 * m) := fun k => by
    have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 3 * m)
      (by linarith [hm k] : 3 * m ≤ 3 * (syr^[k] x : ℝ))
    linarith
  have fac_ge : ∀ k, (1 : ℝ) ≤ 1 + 1 / (3 * (syr^[k] x : ℝ)) := fun k => by
    have := pos k; have : (0 : ℝ) ≤ 1 / (3 * (syr^[k] x : ℝ)) := by positivity
    linarith
  have Pi_le : ∏ k ∈ range ℓ, (1 + 1 / (3 * (syr^[k + i] x : ℝ))) ≤ Q := by
    calc ∏ k ∈ range ℓ, (1 + 1 / (3 * (syr^[k + i] x : ℝ))) ≤ ∏ _k ∈ range ℓ, (1 + 1 / (3 * m)) :=
          Finset.prod_le_prod₀ (fun k _ => by linarith [fac_ge (k + i)]) (fun k _ => fac_le (k + i))
      _ = Q := by simp [Q]
  have Pj_ge : (1 : ℝ) ≤ ∏ k ∈ range ℓ, (1 + 1 / (3 * (syr^[k + j] x : ℝ))) := by
    calc (1 : ℝ) = ∏ _k ∈ range ℓ, (1 : ℝ) := by simp
      _ ≤ ∏ k ∈ range ℓ, (1 + 1 / (3 * (syr^[k + j] x : ℝ))) :=
          Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun k _ => fac_ge (k + j))
  set A := (2 : ℝ) ^ (gapWord (syr^[i] x) ℓ).sum
  set Bj := (2 : ℝ) ^ (gapWord (syr^[j] x) ℓ).sum
  set T := (3 : ℝ) ^ ℓ
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ Bj := by positivity
  have hT0 : 0 ≤ T := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  -- `A·m ≤ T·M·Q`
  have h1 : A * m ≤ T * M * Q := by
    calc A * m ≤ A * (syr^[ℓ + i] x : ℝ) := mul_le_mul_of_nonneg_left (hm _) hA0
      _ = T * (syr^[i] x : ℝ) * ∏ k ∈ range ℓ, (1 + 1 / (3 * (syr^[k + i] x : ℝ))) := wi
      _ ≤ T * M * Q := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (hM i) hT0) Pi_le
            (prod_nonneg fun k _ => by linarith [fac_ge (k + i)])
            (mul_nonneg hT0 (by linarith [hM 0, pos 0]))
  -- `T·m ≤ Bj·M`
  have h2 : T * m ≤ Bj * M := by
    calc T * m ≤ T * (syr^[j] x : ℝ) * 1 := by rw [mul_one]; exact mul_le_mul_of_nonneg_left (hm j) hT0
      _ ≤ T * (syr^[j] x : ℝ) * ∏ k ∈ range ℓ, (1 + 1 / (3 * (syr^[k + j] x : ℝ))) :=
          mul_le_mul_of_nonneg_left Pj_ge (by nlinarith [pos j])
      _ = Bj * (syr^[ℓ + j] x : ℝ) := wj.symm
      _ ≤ Bj * M := mul_le_mul_of_nonneg_left (hM _) hB0
  have hMm : 0 < M := lt_of_lt_of_le (pos 0) (hM 0)
  rw [show (M / m) ^ 2 * Q * Bj = M ^ 2 * Q * Bj / m ^ 2 by field_simp, le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ M * Q)]

/-- **On a cycle the window product is at most `2^E/3^o`.** For a positive cycle and `ℓ ≤ o`,
`3^o·Π_{k<ℓ}(1 + 1/(3x_{i+k})) ≤ 2^E`: the window's product is a sub-product of the whole cycle's,
every factor is at least `1`, and the whole product is `2^E/3^o`. -/
lemma window_prod_le {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x) (i : ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ o) :
    (3 : ℝ) ^ o * ∏ k ∈ range ℓ, (1 + 1 / (3 * (syr^[k + i] x : ℝ))) ≤ 2 ^ (gapWord x o).sum := by
  have hyi := CycleLiterature.syr_iterate_pos hx i
  have full := window_identity hyi o
  rw [(Repeat.isSyrCycle_iterate h i).2.2, Repeat.sum_gapWord_iterate h i] at full
  simp only [← Function.iterate_add_apply] at full
  have hy : (0 : ℝ) < syr^[i] x := by exact_mod_cast hyi
  set f : ℕ → ℝ := fun k => 1 + 1 / (3 * (syr^[k + i] x : ℝ))
  have f1 : ∀ k, 1 ≤ f k := fun k => by
    have : (0 : ℝ) < syr^[k + i] x := by exact_mod_cast CycleLiterature.syr_iterate_pos hx (k + i)
    have : (0 : ℝ) ≤ 1 / (3 * (syr^[k + i] x : ℝ)) := by positivity
    simp only [f]; linarith
  have hsplit := prod_range_mul_prod_Ico f hℓ
  have hIco : 1 ≤ ∏ k ∈ Ico ℓ o, f k := one_le_prod₀ (fun k _ => f1 k)
  have hpre : 0 ≤ ∏ k ∈ range ℓ, f k := prod_nonneg (fun k _ => by linarith [f1 k])
  have hsub : ∏ k ∈ range ℓ, f k ≤ ∏ k ∈ range o, f k := by
    rw [← hsplit]; nlinarith
  have hfull : (2 : ℝ) ^ (gapWord x o).sum = 3 ^ o * ∏ k ∈ range o, f k := by
    have := full
    rw [show (3 : ℝ) ^ o * (syr^[i] x : ℝ) * ∏ k ∈ range o, f k =
      (3 ^ o * ∏ k ∈ range o, f k) * (syr^[i] x : ℝ) by ring] at this
    exact mul_right_cancel₀ hy.ne' this
  rw [hfull]
  exact mul_le_mul_of_nonneg_left hsub (by positivity)

/-- **Cycle words are `C`-balanced, with the exact defect.** In a positive cycle with gap word `w`
(`E = |w|`) whose points lie in `[m, M]`, two windows of the same length `ℓ ≤ o` satisfy
`3^o·2^{E(u)} ≤ (M/m)²·2^E·2^{E(u')}`, i.e.
`E(u) − E(u') ≤ 2 log₂(M/m) + (E − o log₂3)`. The defect `E − o log₂3` replaces the `+1` of the
derivation; it is below `1` exactly when `2^E < 2·3^o`. -/
theorem c_balanced_cycle {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x) {m M : ℝ} (hm0 : 0 < m)
    (hm : ∀ k, m ≤ (syr^[k] x : ℝ)) (hM : ∀ k, (syr^[k] x : ℝ) ≤ M) (i j : ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ o) :
    (3 : ℝ) ^ o * 2 ^ (gapWord (syr^[i] x) ℓ).sum ≤
      (M / m) ^ 2 * 2 ^ (gapWord x o).sum * (2 : ℝ) ^ (gapWord (syr^[j] x) ℓ).sum := by
  have hyi := CycleLiterature.syr_iterate_pos hx i
  have hyj := CycleLiterature.syr_iterate_pos hx j
  have wi := window_identity hyi ℓ
  have wj := window_identity hyj ℓ
  simp only [← Function.iterate_add_apply] at wi wj
  have pos : ∀ k, (0 : ℝ) < syr^[k] x := fun k => lt_of_lt_of_le hm0 (hm k)
  have fac_ge : ∀ k, (1 : ℝ) ≤ 1 + 1 / (3 * (syr^[k] x : ℝ)) := fun k => by
    have := pos k; have : (0 : ℝ) ≤ 1 / (3 * (syr^[k] x : ℝ)) := by positivity
    linarith
  have Pi_le := window_prod_le h hx i hℓ
  have Pi_ge : (0 : ℝ) ≤ ∏ k ∈ range ℓ, (1 + 1 / (3 * (syr^[k + i] x : ℝ))) :=
    prod_nonneg fun k _ => by linarith [fac_ge (k + i)]
  have Pj_ge : (1 : ℝ) ≤ ∏ k ∈ range ℓ, (1 + 1 / (3 * (syr^[k + j] x : ℝ))) :=
    one_le_prod₀ fun k _ => fac_ge (k + j)
  set A := (2 : ℝ) ^ (gapWord (syr^[i] x) ℓ).sum
  set Bj := (2 : ℝ) ^ (gapWord (syr^[j] x) ℓ).sum
  set T := (3 : ℝ) ^ ℓ
  set F := (2 : ℝ) ^ (gapWord x o).sum
  set H := (3 : ℝ) ^ o
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ Bj := by positivity
  have hT0 : 0 ≤ T := by positivity
  have hH0 : 0 ≤ H := by positivity
  have hMm : 0 < M := lt_of_lt_of_le (pos 0) (hM 0)
  -- `H·A·m ≤ T·M·F`
  have h1 : H * A * m ≤ T * M * F := by
    calc H * A * m ≤ H * (A * (syr^[ℓ + i] x : ℝ)) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hm _) hA0) hH0
      _ = T * (syr^[i] x : ℝ) * (H * ∏ k ∈ range ℓ, (1 + 1 / (3 * (syr^[k + i] x : ℝ)))) := by
          rw [wi]; ring
      _ ≤ T * M * F := mul_le_mul (mul_le_mul_of_nonneg_left (hM i) hT0) Pi_le
            (mul_nonneg hH0 Pi_ge) (mul_nonneg hT0 hMm.le)
  -- `T·m ≤ Bj·M`
  have h2 : T * m ≤ Bj * M := by
    calc T * m ≤ T * (syr^[j] x : ℝ) * 1 := by rw [mul_one]; exact mul_le_mul_of_nonneg_left (hm j) hT0
      _ ≤ T * (syr^[j] x : ℝ) * ∏ k ∈ range ℓ, (1 + 1 / (3 * (syr^[k + j] x : ℝ))) :=
          mul_le_mul_of_nonneg_left Pj_ge (by nlinarith [pos j])
      _ = Bj * (syr^[ℓ + j] x : ℝ) := wj.symm
      _ ≤ Bj * M := mul_le_mul_of_nonneg_left (hM _) hB0
  have hF0 : 0 ≤ F := by positivity
  rw [show (M / m) ^ 2 * F * Bj = M ^ 2 * F * Bj / m ^ 2 by field_simp, le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ M * F)]

end Syracuse.Estimators
