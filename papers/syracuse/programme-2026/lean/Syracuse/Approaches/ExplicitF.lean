import Syracuse.Approaches.MRunsSigned

/-!
# PROGRAM.md §5: an explicit `f(w)` for every few-run word

PROGRAM.md §5 sets the program's first objective: an **explicit** upper bound `f(w)` on a move
representative (a combination of `S` and `D` in the rotation ideal), proved below `3^o` for critical
words, together with "how far below".

For words with `m` runs of base blocks this is now explicit (`explicit_f`). No cycle is assumed. For every
`m`-periodic family of positive nonempty base blocks of total weight `B`, some rotation `R` of the word
`W` gives

`C_R := D'·S(W_R) - A_R·D(W_R) = 2^{E(Q_R)}·T_R`  (a combination in the rotation ideal),

`|T_R| ≤ m·2^{6B+1}·2^{c_m·max(E, o log₂3)}`,  `c_m = 1 - 1/Σ_{i<m}(log₂3)^i`.

So `f(w) = m·2^{6B+1}·2^{c_m·max(E, o log₂3)}`. At the critical slope it lies below `3^o` by a factor
`2^{-(1-c_m)·o log₂3}`, up to the block-dependent `2^{6B+1}`. The exponent `c_m` is sharp
(`Reach.reach_tight`), and it tends to `1` as `m` grows. This quantifies the §5 objective and its limit:
move representatives built from wedge cores are exponentially smaller than `3^o` for each fixed number of
runs, with a margin that shrinks like `(log₂3)^{-m}`.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| some rotation has `|T_R| ≤ m·2^K·2^{c_m·max}` (no cycle assumed) | `exists_small_T` | proved |
| **explicit `f(w)` for every `m`-run word** | `explicit_f` | proved |
-/

namespace Syracuse.ExplicitF

open Finset Syracuse.MRuns Syracuse.MRunsExplicit

/-- **Some rotation has a small `T`.** No cycle is assumed. -/
theorem exists_small_T {Q : ℕ → Word} {m : ℕ} (hm : 1 ≤ m) (hQ : ∀ i, Q (i + m) = Q i)
    (hpos : ∀ i, (Q i).Pos) {A : ℕ → ℤ} (hAper : ∀ i, A (i + m) = A i) {K : ℕ}
    (hK : ∀ i, |A i - A (i + 1)| ≤ 2 ^ K) :
    ∃ R : ℕ, |((T (2 : ℤ) 3 (fun k => Q (R + k)) (fun k => A (R + k)) m : ℤ) : ℝ)| ≤
      m * (2 ^ K * (2 : ℝ) ^ ((1 - 1 / Reach.σ (Real.logb 2 3) m) *
        max ((cat Q m).sum : ℝ) (Real.logb 2 3 * (cat Q m).length))) := by
  set lam := Real.logb 2 3 with hlam_def
  have hlam : 1 ≤ lam := by
    rw [hlam_def, Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]; norm_num
  set xs : ℕ → ℝ := fun i => ((Q i).sum : ℝ)
  set ys : ℕ → ℝ := fun i => lam * (Q i).length
  have hy0 : ∀ i, 0 ≤ ys i := fun i => by simp only [ys]; positivity
  have hcap : ∀ i, ys i ≤ lam * xs i := fun i => by
    simp only [ys, xs]
    have := CycleLiterature.length_le_sum (hpos i)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by linarith)
  have pxs : ∀ i, xs (i + m) = xs i := fun i => by simp only [xs, hQ]
  have pys : ∀ i, ys (i + m) = ys i := fun i => by simp only [ys, hQ]
  obtain ⟨R, hR⟩ := Reach.reach_upper hlam hm hy0 hcap pxs pys
  have hX : Reach.P xs m = ((cat Q m).sum : ℝ) := by
    simp only [Reach.P, xs, cat_sum, Es]; push_cast; rw [range_eq_Ico]
  have hY : Reach.P ys m = lam * (cat Q m).length := by
    simp only [Reach.P, ys, cat_length, Os]; push_cast; rw [range_eq_Ico, mul_sum]
  rw [hX, hY] at hR
  set Mx := max ((cat Q m).sum : ℝ) (lam * (cat Q m).length)
  set c := 1 - 1 / Reach.σ lam m
  set Q' : ℕ → Word := fun k => Q (R + k)
  set A' : ℕ → ℤ := fun k => A (R + k)
  refine ⟨R, ?_⟩
  rw [T]; push_cast
  calc |∑ j ∈ Ico 1 (m + 1), ((A' (j - 1) : ℝ) - A' (j % m)) * (2 ^ Es Q' 1 j * 3 ^ Os Q' j m)|
      ≤ ∑ j ∈ Ico 1 (m + 1), |((A' (j - 1) : ℝ) - A' (j % m)) * (2 ^ Es Q' 1 j * 3 ^ Os Q' j m)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Ico 1 (m + 1), (2 ^ K * (2 : ℝ) ^ (c * Mx)) := by
        refine sum_le_sum (fun j hj => ?_)
        rw [mem_Ico] at hj
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ Es Q' 1 j * 3 ^ Os Q' j m)]
        apply mul_le_mul _ _ (by positivity) (by positivity)
        · have hc : A' (j % m) = A (R + (j - 1) + 1) := by
            simp only [A']
            rcases Nat.lt_or_ge j m with hjm | hjm
            · rw [Nat.mod_eq_of_lt hjm]; congr 1; omega
            · rw [show j = m by omega, Nat.mod_self, show R + (m - 1) + 1 = R + m by omega,
                hAper, add_zero]
          rw [hc]
          have := hK (R + (j - 1))
          have hcast : |((A' (j - 1) : ℤ) : ℝ) - ((A (R + (j - 1) + 1) : ℤ) : ℝ)| =
              ((|A (R + (j - 1)) - A (R + (j - 1) + 1)| : ℤ) : ℝ) := by
            push_cast; rfl
          rw [hcast]; exact_mod_cast this
        · rw [two_three_rpow]
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hf := hR (j - 1) (by omega)
          have hfx : (Es Q' 1 j : ℝ) + (Os Q' j m : ℝ) * lam = Reach.f xs ys m R (j - 1) := by
            simp only [Reach.f, Es, Os, Q', xs, ys]
            rw [Nat.cast_sum, Nat.cast_sum, sum_shift (fun i => ((Q i).sum : ℝ)),
              sum_shift (fun i => ((Q i).length : ℝ)), show R + 1 + (j - 1) = R + j by omega,
              sum_mul]
            congr 1
            exact sum_congr rfl (fun _ _ => mul_comm _ _)
          rw [hfx]; exact hf
    _ = m * (2 ^ K * (2 : ℝ) ^ (c * Mx)) := by simp

/-- **Explicit `f(w)` for every `m`-run word** (`m ≥ 2`). For `m`-periodic positive nonempty base blocks
`p` of total weight `B`, exponents `a`, and `Q_i = p_i^{a_i}`, some rotation `R` gives a combination
`D'·S(W_R) - A_R·D(W_R) = 2^{E(Q_R)}·T_R` in the rotation ideal, with
`|T_R| ≤ m·2^{6B+1}·2^{c_m·max(E, o log₂3)}`. -/
theorem explicit_f {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 2 ≤ m)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos) :
    ∃ R : ℕ,
      (∏ k ∈ range m, D (2 : ℤ) 3 (p k)) *
          Sz (cat (fun k => TwoBackground.bpow (p (R + k)) (a (R + k))) m) -
        Acoef p m R * Dz (cat (fun k => TwoBackground.bpow (p (R + k)) (a (R + k))) m) =
        2 ^ (TwoBackground.bpow (p R) (a R)).sum *
          T (2 : ℤ) 3 (fun k => TwoBackground.bpow (p (R + k)) (a (R + k)))
            (fun k => Acoef p m (R + k)) m ∧
      |((T (2 : ℤ) 3 (fun k => TwoBackground.bpow (p (R + k)) (a (R + k)))
            (fun k => Acoef p m (R + k)) m : ℤ) : ℝ)| ≤
        m * (2 ^ (6 * (∑ k ∈ range m, (p k).sum) + 1) *
          (2 : ℝ) ^ ((1 - 1 / Reach.σ (Real.logb 2 3) m) *
            max ((cat (fun i => TwoBackground.bpow (p i) (a i)) m).sum : ℝ)
              (Real.logb 2 3 * (cat (fun i => TwoBackground.bpow (p i) (a i)) m).length))) := by
  set Q : ℕ → Word := fun i => TwoBackground.bpow (p i) (a i)
  have hQ : ∀ i, Q (i + m) = Q i := fun i => by simp only [Q, hp, ha]
  have hQpos : ∀ i, (Q i).Pos := fun i => StdPairs.pos_bpow (hpos i) (a i)
  obtain ⟨R, hR⟩ := exists_small_T (by omega) hQ hQpos (Acoef_period hp) (Acoef_diff_le hm hp hpos)
  refine ⟨R, ?_, hR⟩
  have hk := key_identity (2 : ℤ) 3 (fun k => Q (R + k)) (by omega : 1 ≤ m)
    (D' := ∏ k ∈ range m, D (2 : ℤ) 3 (p k)) (A := fun k => Acoef p m (R + k))
    (fun i _ => Acoef_spec (a := a) (by omega) hp (R + i))
  simp only [add_zero] at hk
  simp only [Sz, Dz]
  rw [hk]; ring

end Syracuse.ExplicitF
