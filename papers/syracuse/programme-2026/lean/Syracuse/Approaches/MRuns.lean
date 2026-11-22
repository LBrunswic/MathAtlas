import Syracuse.Approaches.Reach

/-!
# `m` runs: the general identity, and the end-to-end bound

For blocks `Q₀, …, Q_{m-1}` and the word `W = Q₀ ⋯ Q_{m-1}`, take any `D'` and `A_i` with
`D'·S(Q_i) = A_i·D(Q_i)`. For `Q_i = p_i^{a_i}`, take `D' = Π D(p_k)` and
`A_i = S(p_i) Π_{k≠i} D(p_k)`. The cocycle telescopes (`telescope`), and summation by parts gives
(`key_identity`):

`D'·S(W) = X^{E₀}·T + A₀·D(W)`,  `T = Σ_{j=1}^{m} (A_{j-1} - A_{j mod m})·X^{E_{[1,j)}} Y^{o_{[j,m)}}`.

The coefficients `A_{j-1} - A_j` are, up to sign and the other `D`s, the wedge cores of adjacent blocks.
On a cycle `D(W) ∣ T` (`dvd_T`). Rotating the word gives one such divisibility per excluded run. The
monomials of `T` are exactly the splits measured by `Reach`, so (`mruns_bounded`):

> If `|A_i - A_{i+1}| ≤ 2^K`, every rotated `T` is nonzero, and `|D(W)| ≥ 2^{θ·max(E, o log₂3) - L}`, then
> `(θ - c_m)·max(E, o log₂3) ≤ K + L + log₂ m`, `c_m = 1 - 1/Σ_{i<m}(log₂3)^i`.

With Ellison, `|D| ≥ 2^{θ_E max - 1}` with `θ_E = 1 - 1/(10 ln 2)` (`ellison_lower`), and
`θ_E > c_m` exactly when `m ≤ 3` (`Reach.ellison_reach`).

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| telescoping of the cocycle over `m` blocks | `telescope` | proved |
| `D'·S(W) = X^{E₀}·T + A₀·D(W)` | `key_identity` | proved |
| `D(W) ∣ T` on a cycle | `dvd_T` | proved |
| rotations of a periodic block word | `rot_cat` | proved |
| `2^α 3^β = 2^{α + β log₂ 3}` | `two_three_rpow` | proved |
| **end-to-end**: `(θ - c_m)·max(E, o log₂3) ≤ K + L + log₂ m` | `mruns_bounded` | proved |
| coefficients exist: `D' = Π D(p_k)`, `A_i = S(p_i) Π_{k≠i} D(p_k)` | `exists_coeffs` | proved |
| Ellison as `|D| ≥ 2^{θ_E·max(E, o log₂3) - 1}` | `ellison_lower` | proved (conditional on `Ellison1971`) |
| **every `m ≤ 3`, any blocks**: `(θ_E - c_3)·max(E, o log₂3) ≤ K + 1 + log₂ 3`, `θ_E - c_3 > 0` | `mruns_ellison` | proved (conditional on `Ellison1971`) |
-/

namespace Syracuse.MRuns

open Finset

/-- Concatenation `Q 0 ++ ⋯ ++ Q (n-1)`. -/
def cat (Q : ℕ → Word) (n : ℕ) : Word := ((List.range n).map Q).flatten

lemma cat_zero (Q : ℕ → Word) : cat Q 0 = [] := rfl

lemma cat_succ (Q : ℕ → Word) (n : ℕ) : cat Q (n + 1) = cat Q n ++ Q n := by
  simp [cat, List.range_succ]

/-- `E` over blocks `[a, b)`. -/
def Es (Q : ℕ → Word) (a b : ℕ) : ℕ := ∑ i ∈ Ico a b, (Q i).sum

/-- `o` over blocks `[a, b)`. -/
def Os (Q : ℕ → Word) (a b : ℕ) : ℕ := ∑ i ∈ Ico a b, (Q i).length

lemma cat_sum (Q : ℕ → Word) (n : ℕ) : (cat Q n).sum = Es Q 0 n := by
  induction n with
  | zero => simp [cat, Es]
  | succ n ih => rw [cat_succ, List.sum_append, ih, Es, Es, sum_Ico_succ_top (by omega)]

lemma cat_length (Q : ℕ → Word) (n : ℕ) : (cat Q n).length = Os Q 0 n := by
  induction n with
  | zero => simp [cat, Os]
  | succ n ih => rw [cat_succ, List.length_append, ih, Os, Os, sum_Ico_succ_top (by omega)]

section Generic

variable {R : Type*} [CommRing R] (X Y : R)

/-- `M_n(j) = X^{E_{[0,j)}} Y^{o_{[j,n)}}`. -/
def M (Q : ℕ → Word) (n j : ℕ) : R := X ^ Es Q 0 j * Y ^ Os Q j n

/-- **Telescoping.** -/
theorem telescope (Q : ℕ → Word) {D' : R} {A : ℕ → R} (n : ℕ)
    (hA : ∀ i < n, D' * S X Y (Q i) = A i * D X Y (Q i)) :
    D' * S X Y (cat Q n) = ∑ i ∈ range n, A i * (M X Y Q n (i + 1) - M X Y Q n i) := by
  induction n with
  | zero => simp [cat]
  | succ n ih =>
    have ih' := ih (fun i hi => hA i (by omega))
    rw [cat_succ, S_append, sum_range_succ, cat_sum]
    -- shift the old sum by `Y^{o_n}`
    have shift : ∀ i ∈ range n, A i * (M X Y Q (n + 1) (i + 1) - M X Y Q (n + 1) i) =
        Y ^ (Q n).length * (A i * (M X Y Q n (i + 1) - M X Y Q n i)) := by
      intro i hi
      rw [mem_range] at hi
      simp only [M, Os]
      rw [sum_Ico_succ_top (by omega), sum_Ico_succ_top (by omega)]
      ring
    rw [sum_congr rfl shift, ← mul_sum, ← ih']
    have hn := hA n (by omega)
    have m1 : M X Y Q (n + 1) (n + 1) = X ^ Es Q 0 n * X ^ (Q n).sum := by
      simp only [M, Os, Ico_self, sum_empty, pow_zero, mul_one]
      rw [Es, sum_Ico_succ_top (by omega), pow_add, ← Es]
    have m2 : M X Y Q (n + 1) n = X ^ Es Q 0 n * Y ^ (Q n).length := by
      simp only [M, Os]
      rw [sum_Ico_succ_top (le_refl n), Ico_self, sum_empty, zero_add]
    rw [m1, m2]
    simp only [D] at hn
    linear_combination X ^ Es Q 0 n * hn

/-- The excluded-run sum `T = Σ_{j=1}^{n} (A_{j-1} - A_{j mod n})·X^{E_{[1,j)}} Y^{o_{[j,n)}}`. -/
def T (Q : ℕ → Word) (A : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ Ico 1 (n + 1), (A (j - 1) - A (j % n)) * (X ^ Es Q 1 j * Y ^ Os Q j n)

/-- **Key identity.** `D'·S(W) = X^{E₀}·T + A₀·D(W)` for `n ≥ 1` blocks. -/
theorem key_identity (Q : ℕ → Word) {D' : R} {A : ℕ → R} {n : ℕ} (hn : 1 ≤ n)
    (hA : ∀ i < n, D' * S X Y (Q i) = A i * D X Y (Q i)) :
    D' * S X Y (cat Q n) = X ^ (Q 0).sum * T X Y Q A n + A 0 * D X Y (cat Q n) := by
  rw [telescope X Y Q n hA]
  -- `X^{E₀}·(monomial j) = M_n(j)` for `j ≥ 1`
  have hM : ∀ j, 1 ≤ j → X ^ (Q 0).sum * (X ^ Es Q 1 j * Y ^ Os Q j n) = M X Y Q n j := by
    intro j hj
    simp only [M, Es]
    rw [← sum_Ico_consecutive _ (Nat.zero_le 1) hj, pow_add]
    simp; ring
  have hT : X ^ (Q 0).sum * T X Y Q A n =
      ∑ j ∈ Ico 1 (n + 1), (A (j - 1) - A (j % n)) * M X Y Q n j := by
    rw [T, mul_sum]
    refine sum_congr rfl (fun j hj => ?_)
    rw [mem_Ico] at hj
    rw [← hM j hj.1]; ring
  rw [hT]
  -- reindex and peel
  have e1 : ∑ j ∈ Ico 1 (n + 1), (A (j - 1) - A (j % n)) * M X Y Q n j =
      ∑ i ∈ range n, A i * M X Y Q n (i + 1) - ∑ j ∈ Ico 1 (n + 1), A (j % n) * M X Y Q n j := by
    simp only [sub_mul, sum_sub_distrib]
    congr 1
    rw [sum_Ico_eq_sum_range, show n + 1 - 1 = n by omega]
    refine sum_congr rfl (fun i _ => ?_)
    rw [show 1 + i - 1 = i by omega, show 1 + i = i + 1 by omega]
  have e2 : ∑ j ∈ Ico 1 (n + 1), A (j % n) * M X Y Q n j =
      ∑ j ∈ Ico 1 n, A j * M X Y Q n j + A 0 * M X Y Q n n := by
    rw [sum_Ico_succ_top (by omega), Nat.mod_self]
    congr 1
    refine sum_congr rfl (fun j hj => ?_)
    rw [mem_Ico] at hj
    rw [Nat.mod_eq_of_lt hj.2]
  have e3 : ∑ i ∈ range n, A i * M X Y Q n i = A 0 * M X Y Q n 0 + ∑ j ∈ Ico 1 n, A j * M X Y Q n j := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hn]
  have hM0 : M X Y Q n 0 = Y ^ (cat Q n).length := by simp [M, Es, cat_length]
  have hMn : M X Y Q n n = X ^ (cat Q n).sum := by simp [M, Os, cat_sum]
  have e4 : ∑ i ∈ range n, A i * (M X Y Q n (i + 1) - M X Y Q n i) =
      ∑ i ∈ range n, A i * M X Y Q n (i + 1) - ∑ i ∈ range n, A i * M X Y Q n i := by
    rw [← sum_sub_distrib]; refine sum_congr rfl (fun i _ => by ring)
  rw [e1, e2, e4, e3, hM0, hMn]
  simp only [D]
  ring

end Generic

/-- **`m`-run divisibility.** On a cycle whose gap word is a rotation of `cat Q n` (`n ≥ 1`), for any
integers `D'`, `A_i` with `D'·S(Q_i) = A_i·D(Q_i)`, `D(cat Q n) ∣ T`. -/
theorem dvd_T {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {Q : ℕ → Word} {n : ℕ} (hn : 1 ≤ n)
    (hw : gapWord x o ~r cat Q n) (hne : cat Q n ≠ []) (hE : (cat Q n).sum ≠ 0)
    {D' : ℤ} {A : ℕ → ℤ} (hA : ∀ i < n, D' * Sz (Q i) = A i * Dz (Q i)) :
    Dz (cat Q n) ∣ T (2 : ℤ) 3 Q A n := by
  have hS := TwoBackground.dvd_S_of_rotated h hw
  have hc := TwoBackground.isCoprime_six hne hE
  have hk := key_identity (2 : ℤ) 3 Q hn hA
  have : Dz (cat Q n) ∣ 2 ^ (Q 0).sum * 3 ^ 0 * T (2 : ℤ) 3 Q A n := by
    have e : (2 : ℤ) ^ (Q 0).sum * 3 ^ 0 * T (2 : ℤ) 3 Q A n =
        D' * Sz (cat Q n) - A 0 * Dz (cat Q n) := by
      rw [Sz, hk, Dz]; ring
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right hS _) (dvd_mul_left _ _)
  exact CocycleCombine.dvd_of_isCoprime_six_of_dvd hc _ _ this

/-! ## Rotations -/

lemma cat_front (Q : ℕ → Word) (n : ℕ) : cat Q (n + 1) = Q 0 ++ cat (fun k => Q (k + 1)) n := by
  induction n with
  | zero => simp [cat]
  | succ n ih => rw [cat_succ, ih, cat_succ, List.append_assoc]

lemma rot_step (Q : ℕ → Word) {m : ℕ} (hm : 1 ≤ m) (hQ : ∀ i, Q (i + m) = Q i) (R : ℕ) :
    cat (fun k => Q (R + 1 + k)) m ~r cat (fun k => Q (R + k)) m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [cat_front (fun k => Q (R + k)), cat_succ (fun k => Q (R + 1 + k))]
  have e1 : cat (fun k => Q (R + 1 + k)) m' = cat (fun k => Q (R + (k + 1))) m' := by
    congr 1; funext k; congr 1; omega
  have e2 : Q (R + 1 + m') = Q (R + 0) := by
    rw [show R + 1 + m' = R + (m' + 1) by omega, hQ, add_zero]
  rw [e1, e2]
  exact List.isRotated_append

/-- Every rotation by whole blocks of a periodic block word is a rotation of the word. -/
lemma rot_cat (Q : ℕ → Word) {m : ℕ} (hm : 1 ≤ m) (hQ : ∀ i, Q (i + m) = Q i) (R : ℕ) :
    cat (fun k => Q (R + k)) m ~r cat Q m := by
  induction R with
  | zero => simp only [zero_add]; exact List.IsRotated.refl _
  | succ R ih => exact (rot_step Q hm hQ R).trans ih

/-! ## Sizes -/

/-- `2^α 3^β = 2^{α + β log₂ 3}`. -/
lemma two_three_rpow (α β : ℕ) :
    ((2 : ℝ) ^ α * 3 ^ β) = (2 : ℝ) ^ ((α : ℝ) + β * Real.logb 2 3) := by
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast, mul_comm (β : ℝ),
    Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
    Real.rpow_natCast]

lemma sum_shift (g : ℕ → ℝ) (R a b : ℕ) :
    ∑ k ∈ Ico a b, g (R + k) = ∑ i ∈ Ico (R + a) (R + b), g i := by
  have := Finset.sum_Ico_add' g a b R
  simp only [add_comm _ R] at this
  exact this

/-- **End to end.** For an `m`-periodic family of positive nonempty blocks `Q`, a cycle whose gap word is
a rotation of `cat Q m`, integers `D', A_i` (`m`-periodic) with `D'·S(Q_i) = A_i·D(Q_i)` and
`|A_i - A_{i+1}| ≤ 2^K`, every rotated `T` nonzero, and a lower bound `|D| ≥ 2^{θ M - L}` with
`M = max(E, o log₂ 3)`: `(θ - c_m)·M ≤ K + L + log₂ m`. -/
theorem mruns_bounded {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {Q : ℕ → Word} {m : ℕ} (hm : 1 ≤ m)
    (hQ : ∀ i, Q (i + m) = Q i) (hpos : ∀ i, (Q i).Pos) (hne : ∀ i, Q i ≠ [])
    (hrot : gapWord x o ~r cat Q m)
    {D' : ℤ} {A : ℕ → ℤ} (hA : ∀ i, D' * Sz (Q i) = A i * Dz (Q i)) (hAper : ∀ i, A (i + m) = A i)
    {K : ℕ} (hK : ∀ i, |A i - A (i + 1)| ≤ 2 ^ K)
    (hT : ∀ R, T (2 : ℤ) 3 (fun k => Q (R + k)) (fun k => A (R + k)) m ≠ 0)
    {θ L : ℝ}
    (hLB : (2 : ℝ) ^ (θ * max ((cat Q m).sum : ℝ) (Real.logb 2 3 * (cat Q m).length) - L) ≤
      |((Dz (cat Q m) : ℤ) : ℝ)|) :
    (θ - (1 - 1 / Reach.σ (Real.logb 2 3) m)) *
        max ((cat Q m).sum : ℝ) (Real.logb 2 3 * (cat Q m).length) ≤ K + L + Real.logb 2 m := by
  set lam := Real.logb 2 3 with hlam_def
  have hlam : 1 ≤ lam := by
    rw [hlam_def, Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]; norm_num
  -- the size profile
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
  -- `X = E`, `Y = λ o`
  have hX : Reach.P xs m = ((cat Q m).sum : ℝ) := by
    simp only [Reach.P, xs, cat_sum, Es]; push_cast; rw [range_eq_Ico]
  have hY : Reach.P ys m = lam * (cat Q m).length := by
    simp only [Reach.P, ys, cat_length, Os]; push_cast; rw [range_eq_Ico, mul_sum]
  rw [hX, hY] at hR
  set Mx := max ((cat Q m).sum : ℝ) (lam * (cat Q m).length)
  set c := 1 - 1 / Reach.σ lam m
  -- the rotated word and its divisibility
  set Q' : ℕ → Word := fun k => Q (R + k)
  set A' : ℕ → ℤ := fun k => A (R + k)
  have hrot' : gapWord x o ~r cat Q' m := hrot.trans (rot_cat Q hm hQ R).symm
  have hDeq : Dz (cat Q' m) = Dz (cat Q m) := by
    simp only [Dz, D]
    rw [(rot_cat Q hm hQ R).perm.sum_eq, (rot_cat Q hm hQ R).perm.length_eq]
  have hsum_pos : 1 ≤ (cat Q m).sum := by
    rw [cat_sum, Es]
    have h0 := hne 0; have hp0 := hpos 0
    have : 1 ≤ (Q 0).sum := by
      have := CycleLiterature.length_le_sum hp0; have := List.length_pos_of_ne_nil h0; omega
    calc 1 ≤ (Q 0).sum := this
      _ ≤ ∑ i ∈ Ico 0 m, (Q i).sum :=
          single_le_sum (f := fun i => (Q i).sum) (fun i _ => Nat.zero_le _) (by simp; omega)
  have hne' : cat Q' m ≠ [] := by
    intro h0; have := congrArg List.sum h0
    rw [(rot_cat Q hm hQ R).perm.sum_eq] at this; simp at this; omega
  have hE' : (cat Q' m).sum ≠ 0 := by rw [(rot_cat Q hm hQ R).perm.sum_eq]; omega
  have hdvd := dvd_T h hm hrot' hne' hE' (D' := D') (A := A') (fun i _ => hA (R + i))
  rw [hDeq] at hdvd
  have hTne := hT R
  have hDle : |(Dz (cat Q m) : ℝ)| ≤ |((T (2 : ℤ) 3 Q' A' m : ℤ) : ℝ)| := by
    have := Int.le_of_dvd (abs_pos.2 hTne) ((abs_dvd_abs _ _).2 hdvd)
    exact_mod_cast this
  -- bound `|T|` by `m·2^K·2^{cM}`
  have hTle : |((T (2 : ℤ) 3 Q' A' m : ℤ) : ℝ)| ≤ m * (2 ^ K * (2 : ℝ) ^ (c * Mx)) := by
    rw [T]; push_cast
    calc |∑ j ∈ Ico 1 (m + 1), ((A' (j - 1) : ℝ) - A' (j % m)) * (2 ^ Es Q' 1 j * 3 ^ Os Q' j m)|
        ≤ ∑ j ∈ Ico 1 (m + 1), |((A' (j - 1) : ℝ) - A' (j % m)) * (2 ^ Es Q' 1 j * 3 ^ Os Q' j m)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Ico 1 (m + 1), (2 ^ K * (2 : ℝ) ^ (c * Mx)) := by
          refine sum_le_sum (fun j hj => ?_)
          rw [mem_Ico] at hj
          rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ Es Q' 1 j * 3 ^ Os Q' j m)]
          apply mul_le_mul _ _ (by positivity) (by positivity)
          · -- the coefficient
            have hc : A' (j % m) = A (R + (j - 1) + 1) := by
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
          · -- the monomial is `2^{f_R(j-1)} ≤ 2^{cM}`
            rw [two_three_rpow]
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
  -- combine with the lower bound
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hchain : (2 : ℝ) ^ (θ * Mx - L) ≤ (2 : ℝ) ^ (Real.logb 2 m + K + c * Mx) := by
    calc (2 : ℝ) ^ (θ * Mx - L) ≤ m * (2 ^ K * (2 : ℝ) ^ (c * Mx)) := hLB.trans (hDle.trans hTle)
      _ = (2 : ℝ) ^ (Real.logb 2 m + K + c * Mx) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
            Real.rpow_logb (by norm_num) (by norm_num) hm0, Real.rpow_natCast]; ring
  have := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).1 hchain
  linarith

/-! ## The coefficients exist -/

/-- For `m`-periodic blocks `p` and exponents `a`, `D' = Π_{k<m} D(p_k)` and
`A_i = S(p_i)·Π_{k<m, k ≠ i mod m} D(p_k)` satisfy `D'·S(p_i^{a_i}) = A_i·D(p_i^{a_i})` and are periodic. -/
theorem exists_coeffs {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m) (hp : ∀ i, p (i + m) = p i)
    (ha : ∀ i, a (i + m) = a i) :
    ∃ (D' : ℤ) (A : ℕ → ℤ), (∀ i, D' * Sz (TwoBackground.bpow (p i) (a i)) =
      A i * Dz (TwoBackground.bpow (p i) (a i))) ∧
      ∀ i, A (i + m) = A i := by
  have hpm : ∀ i, p i = p (i % m) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rcases Nat.lt_or_ge i m with hi | hi
      · rw [Nat.mod_eq_of_lt hi]
      · have := ih (i - m) (by omega)
        rw [show i = (i - m) + m by omega, hp, this, Nat.add_mod_right]
  refine ⟨∏ k ∈ range m, D (2 : ℤ) 3 (p k),
    fun i => S (2 : ℤ) 3 (p i) * ∏ k ∈ (range m).erase (i % m), D (2 : ℤ) 3 (p k), fun i => ?_, fun i => ?_⟩
  · have hmem : i % m ∈ range m := mem_range.2 (Nat.mod_lt _ (by omega))
    rw [← mul_prod_erase _ _ hmem, ← hpm i]
    have := TwoBackground.D_mul_S_bpow (2 : ℤ) 3 (p i) (a i)
    simp only [Sz, Dz] at this ⊢
    linear_combination (∏ k ∈ (range m).erase (i % m), D (2 : ℤ) 3 (p k)) * this
  · simp only [hp, Nat.add_mod_right]

/-! ## Ellison as an exponential separation -/

/-- `2^E e^{-E/10} = 2^{θ_E E}` with `θ_E = 1 - 1/(10 ln 2)`. -/
lemma ellison_rpow (E : ℕ) :
    (2 : ℝ) ^ E * Real.exp (-(E : ℝ) / 10) = (2 : ℝ) ^ ((1 - 1 / (10 * Real.log 2)) * E) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos (by norm_num), ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num),
    ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **Ellison, as a separation.** For `E` outside Ellison's exceptions and `o ≥ 1`,
`|2^E - 3^o| ≥ 2^{θ_E·max(E, o log₂ 3) - 1}`. -/
theorem ellison_lower (hEl : CycleLiterature.Ellison1971) {E o : ℕ} (hE : 0 < E) (ho : 0 < o)
    (hx : E ∉ CycleLiterature.ellisonExceptions) :
    (2 : ℝ) ^ ((1 - 1 / (10 * Real.log 2)) * max (E : ℝ) (Real.logb 2 3 * o) - 1) ≤
      |(2 : ℝ) ^ E - 3 ^ o| := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' := Real.log_two_gt_d9
  set θ := 1 - 1 / (10 * Real.log 2)
  have hθ1 : θ ≤ 1 := by have : 0 < 1 / (10 * Real.log 2) := by positivity
                         linarith
  have hθ0 : 0 ≤ θ := by
    have : 1 / (10 * Real.log 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  -- `3^o = 2^{λ o}`
  have h3 : (3 : ℝ) ^ o = (2 : ℝ) ^ (Real.logb 2 3 * o) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
      Real.rpow_natCast]
  have h2 : (2 : ℝ) ^ E = (2 : ℝ) ^ (E : ℝ) := (Real.rpow_natCast 2 E).symm
  set lo := Real.logb 2 3 * o
  have mono : ∀ a b : ℝ, a ≤ b → (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
    fun a b hab => Real.rpow_le_rpow_of_exponent_le (by norm_num) hab
  by_cases A : 2 * (3 : ℝ) ^ o ≤ 2 ^ E
  · -- `D ≥ 2^{E-1}` and `max = E`
    have hlo : lo ≤ E := by
      have : (2 : ℝ) ^ lo ≤ 2 ^ (E : ℝ) := by rw [← h3, ← h2]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 3) o]
      exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 this
    rw [max_eq_left hlo, abs_of_pos (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 3) o])]
    calc (2 : ℝ) ^ (θ * E - 1) ≤ (2 : ℝ) ^ ((E : ℝ) - 1) := mono _ _ (by nlinarith)
      _ = 2 ^ E / 2 := by rw [Real.rpow_sub (by norm_num), Real.rpow_one, ← h2]
      _ ≤ 2 ^ E - 3 ^ o := by linarith
  by_cases B : 2 * (2 : ℝ) ^ E ≤ 3 ^ o
  · have hlo : (E : ℝ) ≤ lo := by
      have : (2 : ℝ) ^ (E : ℝ) ≤ 2 ^ lo := by rw [← h3, ← h2]; nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) E]
      exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 this
    rw [max_eq_right hlo, abs_of_neg (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) E])]
    have hlo0 : 0 ≤ lo := mul_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (Nat.cast_nonneg o)
    calc (2 : ℝ) ^ (θ * lo - 1) ≤ (2 : ℝ) ^ (lo - 1) := mono _ _ (by nlinarith)
      _ = 3 ^ o / 2 := by rw [Real.rpow_sub (by norm_num), Real.rpow_one, ← h3]
      _ ≤ -(2 ^ E - 3 ^ o) := by linarith
  -- near-critical: Ellison
  push_neg at A B
  have hlo : lo < E + 1 := by
    have : (2 : ℝ) ^ lo < 2 ^ ((E : ℝ) + 1) := by
      rw [← h3, Real.rpow_add (by norm_num), Real.rpow_one, ← h2]; linarith
    exact (Real.rpow_lt_rpow_left_iff (by norm_num)).1 this
  have hEll := hEl E o hE ho hx
  rw [ellison_rpow] at hEll
  refine le_trans (mono _ _ ?_) hEll.le
  rcases le_total (E : ℝ) lo with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

/-- **Every `m ≤ 3`, any blocks, given Ellison.** Under the hypotheses of `mruns_bounded` with Ellison's
separation, `(θ_E - c_3)·max(E, o log₂3) ≤ K + 1 + log₂ 3` and `θ_E - c_3 > 0`. -/
theorem mruns_ellison (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    {Q : ℕ → Word} {m : ℕ} (hm : 1 ≤ m) (hm3 : m ≤ 3)
    (hQ : ∀ i, Q (i + m) = Q i) (hpos : ∀ i, (Q i).Pos) (hne : ∀ i, Q i ≠ [])
    (hrot : gapWord x o ~r cat Q m)
    {D' : ℤ} {A : ℕ → ℤ} (hA : ∀ i, D' * Sz (Q i) = A i * Dz (Q i)) (hAper : ∀ i, A (i + m) = A i)
    {K : ℕ} (hK : ∀ i, |A i - A (i + 1)| ≤ 2 ^ K)
    (hT : ∀ R, T (2 : ℤ) 3 (fun k => Q (R + k)) (fun k => A (R + k)) m ≠ 0)
    (hx : (cat Q m).sum ∉ CycleLiterature.ellisonExceptions) :
    0 < (1 - 1 / (10 * Real.log 2)) - (1 - 1 / Reach.σ (Real.logb 2 3) 3) ∧
      ((1 - 1 / (10 * Real.log 2)) - (1 - 1 / Reach.σ (Real.logb 2 3) 3)) *
        max ((cat Q m).sum : ℝ) (Real.logb 2 3 * (cat Q m).length) ≤ K + 1 + Real.logb 2 3 := by
  have hreach := Reach.ellison_reach
  have hlb : Real.logb 2 3 = Real.log 3 / Real.log 2 := rfl
  rw [← hlb] at hreach
  have hpos3 : 0 < (1 - 1 / (10 * Real.log 2)) - (1 - 1 / Reach.σ (Real.logb 2 3) 3) := by
    linarith [hreach.1]
  refine ⟨hpos3, ?_⟩
  -- the cycle's `E`, `o`
  have hsum_pos : 0 < (cat Q m).sum := by
    rw [cat_sum, Es]
    have : 1 ≤ (Q 0).sum := by
      have := CycleLiterature.length_le_sum (hpos 0); have := List.length_pos_of_ne_nil (hne 0); omega
    have h1 : (Q 0).sum ≤ ∑ i ∈ Ico 0 m, (Q i).sum :=
      single_le_sum (f := fun i => (Q i).sum) (fun i _ => Nat.zero_le _) (by simp; omega)
    omega
  have hlen_pos : 0 < (cat Q m).length := by
    rw [cat_length, Os]
    have h1 : (Q 0).length ≤ ∑ i ∈ Ico 0 m, (Q i).length :=
      single_le_sum (f := fun i => (Q i).length) (fun i _ => Nat.zero_le _) (by simp; omega)
    have := List.length_pos_of_ne_nil (hne 0)
    omega
  have hLB := ellison_lower hEl hsum_pos hlen_pos hx
  have hLB' : (2 : ℝ) ^ ((1 - 1 / (10 * Real.log 2)) *
      max ((cat Q m).sum : ℝ) (Real.logb 2 3 * (cat Q m).length) - 1) ≤ |((Dz (cat Q m) : ℤ) : ℝ)| := by
    have e : ((Dz (cat Q m) : ℤ) : ℝ) = (2 : ℝ) ^ (cat Q m).sum - 3 ^ (cat Q m).length := by
      simp [Dz, D]
    rw [e]; exact hLB
  have hb := mruns_bounded h hm hQ hpos hne hrot hA hAper hK hT hLB'
  -- `c_m ≤ c_3`, `log₂ m ≤ log₂ 3`
  have hσ : Reach.σ (Real.logb 2 3) m ≤ Reach.σ (Real.logb 2 3) 3 := by
    unfold Reach.σ
    exact sum_le_sum_of_subset_of_nonneg (range_mono hm3) (fun i _ _ => by
      have : (0 : ℝ) ≤ Real.logb 2 3 := Real.logb_nonneg (by norm_num) (by norm_num)
      positivity)
  have hlam1 : 1 ≤ Real.logb 2 3 := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]; norm_num
  have hσm := Reach.σ_pos hlam1 hm
  have hcm : 1 / Reach.σ (Real.logb 2 3) 3 ≤ 1 / Reach.σ (Real.logb 2 3) m :=
    one_div_le_one_div_of_le hσm hσ
  have hlog : Real.logb 2 m ≤ Real.logb 2 3 :=
    Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hm) (by exact_mod_cast hm3)
  have hM0 : 0 ≤ max ((cat Q m).sum : ℝ) (Real.logb 2 3 * (cat Q m).length) :=
    le_max_of_le_left (by positivity)
  nlinarith

end Syracuse.MRuns
