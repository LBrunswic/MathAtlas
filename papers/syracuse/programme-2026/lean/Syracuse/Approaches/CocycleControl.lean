import Syracuse.Basic

/-!
# Cocycle control: the range of `S(w)` at fixed `E = |w|`

Formalisation of `approaches/cocycle-control` (`RATIONALE.md`, `STATUS.md`). Notation as in
`Syracuse.Basic`: `E = w.sum` (written `|w|` in the notes), `o = w.length` (`len w`), and a word is
positive (`Word.Pos`) when every gap is `≥ 1`. Since every term of `S(w) = Σ_k 2^{e_k} 3^{o-1-k}`
is nonnegative, we work with `Sn w = S 2 3 w ∈ ℕ` and transfer to `Sz` in `ℤ` (`natCast_Sn`).

## Coverage

| Note claim | Lean name | Status |
|---|---|---|
| STATUS "observed range": `min S = 1`, attained at the word `(E)` | `one_le_Sn`, `Sn_eq_one_iff`, `isLeast_Sn` | proved (the note: "numeric, not yet proved"); the minimisers are exactly the one-letter words |
| STATUS "observed range": `max S = 3^E - 2^E = -D(1^E)`, attained at `1^E` | `Sn_add_two_pow_le`, `Sn_replicate_one`, `isGreatest_Sn`, `Sn_add_two_pow_eq_iff`, `neg_Dz_replicate_one` | proved; `1^E` is the unique maximiser |
| combined range `1 ≤ S(w) ≤ 3^E - 2^E` | `Sn_range` (`ℕ`), `Sz_range` (`ℤ`) | proved |
| STATUS "length dominates magnitude" (per-`o` bands slide right as `o` grows) | `Sn_band`, `three_pow_le_Sn_add`, `Sn_minWord`, `Sn_add_two_pow_le_band`, `Sn_maxWord`, `band_lower_strictMono`, `band_upper_lt` | proved in precise form: at fixed `(E, o)`, `3^o - 2^o ≤ S ≤ 3^{o-1} + 2^{E-o+1} (3^{o-1} - 2^{o-1})`; both edges are attained and strictly increase with `o` |
| strict dominance (every length-`o` word below every length-`(o+1)` word) | `length_not_dominant` | false: at `E = 20`, `S(19, 1) = 524291 > 19 = S(1, 1, 18)`; the bands overlap |
| sub-goal 2: moving one unit of gap to an earlier letter increases `S` | `Sn_transfer_lt` | proved (strictly; positivity not needed) |
| sub-goal 3: `S` monotone for the componentwise order on prefix sums | `Sn_le_of_e_le` | proved; the lattice structure itself is not formalized |
| CDF sweeps, rotation-range `R` tables, `TOP_*` / `BOTTOM_*` extremes | — | empirical, not formalized |
-/

namespace Syracuse.CocycleControl

/-- `S(w)` at `(X, Y) = (2, 3)` in `ℕ` (all terms are nonnegative, so `ℕ` is the natural home). -/
abbrev Sn (w : Word) : ℕ := S (2 : ℕ) 3 w

/-- The natural-number `S` cast to `ℤ` is `Sz`. -/
theorem natCast_Sn (w : Word) : ((Sn w : ℕ) : ℤ) = Sz w := by
  induction w with
  | nil => simp
  | cons d w ih => simp [Sn, Sz] at ih ⊢; rw [ih]

/-- A positive word has at most as many letters as its gap-sum: `o ≤ E`. -/
theorem length_le_sum {w : Word} (hw : w.Pos) : w.length ≤ w.sum := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have hd := hw d List.mem_cons_self
    have := ih fun x hx => hw x (List.mem_cons_of_mem d hx)
    simp only [List.length_cons, List.sum_cons]
    omega

/-- `1 + 2^d ≤ 3^d` for `d ≥ 1`. -/
lemma one_add_two_pow_le_three_pow {d : ℕ} (hd : 1 ≤ d) : 1 + 2 ^ d ≤ 3 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih => rw [pow_succ, pow_succ]; omega

/-- `1 + 2^d < 3^d` for `d ≥ 2`. -/
lemma one_add_two_pow_lt_three_pow {d : ℕ} (hd : 2 ≤ d) : 1 + 2 ^ d < 3 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih => rw [pow_succ, pow_succ]; omega

/-! ## The global range at fixed `E` -/

/-- `S(w) ≥ 1` for every nonempty word. -/
theorem one_le_Sn {w : Word} (hne : w ≠ []) : 1 ≤ Sn w := by
  obtain ⟨d, w, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [Sn, S_cons]
  have := Nat.one_le_pow w.length 3 (by norm_num)
  omega

/-- `S(w) = 1` exactly for one-letter words (for positive words with `E` fixed: the word `(E)`). -/
theorem Sn_eq_one_iff (w : Word) : Sn w = 1 ↔ w.length = 1 := by
  match w with
  | [] => simp [Sn]
  | [d] => simp [Sn]
  | d :: d' :: w =>
    simp only [Sn, S_cons, List.length_cons]
    have h3 : 3 ≤ 3 ^ (w.length + 1) := Nat.le_self_pow (by omega) 3
    have h1 : 1 ≤ 2 ^ d * (3 ^ w.length + 2 ^ d' * S 2 3 w) :=
      Nat.one_le_iff_ne_zero.2 (mul_ne_zero (by positivity) (by positivity))
    omega

/-- **Upper bound.** For a positive word, `S(w) + 2^E ≤ 3^E`, i.e. `S(w) ≤ 3^E - 2^E`. -/
theorem Sn_add_two_pow_le {w : Word} (hw : w.Pos) : Sn w + 2 ^ w.sum ≤ 3 ^ w.sum := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have hd := hw d List.mem_cons_self
    have hw' : Word.Pos w := fun x hx => hw x (List.mem_cons_of_mem d hx)
    have ih := ih hw'
    have hlen : 3 ^ w.length ≤ 3 ^ w.sum := Nat.pow_le_pow_right (by norm_num) (length_le_sum hw')
    have h13 := one_add_two_pow_le_three_pow hd
    simp only [Sn, S_cons, List.sum_cons, pow_add] at ih ⊢
    calc 3 ^ w.length + 2 ^ d * S 2 3 w + 2 ^ d * 2 ^ w.sum
        = 3 ^ w.length + 2 ^ d * (S 2 3 w + 2 ^ w.sum) := by ring
      _ ≤ 3 ^ w.sum + 2 ^ d * 3 ^ w.sum := add_le_add hlen (Nat.mul_le_mul_left _ ih)
      _ = (1 + 2 ^ d) * 3 ^ w.sum := by ring
      _ ≤ 3 ^ d * 3 ^ w.sum := Nat.mul_le_mul_right _ h13

/-- The all-ones circuit word `1^E` has `S + 2^E = 3^E`, i.e. `S(1^E) = 3^E - 2^E = |D(1^E)|`. -/
theorem Sn_replicate_one (E : ℕ) : Sn (List.replicate E 1) + 2 ^ E = 3 ^ E := by
  induction E with
  | zero => simp [Sn]
  | succ E ih =>
    simp only [Sn, List.replicate_succ, S_cons, List.length_replicate] at ih ⊢
    rw [pow_succ, pow_succ, pow_succ]
    linarith

/-- **The maximiser is unique.** For a positive word, `S(w) = 3^E - 2^E` iff `w = 1^E`. -/
theorem Sn_add_two_pow_eq_iff {w : Word} (hw : w.Pos) :
    Sn w + 2 ^ w.sum = 3 ^ w.sum ↔ w = List.replicate w.sum 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  swap
  · rw [h, List.sum_replicate, smul_eq_mul, mul_one]
    exact Sn_replicate_one _
  induction w with
  | nil => rfl
  | cons d w ih =>
    have hd := hw d List.mem_cons_self
    have hw' : Word.Pos w := fun x hx => hw x (List.mem_cons_of_mem d hx)
    have hle := Sn_add_two_pow_le hw'
    have hlen : 3 ^ w.length ≤ 3 ^ w.sum := Nat.pow_le_pow_right (by norm_num) (length_le_sum hw')
    have h13 := one_add_two_pow_le_three_pow hd
    have hP : 0 < 2 ^ d := by positivity
    have hA : 0 < 3 ^ w.sum := by positivity
    simp only [Sn, S_cons, List.sum_cons, pow_add] at h hle
    -- write `X = S w + 2^{E'}`, `A' = 3^{E'}`
    set X := S 2 3 w + 2 ^ w.sum with hX
    have h' : 3 ^ w.length + 2 ^ d * X = 3 ^ d * 3 ^ w.sum := by rw [hX]; linarith
    have hXeq : X = 3 ^ w.sum := by
      by_contra hne
      have hlt : X < 3 ^ w.sum := lt_of_le_of_ne hle hne
      have : 2 ^ d * X < 2 ^ d * 3 ^ w.sum := Nat.mul_lt_mul_of_pos_left hlt hP
      have : (1 + 2 ^ d) * 3 ^ w.sum ≤ 3 ^ d * 3 ^ w.sum := Nat.mul_le_mul_right _ h13
      nlinarith
    have hd1 : d = 1 := by
      by_contra hne
      have h2 : 1 + 2 ^ d < 3 ^ d := one_add_two_pow_lt_three_pow (by omega)
      have : (1 + 2 ^ d) * 3 ^ w.sum < 3 ^ d * 3 ^ w.sum := Nat.mul_lt_mul_of_pos_right h2 hA
      rw [hXeq] at h'
      nlinarith
    have hrec := ih hw' (by simpa [Sn, hX] using hXeq)
    rw [hd1, List.sum_cons, Nat.add_comm, List.replicate_succ, ← hrec]

/-- **Range of `S` at fixed `E` (cocycle-control STATUS, "observed range", now proved).** For every
nonempty positive word, `1 ≤ S(w) ≤ 3^E - 2^E`. -/
theorem Sn_range {w : Word} (hw : w.Pos) (hne : w ≠ []) :
    1 ≤ Sn w ∧ Sn w ≤ 3 ^ w.sum - 2 ^ w.sum :=
  ⟨one_le_Sn hne, Nat.le_sub_of_add_le (Sn_add_two_pow_le hw)⟩

/-- **The minimum `1` is attained exactly by the one-letter word `(E)`** (among positive words with
gap-sum `E ≥ 1`). -/
theorem isLeast_Sn {E : ℕ} (hE : 1 ≤ E) :
    IsLeast {s | ∃ w : Word, w.Pos ∧ w ≠ [] ∧ w.sum = E ∧ Sn w = s} 1 :=
  ⟨⟨[E], by simpa [Word.Pos] using hE, by simp, by simp, by simp [Sn]⟩,
    fun _ ⟨_, _, hne, _, hs⟩ => hs ▸ one_le_Sn hne⟩

/-- **The maximum `3^E - 2^E` is attained by the circuit word `1^E`.** -/
theorem isGreatest_Sn (E : ℕ) :
    IsGreatest {s | ∃ w : Word, w.Pos ∧ w.sum = E ∧ Sn w = s} (3 ^ E - 2 ^ E) := by
  refine ⟨⟨List.replicate E 1, fun x hx => by simp [List.eq_of_mem_replicate hx], by simp,
    by have := Sn_replicate_one E; omega⟩, ?_⟩
  rintro _ ⟨w, hw, rfl, rfl⟩
  exact Nat.le_sub_of_add_le (Sn_add_two_pow_le hw)

/-- **Integer form.** `1 ≤ S(w) ≤ 3^E - 2^E = -D(1^E)` for nonempty positive words. -/
theorem Sz_range {w : Word} (hw : w.Pos) (hne : w ≠ []) :
    1 ≤ Sz w ∧ Sz w ≤ 3 ^ w.sum - 2 ^ w.sum := by
  rw [← natCast_Sn]
  have h1 := one_le_Sn hne
  have h2 := Sn_add_two_pow_le hw
  constructor
  · exact_mod_cast h1
  · have : ((Sn w + 2 ^ w.sum : ℕ) : ℤ) ≤ ((3 ^ w.sum : ℕ) : ℤ) := by exact_mod_cast h2
    push_cast at this
    linarith

/-- The maximum `3^E - 2^E` is `|D(1^E)| = -D(1^E)`. -/
theorem neg_Dz_replicate_one (E : ℕ) : -Dz (List.replicate E 1) = 3 ^ E - 2 ^ E := by
  simp [Dz, D]


/-! ## The band at fixed `(E, o)` -/

/-- **Lower edge of the `(E, o)` band.** For a positive word of length `o`, `S(w) ≥ 3^o - 2^o`
(independently of `E`). -/
theorem three_pow_le_Sn_add {w : Word} (hw : w.Pos) : 3 ^ w.length ≤ Sn w + 2 ^ w.length := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have hd := hw d List.mem_cons_self
    have ih := ih fun x hx => hw x (List.mem_cons_of_mem d hx)
    have h2 : 2 ≤ 2 ^ d := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    simp only [Sn, S_cons, List.length_cons, pow_succ] at ih ⊢
    nlinarith

/-- The lower edge is attained by `1^{o-1} · (m)` for every last gap `m`: `S = 3^o - 2^o`. -/
theorem Sn_minWord (n m : ℕ) : Sn (List.replicate n 1 ++ [m]) + 2 ^ (n + 1) = 3 ^ (n + 1) := by
  have h := Sn_replicate_one n
  simp only [Sn, S_append, S_singleton, List.length_singleton, List.sum_replicate, smul_eq_mul,
    mul_one, pow_one] at h ⊢
  rw [pow_succ 2 n, pow_succ 3 n]
  linarith

/-- Upper edge of the `(E, o)` band, multiplied out: for a positive word `d :: w` with
`k = len w`, `(S + 2^E) · 2^k ≤ 3^k (2^k + 2^E)`. -/
theorem Sn_add_two_pow_mul_le (w : Word) :
    ∀ d, Word.Pos (d :: w) →
      (Sn (d :: w) + 2 ^ (d :: w).sum) * 2 ^ w.length ≤
        3 ^ w.length * (2 ^ w.length + 2 ^ (d :: w).sum) := by
  induction w with
  | nil => intro d _; simp [Sn, add_comm]
  | cons d' w ih =>
    intro d hw
    have hw' : Word.Pos (d' :: w) := fun x hx => hw x (List.mem_cons_of_mem d hx)
    have ih := ih d' hw'
    have hlen := length_le_sum hw'
    have hQR : 2 * 2 ^ w.length ≤ 2 ^ (d' :: w).sum := by
      rw [← pow_succ']
      exact Nat.pow_le_pow_right (by norm_num) (by simpa using hlen)
    set a := Sn (d' :: w) + 2 ^ (d' :: w).sum with ha
    have hS : Sn (d :: d' :: w) + 2 ^ (d :: d' :: w).sum = 3 ^ (w.length + 1) + 2 ^ d * a := by
      simp only [ha, Sn, S_cons, List.sum_cons, List.length_cons, pow_add]
      ring
    rw [hS, List.length_cons, List.sum_cons, pow_add 2 d, pow_succ 2 w.length,
      pow_succ 3 w.length]
    set P := 2 ^ d
    set T := 3 ^ w.length
    set Q := 2 ^ w.length
    set R := 2 ^ (d' :: w).sum
    have h1 := Nat.mul_le_mul_left (2 * P) ih
    have h2 := Nat.mul_le_mul_left (P * T) hQR
    nlinarith

/-- **Upper edge of the `(E, o)` band.** For a positive word of length `o = n + 1` and gap-sum `E`,
`S(w) + 2^E ≤ 3^n (1 + 2^{E-n})`, i.e. `S(w) ≤ 3^{o-1} + 2^{E-o+1}(3^{o-1} - 2^{o-1})`. -/
theorem Sn_add_two_pow_le_band {w : Word} (hw : w.Pos) {n : ℕ} (hn : w.length = n + 1) :
    Sn w + 2 ^ w.sum ≤ 3 ^ n + 2 ^ (w.sum - n) * 3 ^ n := by
  obtain ⟨d, w', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_eq_add_one hn)
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hn
  subst hn
  have h := Sn_add_two_pow_mul_le w' d hw
  have hle : w'.length ≤ (d :: w').sum := by have := length_le_sum hw; simp at this ⊢; omega
  have hsplit : 2 ^ (d :: w').sum = 2 ^ w'.length * 2 ^ ((d :: w').sum - w'.length) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  rw [hsplit] at h ⊢
  have hpos : 0 < 2 ^ w'.length := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc (Sn (d :: w') + 2 ^ w'.length * 2 ^ ((d :: w').sum - w'.length)) * 2 ^ w'.length
      ≤ 3 ^ w'.length * (2 ^ w'.length + 2 ^ w'.length * 2 ^ ((d :: w').sum - w'.length)) := h
    _ = (3 ^ w'.length + 2 ^ ((d :: w').sum - w'.length) * 3 ^ w'.length) * 2 ^ w'.length := by
      ring

/-- **The `(E, o)` band.** For a positive word of length `o = n + 1` and gap-sum `E`,
`3^o - 2^o ≤ S(w) ≤ 3^{o-1} + 2^{E-o+1}(3^{o-1} - 2^{o-1})` (stated additively in `ℕ`). -/
theorem Sn_band {w : Word} (hw : w.Pos) {n : ℕ} (hn : w.length = n + 1) :
    3 ^ (n + 1) ≤ Sn w + 2 ^ (n + 1) ∧ Sn w + 2 ^ w.sum ≤ 3 ^ n + 2 ^ (w.sum - n) * 3 ^ n :=
  ⟨hn ▸ three_pow_le_Sn_add hw, Sn_add_two_pow_le_band hw hn⟩

/-- The upper edge is attained by `(m+1) · 1^n` (the single big gap first). -/
theorem Sn_maxWord (n m : ℕ) :
    Sn ((m + 1) :: List.replicate n 1) + 2 ^ (m + 1 + n) = 3 ^ n + 2 ^ (m + 1) * 3 ^ n := by
  have h := Sn_replicate_one n
  simp only [Sn, S_cons, List.length_replicate] at h ⊢
  rw [pow_add, ← h]
  ring

/-- **Both band edges increase with the length** (the precise content of "length dominates
magnitude"). The lower edge `3^o - 2^o` is strictly increasing in `o`. -/
theorem band_lower_strictMono : StrictMono fun o : ℕ => 3 ^ o - 2 ^ o := by
  refine strictMono_nat_of_lt_succ fun o => ?_
  have h1 : 2 ^ o ≤ 3 ^ o := Nat.pow_le_pow_left (by norm_num) o
  have h2 : 0 < 2 ^ o := by positivity
  simp only [pow_succ]
  omega

/-- The upper edge (plus `2^E`) at length `n + 1`, `3^n (1 + 2^{m+1})` with `E = n + 1 + m`, is
strictly below the one at length `n + 2`, `3^{n+1} (1 + 2^m)`. -/
theorem band_upper_lt (n m : ℕ) : 3 ^ n + 2 ^ (m + 1) * 3 ^ n < 3 ^ (n + 1) + 2 ^ m * 3 ^ (n + 1) := by
  have h3 : 0 < 3 ^ n := by positivity
  have h2 : 0 < 2 ^ m := by positivity
  simp only [pow_succ]
  nlinarith

/-- **Strict length dominance is false.** The bands at fixed `E` overlap: at `E = 20`, the
length-`2` word `(19, 1)` has `S = 524291`, larger than `S = 19` of the length-`3` word
`(1, 1, 18)`. Only the band *edges* are monotone in `o`. -/
theorem length_not_dominant :
    Word.Pos [19, 1] ∧ Word.Pos [1, 1, 18] ∧ [19, 1].sum = 20 ∧ [1, 1, 18].sum = 20 ∧
      Sn [19, 1] = 524291 ∧ Sn [1, 1, 18] = 19 := by
  refine ⟨by simp [Word.Pos], by simp [Word.Pos], rfl, rfl, by simp [Sn], by simp [Sn]⟩

/-! ## Monotone moves and the prefix-sum order (sub-goals 2–3) -/

/-- **`S` is monotone for the componentwise order on prefix sums.** If `u`, `v` have the same length
and `e_k(u) ≤ e_k(v)` for every `k < o`, then `S(u) ≤ S(v)`. -/
theorem Sn_le_of_e_le {u v : Word} (hl : u.length = v.length)
    (he : ∀ k < u.length, e u k ≤ e v k) : Sn u ≤ Sn v := by
  simp only [Sn, S_eq_sum, hl] at he ⊢
  refine Finset.sum_le_sum fun k hk => Nat.mul_le_mul_right _ ?_
  exact Nat.pow_le_pow_right (by norm_num) (he k (Finset.mem_range.1 hk))

/-- **Monotone move (sub-goal 2).** Transferring one unit of gap from a later letter to an earlier
one (`d_i ↦ d_i + 1`, `d_j ↦ d_j - 1`, `i < j`) preserves `E` and `o` and strictly increases `S`. -/
theorem Sn_transfer_lt (u v t : Word) (a b : ℕ) :
    Sn (u ++ a :: (v ++ (b + 1) :: t)) < Sn (u ++ (a + 1) :: (v ++ b :: t)) := by
  have key : Sn ((a + 1) :: (v ++ b :: t)) =
      Sn (a :: (v ++ (b + 1) :: t)) + 2 ^ a * (3 ^ (t.length + 1) * Sn v + 2 ^ v.sum * 3 ^ t.length) := by
    simp only [Sn, S_cons, S_append, List.length_append, List.length_cons, pow_succ]
    ring
  have hlen : (a :: (v ++ (b + 1) :: t)).length = ((a + 1) :: (v ++ b :: t)).length := by simp
  simp only [Sn, S_append] at key ⊢
  rw [hlen, key]
  have : 0 < 2 ^ a * (3 ^ (t.length + 1) * S 2 3 v + 2 ^ v.sum * 3 ^ t.length) := by positivity
  have h2 : 0 < 2 ^ u.sum := by positivity
  nlinarith

end Syracuse.CocycleControl
