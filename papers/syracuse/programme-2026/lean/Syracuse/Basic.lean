import Mathlib

/-!
# Gap words, the Syracuse cocycle `S`, and the denominator `D`

Project-wide notation, fixed in `approaches/diophantine` and `cocycle-combine/structure/structure.md`.
A *gap word* is `w = (d₀, …, d_{o-1})`, where `d_k` is the number of halvings after the `k`-th odd step.
Its prefix sums are `e_k = Σ_{i<k} d_i`, and we write `E = Σ d_i = w.sum` and `o = len w = w.length`:

  `S(w) = Σ_{k<o} X^{e_k} Y^{o-1-k}`,   `D(w) = X^E - Y^o`.

All algebra is generic in a commutative (semi)ring with two distinguished elements `X Y`. An
identity proved for arbitrary `X Y` in an arbitrary commutative ring is the same thing as an
identity in `ℤ[X,Y]`, which is what the notes call "certified as a `ℤ[X,Y]` identity". Specialising
to `(X, Y) = (2, 3)` in `ℤ` recovers the integer quantities of the cycle problem.

The recursion `S(d :: w) = Y^{len w} + X^d S(w)` is taken as the definition; `S_eq_sum` recovers the
closed sum.
-/

namespace Syracuse

/-- A gap word `(d₀, …, d_{o-1})`. Genuine Syracuse words have every `d_i ≥ 1`. -/
abbrev Word := List ℕ

/-- A word is *positive* when every gap is at least `1`, as in every genuine Syracuse word. -/
def Word.Pos (w : Word) : Prop := ∀ d ∈ w, 1 ≤ d

/-! ## The cocycle `S` -/

section Semiring

variable {R : Type*} [CommSemiring R] (X Y : R)

/-- The homogenised cocycle `S(w) = Σ_{k<o} X^{e_k} Y^{o-1-k}`, defined by the recursion
`S(d :: w) = Y^{len w} + X^d S(w)`. -/
def S : Word → R
  | [] => 0
  | d :: w => Y ^ w.length + X ^ d * S w

@[simp] lemma S_nil : S X Y [] = 0 := rfl

@[simp] lemma S_cons (d : ℕ) (w : Word) : S X Y (d :: w) = Y ^ w.length + X ^ d * S X Y w := rfl

@[simp] lemma S_singleton (d : ℕ) : S X Y [d] = 1 := by simp [S]

/-- Prefix sums `e_k = Σ_{i<k} d_i` (so `e w 0 = 0` and `e w (len w) = E`). -/
def e (w : Word) (k : ℕ) : ℕ := (w.take k).sum

@[simp] lemma e_zero (w : Word) : e w 0 = 0 := by simp [e]

@[simp] lemma e_cons_succ (d : ℕ) (w : Word) (k : ℕ) : e (d :: w) (k + 1) = d + e w k := by
  simp [e]

/-- The closed form `S(w) = Σ_{k<o} X^{e_k} Y^{o-1-k}`. -/
theorem S_eq_sum (w : Word) :
    S X Y w = ∑ k ∈ Finset.range w.length, X ^ e w k * Y ^ (w.length - 1 - k) := by
  induction w with
  | nil => simp
  | cons d w ih =>
    rw [S_cons, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [e_cons_succ, e_zero, pow_zero, one_mul, add_tsub_cancel_right, tsub_zero]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add, mul_assoc]
    congr 3
    omega

/-- **Concatenation cocycle.** `S(uv) = Y^{len v} S(u) + X^{|u|} S(v)`. -/
theorem S_append (u v : Word) :
    S X Y (u ++ v) = Y ^ v.length * S X Y u + X ^ u.sum * S X Y v := by
  induction u with
  | nil => simp
  | cons d u ih =>
    simp only [List.cons_append, S_cons, List.length_append, ih, List.sum_cons, pow_add]
    ring

/-! ## The transfer-matrix representation

`structure.md` C1/C2: `M(d) = !![Y, 0; 1, X^d]` and `M(w) = ∏ M(d_k) = !![Y^o, 0; S(w), X^E]`. -/

/-- The transfer matrix of one gap `d`. -/
def M (d : ℕ) : Matrix (Fin 2) (Fin 2) R := !![Y, 0; 1, X ^ d]

/-- The transfer matrix of a word is the ordered product of its letters' matrices. -/
def Mw (w : Word) : Matrix (Fin 2) (Fin 2) R := (w.map (M X Y)).prod

/-- **C1/C2.** The word matrix is `!![Y^o, 0; S(w), X^E]`: `S` is its off-diagonal entry. -/
theorem Mw_eq (w : Word) : Mw X Y w = !![Y ^ w.length, 0; S X Y w, X ^ w.sum] := by
  induction w with
  | nil =>
    simp only [Mw, List.map_nil, List.prod_nil, List.length_nil, pow_zero, S_nil, List.sum_nil]
    exact Matrix.one_fin_two
  | cons d w ih =>
    simp only [Mw] at ih ⊢
    rw [List.map_cons, List.prod_cons, ih, M, Matrix.mul_fin_two]
    simp only [List.length_cons, List.sum_cons, S_cons, pow_succ, pow_add]
    congr 1
    simp
    ring

/-- `Mw` is a monoid homomorphism from the free monoid of gap words. -/
theorem Mw_append (u v : Word) : Mw X Y (u ++ v) = Mw X Y u * Mw X Y v := by
  simp [Mw, List.map_append, List.prod_append]

/-! ## Orbits along a word

`Follows X Y w a b` says that the affine recurrence `X^{d_k} a_{k+1} = Y a_k + 1` carries
`a₀ = a` to `a_o = b` along the gaps of `w`. At `(X, Y) = (2, 3)` this is the accelerated
Syracuse step `a_{k+1} = (3 a_k + 1) / 2^{d_k}`. Nothing here assumes oddness or positivity, so
the same statement serves over `ℤ`, `ℚ` and `ℤ₂`. -/

/-- `Follows X Y w a b`: the orbit of `a` along the gaps of `w` ends at `b`. -/
inductive Follows : Word → R → R → Prop
  | nil (a : R) : Follows [] a a
  | cons {d : ℕ} {w : Word} {a a' b : R} :
      X ^ d * a' = Y * a + 1 → Follows w a' b → Follows (d :: w) a b

variable {X Y}

theorem Follows.append {u v : Word} {a b c : R} (hu : Follows X Y u a b) (hv : Follows X Y v b c) :
    Follows X Y (u ++ v) a c := by
  induction hu with
  | nil => simpa using hv
  | cons h _ ih => exact Follows.cons h (ih hv)

theorem Follows.of_append {u v : Word} {a c : R} (h : Follows X Y (u ++ v) a c) :
    ∃ b, Follows X Y u a b ∧ Follows X Y v b c := by
  induction u generalizing a with
  | nil => exact ⟨a, Follows.nil a, by simpa using h⟩
  | cons d u ih =>
    cases h with
    | cons hstep hrest =>
      obtain ⟨b, hub, hvb⟩ := ih hrest
      exact ⟨b, Follows.cons hstep hub, hvb⟩

/-- **The Diophantine closed form** (`approaches/diophantine`):
`X^{e_o} a_o = Y^o a₀ + S(w)`, i.e. `2^{e_o} a_o - 3^o a₀ = Σ_k 2^{e_k} 3^{o-1-k}` at `(2,3)`.
It is purely algebraic: it uses only the recurrence. -/
theorem Follows.closed_form {w : Word} {a b : R} (h : Follows X Y w a b) :
    X ^ w.sum * b = Y ^ w.length * a + S X Y w := by
  induction h with
  | nil => simp
  | @cons d w a a' b hstep _ ih =>
    simp only [List.sum_cons, List.length_cons, S_cons, pow_add, pow_succ]
    calc X ^ d * X ^ w.sum * b = X ^ d * (X ^ w.sum * b) := by ring
      _ = X ^ d * (Y ^ w.length * a' + S X Y w) := by rw [ih]
      _ = Y ^ w.length * (X ^ d * a') + X ^ d * S X Y w := by ring
      _ = Y ^ w.length * (Y * a + 1) + X ^ d * S X Y w := by rw [hstep]
      _ = Y ^ w.length * Y * a + (Y ^ w.length + X ^ d * S X Y w) := by ring

/-- Along a closed orbit, every rotation of the word is again a closed orbit. -/
theorem Follows.rotate {w : Word} {a : R} (h : Follows X Y w a a) (j : ℕ) :
    ∃ b, Follows X Y (w.rotate j) b b := by
  rw [List.rotate_eq_drop_append_take_mod]
  rw [← List.take_append_drop (j % w.length) w] at h
  obtain ⟨b, h1, h2⟩ := h.of_append
  exact ⟨b, h2.append h1⟩

end Semiring

/-! ## The denominator `D` and rotations -/

section Ring

variable {R : Type*} [CommRing R] (X Y : R)

/-- The cycle denominator `D(w) = X^E - Y^o`. -/
def D (w : Word) : R := X ^ w.sum - Y ^ w.length

@[simp] lemma D_nil : D X Y [] = 0 := by simp [D]

/-- `D` obeys the same concatenation law as `S` (Trümper). -/
theorem D_append (u v : Word) :
    D X Y (u ++ v) = Y ^ v.length * D X Y u + X ^ u.sum * D X Y v := by
  simp only [D, List.sum_append, List.length_append, pow_add]
  ring

/-- `D` is invariant under rotation: rotation preserves `(E, o)`. -/
@[simp] theorem D_rotate (w : Word) (j : ℕ) : D X Y (w.rotate j) = D X Y w := by
  simp [D, (List.rotate_perm w j).sum_eq]

/-- **Rotation recursion** (`cycle-gcd`): for `w = d :: w'` and its left rotation `w' ++ [d]`,
`X^d S(rot w) = Y S(w) + D(w)`. Holds in `ℤ[X,Y]` for every word. -/
theorem rotation_recursion (d : ℕ) (w : Word) :
    X ^ d * S X Y (w ++ [d]) = Y * S X Y (d :: w) + D X Y (d :: w) := by
  rw [S_append, S_singleton, S_cons, D]
  simp only [List.length_nil, List.sum_cons, List.length_cons, pow_add,
    pow_succ, pow_zero]
  ring

/-- `rotate 1` of a nonempty word moves its first gap to the end. -/
lemma rotate_one_cons (d : ℕ) (w : Word) : (d :: w).rotate 1 = w ++ [d] := by
  simp [List.rotate_cons_succ]

/-- **Cycle equation.** On a closed orbit `D(w) a = S(w)`. -/
theorem Follows.cycle_equation {w : Word} {a : R} (h : Follows X Y w a a) :
    D X Y w * a = S X Y w := by
  have := h.closed_form
  simp only [D, sub_mul]
  rw [this]
  ring

/-- On a closed orbit, `D(w)` divides every rotation sum `S(w.rotate j)`. -/
theorem Follows.D_dvd_S_rotate {w : Word} {a : R} (h : Follows X Y w a a) (j : ℕ) :
    D X Y w ∣ S X Y (w.rotate j) := by
  obtain ⟨b, hb⟩ := h.rotate j
  exact ⟨b, by rw [← D_rotate X Y w j, hb.cycle_equation]⟩

end Ring

/-! ## The integer specialisation `(X, Y) = (2, 3)` -/

/-- Integer rotation sum `S(w)` at `(2, 3)`. -/
abbrev Sz (w : Word) : ℤ := S (2 : ℤ) 3 w

/-- Integer denominator `D(w) = 2^E - 3^o`. -/
abbrev Dz (w : Word) : ℤ := D (2 : ℤ) 3 w

/-! ## The accelerated Syracuse map on `ℤ` -/

/-- Number of halvings after the odd step at `a`: `ν₂(3a + 1)`. -/
def gap (a : ℤ) : ℕ := padicValInt 2 (3 * a + 1)

/-- The accelerated (odd-to-odd) Syracuse map `a ↦ (3a + 1) / 2^{ν₂(3a+1)}` on `ℤ`. -/
def syr (a : ℤ) : ℤ := (3 * a + 1) / 2 ^ gap a

lemma two_pow_gap_mul_syr (a : ℤ) : 2 ^ gap a * syr a = 3 * a + 1 := by
  have h : ((2 : ℕ) : ℤ) ^ padicValInt 2 (3 * a + 1) ∣ 3 * a + 1 := padicValInt_dvd _
  push_cast at h
  rw [syr, gap, mul_comm]
  exact Int.ediv_mul_cancel h

/-- The gap word of the first `o` odd steps from `a`. -/
def gapWord (a : ℤ) : ℕ → Word
  | 0 => []
  | o + 1 => gap a :: gapWord (syr a) o

@[simp] lemma gapWord_length (a : ℤ) (o : ℕ) : (gapWord a o).length = o := by
  induction o generalizing a with
  | zero => rfl
  | succ o ih => simp [gapWord, ih]

/-- The genuine Syracuse orbit follows its own gap word at `(2, 3)`. -/
theorem follows_gapWord (a : ℤ) (o : ℕ) : Follows (2 : ℤ) 3 (gapWord a o) a (syr^[o] a) := by
  induction o generalizing a with
  | zero => exact Follows.nil a
  | succ o ih =>
    rw [Function.iterate_succ_apply]
    exact Follows.cons (two_pow_gap_mul_syr a) (ih (syr a))

/-- `3a + 1 ≠ 0` for every integer `a`. -/
lemma three_mul_add_one_ne_zero (a : ℤ) : 3 * a + 1 ≠ 0 := by omega

/-- The Syracuse map always lands on an odd integer: all factors of `2` are divided out. -/
theorem syr_odd (a : ℤ) : Odd (syr a) := by
  have hne := three_mul_add_one_ne_zero a
  rw [← Int.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  have hdvd : (2 : ℤ) ^ (gap a + 1) ∣ 3 * a + 1 := by
    rw [← two_pow_gap_mul_syr a, pow_succ]
    exact mul_dvd_mul_left _ h2
  have := (padicValInt_dvd_iff (p := 2) (gap a + 1) (3 * a + 1)).1 (by exact_mod_cast hdvd)
  rcases this with h | h
  · exact hne h
  · simp [gap] at h

/-- For odd `a`, at least one halving follows the odd step: `gap a ≥ 1`. -/
theorem one_le_gap {a : ℤ} (ha : Odd a) : 1 ≤ gap a := by
  have hne := three_mul_add_one_ne_zero a
  have h2 : ((2 : ℕ) : ℤ) ^ 1 ∣ 3 * a + 1 := by
    obtain ⟨k, rfl⟩ := ha
    exact ⟨3 * k + 2, by push_cast; ring⟩
  rcases (padicValInt_dvd_iff (p := 2) 1 (3 * a + 1)).1 h2 with h | h
  · exact absurd h hne
  · exact h

/-- The gap word of an odd start is positive. -/
theorem gapWord_pos {a : ℤ} (ha : Odd a) (o : ℕ) : (gapWord a o).Pos := by
  induction o generalizing a with
  | zero => intro d hd; simp [gapWord] at hd
  | succ o ih =>
    intro d hd
    simp only [gapWord, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact one_le_gap ha
    · exact ih (syr_odd a) d hd

/-- A Syracuse cycle of period `o ≥ 1` through the odd integer `a` (positive or negative). -/
def IsSyrCycle (a : ℤ) (o : ℕ) : Prop := 0 < o ∧ Odd a ∧ syr^[o] a = a

/-- **Cycle equation for genuine cycles.** `(2^E - 3^o) a = S(w)` for the cycle's gap word. -/
theorem IsSyrCycle.cycle_equation {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    Dz (gapWord a o) * a = Sz (gapWord a o) := by
  have hf := follows_gapWord a o
  rw [h.2.2] at hf
  exact hf.cycle_equation

/-- The trivial cycle `1 → 1` (gap word `(2)`). -/
theorem isSyrCycle_one : IsSyrCycle 1 1 := by
  refine ⟨Nat.one_pos, odd_one, ?_⟩
  have h4 : gap 1 = 2 := by
    rw [gap, show (3 : ℤ) * 1 + 1 = ((2 ^ 2 : ℕ) : ℤ) by norm_num, padicValInt.of_nat,
      padicValNat.prime_pow]
  simp only [Function.iterate_one, syr, h4]
  norm_num

/-! ## The Collatz conjecture -/

/-- The full Collatz map `n ↦ n/2` (even), `3n + 1` (odd). -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The Collatz conjecture: every positive integer reaches `1`. -/
def CollatzConjecture : Prop := ∀ n : ℕ, 0 < n → ∃ k, collatz^[k] n = 1

/-- No positive Syracuse cycle other than the trivial one `1 → 1`. -/
def NoNontrivialPositiveCycle : Prop := ∀ a : ℤ, ∀ o : ℕ, 0 < a → IsSyrCycle a o → a = 1

/-! ## The `6`-free part

The exclusion squeeze of `PROGRAM.md` lives on the 6-free axis: stripping all factors of `2` and
`3` from an integer, i.e. working up to units of `ℤ[1/6]`. -/

/-- The `6`-free part of an integer: `|n|` with all factors of `2` and `3` removed
(`sixFree 0 = 0`). -/
def sixFree (n : ℤ) : ℕ := ordCompl[3] (ordCompl[2] n.natAbs)

/-- A divisor coprime to `6` of `c` divides the `6`-free part of `c`. -/
theorem dvd_sixFree {g : ℕ} {c : ℤ} (hg : Nat.Coprime g 6) (h : (g : ℤ) ∣ c) : g ∣ sixFree c := by
  have hg2 : Nat.Coprime g 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hg
  have hg3 : Nat.Coprime g 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hg
  have h0 : g ∣ c.natAbs := Int.natCast_dvd.mp h
  have h1 : g ∣ ordCompl[2] c.natAbs := by
    have := Nat.ordProj_mul_ordCompl_eq_self c.natAbs 2
    rw [← this] at h0
    exact (Nat.Coprime.pow_right _ hg2).dvd_of_dvd_mul_left h0
  have := Nat.ordProj_mul_ordCompl_eq_self (ordCompl[2] c.natAbs) 3
  rw [← this] at h1
  exact (Nat.Coprime.pow_right _ hg3).dvd_of_dvd_mul_left h1

end Syracuse
