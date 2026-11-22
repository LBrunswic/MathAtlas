import Syracuse.Basic

/-!
# Diophantine distribution: the fundamental solution `x*_w = S(w)/D(w)`

Formalisation of `approaches/diophantine-distribution` (`RATIONALE.md`, `STATUS.md`,
`fundamental.md` FS1–FS5). Notation as in `Syracuse.Basic`: a gap word `w : Word`, `E = w.sum`
(written `|w|` in the notes), `o = w.length` (`len w`), `S(w) = S 2 3 w`, `D(w) = 2^E - 3^o`.
The accelerated step with prescribed gap is `T_d(x) = (3x + 1)/2^d`, the word map is
`F_w = T_{d_{o-1}} ∘ ⋯ ∘ T_{d_0}`, and the fundamental solution is `x*_w = Z(w) = S(w)/D(w)`
(`xstar` in a field, `xstar2` in `ℤ_[2]`). A word is positive (`Word.Pos`) when all gaps are `≥ 1`.

## Coverage

| Note claim | Lean name | Status |
|---|---|---|
| FS1: `F_w(x) = (3^o/2^E) x + S/2^E` | `F_eq` | proved (any field with `2 ≠ 0`) |
| FS1: the unique fixed point is `S/D` | `F_eq_self_iff`, `D_ne_zero` | proved |
| FS1: `D` odd, hence `x*_w ∈ ℤ_2` | `odd_Dz`, `isUnit_D_padic`, `xstar2`, `eq_xstar2_iff`, `coe_xstar2` | corrected: needs `E ≥ 1` (for `E = 0`, `D = 1 - 3^o` is even); holds for nonempty positive words |
| FS2: `x*_w ∈ ℤ` iff `D ∣ S` | `xstar_isInt_iff` | proved |
| FS2: integer cycle iff `D ∣ S` and parities consistent | `isSyrCycle_and_gapWord_iff`, `exists_cycle_iff` | proved, strengthened: for positive words parity consistency is automatic |
| FS2: examples `-1` (word `(1)`), `-7` (word `(2,1)`) | `xstar_one`, `xstar_two_one`, `isSyrCycle_neg_one`, `isSyrCycle_neg_seven` | proved |
| RATIONALE obs. 1: `Z ∘ shift = T ∘ Z` | `xstar_rotate` (field), `xstar2_rotate` (`ℤ_2`, with `ν₂(3x* + 1) = d₀` exactly), `syr_xstar_rotate` (`ℤ`) | proved, reading shift = rotation `d·w ↦ w·d` of a finite (periodic) word and `T = T_{d₀}` |
| RATIONALE obs. 1: "`S` is injective" | `Sz_one_eq_Sz_two`, `eq_of_Sz_eq` | corrected: false on all words (`S(1) = S(2) = 1`); true on each stratum of positive words with fixed `(E, o)` |
| RATIONALE obs. 1 / FS3 corollary: `Z(u) = Z(v)` ⇒ common root word | `xstar_eq_iff_common_root` (via `exists_root_of_append_comm`) | proved, both directions, nonempty positive words |
| FS3: `{x : word(x) = w, a_o odd} = x*_w + 2^{E+1} ℤ_2` | `odd_and_gapWord_iff`, `odd_and_gapWord_iff_modEq`, `odd_and_gapWord_iff_padic` | proved for integer starts `x ∈ ℤ` (Terras form); for `x ∈ ℤ_2 \ ℤ` not formalized (needs a `2`-adic Syracuse map, absent from `Basic`) |
| FS4: balanced-word lemma `Σ β^k 3^{o-1-k} = D/(β - 3)` | `balanced_sum` | proved |
| FS4: `S/D = η/(β - 3)` with `η ∈ [2^{-p}, 2^p]` | `xstar_eq_eta_div`, `eta_mem`, `eta_mem_of_le` | proved (positivity of the word not needed) |
| FS5: sign / regime dictionary | `three_lt_beta_iff`, `xstar_neg_of_beta_lt`, `inv_beta_sub_three_lt` | proved |
| FS5a: `β ≥ 7/2 ⇒ 0 < x*_w ≤ 2^{p+1}` | `xstar_le_two_pow_imbalance`, `xstar_le_of_le` | proved |
| FS5b: `S ≥ 2^{E - d_{o-1}}` | `two_pow_e_last_le_Sz` | proved |
| FS5b: Matveev lower bound on `D`; polynomial denominator | — | not formalized (cited external bound; open in the note) |
| RATIONALE regime 3: `E > (log₂ 3 + ε) o ⇒ 1/(β - 3) < 2` | `inv_beta_sub_three_lt` | corrected: needs `β > 7/2`, i.e. `ε > log₂(7/6)` (`fundamental.md` form); false for smaller `ε` |
| STATUS: finite flying time for all `x > 0` ⇒ Collatz | `collatzConjecture_of_finiteFlyingTime`, `collatzConjecture_iff_finiteFlyingTime`, `not_finiteFlyingTime_le_four`; accelerated map: `collatzConjecture_of_finiteFlyingTime_syr`, `not_finiteFlyingTime_syr_one` | corrected: the hypothesis is false as written (`1, 2, 3, 4` never fly down under `collatz`, `1` never under `syr`); proved for `x ≥ 5` (resp. odd `x ≥ 3`); the full-map form is an equivalence |
| integrality amendment bound; threshold `f(n, p)`; `x* ∈ [2^E/Poly, 2^E]` | — | open in the note; not formalized |
| `results/RESULTS.md` statistics | — | empirical, not formalized |
-/

namespace Syracuse.DiophantineDistribution

/-! ## Casting `S` and `D` along ring homomorphisms -/

/-- `S` commutes with ring homomorphisms. -/
theorem map_S {R R' : Type*} [CommSemiring R] [CommSemiring R'] (f : R →+* R') (X Y : R)
    (w : Word) : f (S X Y w) = S (f X) (f Y) w := by
  induction w with
  | nil => simp
  | cons d w ih => simp [ih]

/-- The integer `S(w)` cast into any commutative ring is `S` evaluated at `(2, 3)` there. -/
theorem intCast_Sz {R : Type*} [CommRing R] (w : Word) : ((Sz w : ℤ) : R) = S (2 : R) 3 w := by
  simpa using map_S (Int.castRingHom R) 2 3 w

/-- The integer `D(w)` cast into any commutative ring is `D` evaluated at `(2, 3)` there. -/
theorem intCast_Dz {R : Type*} [CommRing R] (w : Word) : ((Dz w : ℤ) : R) = D (2 : R) 3 w := by
  simp [D]

/-- `D` commutes with ring homomorphisms. -/
theorem map_D {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R') (X Y : R)
    (w : Word) : f (D X Y w) = D (f X) (f Y) w := by
  simp [D]

/-! ## Parity of `D` and `S` -/

/-- `D(w) = 2^E - 3^o` is odd as soon as `E ≥ 1`. -/
theorem odd_Dz {w : Word} (hE : 0 < w.sum) : Odd (Dz w) := by
  have h2 : Even ((2 : ℤ) ^ w.sum) := (Int.even_pow).2 ⟨even_two, hE.ne'⟩
  have h3 : Odd ((3 : ℤ) ^ w.length) := Odd.pow (by decide)
  simpa [Dz, D] using h2.sub_odd h3

/-- `D(w) ≠ 0` in `ℤ` for every nonempty word (`2^E` and `3^o` differ in parity or size). -/
theorem Dz_ne_zero {w : Word} (hw : w ≠ []) : Dz w ≠ 0 := by
  have ho : 0 < w.length := List.length_pos_iff.2 hw
  rcases Nat.eq_zero_or_pos w.sum with hE | hE
  · simp only [Dz, D, hE, pow_zero]
    have : (1 : ℤ) < 3 ^ w.length := one_lt_pow₀ (by norm_num) ho.ne'
    omega
  · intro h
    have := odd_Dz hE
    rw [h] at this
    simp at this


/-- For a word `d :: w` with `d ≥ 1`, `S` is odd: the `k = 0` term `3^{o-1}` is odd, all others even. -/
theorem odd_Sz_cons {d : ℕ} (hd : 1 ≤ d) (w : Word) : Odd (Sz (d :: w)) := by
  have h3 : Odd ((3 : ℤ) ^ w.length) := Odd.pow (by decide)
  have h2 : Even ((2 : ℤ) ^ d * Sz w) :=
    ((Int.even_pow).2 ⟨even_two, (Nat.one_le_iff_ne_zero.1 hd)⟩).mul_right _
  simpa [Sz] using h3.add_even h2

/-- A nonempty positive word has odd `S`. -/
theorem odd_Sz {w : Word} (hw : w.Pos) (hne : w ≠ []) : Odd (Sz w) := by
  obtain ⟨d, w', rfl⟩ := List.exists_cons_of_ne_nil hne
  exact odd_Sz_cons (hw d List.mem_cons_self) w'

/-- A nonempty positive word has `E ≥ 1`. -/
theorem sum_pos {w : Word} (hw : w.Pos) (hne : w ≠ []) : 0 < w.sum := by
  obtain ⟨d, w', rfl⟩ := List.exists_cons_of_ne_nil hne
  have := hw d List.mem_cons_self
  simp only [List.sum_cons]
  omega

/-! ## FS1 — the word map is affine -/

section Field

variable {K : Type*} [Field K]

/-- One accelerated Syracuse step with prescribed gap `d`: `T_d(x) = (3x + 1) / 2^d`. -/
def T (d : ℕ) (x : K) : K := (3 * x + 1) / 2 ^ d

/-- The word map `F_w = T_{d_{o-1}} ∘ ⋯ ∘ T_{d_0}` (the first letter acts first). -/
def F : Word → K → K
  | [], x => x
  | d :: w, x => F w (T d x)

/-- The word map follows the recurrence `2^{d_k} a_{k+1} = 3 a_k + 1` along `w`. -/
theorem follows_F (h2 : (2 : K) ≠ 0) (w : Word) (x : K) : Follows (2 : K) 3 w x (F w x) := by
  induction w generalizing x with
  | nil => exact Follows.nil x
  | cons d w ih =>
    refine Follows.cons ?_ (ih (T d x))
    rw [T, mul_div_cancel₀ _ (pow_ne_zero _ h2)]

/-- **FS1.** `F_w(x) = (3^o / 2^E) x + S(w) / 2^E` (any field with `2 ≠ 0`, e.g. `ℚ`, `ℝ`, `ℚ_[2]`). -/
theorem F_eq (h2 : (2 : K) ≠ 0) (w : Word) (x : K) :
    F w x = 3 ^ w.length / 2 ^ w.sum * x + S (2 : K) 3 w / 2 ^ w.sum := by
  have h := (follows_F h2 w x).closed_form
  have hE : (2 : K) ^ w.sum ≠ 0 := pow_ne_zero _ h2
  field_simp
  linear_combination h

/-- The fundamental solution `x*_w = S(w) / D(w)`. -/
def xstar (w : Word) : K := S (2 : K) 3 w / D (2 : K) 3 w

/-- **FS1/FS2.** When `D(w) ≠ 0`, the fixed points of `F_w` are exactly `x*_w = S(w)/D(w)`. -/
theorem F_eq_self_iff (h2 : (2 : K) ≠ 0) {w : Word} (hD : D (2 : K) 3 w ≠ 0) (x : K) :
    F w x = x ↔ x = xstar w := by
  have h := (follows_F h2 w x).closed_form
  have hE : (2 : K) ^ w.sum ≠ 0 := pow_ne_zero _ h2
  rw [xstar, eq_div_iff hD]
  constructor
  · intro hx
    rw [hx] at h
    simp only [D]
    linear_combination h
  · intro hx
    apply mul_left_cancel₀ hE
    simp only [D] at hx
    linear_combination h - hx

/-- In characteristic zero `D(w) ≠ 0` for every nonempty word. -/
theorem D_ne_zero [CharZero K] {w : Word} (hw : w ≠ []) : D (2 : K) 3 w ≠ 0 := by
  rw [← intCast_Dz]
  exact_mod_cast Dz_ne_zero hw

/-- **FS2 (conjugacy with the shift).** Rotating `d :: w` to `w ++ [d]` moves the fundamental
solution by one accelerated step of gap `d`: `x*_{w·d} = T_d(x*_{d·w})`. -/
theorem xstar_rotate (h2 : (2 : K) ≠ 0) (d : ℕ) (w : Word) (hD : D (2 : K) 3 (d :: w) ≠ 0) :
    xstar (w ++ [d]) = T d (xstar (d :: w) : K) := by
  have hrot := rotation_recursion (2 : K) 3 d w
  have hDr : D (2 : K) 3 (w ++ [d]) = D (2 : K) 3 (d :: w) := by
    simpa [rotate_one_cons] using D_rotate (2 : K) 3 (d :: w) 1
  rw [xstar, xstar, T, hDr, div_eq_div_iff hD (pow_ne_zero _ h2)]
  field_simp
  linear_combination hrot

/-- The rational fundamental solution, cast into any field of characteristic zero, is the
fundamental solution computed there. -/
theorem ratCast_xstar [CharZero K] (w : Word) : ((xstar w : ℚ) : K) = xstar w := by
  simp only [xstar, Rat.cast_div]
  rw [← intCast_Sz (R := ℚ), ← intCast_Dz (R := ℚ), ← intCast_Sz (R := K), ← intCast_Dz (R := K)]
  push_cast
  rfl

end Field

/-! ## FS2 over `ℚ`: integrality -/

/-- **FS2 (integrality).** For a nonempty word, `x*_w ∈ ℚ` is an integer iff `D(w) ∣ S(w)`. -/
theorem xstar_isInt_iff {w : Word} (hw : w ≠ []) :
    (∃ n : ℤ, (n : ℚ) = xstar w) ↔ Dz w ∣ Sz w := by
  have hD := Dz_ne_zero hw
  have hDq : (Dz w : ℚ) ≠ 0 := by exact_mod_cast hD
  rw [xstar, ← intCast_Dz, ← intCast_Sz]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [eq_div_iff hDq] at hn
    exact_mod_cast (by linarith : (Sz w : ℚ) = Dz w * n)
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [eq_div_iff hDq, hn]
    push_cast
    ring


/-! ## FS2 in `ℤ_[2]`: the fundamental solution is a `2`-adic integer -/

/-- An odd integer is a unit of `ℤ_[2]`. -/
theorem isUnit_intCast_of_odd {z : ℤ} (hz : Odd z) : IsUnit (z : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd]
  have := Int.not_even_iff_odd.2 hz
  rw [even_iff_two_dvd] at this
  exact_mod_cast this

/-- `D(w)` is a unit of `ℤ_[2]` as soon as `E ≥ 1`, because it is odd. -/
theorem isUnit_D_padic {w : Word} (hE : 0 < w.sum) : IsUnit (D (2 : ℤ_[2]) 3 w) := by
  rw [← intCast_Dz]
  exact isUnit_intCast_of_odd (odd_Dz hE)

/-- The fundamental solution in `ℤ_[2]`: `x*_w = S(w) · D(w)⁻¹` (`Ring.inverse` of the unit `D`). -/
noncomputable def xstar2 (w : Word) : ℤ_[2] :=
  S (2 : ℤ_[2]) 3 w * Ring.inverse (D (2 : ℤ_[2]) 3 w)

/-- `D(w) · x*_w = S(w)` in `ℤ_[2]` (for `E ≥ 1`). -/
theorem D_mul_xstar2 {w : Word} (hE : 0 < w.sum) :
    D (2 : ℤ_[2]) 3 w * xstar2 w = S (2 : ℤ_[2]) 3 w := by
  rw [xstar2, mul_left_comm, Ring.mul_inverse_cancel _ (isUnit_D_padic hE), mul_one]

/-- **FS1/FS2 in `ℤ_[2]`.** `x*_w` is the unique `2`-adic integer with `D(w) x = S(w)`. -/
theorem eq_xstar2_iff {w : Word} (hE : 0 < w.sum) (x : ℤ_[2]) :
    D (2 : ℤ_[2]) 3 w * x = S (2 : ℤ_[2]) 3 w ↔ x = xstar2 w := by
  constructor
  · intro h
    exact (isUnit_D_padic hE).mul_left_cancel (h.trans (D_mul_xstar2 hE).symm)
  · rintro rfl
    exact D_mul_xstar2 hE

/-- **FS1.** The rational number `S(w)/D(w)` lies in `ℤ_[2]`: its image in `ℚ_[2]` is the image of
the `2`-adic integer `x*_w`. -/
theorem coe_xstar2 {w : Word} (hE : 0 < w.sum) :
    ((xstar2 w : ℤ_[2]) : ℚ_[2]) = ((xstar w : ℚ) : ℚ_[2]) := by
  have hne : w ≠ [] := by rintro rfl; simp at hE
  have hD : D (2 : ℚ_[2]) 3 w ≠ 0 := D_ne_zero hne
  have h := congrArg (PadicInt.Coe.ringHom (p := 2)) (D_mul_xstar2 hE)
  rw [map_mul, map_S, map_D, map_ofNat, map_ofNat] at h
  rw [ratCast_xstar, xstar, eq_div_iff hD, mul_comm]
  exact h

/-- For a positive nonempty word, `x*_w` is a `2`-adic unit (it is "odd"): `S` and `D` are odd. -/
theorem isUnit_xstar2 {w : Word} (hw : w.Pos) (hne : w ≠ []) : IsUnit (xstar2 w) := by
  have hE := sum_pos hw hne
  have hS : IsUnit (S (2 : ℤ_[2]) 3 w) := by
    rw [← intCast_Sz]; exact isUnit_intCast_of_odd (odd_Sz hw hne)
  exact hS.mul (isUnit_D_padic hE).ringInverse

/-- **FS2 (`2`-adic conjugacy `Z ∘ shift = T ∘ Z`).** For a positive word `d :: w`,
`3 x*_{d·w} + 1 = 2^d · x*_{w·d}` with `x*_{w·d}` a `2`-adic unit. So `ν₂(3 x* + 1) = d` exactly,
and the accelerated `2`-adic Syracuse step sends `Z(d·w)` to `Z(w·d) = Z(shift(d·w))`. -/
theorem xstar2_rotate {d : ℕ} {w : Word} (hw : Word.Pos (d :: w)) :
    3 * xstar2 (d :: w) + 1 = 2 ^ d * xstar2 (w ++ [d]) ∧ IsUnit (xstar2 (w ++ [d])) := by
  have hE := sum_pos hw (List.cons_ne_nil d w)
  have hrot := rotation_recursion (2 : ℤ_[2]) 3 d w
  have hDr : D (2 : ℤ_[2]) 3 (w ++ [d]) = D (2 : ℤ_[2]) 3 (d :: w) := by
    simpa [rotate_one_cons] using D_rotate (2 : ℤ_[2]) 3 (d :: w) 1
  have hE' : 0 < (w ++ [d]).sum := by simpa [add_comm] using hE
  have hwr : Word.Pos (w ++ [d]) := fun x hx => hw x (by simp at hx ⊢; tauto)
  refine ⟨?_, isUnit_xstar2 hwr (by simp)⟩
  apply (isUnit_D_padic hE).mul_left_cancel
  have h1 := D_mul_xstar2 hE
  have h2 := D_mul_xstar2 hE'
  rw [hDr] at h2
  linear_combination 3 * h1 - (2 : ℤ_[2]) ^ d * h2 - hrot

/-! ## FS3 — the fundamental solution organises all trajectories (integer form) -/

/-- If `3a + 1 = 2^d y` with `y` odd then `gap a = d` and `syr a = y`. -/
theorem gap_syr_of {a y : ℤ} {d : ℕ} (hy : Odd y) (h : 2 ^ d * y = 3 * a + 1) :
    gap a = d ∧ syr a = y := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have h2y : ¬ ((2 : ℕ) : ℤ) ∣ y := by
    have := Int.not_even_iff_odd.2 hy
    rwa [even_iff_two_dvd] at this
  have hg : gap a = d := by
    rw [gap, ← h, padicValInt.mul (pow_ne_zero _ two_ne_zero) hy0,
      padicValInt.eq_zero_of_not_dvd h2y, add_zero,
      show (2 : ℤ) ^ d = ((2 ^ d : ℕ) : ℤ) by push_cast; rfl, padicValInt.of_nat,
      padicValNat.prime_pow]
  refine ⟨hg, ?_⟩
  rw [syr, hg, ← h, Int.mul_ediv_cancel_left _ (pow_ne_zero _ two_ne_zero)]

/-- **FS3 (integer form).** For a positive word `w` and any integer `x`, the accelerated orbit of
`x` performs exactly the word `w` from an odd start (so every `a_k`, including `a_o`, is odd)
iff `3^o x + S(w) ≡ 2^E (mod 2^{E+1})`, i.e. iff `a_o = (3^o x + S(w))/2^E` is an odd integer.
This is a single residue class modulo `2^{E+1}`. -/
theorem odd_and_gapWord_iff {w : Word} (hw : w.Pos) (x : ℤ) :
    (Odd x ∧ gapWord x w.length = w) ↔
      3 ^ w.length * x + Sz w ≡ 2 ^ w.sum [ZMOD 2 ^ (w.sum + 1)] := by
  induction w generalizing x with
  | nil => simp [gapWord, Int.ModEq, Int.odd_iff]
  | cons d w ih =>
    have hd : 1 ≤ d := hw d List.mem_cons_self
    have hw' : Word.Pos w := fun e he => hw e (List.mem_cons_of_mem d he)
    have h2d : (2 : ℤ) ^ d ≠ 0 := pow_ne_zero _ two_ne_zero
    simp only [List.length_cons, gapWord, List.cons.injEq, List.sum_cons, Sz, S_cons]
    rw [Int.modEq_iff_dvd]
    constructor
    · rintro ⟨hx, rfl, hgw⟩
      have hy := (ih hw' (syr x)).1 ⟨syr_odd x, hgw⟩
      rw [Int.modEq_iff_dvd] at hy
      have := mul_dvd_mul_left ((2 : ℤ) ^ gap x) hy
      rw [← pow_add] at this
      rw [add_assoc]
      convert this using 1
      have := two_pow_gap_mul_syr x
      rw [pow_add, pow_succ]
      linear_combination (3 : ℤ) ^ w.length * this
    · intro h
      -- `2^d ∣ 3^o (3x + 1)`, hence `2^d ∣ 3x + 1`
      have hdvd : (2 : ℤ) ^ d ∣ 3 ^ w.length * (3 * x + 1) := by
        have h1 : (2 : ℤ) ^ d ∣ 2 ^ (d + w.sum + 1) := pow_dvd_pow _ (by omega)
        have h2 := h1.trans h
        have h3 : (2 : ℤ) ^ d ∣ 2 ^ (d + w.sum) - 2 ^ d * Sz w :=
          dvd_sub (pow_dvd_pow _ (by omega)) (dvd_mul_right _ _)
        convert dvd_sub h3 h2 using 1
        ring
      have hcop : IsCoprime ((2 : ℤ) ^ d) (3 ^ w.length) :=
        (Int.isCoprime_iff_gcd_eq_one.2 (by norm_num)).pow
      obtain ⟨y, hy⟩ := hcop.dvd_of_dvd_mul_left hdvd
      have hmod : (2 : ℤ) ^ (w.sum + 1) ∣ 2 ^ w.sum - (3 ^ w.length * y + Sz w) := by
        rw [← mul_dvd_mul_iff_left h2d, ← pow_add, ← add_assoc]
        convert h using 1
        rw [pow_add, pow_succ]
        linear_combination (3 : ℤ) ^ w.length * hy
      obtain ⟨hyo, hgw⟩ := (ih hw' y).2 ((Int.modEq_iff_dvd).2 hmod)
      obtain ⟨hg, hs⟩ := gap_syr_of hyo hy.symm
      refine ⟨?_, hg, by rwa [hs]⟩
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      rw [pow_succ] at hy
      rw [Int.odd_iff]
      have : 3 * x + 1 = 2 * (2 ^ d' * y) := by rw [hy]; ring
      omega


/-- For odd `x`, `2^E x ≡ 2^E (mod 2^{E+1})`. -/
lemma two_pow_mul_odd_modEq {x : ℤ} (hx : Odd x) (E : ℕ) :
    2 ^ E * x ≡ 2 ^ E [ZMOD 2 ^ (E + 1)] := by
  obtain ⟨k, rfl⟩ := hx
  rw [Int.modEq_iff_dvd]
  exact ⟨-k, by ring⟩

/-- **FS3 (class form).** For a nonempty positive word, the integers whose orbit performs exactly `w`
from an odd start are those with `D(w) x ≡ S(w) (mod 2^{E+1})`, i.e. `x ≡ x*_w (mod 2^{E+1})`. -/
theorem odd_and_gapWord_iff_modEq {w : Word} (hw : w.Pos) (hne : w ≠ []) (x : ℤ) :
    (Odd x ∧ gapWord x w.length = w) ↔ Dz w * x ≡ Sz w [ZMOD 2 ^ (w.sum + 1)] := by
  have hE := sum_pos hw hne
  rw [odd_and_gapWord_iff hw]
  have key : Dz w * x = 2 ^ w.sum * x - (3 ^ w.length * x + Sz w) + Sz w := by
    simp only [Dz, D]; ring
  constructor
  · intro h
    have hx : Odd x := ((odd_and_gapWord_iff hw x).2 h).1
    rw [key]
    calc 2 ^ w.sum * x - (3 ^ w.length * x + Sz w) + Sz w
        ≡ 2 ^ w.sum - 2 ^ w.sum + Sz w [ZMOD 2 ^ (w.sum + 1)] :=
          ((two_pow_mul_odd_modEq hx _).sub h).add_right _
      _ = Sz w := by ring
  · intro h
    -- reduce mod 2: `x` is odd because `D` and `S` are
    have h2 : Dz w * x ≡ Sz w [ZMOD 2] :=
      Int.ModEq.of_mul_left (2 ^ w.sum) (by rwa [← pow_succ])
    have hx : Odd x := by
      have hD := odd_Dz hE
      have hS := odd_Sz hw hne
      rw [Int.odd_iff] at hD hS ⊢
      rw [Int.ModEq, Int.mul_emod, hD, hS] at h2
      omega
    have h' := (two_pow_mul_odd_modEq hx w.sum).sub h
    rw [key] at h'
    calc 3 ^ w.length * x + Sz w
        = 2 ^ w.sum * x - (2 ^ w.sum * x - (3 ^ w.length * x + Sz w) + Sz w) + Sz w := by ring
      _ ≡ 2 ^ w.sum - Sz w + Sz w [ZMOD 2 ^ (w.sum + 1)] := h'.add_right _
      _ = 2 ^ w.sum := by ring

/-- **FS3 (`2`-adic class form, integer points).** For a nonempty positive word, an integer `x`
performs exactly `w` from an odd start iff `x ∈ x*_w + 2^{E+1} ℤ_[2]`. -/
theorem odd_and_gapWord_iff_padic {w : Word} (hw : w.Pos) (hne : w ≠ []) (x : ℤ) :
    (Odd x ∧ gapWord x w.length = w) ↔ (2 : ℤ_[2]) ^ (w.sum + 1) ∣ (x : ℤ_[2]) - xstar2 w := by
  have hE := sum_pos hw hne
  rw [odd_and_gapWord_iff_modEq hw hne, Int.modEq_comm, Int.modEq_iff_dvd,
    ← (isUnit_D_padic hE).dvd_mul_left, mul_sub, D_mul_xstar2 hE, ← intCast_Dz, ← intCast_Sz]
  have := PadicInt.pow_p_dvd_int_iff (p := 2) (w.sum + 1) (Dz w * x - Sz w)
  push_cast at this
  exact this.symm

/-- **FS2 (genuine cycles).** For a nonempty positive word `w`, an integer `a` starts a genuine
Syracuse cycle whose gap word is exactly `w` iff `D(w) a = S(w)`, i.e. iff `a = x*_w`. The note's
extra condition "parities consistent" is automatic for positive words. -/
theorem isSyrCycle_and_gapWord_iff {w : Word} (hw : w.Pos) (hne : w ≠ []) (a : ℤ) :
    (IsSyrCycle a w.length ∧ gapWord a w.length = w) ↔ Dz w * a = Sz w := by
  constructor
  · rintro ⟨hc, hg⟩
    simpa [hg] using hc.cycle_equation
  · intro h
    obtain ⟨ha, hg⟩ := (odd_and_gapWord_iff_modEq hw hne a).2 (by rw [h])
    refine ⟨⟨List.length_pos_iff.2 hne, ha, ?_⟩, hg⟩
    have hc := (follows_gapWord a w.length).closed_form
    rw [hg] at hc
    have h2 : (2 : ℤ) ^ w.sum ≠ 0 := pow_ne_zero _ two_ne_zero
    apply mul_left_cancel₀ h2
    simp only [Dz, D] at h
    linear_combination hc - h

/-- **FS2.** A genuine integer cycle with positive gap word `w` exists iff `D(w) ∣ S(w)`. -/
theorem exists_cycle_iff {w : Word} (hw : w.Pos) (hne : w ≠ []) :
    (∃ a : ℤ, IsSyrCycle a w.length ∧ gapWord a w.length = w) ↔ Dz w ∣ Sz w := by
  simp only [isSyrCycle_and_gapWord_iff hw hne]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

/-- **FS2 (integer conjugacy `Z ∘ shift = syr ∘ Z`).** If `a = x*_{d·w}` is an integer
(`D a = S`) for a positive word `d :: w`, then `gap a = d` and `syr a = x*_{w·d}`
(`D(w·d) · syr a = S(w·d)`). -/
theorem syr_xstar_rotate {d : ℕ} {w : Word} (hw : Word.Pos (d :: w)) {a : ℤ}
    (h : Dz (d :: w) * a = Sz (d :: w)) :
    gap a = d ∧ Dz (w ++ [d]) * syr a = Sz (w ++ [d]) := by
  have hg := ((isSyrCycle_and_gapWord_iff hw (List.cons_ne_nil d w) a).2 h).2
  simp only [List.length_cons, gapWord, List.cons.injEq] at hg
  refine ⟨hg.1, ?_⟩
  have hrot := rotation_recursion (2 : ℤ) 3 d w
  have hDr : Dz (w ++ [d]) = Dz (d :: w) := by
    simpa [rotate_one_cons] using D_rotate (2 : ℤ) 3 (d :: w) 1
  have hs := two_pow_gap_mul_syr a
  rw [hg.1] at hs
  rw [hDr]
  apply mul_left_cancel₀ (pow_ne_zero d (two_ne_zero : (2 : ℤ) ≠ 0))
  linear_combination Dz (d :: w) * hs + 3 * h - hrot

/-! ### The examples of `fundamental.md` FS2 -/

/-- `w = (1)`: `S = 1`, `D = -1`, `x*_w = -1` (the fixed point `-1`). -/
theorem xstar_one : (xstar [1] : ℚ) = -1 := by norm_num [xstar, D]

/-- `w = (2, 1)`: `S = 7`, `D = -1`, `x*_w = -7` (the cycle `-7 → -5 → -7`). -/
theorem xstar_two_one : (xstar [2, 1] : ℚ) = -7 := by norm_num [xstar, D]

/-- `-1` is a genuine Syracuse cycle with gap word `(1)`. -/
theorem isSyrCycle_neg_one : IsSyrCycle (-1) 1 ∧ gapWord (-1) 1 = [1] :=
  (isSyrCycle_and_gapWord_iff (w := [1]) (by simp [Word.Pos]) (by simp) (-1)).2
    (by norm_num [Dz, Sz, D])

/-- `-7 → -5 → -7` is a genuine Syracuse cycle with gap word `(2, 1)`. -/
theorem isSyrCycle_neg_seven : IsSyrCycle (-7) 2 ∧ gapWord (-7) 2 = [2, 1] :=
  (isSyrCycle_and_gapWord_iff (w := [2, 1]) (by simp [Word.Pos]) (by simp) (-7)).2
    (by norm_num [Dz, Sz, D])


/-! ## FS3 corollary — injectivity and common-root rigidity -/

/-- The RATIONALE's "`S` is injective" is false on all words: `S(1) = S(2) = 1`. -/
theorem Sz_one_eq_Sz_two : Sz [1] = Sz [2] := by simp

/-- `Z` is not injective on all words either: `Z(1) = Z(1,1) = -1` (common root `(1)`). -/
theorem xstar_one_one : (xstar [1, 1] : ℚ) = -1 := by norm_num [xstar, D]

/-- An integer `n` in the FS3 class of `w`: `D(w) n ≡ S(w) (mod 2^N)` is solvable since `D` is odd. -/
theorem exists_modEq_of_odd {D S : ℤ} (hD : Odd D) (N : ℕ) : ∃ n : ℤ, D * n ≡ S [ZMOD 2 ^ N] := by
  obtain ⟨k, rfl⟩ := hD
  have hc : IsCoprime (2 * k + 1) ((2 : ℤ) ^ N) := IsCoprime.pow_right ⟨1, -k, by ring⟩
  obtain ⟨a, b, hab⟩ := hc
  refine ⟨a * S, (Int.modEq_iff_dvd).2 ⟨b * S, ?_⟩⟩
  linear_combination (-S) * hab

/-- **`S` is injective on each stratum `(E, o)`** (corrected form of RATIONALE's "`S` is injective"):
two nonempty positive words with the same length, the same gap-sum and the same `S` are equal.
Proof: an integer in the common FS3 class performs both words. -/
theorem eq_of_Sz_eq {u v : Word} (hu : u.Pos) (hv : v.Pos) (hne : u ≠ [])
    (hl : u.length = v.length) (hs : u.sum = v.sum) (hS : Sz u = Sz v) : u = v := by
  have hnev : v ≠ [] := by rintro rfl; simp_all
  have hD : Dz u = Dz v := by simp [Dz, D, hl, hs]
  obtain ⟨n, hn⟩ := exists_modEq_of_odd (S := Sz u) (odd_Dz (sum_pos hu hne)) (u.sum + 1)
  have h1 := ((odd_and_gapWord_iff_modEq hu hne n).2 hn).2
  have h2 := ((odd_and_gapWord_iff_modEq hv hnev n).2 (by rw [← hD, ← hS, ← hs]; exact hn)).2
  rw [← h1, ← h2, hl]

/-- Equal fundamental solutions give equal `S` on the two concatenation orders:
`S(u)D(v) = S(v)D(u) ⇒ S(uv) = S(vu)`. -/
theorem Sz_append_comm {u v : Word} (hu : u ≠ []) (hv : v ≠ [])
    (h : Sz u * Dz v = Sz v * Dz u) : Sz (u ++ v) = Sz (v ++ u) := by
  have hDu := Dz_ne_zero hu
  have hDv := Dz_ne_zero hv
  apply mul_left_cancel₀ (mul_ne_zero hDu hDv)
  simp only [Sz, Dz, S_append, D] at h ⊢
  linear_combination
    (-((2 ^ u.sum - 3 ^ u.length) * (2 ^ v.sum - 3 ^ v.length) : ℤ)) * h

/-- `w^p`: the word `w` repeated `p` times. -/
def wpow (w : Word) (p : ℕ) : Word := (List.replicate p w).flatten

/-- `w^{p+q} = w^p w^q`. -/
lemma wpow_add (w : Word) (p q : ℕ) : wpow w (p + q) = wpow w p ++ wpow w q := by
  rw [wpow, wpow, wpow, List.replicate_add, List.flatten_append]

/-- `w^{p+1} = w · w^p`. -/
lemma wpow_succ (w : Word) (p : ℕ) : wpow w (p + 1) = w ++ wpow w p := by
  simp [wpow, List.replicate_succ]

/-- Lyndon–Schützenberger, bounded form (induction on `|u| + |v|`). -/
theorem exists_root_of_append_comm_aux (n : ℕ) : ∀ u v : Word, u.length + v.length ≤ n →
    u ++ v = v ++ u → ∃ w p q, u = wpow w p ∧ v = wpow w q := by
  induction n with
  | zero =>
    intro u v hn _
    have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv : v = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], 0, 0, by simp [hu, wpow], by simp [hv, wpow]⟩
  | succ n ih =>
    intro u v hn h
    rcases List.append_eq_append_iff.1 h with ⟨a, hv1, hv2⟩ | ⟨c, hu1, hu2⟩
    · rcases u with _ | ⟨x, u'⟩
      · exact ⟨v, 0, 1, by simp [wpow], by simp [wpow]⟩
      · have hlen : (x :: u').length + a.length ≤ n := by
          rw [hv1] at hn; simp only [List.length_cons, List.length_append] at hn ⊢; omega
        obtain ⟨w, p, q, hu, ha⟩ := ih _ _ hlen (hv1.symm.trans hv2)
        exact ⟨w, p, p + q, hu, by rw [hv1, wpow_add, ← hu, ← ha]⟩
    · rcases v with _ | ⟨x, v'⟩
      · exact ⟨u, 1, 0, by simp [wpow], by simp [wpow]⟩
      · have hlen : c.length + (x :: v').length ≤ n := by
          rw [hu1] at hn; simp only [List.length_cons, List.length_append] at hn ⊢; omega
        obtain ⟨w, p, q, hc, hv⟩ := ih _ _ hlen (hu2.symm.trans hu1)
        exact ⟨w, q + p, q, by rw [hu1, wpow_add, ← hv, ← hc], hv⟩

/-- **Lyndon–Schützenberger.** Commuting words are powers of a common word. -/
theorem exists_root_of_append_comm {u v : Word} (h : u ++ v = v ++ u) :
    ∃ w p q, u = wpow w p ∧ v = wpow w q :=
  exists_root_of_append_comm_aux _ u v le_rfl h

/-- `S(w^p) D(w) = S(w) D(w^p)`: all powers of `w` share the fundamental solution of `w`. -/
theorem Sz_wpow_mul (w : Word) (p : ℕ) : Sz (wpow w p) * Dz w = Sz w * Dz (wpow w p) := by
  induction p with
  | zero => simp [wpow]
  | succ p ih =>
    rw [wpow_succ]
    simp only [Sz, Dz, S_append, D_append] at ih ⊢
    linear_combination (2 : ℤ) ^ w.sum * ih

/-- `Z(u) = Z(v)` in `ℚ` is the cross-multiplied identity `S(u) D(v) = S(v) D(u)`. -/
theorem xstar_eq_iff_cross {u v : Word} (hu : u ≠ []) (hv : v ≠ []) :
    (xstar u : ℚ) = xstar v ↔ Sz u * Dz v = Sz v * Dz u := by
  rw [xstar, xstar, div_eq_div_iff (D_ne_zero hu) (D_ne_zero hv), ← intCast_Sz, ← intCast_Sz,
    ← intCast_Dz, ← intCast_Dz]
  exact_mod_cast Iff.rfl

/-- **Rigidity (RATIONALE observation 1, `fundamental.md` FS3 corollary).** For nonempty positive
words, `Z(u) = Z(v)` (`S(u)/D(u) = S(v)/D(v)` in `ℚ`) iff `u` and `v` are powers of a common
word. -/
theorem xstar_eq_iff_common_root {u v : Word} (hu : u.Pos) (hv : v.Pos) (hune : u ≠ [])
    (hvne : v ≠ []) : (xstar u : ℚ) = xstar v ↔ ∃ w p q, u = wpow w p ∧ v = wpow w q := by
  rw [xstar_eq_iff_cross hune hvne]
  constructor
  · intro h
    apply exists_root_of_append_comm
    have huv : Word.Pos (u ++ v) := fun x hx => (List.mem_append.1 hx).elim (hu x) (hv x)
    have hvu : Word.Pos (v ++ u) := fun x hx => (List.mem_append.1 hx).elim (hv x) (hu x)
    exact eq_of_Sz_eq huv hvu (by simp [hune]) (by simp [add_comm]) (by simp [add_comm])
      (Sz_append_comm hune hvne h)
  · rintro ⟨w, p, q, rfl, rfl⟩
    have hw : w ≠ [] := by rintro rfl; simp [wpow] at hune
    have hp := Sz_wpow_mul w p
    have hq := Sz_wpow_mul w q
    have hDw := Dz_ne_zero hw
    apply mul_left_cancel₀ hDw
    linear_combination Dz (wpow w q) * hp - Dz (wpow w p) * hq

/-! ## FS4 — the balanced-word lemma and the imbalance factorisation (over `ℝ`) -/

section Real

/-- The mean slope `β = 2^{E/o}` of a word (real power). -/
noncomputable def beta (w : Word) : ℝ := (2 : ℝ) ^ ((w.sum : ℝ) / w.length)

/-- `β > 0`. -/
lemma beta_pos (w : Word) : 0 < beta w := Real.rpow_pos_of_pos two_pos _

/-- `β^k = 2^{(E/o) k}`. -/
lemma beta_pow_eq (w : Word) (k : ℕ) : beta w ^ k = (2 : ℝ) ^ ((w.sum : ℝ) / w.length * k) := by
  rw [beta, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

/-- `β^o = 2^E` for a nonempty word. -/
lemma beta_pow_length {w : Word} (hne : w ≠ []) : beta w ^ w.length = 2 ^ w.sum := by
  have ho : (w.length : ℝ) ≠ 0 := by exact_mod_cast (List.length_pos_iff.2 hne).ne'
  rw [beta_pow_eq, div_mul_cancel₀ _ ho, Real.rpow_natCast]

/-- `β ≠ 3` for a nonempty word (otherwise `2^E = 3^o`, i.e. `D = 0`). -/
lemma beta_ne_three {w : Word} (hne : w ≠ []) : beta w ≠ 3 := by
  intro h
  have h' := beta_pow_length hne
  rw [h] at h'
  exact D_ne_zero (K := ℝ) hne (by simp [D, h'])

/-- **Balanced-word lemma (FS4).** `Σ_{k<o} β^k 3^{o-1-k} = D(w) / (β - 3)`. -/
theorem balanced_sum {w : Word} (hne : w ≠ []) :
    ∑ k ∈ Finset.range w.length, beta w ^ k * 3 ^ (w.length - 1 - k) =
      D (2 : ℝ) 3 w / (beta w - 3) := by
  rw [eq_div_iff (sub_ne_zero.2 (beta_ne_three hne)), geom_sum₂_mul, beta_pow_length hne, D]

/-- The deviation `δ_k = e_k - (E/o) k` of the partial gap-sum from the mean line. -/
noncomputable def dev (w : Word) (k : ℕ) : ℝ := e w k - (w.sum : ℝ) / w.length * k

/-- The imbalance `p = max_{0 ≤ k ≤ o} |e_k - (E/o) k|`. -/
noncomputable def imbalance (w : Word) : ℝ :=
  (Finset.range (w.length + 1)).sup' Finset.nonempty_range_add_one fun k => |dev w k|

/-- Each deviation is bounded by the imbalance. -/
lemma abs_dev_le_imbalance (w : Word) {k : ℕ} (hk : k ≤ w.length) : |dev w k| ≤ imbalance w :=
  Finset.le_sup' (fun k => |dev w k|) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

/-- `2^{e_k} = 2^{δ_k} β^k`. -/
lemma two_pow_e_eq (w : Word) (k : ℕ) : (2 : ℝ) ^ e w k = 2 ^ dev w k * beta w ^ k := by
  rw [beta_pow_eq, ← Real.rpow_add two_pos, dev, sub_add_cancel, Real.rpow_natCast]

/-- The imbalance factor `η = S(w) (β - 3) / D(w)`, so that `S/D = η/(β - 3)`. -/
noncomputable def eta (w : Word) : ℝ := S (2 : ℝ) 3 w * (beta w - 3) / D (2 : ℝ) 3 w

/-- **FS4 (factorisation).** `x*_w = S(w)/D(w) = η / (β - 3)`. -/
theorem xstar_eq_eta_div {w : Word} (hne : w ≠ []) : (xstar w : ℝ) = eta w / (beta w - 3) := by
  have h3 := sub_ne_zero.2 (beta_ne_three hne)
  rw [xstar, eta, div_div, mul_comm (D (2 : ℝ) 3 w), ← div_div, mul_div_cancel_right₀ _ h3]

/-- **FS4 (imbalance bound).** If every deviation `|e_k - (E/o) k|` (`k < o`) is at most `p`,
then `η ∈ [2^{-p}, 2^p]`. -/
theorem eta_mem_of_le {w : Word} (hne : w ≠ []) {p : ℝ} (hp : ∀ k < w.length, |dev w k| ≤ p) :
    (2 : ℝ) ^ (-p) ≤ eta w ∧ eta w ≤ 2 ^ p := by
  set B := ∑ k ∈ Finset.range w.length, beta w ^ k * 3 ^ (w.length - 1 - k) with hB
  have hterm : ∀ k, 0 < beta w ^ k * (3 : ℝ) ^ (w.length - 1 - k) := fun k =>
    mul_pos (pow_pos (beta_pos w) k) (by positivity)
  have hBpos : 0 < B := Finset.sum_pos (fun k _ => hterm k)
    (Finset.nonempty_range_iff.2 (List.length_pos_iff.2 hne).ne')
  have hη : eta w = S (2 : ℝ) 3 w / B := by
    rw [hB, balanced_sum hne, eta, div_div_eq_mul_div]
  have hS : S (2 : ℝ) 3 w =
      ∑ k ∈ Finset.range w.length, 2 ^ dev w k * (beta w ^ k * 3 ^ (w.length - 1 - k)) := by
    rw [S_eq_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [two_pow_e_eq]
    ring
  have hlo : 2 ^ (-p) * B ≤ S (2 : ℝ) 3 w := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right ?_ (hterm k).le
    have := hp k (Finset.mem_range.1 hk)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [neg_abs_le (dev w k)])
  have hhi : S (2 : ℝ) 3 w ≤ 2 ^ p * B := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right ?_ (hterm k).le
    have := hp k (Finset.mem_range.1 hk)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [le_abs_self (dev w k)])
  rw [hη]
  exact ⟨(le_div_iff₀ hBpos).2 hlo, (div_le_iff₀ hBpos).2 hhi⟩

/-- **FS4.** `η ∈ [2^{-p}, 2^p]` with `p = imbalance w = max_k |e_k - (E/o) k|`. -/
theorem eta_mem {w : Word} (hne : w ≠ []) :
    (2 : ℝ) ^ (-imbalance w) ≤ eta w ∧ eta w ≤ 2 ^ imbalance w :=
  eta_mem_of_le hne fun _ hk => abs_dev_le_imbalance w hk.le

/-! ## FS5 — size of the fundamental solution; regime dictionary -/

/-- **FS5 (sign).** `β > 3 ↔ D(w) > 0` (contracting). -/
theorem three_lt_beta_iff {w : Word} (hne : w ≠ []) : 3 < beta w ↔ 0 < D (2 : ℝ) 3 w := by
  have ho := (List.length_pos_iff.2 hne).ne'
  rw [D, sub_pos, ← beta_pow_length hne]
  exact (pow_lt_pow_iff_left₀ (by norm_num) (beta_pos w).le ho).symm

/-- **FS5 (sign).** Expanding words (`β < 3`, equivalently `D < 0`) have `x*_w < 0`. -/
theorem xstar_neg_of_beta_lt {w : Word} (hne : w ≠ []) (h : beta w < 3) : (xstar w : ℝ) < 0 := by
  rw [xstar_eq_eta_div hne]
  exact div_neg_of_pos_of_neg ((Real.rpow_pos_of_pos two_pos _).trans_le (eta_mem hne).1)
    (sub_neg.2 h)

/-- **FS5a (contracting + large ⇒ power of `2` in the imbalance).** If `β ≥ 7/2` and all
deviations are at most `p`, then `0 < x*_w ≤ 2^{p+1}`, independently of `E`. -/
theorem xstar_le_of_le {w : Word} (hne : w ≠ []) (hβ : 7 / 2 ≤ beta w) {p : ℝ}
    (hp : ∀ k < w.length, |dev w k| ≤ p) : 0 < (xstar w : ℝ) ∧ (xstar w : ℝ) ≤ 2 ^ (p + 1) := by
  obtain ⟨hlo, hhi⟩ := eta_mem_of_le hne hp
  have hη : 0 < eta w := (Real.rpow_pos_of_pos two_pos _).trans_le hlo
  have hb : (1 : ℝ) / 2 ≤ beta w - 3 := by linarith
  rw [xstar_eq_eta_div hne]
  refine ⟨div_pos hη (by linarith), ?_⟩
  rw [div_le_iff₀ (by linarith), Real.rpow_add_one two_ne_zero]
  nlinarith [Real.rpow_pos_of_pos (two_pos : (0 : ℝ) < 2) p]

/-- **FS5a** with `p = imbalance w`. -/
theorem xstar_le_two_pow_imbalance {w : Word} (hne : w ≠ []) (hβ : 7 / 2 ≤ beta w) :
    0 < (xstar w : ℝ) ∧ (xstar w : ℝ) ≤ 2 ^ (imbalance w + 1) :=
  xstar_le_of_le hne hβ fun _ hk => abs_dev_le_imbalance w hk.le

/-- **Regime 3.** A large word (`β > 7/2`) has `1/(β - 3) < 2`. -/
theorem inv_beta_sub_three_lt {w : Word} (hβ : 7 / 2 < beta w) : 1 / (beta w - 3) < 2 := by
  rw [div_lt_iff₀ (by linarith)]
  linarith

end Real

/-- **FS5b (ingredient).** `S(w) ≥ 2^{e_{o-1}} = 2^{E - d_{o-1}}` (the last term of the sum). -/
theorem two_pow_e_last_le_Sz {w : Word} (hne : w ≠ []) : 2 ^ e w (w.length - 1) ≤ Sz w := by
  have ho := List.length_pos_iff.2 hne
  rw [Sz, S_eq_sum]
  have := Finset.single_le_sum (f := fun k => (2 : ℤ) ^ e w k * 3 ^ (w.length - 1 - k))
    (fun k _ => by positivity) (Finset.mem_range.2 (Nat.sub_lt ho one_pos))
  simpa using this


/-! ## Flying time and the Collatz conjecture (`STATUS.md`, Results, first bullet) -/

section Flying

variable {α : Type*} [LinearOrder α]

/-- The times at which the `T`-orbit of `x` is at or above its start: `{n : T^n(x) ≥ x}`. -/
def flyingSet (T : α → α) (x : α) : Set ℕ := {n | x ≤ T^[n] x}

/-- `x` has *finite flying time* under `T`: the set `{n : T^n(x) ≥ x}` is bounded. -/
def FiniteFlyingTime (T : α → α) (x : α) : Prop := BddAbove (flyingSet T x)

/-- The flying time `τ(x) = max {n : T^n(x) ≥ x}`. It is the intended value under
`FiniteFlyingTime T x` (the set always contains `0`); otherwise `sSup` returns the junk value `0`. -/
noncomputable def flyingTime (T : α → α) (x : α) : ℕ := sSup (flyingSet T x)

/-- With finite flying time, `T^n(x) < x` for every `n > τ(x)`. -/
theorem iterate_lt_of_flyingTime_lt {T : α → α} {x : α} {n : ℕ} (h : FiniteFlyingTime T x)
    (hn : flyingTime T x < n) : T^[n] x < x :=
  not_le.1 fun hmem => absurd (le_csSup h hmem) (not_le.2 hn)

/-- With finite flying time, `τ(x)` is attained: `T^{τ(x)}(x) ≥ x`. -/
theorem flyingTime_mem {T : α → α} {x : α} (h : FiniteFlyingTime T x) :
    x ≤ T^[flyingTime T x] x :=
  Nat.sSup_mem ⟨0, le_refl x⟩ h

/-- A point that returns to a value `≥ x` periodically has infinite flying time. -/
theorem not_finiteFlyingTime_of_periodic {T : α → α} {x y : α} {j p : ℕ} (hp : 0 < p)
    (hj : T^[j] x = y) (hy : T^[p] y = y) (hxy : x ≤ y) : ¬ FiniteFlyingTime T x := by
  have hcyc : ∀ m, T^[p * m] y = y := fun m => by
    rw [Function.iterate_mul]; exact Function.iterate_fixed hy m
  rintro ⟨b, hb⟩
  have hmem : p * (b + 1) + j ∈ flyingSet T x := by
    show x ≤ T^[p * (b + 1) + j] x
    rw [Function.iterate_add_apply, hj, hcyc]
    exact hxy
  have := hb hmem
  nlinarith

end Flying

/-- Iterates of a positivity-preserving map stay positive. -/
lemma iterate_pos {T : ℕ → ℕ} (hpos : ∀ n, 0 < n → 0 < T n) {x : ℕ} (hx : 0 < x) (k : ℕ) :
    0 < T^[k] x := by
  induction k with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact hpos _ ih

/-- **Descent reduction (strong induction).** If `T` keeps positive integers positive and every
`x > 1` eventually drops strictly below itself, then every positive integer reaches `1`. -/
theorem reaches_one_of_drop (T : ℕ → ℕ) (hpos : ∀ n, 0 < n → 0 < T n)
    (hdrop : ∀ x, 1 < x → ∃ n, T^[n] x < x) : ∀ x, 0 < x → ∃ k, T^[k] x = 1 := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    rcases (show x = 1 ∨ 1 < x by omega) with rfl | h1
    · exact ⟨0, rfl⟩
    · obtain ⟨n, hn⟩ := hdrop x h1
      obtain ⟨k, hk⟩ := ih _ hn (iterate_pos hpos hx n)
      exact ⟨k + n, by rw [Function.iterate_add_apply, hk]⟩

/-- The full Collatz map keeps positive integers positive. -/
lemma collatz_pos {n : ℕ} (hn : 0 < n) : 0 < collatz n := by
  unfold collatz; split_ifs <;> omega

/-- The trivial cycle: the Collatz orbit of `1` is `1, 4, 2, 1, …`. -/
lemma collatz_iterate_one (n : ℕ) :
    collatz^[n] 1 = 1 ∨ collatz^[n] 1 = 4 ∨ collatz^[n] 1 = 2 := by
  induction n with
  | zero => left; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h | h <;> rw [h] <;> decide

/-- **Stopping-time form.** If every `x > 1` eventually drops below itself under the full Collatz
map, the Collatz conjecture holds. -/
theorem collatzConjecture_of_drop (h : ∀ x, 1 < x → ∃ n, collatz^[n] x < x) :
    CollatzConjecture :=
  reaches_one_of_drop collatz (fun _ => collatz_pos) h

/-- **Flying time ⇒ Collatz** (corrected hypothesis). If every `x ≥ 5` has finite flying time under
the full Collatz map, the Collatz conjecture holds. (The small cases `2, 3, 4` drop below themselves
by direct computation; they do *not* have finite flying time, see `not_finiteFlyingTime_le_four`.) -/
theorem collatzConjecture_of_finiteFlyingTime (h : ∀ x, 5 ≤ x → FiniteFlyingTime collatz x) :
    CollatzConjecture := by
  refine collatzConjecture_of_drop fun x hx => ?_
  rcases (show x = 2 ∨ x = 3 ∨ x = 4 ∨ 5 ≤ x by omega) with rfl | rfl | rfl | h5
  · exact ⟨1, by decide⟩
  · exact ⟨6, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨flyingTime collatz x + 1, iterate_lt_of_flyingTime_lt (h x h5) (Nat.lt_succ_self _)⟩

/-- Conversely, under the Collatz conjecture every `x ≥ 5` has finite flying time: once the orbit
reaches `1` it stays in `{1, 2, 4}`. -/
theorem finiteFlyingTime_of_collatzConjecture (hC : CollatzConjecture) :
    ∀ x, 5 ≤ x → FiniteFlyingTime collatz x := by
  intro x hx
  obtain ⟨k, hk⟩ := hC x (by omega)
  refine ⟨k, fun n hn => ?_⟩
  by_contra hlt
  have : collatz^[n] x = collatz^[n - k] 1 := by
    rw [← hk, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
  have h' : x ≤ collatz^[n - k] 1 := this ▸ hn
  rcases collatz_iterate_one (n - k) with h | h | h <;> omega

/-- **The approach's target is equivalent to the conjecture**: Collatz ⇔ every `x ≥ 5` has finite
flying time under the full Collatz map. -/
theorem collatzConjecture_iff_finiteFlyingTime :
    CollatzConjecture ↔ ∀ x, 5 ≤ x → FiniteFlyingTime collatz x :=
  ⟨finiteFlyingTime_of_collatzConjecture, collatzConjecture_of_finiteFlyingTime⟩

/-- The literal hypothesis "every positive integer has finite flying time" is **false**: each of
`1, 2, 3, 4` reaches `4` and then returns to `4` every three steps, so `T^n(x) ≥ x` infinitely
often. Hence the threshold `x ≥ 5` above. -/
theorem not_finiteFlyingTime_le_four {x : ℕ} (hx0 : 0 < x) (hx4 : x ≤ 4) :
    ¬ FiniteFlyingTime collatz x := by
  have h4 : ∃ j, collatz^[j] x = 4 := by
    rcases (show x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 by omega) with rfl | rfl | rfl | rfl
    · exact ⟨1, by decide⟩
    · exact ⟨2, by decide⟩
    · exact ⟨5, by decide⟩
    · exact ⟨0, rfl⟩
  obtain ⟨j, hj⟩ := h4
  exact not_finiteFlyingTime_of_periodic (p := 3) (by norm_num) hj (by decide) hx4

/-! ### The accelerated (Syracuse) version, as in `results/RESULTS.md` -/

/-- The Syracuse map keeps positive integers positive. -/
lemma syr_pos {a : ℤ} (ha : 0 < a) : 0 < syr a :=
  pos_of_mul_pos_right ((two_pow_gap_mul_syr a).symm ▸ (by omega : (0 : ℤ) < 3 * a + 1))
    (by positivity)

/-- Syracuse iterates of a positive integer stay positive. -/
lemma syr_iterate_pos {a : ℤ} (ha : 0 < a) (n : ℕ) : 0 < syr^[n] a := by
  induction n with
  | zero => exact ha
  | succ n ih => rw [Function.iterate_succ_apply']; exact syr_pos ih

/-- Syracuse iterates of an odd integer stay odd. -/
lemma syr_iterate_odd {a : ℤ} (ha : Odd a) (n : ℕ) : Odd (syr^[n] a) := by
  cases n with
  | zero => exact ha
  | succ n => rw [Function.iterate_succ_apply']; exact syr_odd _

/-- **Descent reduction for the Syracuse map.** If every odd `a > 1` eventually drops below itself
under `syr`, every odd positive integer reaches `1` under `syr`. -/
theorem syr_reaches_one_of_drop (h : ∀ a : ℤ, Odd a → 1 < a → ∃ n, syr^[n] a < a) :
    ∀ a : ℤ, Odd a → 0 < a → ∃ k, syr^[k] a = 1 := by
  suffices ∀ N : ℕ, ∀ a : ℤ, Odd a → 0 < a → a ≤ N → ∃ k, syr^[k] a = 1 from
    fun a ha hpos => this a.toNat a ha hpos (Int.self_le_toNat a)
  intro N
  induction N with
  | zero => intro a _ hpos hN; push_cast at hN; omega
  | succ N ih =>
    intro a ha hpos hN
    rcases (show a = 1 ∨ 1 < a by omega) with rfl | h1
    · exact ⟨0, rfl⟩
    · obtain ⟨n, hn⟩ := h a ha h1
      obtain ⟨k, hk⟩ := ih _ (syr_iterate_odd ha n) (syr_iterate_pos hpos n)
        (by push_cast at hN; omega)
      exact ⟨k + n, by rw [Function.iterate_add_apply, hk]⟩

/-- The Collatz map halves even numbers. -/
lemma collatz_two_mul (m : ℕ) : collatz (2 * m) = m := by
  unfold collatz; split_ifs <;> omega

/-- `g` Collatz steps strip `2^g`: `collatz^[g] (2^g y) = y`. -/
lemma collatz_iterate_two_pow_mul (g y : ℕ) : collatz^[g] (2 ^ g * y) = y := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [Function.iterate_succ_apply, pow_succ, mul_comm (2 ^ g) 2, mul_assoc, collatz_two_mul, ih]

/-- One Syracuse step from an odd `a` is `gap a + 1` steps of the full Collatz map. -/
theorem collatz_iterate_gap_succ {a : ℕ} (ha : Odd a) :
    ((collatz^[gap a + 1] a : ℕ) : ℤ) = syr a := by
  have hs := two_pow_gap_mul_syr a
  have hpos : 0 < syr a := syr_pos (by exact_mod_cast ha.pos)
  obtain ⟨s, hs'⟩ : ∃ s : ℕ, (s : ℤ) = syr a := ⟨(syr a).toNat, Int.toNat_of_nonneg hpos.le⟩
  have hnat : 2 ^ gap a * s = 3 * a + 1 := by rw [← hs'] at hs; exact_mod_cast hs
  have hodd : collatz a = 3 * a + 1 := by simp [collatz, Nat.odd_iff.1 ha]
  rw [Function.iterate_succ_apply, hodd, ← hnat, collatz_iterate_two_pow_mul, hs']

/-- If the Syracuse orbit of an odd positive `a` reaches `1`, so does its full Collatz orbit. -/
theorem collatz_reaches_of_syr (k : ℕ) :
    ∀ a : ℕ, Odd a → syr^[k] (a : ℤ) = 1 → ∃ m, collatz^[m] a = 1 := by
  induction k with
  | zero => intro a _ h; exact ⟨0, by simpa using h⟩
  | succ k ih =>
    intro a ha h
    rw [Function.iterate_succ_apply, ← collatz_iterate_gap_succ ha] at h
    have hso : Odd (collatz^[gap a + 1] a) := by
      have := syr_odd a
      rw [← collatz_iterate_gap_succ ha] at this
      exact (Int.odd_coe_nat _).1 this
    obtain ⟨m, hm⟩ := ih _ hso h
    exact ⟨m + (gap a + 1), by rw [Function.iterate_add_apply, hm]⟩

/-- If every odd positive integer reaches `1` under `syr`, the Collatz conjecture holds. -/
theorem collatzConjecture_of_syr (h : ∀ a : ℤ, Odd a → 0 < a → ∃ k, syr^[k] a = 1) :
    CollatzConjecture := by
  intro n hn
  obtain ⟨j, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  obtain ⟨k, hk⟩ := h m ((Int.odd_coe_nat m).2 hm) (by exact_mod_cast hm.pos)
  obtain ⟨i, hi⟩ := collatz_reaches_of_syr k m hm hk
  exact ⟨i + j, by rw [Function.iterate_add_apply, collatz_iterate_two_pow_mul, hi]⟩

/-- **Flying time ⇒ Collatz, accelerated form** (corrected hypothesis). If every odd `a ≥ 3` has
finite flying time under the Syracuse map `syr`, the Collatz conjecture holds. -/
theorem collatzConjecture_of_finiteFlyingTime_syr
    (h : ∀ a : ℤ, Odd a → 3 ≤ a → FiniteFlyingTime syr a) : CollatzConjecture := by
  refine collatzConjecture_of_syr (syr_reaches_one_of_drop fun a ha h1 => ?_)
  have h3 : 3 ≤ a := by obtain ⟨k, rfl⟩ := ha; omega
  exact ⟨flyingTime syr a + 1, iterate_lt_of_flyingTime_lt (h a ha h3) (Nat.lt_succ_self _)⟩

/-- Under `syr` the only obstruction is `1` itself: it is a fixed point, so it never flies down. -/
theorem not_finiteFlyingTime_syr_one : ¬ FiniteFlyingTime syr 1 :=
  not_finiteFlyingTime_of_periodic (j := 0) (p := 1) one_pos rfl isSyrCycle_one.2.2 le_rfl


end Syracuse.DiophantineDistribution
