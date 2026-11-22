import Syracuse.Approaches.CocycleCombine
import Syracuse.Approaches.Program
import Syracuse.Approaches.CycleLiterature

/-!
# Christoffel words and Knight's theorem on high cycles

`CocycleCombine.knight_cycle` (structure.md C9) proves `|2^E - 3^o| = 1` for a genuine cycle whose
parity vector is, up to rotation, *both* `1u0` and `0u1`. For the high cycle, whose parity vector is
the upper Christoffel word, this was left conditional on Cohn's theorem ("the reverse of a
Christoffel word is a rotation of it"). This file proves the input that is actually needed,
elementarily for coprime slopes, and so closes the ledger item.

With mechanical words `m_c(i) = ⌊((i+1)p + c)/n⌋ - ⌊(ip + c)/n⌋`:

* `lower p n` (phase `0`) is `0u1` and `upper p n` (phase `n - 1`, i.e. ceilings) is `1u0`, with
  the **same** middle `u`, because `ip/n` is never an integer for `0 < i < n` (`christoffel_shape`).
* Shifting the index by `j` shifts the phase by `jp`, and the phase only matters mod `n`. For
  `gcd(p, n) = 1`, some `j` has `jp ≡ n - 1`, so `lower` and `upper` are rotations of each other
  (`lower_isRotated_upper`).

Consequence (Knight 2023, *no high cycles*): a positive cycle with coprime `(o, E)` whose parity
vector is a rotation of the upper Christoffel word of slope `o/E` is the trivial cycle `1 → 1`
(`no_high_cycle`). The finish is the cheap-arithmetic step `2^E - 3^o = 1 ⇒ (E, o) = (2, 1)`
(Gersonides; `two_pow_eq_three_pow_add_one`).

## Coverage

| Claim (source) | Lean name | Status |
|---|---|---|
| mechanical word: index shift = phase shift, phase mod `n` | `mech_shift`, `mech_phase_mod`, `mech_index_mod` | proved |
| rotations of a mechanical word are mechanical words | `word_rotate` | proved |
| upper/lower Christoffel words share the middle: `1u0`, `0u1` (Christoffel / Cohn) | `christoffel_shape` | proved (coprime, `0 < p < n`) |
| upper and lower Christoffel words are conjugate (Cohn 1972 via Berstel et al.) | `lower_isRotated_upper` | proved (coprime) |
| `2^E = 3^o + 1 ⇒ (E, o) ∈ {(1,0), (2,1)}` (Gersonides) | `two_pow_eq_three_pow_add_one` | proved |
| Knight: no nontrivial positive high cycle (structure.md C9, `knight_cycle` made unconditional) | `no_high_cycle` | proved (coprime `(o, E)`) |
-/

namespace Syracuse.Christoffel

open Syracuse

/-- Letter `i` of the mechanical word of slope `p/n` and phase `c`:
`true` iff `⌊((i+1)p + c)/n⌋ > ⌊(ip + c)/n⌋`. -/
def mech (p n c i : ℕ) : Bool := decide ((i * p + c) / n < ((i + 1) * p + c) / n)

/-- The mechanical word of length `n`, slope `p/n`, phase `c`. -/
def word (p n c : ℕ) : List Bool := (List.range n).map (mech p n c)

/-- The lower Christoffel word (floors, phase `0`). -/
def lower (p n : ℕ) : List Bool := word p n 0

/-- The upper Christoffel word (ceilings `⌈ip/n⌉ = ⌊(ip + n - 1)/n⌋`, phase `n - 1`). -/
def upper (p n : ℕ) : List Bool := word p n (n - 1)

variable {p n c : ℕ}

@[simp] lemma word_length : (word p n c).length = n := by simp [word]

/-- Shifting the index by `j` shifts the phase by `jp`. -/
lemma mech_shift (i j : ℕ) : mech p n c (i + j) = mech p n (c + j * p) i := by
  have h1 : (i + j) * p + c = i * p + (c + j * p) := by ring
  have h2 : (i + j + 1) * p + c = (i + 1) * p + (c + j * p) := by ring
  simp only [mech, h1, h2]

/-- The phase only matters modulo `n`. -/
lemma mech_phase_add (hn : 0 < n) (i : ℕ) : mech p n (c + n) i = mech p n c i := by
  simp only [mech, ← add_assoc, Nat.add_div_right _ hn, Nat.add_lt_add_iff_right]

/-- The phase only matters modulo `n`. -/
lemma mech_phase_mod (hn : 0 < n) (i : ℕ) : mech p n (c % n) i = mech p n c i := by
  conv_rhs => rw [← Nat.mod_add_div c n]
  generalize c / n = k
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, mech_phase_add hn, ih]

/-- The index is periodic with period `n`. -/
lemma mech_index_add (hn : 0 < n) (i : ℕ) : mech p n c (i + n) = mech p n c i := by
  have h1 : (i + n) * p + c = (i * p + c) + n * p := by ring
  have h2 : (i + n + 1) * p + c = ((i + 1) * p + c) + n * p := by ring
  simp only [mech, h1, h2, Nat.add_mul_div_left _ _ hn, Nat.add_lt_add_iff_right]

/-- The index only matters modulo `n`. -/
lemma mech_index_mod (hn : 0 < n) (i : ℕ) : mech p n c (i % n) = mech p n c i := by
  conv_rhs => rw [← Nat.mod_add_div i n]
  generalize i / n = k
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, mech_index_add hn, ih]

/-- **Rotations of mechanical words are mechanical words**: rotating by `j` adds `jp` to the phase. -/
theorem word_rotate (hn : 0 < n) (j : ℕ) : (word p n c).rotate j = word p n (c + j * p) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_rotate, word, List.getElem_map, List.getElem_range, List.length_map,
      List.length_range]
    rw [mech_index_mod hn, mech_shift]

/-- The phase of a mechanical word only matters modulo `n`. -/
lemma word_phase_mod (hn : 0 < n) : word p n (c % n) = word p n c := by
  simp only [word]
  exact List.map_congr_left fun i _ => mech_phase_mod hn i

/-- **Upper and lower Christoffel words are conjugate** for coprime slope: some rotation of
`lower p n` is `upper p n`. -/
theorem lower_isRotated_upper (hn : 1 < n) (hc : Nat.Coprime p n) : lower p n ~r upper p n := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hn
  refine ⟨m * (n - 1), ?_⟩
  rw [lower, word_rotate (by omega), zero_add, ← word_phase_mod (by omega), upper]
  congr 1
  have : m * (n - 1) * p = (p * m) * (n - 1) := by ring
  rw [this, Nat.mul_mod, hm, one_mul, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]

/-- Ceiling step: if `n ∤ m` then `⌊(m + n - 1)/n⌋ = ⌊m/n⌋ + 1`. -/
lemma add_pred_div_of_not_dvd (hn : 0 < n) {m : ℕ} (h : m % n ≠ 0) :
    (m + (n - 1)) / n = m / n + 1 := by
  have hm := Nat.mod_add_div m n
  have hr := Nat.mod_lt m hn
  rw [show m + (n - 1) = (m % n - 1) + n * (m / n + 1) by
    conv_lhs => rw [← hm]
    rw [Nat.mul_succ]; omega]
  rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt (by omega), zero_add]

/-- For coprime `p, n` and `0 < i < n`, `ip` is not a multiple of `n`. -/
lemma mul_mod_ne_zero (hc : Nat.Coprime p n) {i : ℕ} (hi : 0 < i) (hin : i < n) :
    (i * p) % n ≠ 0 := by
  intro h
  have : n ∣ i := (Nat.Coprime.symm hc).dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero h)
  exact absurd (Nat.le_of_dvd hi this) (by omega)

/-- In the middle (`0 < i`, `i + 1 < n`) the lower and upper Christoffel words agree. -/
lemma mech_lower_eq_upper (hc : Nat.Coprime p n) {i : ℕ} (hi : 0 < i) (hin : i + 1 < n) :
    mech p n 0 i = mech p n (n - 1) i := by
  have hn : 0 < n := by omega
  simp only [mech, add_zero]
  rw [add_pred_div_of_not_dvd hn (mul_mod_ne_zero hc hi (by omega)),
    add_pred_div_of_not_dvd hn (mul_mod_ne_zero hc (by omega) hin)]
  simp

/-- The lower Christoffel word starts with `0`. -/
lemma mech_lower_first (hpn : p < n) : mech p n 0 0 = false := by
  simp [mech, Nat.div_eq_of_lt hpn]

/-- The upper Christoffel word starts with `1`. -/
lemma mech_upper_first (hp : 0 < p) (hpn : p < n) : mech p n (n - 1) 0 = true := by
  have h1 : (n - 1) / n = 0 := Nat.div_eq_of_lt (by omega)
  have h2 : (p + (n - 1)) / n = 1 := by
    rw [show p + (n - 1) = (p - 1) + n * 1 by omega, Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt (by omega)]
  simp [mech, h1, h2]

/-- The lower Christoffel word ends with `1`. -/
lemma mech_lower_last (hp : 0 < p) (hn : 0 < n) : mech p n 0 (n - 1) = true := by
  have h1 : (n - 1 + 1) * p / n = p := by
    rw [Nat.sub_add_cancel hn, Nat.mul_div_cancel_left _ hn]
  have h2 : (n - 1) * p / n < p := by
    rw [Nat.div_lt_iff_lt_mul hn]
    have : (n - 1) * p < n * p := Nat.mul_lt_mul_of_pos_right (by omega) hp
    linarith [mul_comm n p]
  simp [mech, h1, h2]

/-- The upper Christoffel word ends with `0`. -/
lemma mech_upper_last (hpn : p < n) : mech p n (n - 1) (n - 1) = false := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hq : p ≤ q := by omega
  have h1 : (q * p + q) / (q + 1) = p :=
    Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  have h2 : ((q + 1) * p + q) / (q + 1) = p :=
    Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  simp [mech, h1, h2]

/-- **Christoffel shape**: for coprime `0 < p < n`, the upper Christoffel word is `1u0` and the
lower one is `0u1`, with the same middle `u`. -/
theorem christoffel_shape (hp : 0 < p) (hpn : p < n) (hc : Nat.Coprime p n) :
    ∃ u, upper p n = true :: (u ++ [false]) ∧ lower p n = false :: (u ++ [true]) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hr : List.range (m + 2) = 0 :: ((List.range m).map Nat.succ ++ [m + 1]) := by
    rw [List.range_succ, List.range_succ_eq_map]; rfl
  have hlast : m + 2 - 1 = m + 1 := by omega
  refine ⟨(List.range m).map (fun i => mech p (m + 2) 0 (i + 1)), ?_, ?_⟩
  · simp only [upper, word, hr, List.map_cons, List.map_append, List.map_map]
    rw [mech_upper_first hp hpn, ← hlast, mech_upper_last hpn]
    congr 2
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.1 hi
    simp only [Function.comp_apply, Nat.succ_eq_add_one, hlast]
    exact (mech_lower_eq_upper hc (by omega) (by omega)).symm
  · simp only [lower, word, hr, List.map_cons, List.map_append, List.map_map]
    rw [mech_lower_first hpn, show m + 1 = m + 2 - 1 by omega, mech_lower_last hp (by omega)]
    rfl

/-! ## Knight's theorem: no nontrivial positive high cycle -/

/-- `3^o mod 8 ∈ {1, 3}`. -/
lemma three_pow_mod_eight (o : ℕ) : 3 ^ o % 8 = 1 ∨ 3 ^ o % 8 = 3 := by
  induction o with
  | zero => simp
  | succ o ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> simp

/-- **Gersonides**: `2^E = 3^o + 1` only for `(E, o) = (1, 0)` or `(2, 1)`. -/
theorem two_pow_eq_three_pow_add_one {E o : ℕ} (h : 2 ^ E = 3 ^ o + 1) :
    (E = 1 ∧ o = 0) ∨ (E = 2 ∧ o = 1) := by
  rcases Nat.lt_or_ge E 3 with hE | hE
  · interval_cases E
    · have := Nat.one_le_pow o 3 (by norm_num); omega
    · left; refine ⟨rfl, ?_⟩
      have h1 : 3 ^ o = 3 ^ 0 := by simpa using h
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
    · right; refine ⟨rfl, ?_⟩
      have h1 : 3 ^ o = 3 ^ 1 := by simpa using h
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
  · exfalso
    have h8 : 8 ∣ 2 ^ E := by
      rw [show E = 3 + (E - 3) by omega, pow_add]; exact dvd_mul_right _ _
    rw [h] at h8
    rcases three_pow_mod_eight o with h3 | h3 <;> omega

/-- **Knight's theorem** (no high cycles, Knight 2023; structure.md C9 made unconditional): a
positive Syracuse cycle with coprime `(o, E)` whose parity vector is a rotation of the upper
Christoffel word of slope `o/E` is the trivial cycle. -/
theorem no_high_cycle {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hcop : Nat.Coprime o (gapWord x o).sum)
    (hC : CocycleCombine.pv (gapWord x o) ~r upper o (gapWord x o).sum) : x = 1 := by
  set E := (gapWord x o).sum with hE
  have ho : 0 < o := h.1
  -- `o < E` from `3^o < 2^E`
  have h32 := Program.three_pow_lt_two_pow h hx
  have hoE : o < E := by
    by_contra hle
    replace hle := not_lt.mp hle
    have : (2 : ℤ) ^ E ≤ 2 ^ o := pow_le_pow_right₀ (by norm_num) hle
    have : (2 : ℤ) ^ o ≤ 3 ^ o := pow_le_pow_left₀ (by norm_num) (by norm_num) o
    linarith
  obtain ⟨u, hu, hl⟩ := christoffel_shape ho hoE hcop
  have h1 : CocycleCombine.pv (gapWord x o) ~r true :: (u ++ [false]) := hu ▸ hC
  have h2 : CocycleCombine.pv (gapWord x o) ~r false :: (u ++ [true]) :=
    hl ▸ hC.trans (lower_isRotated_upper (by omega) hcop).symm
  have hD1 := CocycleCombine.knight_cycle h u h1 h2
  have hDpos := CycleLiterature.cycle_Dz_pos h hx
  have hD : Dz (gapWord x o) = 1 := by omega
  have hnat : 2 ^ E = 3 ^ o + 1 := by
    have : (2 : ℤ) ^ E - 3 ^ o = 1 := by simpa [Dz, D] using hD
    exact_mod_cast (by linarith : (2 : ℤ) ^ E = 3 ^ o + 1)
  rcases two_pow_eq_three_pow_add_one hnat with ⟨-, h0⟩ | ⟨-, h1o⟩
  · omega
  · subst h1o
    exact (CycleLiterature.period_one_pos hx h).1

end Syracuse.Christoffel
