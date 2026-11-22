import Syracuse.Approaches.Circuits
import Syracuse.Approaches.StdClass
import Syracuse.Approaches.Renormalize
import Syracuse.Approaches.BalancedClass

/-!
# The closed word classes on all of `ℤ`: only `1`, `-1`, `-5`, `-7`

The two-letter-run theorem (`Circuits.no_cycle_two_letters`), Steiner's circuit theorem
(`Circuits.steiner_of_ellison`) and the re-bracketing results (`Renormalize`) were proved for positive
cycles, the last two also assuming Barina. Here all of them are extended to cycles **of either sign**,
assuming **Ellison only**. Every cycle of the accelerated `3x+1` map on `ℤ` whose gap word lies in one of
the closed classes is one of the known small cycles:

* **two letter runs** `1^a d^b` (`a, b ≥ 1`, `d ≥ 2`): only `-5 → -7` (`two_letter_cycles`);
* **at most one gap `≥ 2`** (circuits and the all-ones word): only `1`, `-1`, `-5 → -7`
  (`few_blocks_cycles`). This is Steiner's theorem on `ℤ`;
* **level-`(u,v)` two-cycles** `u^{a₁} v u^{a₂} v` and **powers** `(u^a v^b)^g` of standard-pair
  two-run words: only `-5 → -7` (`two_cycle_classification`, `std_pair_pow_cycles`). Barina's
  hypothesis is no longer needed, because `StdClass.std_pair_cycles` settles Ellison's exceptional `E`
  by enumeration.

The negative two-letter case needs no window. For a negative cycle `2^E < 3^o`, so
`1000 E < 1585 o` (`sign_linear`, from `3^{1000} < 2^{1585}`). The divisibility
`D ∣ (2^{d-1} - 1)(2^{db} - 3^b)` still gives `|D| < 2^{d-1+db}` (`abs_D_lt`). Ellison and the sign
bound are then incompatible with `E ≥ 28` by linear arithmetic, once the product `db` is bounded below
by `d + 3b - 3`. The cases `E ≤ 27` are a finite check of both signs (`small_check_signed`).

The seven-point cycle `-17` (gap word `1,1,1,2,1,1,4`, two gaps `≥ 2` of different sizes) lies outside
every class closed here. It is a negative Simons 2-cycle with distinct big letters.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `2^E < 3^o ⇒ 1000 E < 1585 o` | `sign_linear` | proved |
| `|D| < 2^{d-1+db}` on a cycle of either sign with word `1^a d^b` | `abs_D_lt` | proved |
| no `1^a d^b` (`d ≥ 3`, `E ≤ 27`) has `D ∣ S`, either sign | `small_check_signed` | proved (`decide +kernel`) |
| no negative cycle on `1^a d^b`, `d ≥ 3` | `no_neg_cycle_one_d` | proved (conditional on `Ellison1971`) |
| the only cycle on `1^a d^b` (`d ≥ 2`, either sign) is `-5 → -7` | `two_letter_cycles` | proved (conditional on `Ellison1971`) |
| a cycle with all gaps `1` is `-1` | `all_ones_cycle` | proved |
| the cycles with at most one gap `≥ 2` are `1`, `-1`, `-5`, `-7` (Steiner on `ℤ`) | `few_blocks_cycles` | proved (conditional on `Ellison1971`) |
| rotating a power is powering a rotation | `rotate_bpow` | proved |
| a cycle on a rotation of `Z^g` is a cycle on a rotation of `Z`, same point | `cycle_of_pow` | proved |
| level-`(u,v)` two-cycles, either sign: only `-5 → -7` | `two_cycle_classification` | proved (conditional on `Ellison1971`) |
| powers of standard two-run words, either sign: only `-5 → -7` | `std_pair_pow_cycles` | proved (conditional on `Ellison1971`) |
| every cycle on `ℤ` with a word in a closed class is `1`, `-1`, `-5` or `-7` | `closed_classes` | proved (conditional on `Ellison1971`) |
| the `-17` cycle's word is in no closed class | `neg_seventeen_outside` | proved (conditional on `Ellison1971`) |
-/

namespace Syracuse.SignedCycles

open Syracuse Syracuse.TwoBackground Syracuse.Circuits Syracuse.StdPairs

/-! ## Two letter runs, negative sign -/

/-- **Sign, linearised.** `2^E < 3^o` forces `1000·E < 1585·o`, because `3^{1000} < 2^{1585}`. -/
theorem sign_linear {E o : ℕ} (h : 2 ^ E < 3 ^ o) : 1000 * E < 1585 * o := by
  by_contra hc
  replace hc := not_lt.mp hc
  have h1 : 2 ^ (1585 * o) ≤ 2 ^ (1000 * E) := Nat.pow_le_pow_right (by norm_num) hc
  have h2 : 2 ^ (1000 * E) < 3 ^ (1000 * o) := by
    rw [mul_comm 1000 E, mul_comm 1000 o, pow_mul, pow_mul]
    exact Nat.pow_lt_pow_left h (by norm_num)
  have h3 : 3 ^ (1000 * o) ≤ 2 ^ (1585 * o) := by
    rw [pow_mul, pow_mul]
    exact Nat.pow_le_pow_left (by decide +kernel) o
  exact absurd (lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)) (lt_irrefl _)

/-- A cycle through a negative point has `D < 0`. -/
lemma Dz_neg {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : x < 0) : Dz (gapWord x o) < 0 := by
  have hS := CycleLiterature.Sz_pos (CycleLiterature.cycle_gapWord_ne_nil h)
  rw [← h.cycle_equation] at hS
  by_contra hc
  nlinarith

/-- **Upper bound, either sign.** On a cycle whose word is a rotation of `1^a d^b` (`d ≥ 2`, `b ≥ 1`),
`|D| < 2^{d - 1 + db}`. -/
theorem abs_D_lt {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {a b d : ℕ} (hd : 2 ≤ d) (hb : 1 ≤ b)
    (hw : gapWord x o ~r two 1 d a b) : |Dz (two 1 d a b)| < 2 ^ (d - 1 + d * b) := by
  have hdv := dvd_cV h hd (by omega) hw
  have hc1 : (1 : ℤ) ≤ 2 ^ (d - 1) - 1 := by
    have : (2 : ℤ) ^ 1 ≤ 2 ^ (d - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hV : (0 : ℤ) < 2 ^ (d * b) - 3 ^ b := by
    have : (3 : ℤ) ^ b < 4 ^ b := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    have : (4 : ℤ) ^ b ≤ 2 ^ (d * b) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right b hd)
    linarith
  have hle := Int.le_of_dvd (mul_pos (by linarith) hV) ((abs_dvd _ _).2 hdv)
  calc |Dz (two 1 d a b)| ≤ (2 ^ (d - 1) - 1) * (2 ^ (d * b) - 3 ^ b) := hle
    _ < 2 ^ (d - 1) * 2 ^ (d * b) := by
        have h3 : (0 : ℤ) < 3 ^ b := by positivity
        nlinarith
    _ = 2 ^ (d - 1 + d * b) := by rw [pow_add]

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Small cases, both signs** (`E ≤ 27`): no `1^a d^b` with `d ≥ 3` satisfies `D ∣ S`. -/
theorem small_check_signed : ∀ a : ℕ, a < 28 → ∀ b : ℕ, b < 14 → ∀ d : ℕ, d < 28 →
    (1 ≤ a ∧ 1 ≤ b ∧ 3 ≤ d ∧ a + d * b ≤ 27) →
    Sz (two 1 d a b) % Dz (two 1 d a b) ≠ 0 := by
  decide +kernel

/-- **No negative cycle on `1^a d^b` with `d ≥ 3`**, conditional on Ellison. -/
theorem no_neg_cycle_one_d (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (hx : x < 0) {a b d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 3 ≤ d)
    (hw : gapWord x o ~r two 1 d a b) : False := by
  have hS := dvd_S_of_rotated h hw
  have hDeq : Dz (two 1 d a b) = Dz (gapWord x o) := by
    obtain ⟨n, hn⟩ := hw; rw [← hn]; exact D_rotate _ _ _ _
  have hD : Dz (two 1 d a b) < 0 := hDeq ▸ Dz_neg h hx
  have hlen : o = a + b := by
    have := hw.perm.length_eq; rw [gapWord_length, two_length] at this; exact this
  by_cases hE : a + d * b ≤ 27
  · exact small_check_signed a (by omega) b (by nlinarith) d (by nlinarith) ⟨ha, hb, hd, hE⟩
      (Int.emod_eq_zero_of_dvd hS)
  replace hE := not_le.mp hE
  have hDf : Dz (two 1 d a b) = 2 ^ (a + d * b) - 3 ^ (a + b) := by
    simp only [Dz, D, two_sum, two_length]
  -- the sign: `1000 E < 1585 o`
  have hsgn : 2 ^ (a + d * b) < 3 ^ (a + b) := by
    have : (2 : ℤ) ^ (a + d * b) < 3 ^ (a + b) := by rw [hDf] at hD; linarith
    exact_mod_cast this
  have hS1 : (1000 * (a + d * b) : ℤ) < 1585 * (a + b) := by exact_mod_cast sign_linear hsgn
  -- the product `db` from below
  have hmc : (d + 3 * b - 3 : ℤ) ≤ d * b := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 3 by omega) (show (0 : ℤ) ≤ b - 1 by omega)]
  have hE' : (28 : ℤ) ≤ a + d * b := by exact_mod_cast hE
  rcases Nat.lt_or_ge a d with had | had
  · -- `a < d`: the sign bound alone
    have : (a + 1 : ℤ) ≤ d := by exact_mod_cast had
    nlinarith
  · -- `a ≥ d`: Ellison
    have hnot : a + d * b ∉ CycleLiterature.ellisonExceptions := by
      simp only [CycleLiterature.ellisonExceptions, Finset.mem_insert, Finset.mem_singleton]; omega
    have hEl' := hEl (a + d * b) (a + b) (by omega) (by omega) hnot
    have habs : |(2 : ℝ) ^ (a + d * b) - 3 ^ (a + b)| < 2 ^ (d - 1 + d * b) := by
      have := abs_D_lt h (by omega) hb hw
      rw [hDf] at this; exact_mod_cast this
    have hL := ellison_linear (by omega) had hEl' habs
    have : (d : ℤ) ≤ a := by exact_mod_cast had
    nlinarith

/-- `u^n` for a one-letter word is a run. -/
lemma bpow_singleton (d n : ℕ) : bpow [d] n = List.replicate n d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Renormalize.bpow_succ, ih, List.replicate_succ]; rfl

/-- A cycle point is odd, hence nonzero. -/
lemma ne_zero_of_cycle {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) : x ≠ 0 := by
  rintro rfl; obtain ⟨k, hk⟩ := h.2.1; omega

/-- **Two letter runs, both signs.** Given Ellison, the only cycle of the accelerated `3x+1` map on
`ℤ` whose gap word is a rotation of `1^a d^b` (`a, b ≥ 1`, `d ≥ 2`) is `-5 → -7`. -/
theorem two_letter_cycles (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    {a b d : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hd : 2 ≤ d) (hw : gapWord x o ~r two 1 d a b) :
    x = -5 ∨ x = -7 := by
  rcases Nat.lt_or_ge d 3 with h2 | h3
  · obtain rfl : d = 2 := by omega
    refine StdClass.std_pair_cycles hEl StdPair.base h ha hb ?_
    rwa [bpow_singleton, bpow_singleton]
  · rcases lt_trichotomy x 0 with hneg | h0 | hpos
    · exact (no_neg_cycle_one_d hEl h hneg ha hb h3 hw).elim
    · exact absurd h0 (ne_zero_of_cycle h)
    · exact (no_cycle_one_d hEl h hpos ha hb h3 hw).elim

/-! ## Circuits on `ℤ` -/

/-- **All gaps `1`.** A cycle whose gap word is `1^o` is the fixed point `-1`. -/
theorem all_ones_cycle {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (h0 : CycleLiterature.numBlocks (gapWord x o) = 0) : x = -1 := by
  have hp := CocycleCombine.IsSyrCycle.pos h
  have ho : 0 < o := h.1
  have hall : ∀ g ∈ gapWord x o, g = 1 := by
    intro g hg
    have := List.countP_eq_zero.1 h0 g hg
    have := hp g hg
    simp at *; omega
  have hrep : gapWord x o = List.replicate o 1 := by
    rw [List.eq_replicate_iff]; exact ⟨gapWord_length x o, hall⟩
  have hceq := h.cycle_equation
  have hS := BoundedDefectLever.S_replicate_mul (2 : ℤ) 3 1 o
  rw [hrep] at hceq
  simp only [Dz, Sz, D, List.sum_replicate, List.length_replicate, smul_eq_mul, mul_one] at hceq
  simp only [mul_one, pow_one] at hS
  have hD : (2 : ℤ) ^ o - 3 ^ o ≠ 0 := by
    have : (2 : ℤ) ^ o < 3 ^ o := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    linarith
  have : ((2 : ℤ) ^ o - 3 ^ o) * (x + 1) = 0 := by linear_combination hceq - hS
  have := (mul_eq_zero.1 this).resolve_left hD
  linarith

/-- **Steiner's theorem on `ℤ`.** Given Ellison, the cycles of the accelerated `3x+1` map on `ℤ` with
at most one gap `≥ 2` are exactly those through `1`, `-1`, `-5` and `-7`. -/
theorem few_blocks_cycles (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (hb : CycleLiterature.numBlocks (gapWord x o) ≤ 1) : x = 1 ∨ x = -1 ∨ x = -5 ∨ x = -7 := by
  rcases Nat.lt_or_ge (CycleLiterature.numBlocks (gapWord x o)) 1 with h0 | h1
  · exact Or.inr (Or.inl (all_ones_cycle h (by omega)))
  obtain ⟨d, hd, hrot⟩ :=
    isRotated_circuit (CocycleCombine.IsSyrCycle.pos h) (by omega : CycleLiterature.numBlocks _ = 1)
  rw [gapWord_length] at hrot
  rcases Nat.lt_or_ge o 2 with ho | ho
  · -- one point: `(2^d - 3)·x = 1`
    have : o = 1 := by have := h.1; omega
    subst this
    rcases lt_or_gt_of_ne (ne_zero_of_cycle h) with hneg | hpos
    · exfalso
      have hceq := h.cycle_equation
      have hDeq : Dz (gapWord x 1) = Dz (two 1 d 0 1) := by
        obtain ⟨n, hn⟩ := hrot.symm; rw [← hn]; exact D_rotate _ _ _ _
      have hS1 : Sz (gapWord x 1) = 1 := by simp [gapWord, Sz]
      rw [hDeq, hS1] at hceq
      simp only [Dz, D, two_sum, two_length] at hceq
      have : (4 : ℤ) ≤ 2 ^ (0 + d * 1) := by
        rw [show (4 : ℤ) = 2 ^ 2 by norm_num]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      rw [show (3 : ℤ) ^ (0 + 1) = 3 by norm_num] at hceq
      have hx1 : x ≤ -1 := by omega
      nlinarith
    · exact Or.inl (CycleLiterature.period_one_pos hpos h).1
  · have := two_letter_cycles hEl h (by omega) le_rfl hd hrot
    tauto

/-! ## Powers and level-`(u,v)` two-cycles, both signs, without Barina -/

/-- `Z₀ (z Z₀)^k z = (Z₀ z)^{k+1}`. -/
lemma conj_bpow (z : ℕ) (Z₀ : Word) (k : ℕ) :
    Z₀ ++ bpow (z :: Z₀) k ++ [z] = bpow (Z₀ ++ [z]) (k + 1) := by
  induction k with
  | zero => simp [bpow, CocycleCombine.wpow]
  | succ k ih =>
    rw [Renormalize.bpow_succ, Renormalize.bpow_succ (Z₀ ++ [z]) (k + 1), ← ih]
    simp [List.append_assoc]

/-- Rotating a power by one letter powers the rotated word. -/
lemma rotate_one_bpow (Z : Word) (g : ℕ) : (bpow Z g).rotate 1 = bpow (Z.rotate 1) g := by
  rcases g with _ | k
  · simp [bpow, CocycleCombine.wpow]
  cases Z with
  | nil => simp [bpow, CocycleCombine.wpow]
  | cons z Z₀ =>
    rw [Renormalize.bpow_succ, List.cons_append, rotate_one_cons, rotate_one_cons, conj_bpow]

/-- **Rotating a power is powering a rotation.** -/
theorem rotate_bpow (Z : Word) (g n : ℕ) : (bpow Z g).rotate n = bpow (Z.rotate n) g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← List.rotate_rotate, ih, rotate_one_bpow, List.rotate_rotate]

/-- **Power reduction, either sign.** If the gap word of a cycle through `x` is a rotation of `Z^g`
(`g ≥ 1`, `Z` positive and nonempty), then `x` is also a cycle point of period `|Z'|` whose gap word is
a rotation `Z'` of `Z`. -/
theorem cycle_of_pow {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {Z : Word} (hZ : Z.Pos) (hZ0 : Z ≠ [])
    {g : ℕ} (hg : 1 ≤ g) (hw : gapWord x o ~r bpow Z g) :
    ∃ Z' : Word, Z' ~r Z ∧ IsSyrCycle x Z'.length ∧ gapWord x Z'.length = Z' := by
  obtain ⟨m, hm⟩ := hw.symm
  rw [rotate_bpow] at hm
  set Z' := Z.rotate m
  have hZ'r : Z' ~r Z := List.IsRotated.symm ⟨m, rfl⟩
  have hZ' : Word.Pos Z' := fun d hd => hZ d ((List.rotate_perm Z m).subset hd)
  have hZ'0 : Z' ≠ [] := by simpa [Z'] using hZ0
  have hceq := h.cycle_equation
  rw [← hm] at hceq
  have hSZ := CocycleCombine.S_wpow (2 : ℤ) 3 Z' g
  have hDZ := CocycleCombine.D_wpow (2 : ℤ) 3 Z' g
  have hgeo_pos : 0 < CocycleCombine.geo (2 : ℤ) 3 Z' g := by
    rw [CocycleCombine.geo_eq_sum (2 : ℤ) 3]
    exact Finset.sum_pos (fun i _ => by positivity) (by simp; omega)
  have hc : Dz Z' * x = Sz Z' := by
    simp only [Dz, Sz, bpow] at hceq ⊢
    rw [hSZ, hDZ] at hceq
    have : (D 2 3 Z' * x - S 2 3 Z') * CocycleCombine.geo (2 : ℤ) 3 Z' g = 0 := by
      linear_combination hceq
    have := (mul_eq_zero.1 this).resolve_right hgeo_pos.ne'
    linarith
  obtain ⟨hcyc, hgw⟩ := CycleLiterature.isSyrCycle_of_dvd hZ' hZ'0 ⟨x, hc.symm⟩
  have hx : Sz Z' / Dz Z' = x := by
    rw [← hc, Int.mul_ediv_cancel_left _ (Dz_ne_zero hZ'0)]
  rw [hx] at hcyc hgw
  exact ⟨Z', hZ'r, hcyc, hgw⟩

/-- **Level-`(u,v)` two-cycles, both signs.** Given Ellison, the only cycle on `ℤ` whose gap word is a
rotation of `u^{a₁} v u^{a₂} v` (standard pair, `a₁, a₂ ≥ 1`) is `-5 → -7`. -/
theorem two_cycle_classification (hEl : CycleLiterature.Ellison1971) {u v : Word} (hst : StdPair u v)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {a₁ a₂ : ℕ} (h1 : 1 ≤ a₁) (h2 : 1 ≤ a₂)
    (hw : gapWord x o ~r (bpow u a₁ ++ v) ++ (bpow u a₂ ++ v)) : x = -5 ∨ x = -7 := by
  obtain ⟨hu, hv, hu0, hv0⟩ := hst.pos
  have unequal : ∀ b₁ b₂ : ℕ, b₂ < b₁ → gapWord x o ~r (bpow u b₁ ++ v) ++ (bpow u b₂ ++ v) →
      x = -5 ∨ x = -7 := by
    intro b₁ b₂ hlt hw'
    set Z := bpow u b₂ ++ v
    have hst' : StdPair u Z := Renormalize.stdPair_left_pow hst b₂
    have heq : (bpow u b₁ ++ v) ++ (bpow u b₂ ++ v) = bpow u (b₁ - b₂) ++ bpow Z 2 := by
      rw [Renormalize.bpow_two, show b₁ = (b₁ - b₂) + b₂ by omega, Renormalize.bpow_add]
      simp [Z]
    rw [heq] at hw'
    exact StdClass.std_pair_cycles hEl hst' h (by omega) (by norm_num) hw'
  rcases lt_trichotomy a₁ a₂ with hlt | heq | hgt
  · exact unequal a₂ a₁ hlt (hw.trans List.isRotated_append)
  · subst heq
    set Z := bpow u a₁ ++ v
    have hZpos : Z.Pos := fun d hd => by
      simp only [Z, List.mem_append] at hd; rcases hd with hd | hd
      · exact pos_bpow hu a₁ d hd
      · exact hv d hd
    have hZ0 : Z ≠ [] := by simp [Z, hv0]
    rw [← Renormalize.bpow_two] at hw
    obtain ⟨Z', hZ'r, hcyc, hgw⟩ := cycle_of_pow h hZpos hZ0 (by norm_num) hw
    refine StdClass.std_pair_cycles hEl hst hcyc h1 le_rfl ?_
    rw [hgw, Renormalize.bpow_one]; exact hZ'r
  · exact unequal a₁ a₂ hgt hw

/-- **Powers of standard two-run words, both signs.** Given Ellison, the only cycle on `ℤ` whose gap
word is a rotation of `(u^a v^b)^g` (standard pair, `a, b, g ≥ 1`) is `-5 → -7`. -/
theorem std_pair_pow_cycles (hEl : CycleLiterature.Ellison1971) {u v : Word} (hst : StdPair u v)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {a b g : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hg : 1 ≤ g)
    (hw : gapWord x o ~r bpow (bpow u a ++ bpow v b) g) : x = -5 ∨ x = -7 := by
  obtain ⟨hu, hv, -, hv0⟩ := hst.pos
  set Z := bpow u a ++ bpow v b
  have hZpos : Z.Pos := fun d hd => by
    simp only [Z, List.mem_append] at hd; rcases hd with hd | hd
    · exact pos_bpow hu a d hd
    · exact pos_bpow hv b d hd
  have hZ0 : Z ≠ [] := by
    intro h0
    have : bpow v b = [] := (List.append_eq_nil_iff.1 h0).2
    have := congrArg List.length this
    simp [bpow, CocycleCombine.wpow_length] at this
    rcases this with h1 | h1
    · omega
    · exact hv0 h1
  obtain ⟨Z', hZ'r, hcyc, hgw⟩ := cycle_of_pow h hZpos hZ0 hg hw
  exact StdClass.std_pair_cycles hEl hst hcyc ha hb (by rw [hgw]; exact hZ'r)

/-! ## One statement -/

/-- The word classes now closed on all of `ℤ`: balanced parity vector, at most one gap `≥ 2`, two letter
runs, powers of standard-pair two-run words, and level-`(u,v)` two-cycles. -/
def ClosedClass (w : Word) : Prop :=
  Balanced.CircBalanced (CocycleCombine.pv w) ∨ CycleLiterature.numBlocks w ≤ 1 ∨
  (∃ a b d : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 2 ≤ d ∧ w ~r two 1 d a b) ∨
  (∃ (u v : Word) (a b g : ℕ), StdPair u v ∧ 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ g ∧
    w ~r bpow (bpow u a ++ bpow v b) g) ∨
  (∃ (u v : Word) (a₁ a₂ : ℕ), StdPair u v ∧ 1 ≤ a₁ ∧ 1 ≤ a₂ ∧
    w ~r (bpow u a₁ ++ v) ++ (bpow u a₂ ++ v))

/-- **The closed classes on `ℤ`.** Given Ellison, every cycle of the accelerated `3x+1` map on `ℤ`
whose gap word lies in a closed class is the cycle through `1`, `-1`, `-5` or `-7`. -/
theorem closed_classes (hEl : CycleLiterature.Ellison1971) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (hc : ClosedClass (gapWord x o)) : x = 1 ∨ x = -1 ∨ x = -5 ∨ x = -7 := by
  rcases hc with hb | hb | ⟨a, b, d, ha, hb, hd, hw⟩ | ⟨u, v, a, b, g, hst, ha, hb, hg, hw⟩ |
      ⟨u, v, a₁, a₂, hst, h1, h2, hw⟩
  · exact BalancedClass.balanced_cycle_classification h hb
  · exact few_blocks_cycles hEl h hb
  · have := two_letter_cycles hEl h ha hb hd hw; tauto
  · have := std_pair_pow_cycles hEl hst h ha hb hg hw; tauto
  · have := two_cycle_classification hEl hst h h1 h2 hw; tauto

/-- **The `-17` cycle lies outside every closed class** (given Ellison): its gap word
`1,1,1,2,1,1,4` is in none of them, so the closed classes do not exhaust the cycles on `ℤ`. -/
theorem neg_seventeen_outside (hEl : CycleLiterature.Ellison1971) :
    ¬ ClosedClass (gapWord (-17) 7) := by
  intro hc
  have := closed_classes hEl CycleLiterature.isSyrCycle_neg_seventeen.1 hc
  omega

end Syracuse.SignedCycles
