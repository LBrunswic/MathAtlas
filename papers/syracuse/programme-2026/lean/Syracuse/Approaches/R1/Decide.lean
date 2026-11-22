import Syracuse.Approaches.R1.Family
import Syracuse.Approaches.CycleLiterature

/-!
# A verified total decision procedure for cycles in r = 1 families

`decideR1 F` computes the exact set of parameters `a` for which `W(a)` is a cycle word. It does
so by computation over `ℚ`-coefficient lists, and `decide` can run it in the kernel.
`decideR1_correct` proves that the answer is right for every valid family, so the procedure is
total and verified.

**Classification.** Let `h = gcd(δ, γ)`, with `δ = h δ'`. Either `deg δ' = 0`, in which case the
fixed point `S/D` is constant along the family (`const_ratio`) and the cycle set is `∅`, `{0}`, all
`a ≥ 1`, or all `a`. Or `deg δ' ≥ 1`, in which case the cycle set is finite and lies below an
explicit `a₀` (`finite_bound`). The latter is the product formula: units at `2, 3`, the Bézout
constant at `p ∣ D`, and growth at `∞`.
-/

namespace Syracuse.R1

open Syracuse Syracuse.CocycleCombine Polynomial

/-! ## Cycle words and verdicts -/

/-- `w` is the gap word of a (possibly negative) `3x+1` cycle. -/
def IsCycleWord (w : Word) : Prop := w ≠ [] ∧ Dz w ∣ Sz w

/-- Decidable form of `IsCycleWord`. -/
def cycB (w : Word) : Bool := !w.isEmpty && Sz w % Dz w == 0

lemma cycB_iff (w : Word) : cycB w = true ↔ IsCycleWord w := by
  unfold cycB IsCycleWord
  rw [Int.dvd_iff_emod_eq_zero]
  cases w with
  | nil => simp
  | cons d w => simp

/-- The answer: a finite cycle set, or "every `a ≥ b`, plus a finite list". -/
inductive Verdict
  | finite (l : List ℕ)
  | allFrom (b : ℕ) (l : List ℕ)
  deriving DecidableEq, Repr

/-- Membership in a verdict. -/
def Verdict.mem : Verdict → ℕ → Prop
  | .finite l, a => a ∈ l
  | .allFrom b l, a => b ≤ a ∨ a ∈ l

/-! ## The computation -/

/-- lcm of the denominators of a list. -/
def denL : List ℚ → ℕ
  | [] => 1
  | x :: l => Nat.lcm x.den (denL l)

/-- `L · x` as an integer, when `x.den ∣ L`. -/
def zcoef (L : ℕ) (x : ℚ) : ℤ := x.num * ((L / x.den : ℕ) : ℤ)

/-- Running sum `Σ_{i<n} f i`. -/
def hsum (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => hsum f n + f n

/-- First `a' ∈ [a, a + n]` with `g a'`, or `a + n`. -/
def firstPos (g : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, a => a
  | n + 1, a => if g a then a else firstPos g n (a + 1)

namespace Family

variable (F : Family)

/-- `δ`, `γ`, the extended gcd, and the cofactors. -/
def δ : List ℚ := F.data.delta
def γ : List ℚ := F.data.G
def eg : List ℚ × List ℚ × List ℚ := egcd F.δ F.γ
def h : List ℚ := F.eg.1
def u : List ℚ := F.eg.2.1
def v : List ℚ := F.eg.2.2
def δ' : List ℚ := ldiv F.δ F.h
def γ' : List ℚ := ldiv F.γ F.h

/-- Common denominator of all the rational data. -/
def L : ℕ :=
  Nat.lcm (denL (trim F.h)) (Nat.lcm (denL F.δ') (Nat.lcm (denL F.γ') (Nat.lcm (denL F.u) (denL F.v))))

/-- Integer coefficients of `L · h`. -/
def hZ : List ℤ := (trim F.h).map (zcoef F.L)

/-- `deg h`. -/
def dh : ℕ := (trim F.h).length - 1

/-- Whether `2^p > 3^q` (then `2^E` dominates `D`). -/
def twoDom : Bool := decide (3 ^ F.q < 2 ^ F.p)

/-- Dominant base and coefficient, and the subdominant binomial term. -/
def α : ℕ := if F.twoDom then 2 ^ (F.p * F.data.d) else 3 ^ (F.q * F.data.d)
def A : ℚ := if F.twoDom then F.data.xc else F.data.yc
def β₀ : ℕ := if F.twoDom then 3 ^ (F.q * F.data.d) else 2 ^ (F.p * F.data.d)
def B₀ : ℚ := if F.twoDom then F.data.yc else F.data.xc

/-- Bases and coefficients bounding `|h|` at the run point. -/
def βi (i : ℕ) : ℕ := 2 ^ (F.p * i) * 3 ^ (F.q * (F.dh - i))
def ci (i : ℕ) : ℚ := |((F.hZ.getD i 0 : ℤ) : ℚ)|

/-- The growth test: positive means `|D_a| > |h_a|`. -/
def gval (a : ℕ) : ℚ :=
  F.A * (F.α : ℚ) ^ a - F.B₀ * (F.β₀ : ℚ) ^ a - hsum (fun i => F.ci i * (F.βi i : ℚ) ^ a) (F.dh + 1)

/-- Total subdominant weight, and the Bernoulli bound on where the test must succeed. -/
def Btot : ℚ := F.B₀ + hsum F.ci (F.dh + 1)
def amax : ℕ := (F.α - 1) * ⌈F.Btot⌉₊ + 1

/-- The threshold `a₀`: the first parameter passing the growth test. -/
def a₀ : ℕ := firstPos (fun a => decide (0 < F.gval a)) F.amax 0

end Family

/-- **The decision procedure for r = 1 families.** -/
def decideR1 (F : Family) : Verdict :=
  if F.data.d = 0 then
    (if cycB (F.word 0) then .allFrom 0 [] else .finite [])
  else if (trim F.δ').length ≤ 1 then
    (if cycB (F.word 1) then .allFrom 1 (if cycB (F.word 0) then [0] else [])
      else .finite (if cycB (F.word 0) then [0] else []))
  else
    .finite ((List.range F.a₀).filter fun a => cycB (F.word a))

/-! ## Basic facts -/

lemma len_le_sum {w : Word} (hw : w.Pos) : w.length ≤ w.sum := by
  induction w with
  | nil => simp
  | cons d w ih =>
    simp only [List.length_cons, List.sum_cons]
    have hd := hw d (by simp)
    have := ih (fun x hx => hw x (by simp [hx]))
    omega

lemma sum_ne_zero {w : Word} (hw : w.Pos) (hne : w ≠ []) : w.sum ≠ 0 := by
  have := len_le_sum hw
  have := List.length_pos_of_ne_nil hne
  omega

lemma Dz_ne_zero {w : Word} (hw : w.Pos) (hne : w ≠ []) : Dz w ≠ 0 := by
  obtain ⟨k, hk⟩ := Dz_odd (sum_ne_zero hw hne)
  omega

lemma cop6 {w : Word} (hw : w.Pos) (hne : w ≠ []) : IsCoprime (Dz w) 6 :=
  isCoprime_Dz_six hne (sum_ne_zero hw hne)

lemma natDegree_delta (D : Data) (hx : D.xc ≠ 0) : (toPoly D.delta).natDegree = D.d := by
  rw [Data.toPoly_delta, natDegree_sub_C, natDegree_C_mul_X_pow _ _ hx]

lemma delta_ne_zero (D : Data) (hx : D.xc ≠ 0) (hd : 1 ≤ D.d) : toPoly D.delta ≠ 0 := by
  intro h0
  have := natDegree_delta D hx
  rw [h0, natDegree_zero] at this
  omega

/-- The polynomial facts delivered by Euclid. -/
theorem euclid_facts (F : Family) (hN : 1 ≤ F.data.d) :
    toPoly F.δ ≠ 0 ∧ toPoly F.h ≠ 0 ∧ toPoly F.δ = toPoly F.δ' * toPoly F.h ∧
      toPoly F.γ = toPoly F.γ' * toPoly F.h ∧
      toPoly F.u * toPoly F.δ' + toPoly F.v * toPoly F.γ' = 1 := by
  have hx : F.data.xc ≠ 0 := (lt_of_lt_of_le one_pos F.xc_ge).ne'
  have hδ : toPoly F.δ ≠ 0 := delta_ne_zero F.data hx hN
  obtain ⟨hbez, hdδ, hdγ⟩ := egcd_spec F.δ F.γ
  have hdδ' : toPoly F.h ∣ toPoly F.δ := hdδ
  have hdγ' : toPoly F.h ∣ toPoly F.γ := hdγ
  have hb : toPoly F.h = toPoly F.u * toPoly F.δ + toPoly F.v * toPoly F.γ := hbez
  have hH : toPoly F.h ≠ 0 := by
    intro h0
    rw [h0] at hdδ'
    exact hδ (zero_dvd_iff.mp hdδ')
  have e1 : toPoly F.δ = toPoly F.δ' * toPoly F.h := ldiv_spec hH hdδ'
  have e2 : toPoly F.γ = toPoly F.γ' * toPoly F.h := ldiv_spec hH hdγ'
  refine ⟨hδ, hH, e1, e2, ?_⟩
  have key : toPoly F.h * (toPoly F.u * toPoly F.δ' + toPoly F.v * toPoly F.γ' - 1) = 0 := by
    linear_combination (-1 : ℚ[X]) * hb - toPoly F.u * e1 - toPoly F.v * e2
  rcases mul_eq_zero.mp key with h0 | h0
  · exact absurd h0 hH
  · exact sub_eq_zero.mp h0

/-! ## The constant case -/

/-- **Constant fixed point.** If `deg δ' = 0`, then `S(W(a)) = κ · D(W(a))` for one `κ` and all
`a`. -/
theorem const_ratio {F : Family} (hF : F.okB = true) (hN : 1 ≤ F.data.d)
    (hc : (trim F.δ').length ≤ 1) :
    ∃ κ : ℚ, ∀ a, (Sz (F.word a) : ℚ) = κ * Dz (F.word a) := by
  obtain ⟨hδ, hH, e1, e2, -⟩ := euclid_facts F hN
  have hx : F.data.xc ≠ 0 := (lt_of_lt_of_le one_pos F.xc_ge).ne'
  have hδ'0 : toPoly F.δ' ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e1; exact hδ e1
  have hd' : (toPoly F.δ').natDegree = 0 := by
    have := trim_length F.δ'
    simp only [hδ'0, ↓reduceIte] at this
    omega
  set c := (toPoly F.δ').coeff 0
  have hc' : toPoly F.δ' = C c := eq_C_of_natDegree_eq_zero hd'
  have hc0 : c ≠ 0 := by intro h0; rw [hc', h0, C_0] at hδ'0; exact hδ'0 rfl
  have hHdeg : (toPoly F.h).natDegree = F.data.d := by
    have := natDegree_delta F.data hx
    rw [← Family.δ, e1, hc', natDegree_C_mul hc0] at this
    exact this
  have hg' : (toPoly F.γ').natDegree = 0 := by
    by_cases h0 : toPoly F.γ' = 0
    · rw [h0, natDegree_zero]
    · have hG := F.natDegree_G
      rw [← Family.γ, e2, natDegree_mul h0 hH, hHdeg] at hG
      omega
  set c' := (toPoly F.γ').coeff 0
  have hcg : toPoly F.γ' = C c' := eq_C_of_natDegree_eq_zero hg'
  have hμ := Family.mu_ne_zero hF
  refine ⟨c' / (c * F.data.μ), fun a => ?_⟩
  obtain ⟨hS, -, -⟩ := F.closed hF a
  have hD := F.D_closed hF a
  have hγ : toPoly F.data.G = C (c' / c) * toPoly F.data.delta := by
    have h1 : toPoly F.data.G = C c' * toPoly F.h := by rw [← Family.γ, e2, hcg]
    have h2 : toPoly F.data.delta = C c * toPoly F.h := by rw [← Family.δ, e1, hc']
    rw [h1, h2, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ hc0]
  rw [hγ, eval_mul, eval_C] at hS
  have hmul : F.data.μ * ((Sz (F.word a) : ℚ) - c' / (c * F.data.μ) * Dz (F.word a)) = 0 := by
    rw [hD, mul_sub, hS]
    field_simp
    ring
  rcases mul_eq_zero.mp hmul with h0 | h0
  · exact absurd h0 hμ
  · linarith

/-- In the constant case all members with `a ≥ 1` are cycles together or not at all. -/
theorem const_case {F : Family} (hF : F.okB = true) (hN : 1 ≤ F.data.d)
    (hc : (trim F.δ').length ≤ 1) {a : ℕ} (ha : 1 ≤ a) :
    IsCycleWord (F.word a) ↔ IsCycleWord (F.word 1) := by
  obtain ⟨κ, hκ⟩ := const_ratio hF hN hc
  have key : ∀ b, 1 ≤ b → (IsCycleWord (F.word b) ↔ ∃ z : ℤ, (z : ℚ) = κ) := by
    intro b hb
    have hne := F.word_ne_nil hF hN hb
    have hD0 := Dz_ne_zero (F.word_pos hF b) hne
    have hDq : (Dz (F.word b) : ℚ) ≠ 0 := by exact_mod_cast hD0
    constructor
    · rintro ⟨-, k, hk⟩
      have h1 := hκ b
      rw [hk] at h1
      push_cast at h1
      exact ⟨k, (mul_right_cancel₀ hDq (by rw [← h1]; ring) : (k : ℚ) = κ)⟩
    · rintro ⟨z, hz⟩
      refine ⟨hne, z, ?_⟩
      have h1 := hκ b
      rw [← hz] at h1
      have h2 : ((Sz (F.word b) : ℤ) : ℚ) = ((Dz (F.word b) * z : ℤ) : ℚ) := by
        push_cast; rw [h1]; ring
      exact_mod_cast h2
  rw [key a ha, key 1 le_rfl]

/-! ## Integer lifts and homogeneous evaluation -/

lemma den_dvd_denL : ∀ {l : List ℚ} {x : ℚ}, x ∈ l → x.den ∣ denL l
  | y :: l, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.dvd_lcm_left _ _
    · exact (den_dvd_denL h).trans (Nat.dvd_lcm_right _ _)

lemma denL_pos : ∀ l : List ℚ, 0 < denL l
  | [] => Nat.one_pos
  | x :: l => Nat.lcm_pos x.den_pos (denL_pos l)

lemma zcoef_cast {L : ℕ} {x : ℚ} (h : x.den ∣ L) : ((zcoef L x : ℤ) : ℚ) = L * x := by
  unfold zcoef
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div h (by exact_mod_cast x.den_nz)]
  conv_rhs => rw [← Rat.num_div_den x]
  have : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  field_simp

lemma map_zcoef {L : ℕ} : ∀ l : List ℚ, (∀ x ∈ l, x.den ∣ L) →
    (l.map (zcoef L)).map (Int.castRingHom ℚ) = lsmul (L : ℚ) l
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.map_cons, lsmul, eq_intCast, zcoef_cast (h x (by simp))]
    rw [← map_zcoef l (fun y hy => h y (by simp [hy]))]

/-- The integer polynomial `L · P`. -/
noncomputable def lift (L : ℕ) (l : List ℚ) : ℤ[X] := toPoly (l.map (zcoef L))

lemma lift_map {L : ℕ} {l : List ℚ} (hl : ∀ x ∈ l, x.den ∣ L) :
    (lift L l).map (Int.castRingHom ℚ) = C (L : ℚ) * toPoly l := by
  rw [lift, ← toPoly_map, map_zcoef l hl, toPoly_lsmul]

lemma lift_natDegree {L : ℕ} {l : List ℚ} (hl : ∀ x ∈ l, x.den ∣ L) (hL : L ≠ 0) :
    (lift L l).natDegree = (toPoly l).natDegree := by
  have := congrArg natDegree (lift_map hl)
  rwa [natDegree_map_eq_of_injective (RingHom.injective_int _),
    natDegree_C_mul (by exact_mod_cast hL)] at this

/-- `s^d P(z/s)` for an integer polynomial of degree `≤ d`: an integer. -/
def homZ (P : ℤ[X]) (d : ℕ) (z s : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (d + 1), P.coeff i * z ^ i * s ^ (d - i)

lemma homZ_cast (P : ℤ[X]) {d : ℕ} (hd : P.natDegree ≤ d) (z s : ℤ) (hs : s ≠ 0) :
    ((homZ P d z s : ℤ) : ℚ) = (s : ℚ) ^ d * (P.map (Int.castRingHom ℚ)).eval ((z : ℚ) / s) := by
  have hdeg : (P.map (Int.castRingHom ℚ)).natDegree < d + 1 := by
    rw [natDegree_map_eq_of_injective (RingHom.injective_int _)]; omega
  rw [eval_eq_sum_range' hdeg, Finset.mul_sum]
  unfold homZ
  push_cast
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [coeff_map, eq_intCast]
  have hsq : (s : ℚ) ≠ 0 := by exact_mod_cast hs
  rw [div_pow, show (s : ℚ) ^ d = s ^ i * s ^ (d - i) by rw [← pow_add, Nat.add_sub_cancel' hi']]
  field_simp

lemma homZ_abs (P : ℤ[X]) (d : ℕ) {z s : ℤ} (hz : 0 ≤ z) (hs : 0 ≤ s) :
    |homZ P d z s| ≤ ∑ i ∈ Finset.range (d + 1), |P.coeff i| * z ^ i * s ^ (d - i) := by
  unfold homZ
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hz, abs_of_nonneg hs]

lemma hsum_eq (f : ℕ → ℚ) : ∀ n, hsum f n = ∑ i ∈ Finset.range n, f i
  | 0 => by simp [hsum]
  | n + 1 => by rw [hsum, hsum_eq f n, Finset.sum_range_succ]

lemma firstPos_spec (g : ℕ → Bool) : ∀ (n a : ℕ), g (a + n) = true → g (firstPos g n a) = true
  | 0, a, h => by simpa [firstPos] using h
  | n + 1, a, h => by
    simp only [firstPos]
    split_ifs with ha
    · exact ha
    · exact firstPos_spec g n (a + 1) (by rw [show a + 1 + n = a + (n + 1) by omega]; exact h)

/-! ## Growth -/

namespace Family

variable (F : Family)

/-- The bases are dominated: `β₀, βᵢ ≤ α - 1` and `α ≥ 2`, whenever `deg h < N`. -/
theorem bases_lt (hp : 1 ≤ F.p) (hq : 1 ≤ F.q) (hdN : F.dh < F.data.d) :
    F.β₀ < F.α ∧ ∀ i ≤ F.dh, F.βi i < F.α := by
  have hN : F.data.d ≠ 0 := by omega
  unfold β₀ α βi twoDom
  by_cases h23 : 3 ^ F.q < 2 ^ F.p
  · simp only [h23, decide_true, ↓reduceIte]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [pow_mul, pow_mul]; exact Nat.pow_lt_pow_left h23 hN
    · calc 2 ^ (F.p * i) * 3 ^ (F.q * (F.dh - i)) ≤ 2 ^ (F.p * i) * 2 ^ (F.p * (F.dh - i)) := by
            apply Nat.mul_le_mul_left
            rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left h23.le _
        _ = 2 ^ (F.p * F.dh) := by rw [← pow_add, ← mul_add, Nat.add_sub_cancel' hi]
        _ < 2 ^ (F.p * F.data.d) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  · have h32 : 2 ^ F.p < 3 ^ F.q := by
      rcases lt_or_eq_of_le (not_lt.mp h23) with h | h
      · exact h
      · exfalso
        have h2 : 2 ∣ 3 ^ F.q := h ▸ dvd_pow_self 2 (by omega)
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
        omega
    simp only [h23, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [pow_mul, pow_mul]; exact Nat.pow_lt_pow_left h32 hN
    · calc 2 ^ (F.p * i) * 3 ^ (F.q * (F.dh - i)) ≤ 3 ^ (F.q * i) * 3 ^ (F.q * (F.dh - i)) := by
            apply Nat.mul_le_mul_right
            rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left h32.le _
        _ = 3 ^ (F.q * F.dh) := by rw [← pow_add, ← mul_add, Nat.add_sub_cancel' hi]
        _ < 3 ^ (F.q * F.data.d) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)

lemma A_ge : 1 ≤ F.A := by unfold A; split_ifs <;> [exact F.xc_ge; exact F.yc_ge]
lemma B₀_nonneg : 0 ≤ F.B₀ := by
  unfold B₀; split_ifs <;> [exact le_trans zero_le_one F.yc_ge; exact le_trans zero_le_one F.xc_ge]
lemma ci_nonneg (i : ℕ) : 0 ≤ F.ci i := abs_nonneg _

/-- The test, once passed, stays passed: `gval (a+1) ≥ α · gval a`. -/
theorem gval_succ (hb : F.β₀ < F.α ∧ ∀ i ≤ F.dh, F.βi i < F.α) {a : ℕ} (ha : 0 < F.gval a) :
    0 < F.gval (a + 1) := by
  obtain ⟨h0, hi⟩ := hb
  have hα : (1 : ℚ) ≤ F.α := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) h0)
  have key : (F.α : ℚ) * F.gval a ≤ F.gval (a + 1) := by
    unfold gval
    rw [hsum_eq, hsum_eq]
    have hs : ∑ i ∈ Finset.range (F.dh + 1), F.ci i * (F.βi i : ℚ) ^ (a + 1) ≤
        (F.α : ℚ) * ∑ i ∈ Finset.range (F.dh + 1), F.ci i * (F.βi i : ℚ) ^ a := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi' => ?_
      have hle : (F.βi i : ℚ) ≤ F.α :=
        by exact_mod_cast (hi i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi'))).le
      have hnn : 0 ≤ F.ci i * (F.βi i : ℚ) ^ a :=
        mul_nonneg (F.ci_nonneg i) (pow_nonneg (Nat.cast_nonneg _) _)
      calc F.ci i * (F.βi i : ℚ) ^ (a + 1) = (F.ci i * (F.βi i : ℚ) ^ a) * F.βi i := by ring
        _ ≤ (F.ci i * (F.βi i : ℚ) ^ a) * F.α := mul_le_mul_of_nonneg_left hle hnn
        _ = F.α * (F.ci i * (F.βi i : ℚ) ^ a) := by ring
    have hb0 : F.B₀ * (F.β₀ : ℚ) ^ (a + 1) ≤ F.α * (F.B₀ * (F.β₀ : ℚ) ^ a) := by
      have hle : (F.β₀ : ℚ) ≤ F.α := by exact_mod_cast h0.le
      have hnn : 0 ≤ F.B₀ * (F.β₀ : ℚ) ^ a :=
        mul_nonneg F.B₀_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      calc F.B₀ * (F.β₀ : ℚ) ^ (a + 1) = (F.B₀ * (F.β₀ : ℚ) ^ a) * F.β₀ := by ring
        _ ≤ (F.B₀ * (F.β₀ : ℚ) ^ a) * F.α := mul_le_mul_of_nonneg_left hle hnn
        _ = F.α * (F.B₀ * (F.β₀ : ℚ) ^ a) := by ring
    rw [pow_succ]
    nlinarith
  nlinarith

lemma bernoulli (α : ℚ) (hα : 1 ≤ α) : ∀ a : ℕ, (α - 1) ^ a * (α - 1 + a) ≤ α ^ a * (α - 1)
  | 0 => by simp
  | a + 1 => by
    have ih := bernoulli α hα a
    have h0 : 0 ≤ α - 1 := by linarith
    push_cast
    rw [pow_succ, pow_succ]
    nlinarith [pow_nonneg h0 a]

/-- The test passes at the explicit Bernoulli bound `amax`. -/
theorem gval_amax (hb : F.β₀ < F.α ∧ ∀ i ≤ F.dh, F.βi i < F.α) : 0 < F.gval F.amax := by
  obtain ⟨h0, hi⟩ := hb
  have hα2 : (2 : ℚ) ≤ F.α := by
    have : 2 ≤ F.α := by
      have : 1 ≤ F.β₀ := by unfold β₀; split_ifs <;> exact Nat.one_le_pow _ _ (by norm_num)
      omega
    exact_mod_cast this
  set m := F.α - 1 with hm
  have hmq : ((m : ℕ) : ℚ) = (F.α : ℚ) - 1 := by
    rw [hm, Nat.cast_sub (by exact_mod_cast (show (1 : ℚ) ≤ F.α by linarith))]; simp
  set a := F.amax
  have hBt : 0 ≤ F.Btot := by
    unfold Btot; rw [hsum_eq]
    exact add_nonneg F.B₀_nonneg (Finset.sum_nonneg fun i _ => F.ci_nonneg i)
  -- lower bound gval ≥ A α^a - Btot (α-1)^a
  have hlow : F.A * (F.α : ℚ) ^ a - F.Btot * ((F.α : ℚ) - 1) ^ a ≤ F.gval a := by
    unfold gval Btot
    rw [hsum_eq, hsum_eq, add_mul, Finset.sum_mul]
    have hb0 : F.B₀ * (F.β₀ : ℚ) ^ a ≤ F.B₀ * ((F.α : ℚ) - 1) ^ a := by
      apply mul_le_mul_of_nonneg_left _ F.B₀_nonneg
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      have : F.β₀ + 1 ≤ F.α := h0
      have : (F.β₀ : ℚ) + 1 ≤ F.α := by exact_mod_cast this
      linarith
    have hbs : ∑ i ∈ Finset.range (F.dh + 1), F.ci i * (F.βi i : ℚ) ^ a ≤
        ∑ i ∈ Finset.range (F.dh + 1), F.ci i * ((F.α : ℚ) - 1) ^ a := by
      refine Finset.sum_le_sum fun i hi' => ?_
      apply mul_le_mul_of_nonneg_left _ (F.ci_nonneg i)
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      have : F.βi i + 1 ≤ F.α := hi i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi'))
      have : (F.βi i : ℚ) + 1 ≤ F.α := by exact_mod_cast this
      linarith
    linarith
  have hbern := bernoulli (F.α : ℚ) (by linarith) a
  have hceil : F.Btot ≤ (⌈F.Btot⌉₊ : ℚ) := Nat.le_ceil _
  have ha : (a : ℚ) = ((F.α : ℚ) - 1) * ⌈F.Btot⌉₊ + 1 := by
    simp only [a, amax]; push_cast; rw [← hmq]
  have hpos : 0 < ((F.α : ℚ) - 1) ^ a := pow_pos (by linarith) a
  have hαa : 0 ≤ (F.α : ℚ) ^ a := pow_nonneg (by linarith) a
  -- (α-1) α^a ≥ (α-1)^a (α-1+a) > (α-1)^a (α-1) Btot
  have h1 : ((F.α : ℚ) - 1) ^ a * (((F.α : ℚ) - 1) * F.Btot) <
      ((F.α : ℚ) - 1) ^ a * ((F.α : ℚ) - 1 + a) := by
    apply mul_lt_mul_of_pos_left _ hpos
    rw [ha]; nlinarith
  have h2 : F.Btot * ((F.α : ℚ) - 1) ^ a < (F.α : ℚ) ^ a := by
    have : ((F.α : ℚ) - 1) * (F.Btot * ((F.α : ℚ) - 1) ^ a) < ((F.α : ℚ) - 1) * (F.α : ℚ) ^ a := by
      nlinarith
    exact lt_of_mul_lt_mul_left this (by linarith)
  have hA := F.A_ge
  nlinarith

/-- From `a₀` on, the growth test holds. -/
theorem gval_pos (hb : F.β₀ < F.α ∧ ∀ i ≤ F.dh, F.βi i < F.α) {a : ℕ} (ha : F.a₀ ≤ a) :
    0 < F.gval a := by
  have h0 : 0 < F.gval F.a₀ := by
    have := firstPos_spec (fun a => decide (0 < F.gval a)) F.amax 0
      (by simpa using F.gval_amax hb)
    simpa [a₀] using this
  induction a, ha using Nat.le_induction with
  | base => exact h0
  | succ n _ ih => exact F.gval_succ hb ih

end Family

/-! ## The finite case -/

namespace Family

variable {F : Family}

lemma dens_dvd_L :
    (∀ x ∈ trim F.h, x.den ∣ F.L) ∧ (∀ x ∈ F.δ', x.den ∣ F.L) ∧ (∀ x ∈ F.γ', x.den ∣ F.L) ∧
      (∀ x ∈ F.u, x.den ∣ F.L) ∧ (∀ x ∈ F.v, x.den ∣ F.L) := by
  unfold L
  refine ⟨fun x hx => (den_dvd_denL hx).trans (Nat.dvd_lcm_left _ _),
    fun x hx => (den_dvd_denL hx).trans ((Nat.dvd_lcm_left _ _).trans (Nat.dvd_lcm_right _ _)),
    fun x hx => (den_dvd_denL hx).trans ((Nat.dvd_lcm_left _ _).trans
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _))),
    fun x hx => (den_dvd_denL hx).trans ((Nat.dvd_lcm_left _ _).trans ((Nat.dvd_lcm_right _ _).trans
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _)))),
    fun x hx => (den_dvd_denL hx).trans ((Nat.dvd_lcm_right _ _).trans ((Nat.dvd_lcm_right _ _).trans
      ((Nat.dvd_lcm_right _ _).trans (Nat.dvd_lcm_right _ _))))⟩

lemma L_pos : 0 < F.L := by
  unfold L
  exact Nat.lcm_pos (denL_pos _) (Nat.lcm_pos (denL_pos _) (Nat.lcm_pos (denL_pos _)
    (Nat.lcm_pos (denL_pos _) (denL_pos _))))

lemma dh_eq (hH : toPoly F.h ≠ 0) : (toPoly F.h).natDegree = F.dh := by
  have hne : trim F.h ≠ [] := fun h0 => hH ((trim_eq_nil_iff _).mp h0)
  obtain ⟨-, hd, -⟩ := normal_props (trim_normal F.h) hne
  rw [toPoly_trim] at hd
  exact hd

/-- The dominant binomial term bounds `|D|` from below. -/
lemma dom_le (hF : F.okB = true) (a : ℕ) :
    F.A * (F.α : ℚ) ^ a - F.B₀ * (F.β₀ : ℚ) ^ a ≤ |(Dz (F.word a) : ℚ)| := by
  obtain ⟨-, hX, hY⟩ := F.closed hF a
  have hD : (Dz (F.word a) : ℚ) = F.data.xc * (((2 : ℚ) ^ F.p) ^ a) ^ F.data.d -
      F.data.yc * (((3 : ℚ) ^ F.q) ^ a) ^ F.data.d := by
    simp only [Dz, D, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
    rw [hX, hY, ← sv_mul_tv, sv]; ring
  have e2 : (((2 : ℚ) ^ F.p) ^ a) ^ F.data.d = ((2 ^ (F.p * F.data.d) : ℕ) : ℚ) ^ a := by
    push_cast; rw [← pow_mul, ← pow_mul, ← pow_mul]; ring_nf
  have e3 : (((3 : ℚ) ^ F.q) ^ a) ^ F.data.d = ((3 ^ (F.q * F.data.d) : ℕ) : ℚ) ^ a := by
    push_cast; rw [← pow_mul, ← pow_mul, ← pow_mul]; ring_nf
  rw [e2, e3] at hD
  unfold A α β₀ B₀
  split_ifs
  · rw [hD]; exact le_abs_self _
  · rw [hD]; linarith [neg_le_abs ((F.data.xc * ((2 ^ (F.p * F.data.d) : ℕ) : ℚ) ^ a -
      F.data.yc * ((3 ^ (F.q * F.data.d) : ℕ) : ℚ) ^ a))]

set_option maxHeartbeats 2000000 in
/-- **Finite case.** If `deg δ' ≥ 1`, every cycle member has `a < a₀`. -/
theorem finite_bound (hF : F.okB = true) (hN : 1 ≤ F.data.d) (hc : ¬ (trim F.δ').length ≤ 1)
    {a : ℕ} (hcyc : IsCycleWord (F.word a)) : a < F.a₀ := by
  by_contra hge
  push Not at hge
  obtain ⟨hδ, hH, e1, e2, hbez⟩ := euclid_facts F hN
  obtain ⟨hlh, hl1, hlg, hlu, hlv⟩ := dens_dvd_L (F := F)
  have hL0 : F.L ≠ 0 := L_pos.ne'
  have hx : F.data.xc ≠ 0 := (lt_of_lt_of_le one_pos F.xc_ge).ne'
  have hδ'0 : toPoly F.δ' ≠ 0 := by intro h0; rw [h0, zero_mul] at e1; exact hδ e1
  have hd1 : 1 ≤ (toPoly F.δ').natDegree := by
    have := trim_length F.δ'
    simp only [hδ'0, ↓reduceIte] at this
    omega
  have hNsum : F.data.d = F.dh + (toPoly F.δ').natDegree := by
    have := natDegree_delta F.data hx
    rw [← Family.δ, e1, natDegree_mul hδ'0 hH, dh_eq hH] at this
    omega
  have hdhN : F.dh < F.data.d := by omega
  have hγ'deg : (toPoly F.γ').natDegree ≤ F.data.d - F.dh := by
    by_cases h0 : toPoly F.γ' = 0
    · simp [h0]
    · have hG := F.natDegree_G
      rw [← Family.γ, e2, natDegree_mul h0 hH, dh_eq hH] at hG
      omega
  have hok := hF
  simp only [Family.okB, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hb := F.bases_lt hok.1.1 hok.1.2 hdhN
  have hg := F.gval_pos hb hge
  -- notation
  set N := F.data.d
  set dh := F.dh
  set d1 := (toPoly F.δ').natDegree
  set dg := N - dh
  set du := (toPoly F.u).natDegree
  set dv := (toPoly F.v).natDegree
  set z : ℤ := 2 ^ (F.p * a)
  set s : ℤ := 3 ^ (F.q * a)
  have hs0 : s ≠ 0 := by positivity
  have hsq : (s : ℚ) = sv F.q a := by simp [s, sv, pow_mul]
  have htq : (z : ℚ) / s = tv F.p F.q a := by simp [z, s, tv, div_pow, pow_mul]
  set t := tv F.p F.q a
  set Ph := lift F.L (trim F.h)
  set P1 := lift F.L F.δ'
  set Pg := lift F.L F.γ'
  set Pu := lift F.L F.u
  set Pv := lift F.L F.v
  have dPh : Ph.natDegree = dh := by rw [lift_natDegree hlh hL0, toPoly_trim, dh_eq hH]
  have dP1 : P1.natDegree = d1 := lift_natDegree hl1 hL0
  have dPg : Pg.natDegree ≤ dg := by rw [lift_natDegree hlg hL0]; exact hγ'deg
  have dPu : Pu.natDegree = du := lift_natDegree hlu hL0
  have dPv : Pv.natDegree = dv := lift_natDegree hlv hL0
  set Hv := homZ Ph dh z s
  set Δ := homZ P1 d1 z s
  set Γ := homZ Pg dg z s
  set Uv := homZ Pu du z s
  set Vv := homZ Pv dv z s
  have cH : (Hv : ℚ) = (s : ℚ) ^ dh * ((F.L : ℚ) * (toPoly F.h).eval t) := by
    rw [homZ_cast Ph dPh.le z s hs0, lift_map hlh, htq, eval_mul, eval_C, toPoly_trim]
  have cΔ : (Δ : ℚ) = (s : ℚ) ^ d1 * ((F.L : ℚ) * (toPoly F.δ').eval t) := by
    rw [homZ_cast P1 dP1.le z s hs0, lift_map hl1, htq, eval_mul, eval_C]
  have cΓ : (Γ : ℚ) = (s : ℚ) ^ dg * ((F.L : ℚ) * (toPoly F.γ').eval t) := by
    rw [homZ_cast Pg dPg z s hs0, lift_map hlg, htq, eval_mul, eval_C]
  have cU : (Uv : ℚ) = (s : ℚ) ^ du * ((F.L : ℚ) * (toPoly F.u).eval t) := by
    rw [homZ_cast Pu dPu.le z s hs0, lift_map hlu, htq, eval_mul, eval_C]
  have cV : (Vv : ℚ) = (s : ℚ) ^ dv * ((F.L : ℚ) * (toPoly F.v).eval t) := by
    rw [homZ_cast Pv dPv.le z s hs0, lift_map hlv, htq, eval_mul, eval_C]
  obtain ⟨μZ, hμZ⟩ := F.mu_int
  obtain ⟨hS, -, -⟩ := F.closed hF a
  have hD := F.D_closed hF a
  have ev1 : (toPoly F.data.delta).eval t = (toPoly F.δ').eval t * (toPoly F.h).eval t := by
    rw [← Family.δ, e1, eval_mul]
  have ev2 : (toPoly F.data.G).eval t = (toPoly F.γ').eval t * (toPoly F.h).eval t := by
    rw [← Family.γ, e2, eval_mul]
  have ev3 : (toPoly F.u).eval t * (toPoly F.δ').eval t + (toPoly F.v).eval t * (toPoly F.γ').eval t
      = 1 := by
    have := congrArg (eval t) hbez
    simpa [eval_add, eval_mul] using this
  have hNg : N = dh + dg := by omega
  -- (1) L² D = H Δ
  have eq1 : (F.L : ℤ) ^ 2 * Dz (F.word a) = Hv * Δ := by
    have : ((F.L : ℤ) ^ 2 * Dz (F.word a) : ℚ) = (Hv : ℚ) * Δ := by
      rw [cH, cΔ, hD, ev1, ← hsq]
      push_cast
      rw [show F.data.d = dh + d1 from hNsum]; ring
    exact_mod_cast this
  -- (2) L² μ S = H Γ
  have eq2 : (F.L : ℤ) ^ 2 * (μZ * Sz (F.word a)) = Hv * Γ := by
    have : ((F.L : ℤ) ^ 2 * (μZ * Sz (F.word a)) : ℚ) = (Hv : ℚ) * Γ := by
      rw [cH, cΓ]
      push_cast
      rw [hμZ, hS, ev2, ← hsq, show F.data.d = dh + dg from hNg]; ring
    exact_mod_cast this
  -- (3) L² s^K = U Δ s^(dv+dg) + V Γ s^(du+d1)
  have eq3 : (F.L : ℤ) ^ 2 * s ^ (du + d1 + dv + dg) =
      Uv * Δ * s ^ (dv + dg) + Vv * Γ * s ^ (du + d1) := by
    have : ((F.L : ℤ) ^ 2 * s ^ (du + d1 + dv + dg) : ℚ) =
        (Uv : ℚ) * Δ * (s : ℚ) ^ (dv + dg) + (Vv : ℚ) * Γ * (s : ℚ) ^ (du + d1) := by
      rw [cU, cΔ, cV, cΓ]
      push_cast
      linear_combination (-(s : ℚ) ^ (du + d1 + dv + dg) * (F.L : ℚ) ^ 2) * ev3
    exact_mod_cast this
  -- divisibility chain
  obtain ⟨hne, hdvd⟩ := hcyc
  have hD0 : Dz (F.word a) ≠ 0 := Dz_ne_zero (F.word_pos hF a) hne
  have hL2 : (0 : ℤ) < (F.L : ℤ) ^ 2 := by positivity
  have hHv : Hv ≠ 0 := by
    intro h0; rw [h0, zero_mul] at eq1
    exact (mul_ne_zero hL2.ne' hD0) eq1
  have hΔΓ : Δ ∣ Γ := by
    have : Hv * Δ ∣ Hv * Γ := by
      rw [← eq1, ← eq2]
      exact mul_dvd_mul_left _ (dvd_mul_of_dvd_right hdvd _)
    exact (mul_dvd_mul_iff_left hHv).mp this
  have hΔ1 : Δ ∣ (F.L : ℤ) ^ 2 * s ^ (du + d1 + dv + dg) := by
    rw [eq3]
    exact dvd_add ⟨Uv * s ^ (dv + dg), by ring⟩
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hΔΓ _) _)
  have hΔ2 : Δ ∣ (F.L : ℤ) ^ 2 * Dz (F.word a) := ⟨Hv, by rw [eq1]; ring⟩
  have hcop : IsCoprime (Dz (F.word a)) (s ^ (du + d1 + dv + dg)) := by
    have h6 := cop6 (F.word_pos hF a) hne
    have h3 : IsCoprime (Dz (F.word a)) 3 :=
      IsCoprime.of_mul_right_right (show IsCoprime (Dz (F.word a)) (2 * 3) by norm_num; exact h6)
    exact (h3.pow_right).pow_right
  obtain ⟨xa, ya, hxy⟩ := hcop
  have hΔL : Δ ∣ (F.L : ℤ) ^ 2 := by
    have : (F.L : ℤ) ^ 2 = xa * ((F.L : ℤ) ^ 2 * Dz (F.word a)) +
        ya * ((F.L : ℤ) ^ 2 * s ^ (du + d1 + dv + dg)) := by
      linear_combination -((F.L : ℤ) ^ 2) * hxy
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right hΔ2 _) (dvd_mul_of_dvd_right hΔ1 _)
  have hΔle : |Δ| ≤ (F.L : ℤ) ^ 2 := Int.le_of_dvd hL2 ((abs_dvd _ _).mpr hΔL)
  have hDH : |Dz (F.word a)| ≤ |Hv| := by
    have h := congrArg abs eq1
    rw [abs_mul, abs_mul, abs_of_pos hL2] at h
    have : (F.L : ℤ) ^ 2 * |Dz (F.word a)| ≤ (F.L : ℤ) ^ 2 * |Hv| :=
      calc (F.L : ℤ) ^ 2 * |Dz (F.word a)| = |Hv| * |Δ| := h
        _ ≤ |Hv| * (F.L : ℤ) ^ 2 := mul_le_mul_of_nonneg_left hΔle (abs_nonneg _)
        _ = (F.L : ℤ) ^ 2 * |Hv| := mul_comm _ _
    exact le_of_mul_le_mul_left this hL2
  -- |H| ≤ the bound the test subtracts
  have hHA : |Hv| ≤ ∑ i ∈ Finset.range (dh + 1), |Ph.coeff i| * z ^ i * s ^ (dh - i) :=
    homZ_abs Ph dh (by positivity) (by positivity)
  have hHAq : ((∑ i ∈ Finset.range (dh + 1), |Ph.coeff i| * z ^ i * s ^ (dh - i) : ℤ) : ℚ) =
      hsum (fun i => F.ci i * (F.βi i : ℚ) ^ a) (F.dh + 1) := by
    rw [hsum_eq]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc : Ph.coeff i = F.hZ.getD i 0 := coeff_toPoly _ i
    rw [hc]
    simp only [Family.ci, Family.βi, z, s]
    push_cast
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
    ring
  have hdom := dom_le hF a
  have : F.gval a ≤ 0 := by
    unfold gval
    have h1 : (|Dz (F.word a)| : ℚ) ≤ (|Hv| : ℚ) := by exact_mod_cast hDH
    have h2 : (|Hv| : ℚ) ≤ hsum (fun i => F.ci i * (F.βi i : ℚ) ^ a) (F.dh + 1) := by
      rw [← hHAq]; exact_mod_cast hHA
    have h3 : |(Dz (F.word a) : ℚ)| = ((|Dz (F.word a)| : ℤ) : ℚ) := by push_cast; rfl
    linarith
  linarith

end Family

/-! ## Correctness and the classification -/

/-- **The decision procedure is correct and total**: for every valid r = 1 family, the verdict is
exactly the set of `a` with `W(a)` a cycle word. -/
theorem decideR1_correct {F : Family} (hF : F.okB = true) (a : ℕ) :
    IsCycleWord (F.word a) ↔ (decideR1 F).mem a := by
  unfold decideR1
  by_cases h0 : F.data.d = 0
  · simp only [h0, ↓reduceIte]
    rw [F.word_const hF h0 a, ← cycB_iff]
    cases cycB (F.word 0) <;> simp [Verdict.mem]
  · have hN : 1 ≤ F.data.d := Nat.one_le_iff_ne_zero.mpr h0
    simp only [h0, ↓reduceIte]
    by_cases hc : (trim F.δ').length ≤ 1
    · simp only [hc, ↓reduceIte]
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [← cycB_iff]
        cases cycB (F.word 1) <;> cases cycB (F.word 0) <;> simp [Verdict.mem]
      · rw [const_case hF hN hc ha, ← cycB_iff]
        cases cycB (F.word 1) <;> cases cycB (F.word 0) <;> simp [Verdict.mem] <;> omega
    · simp only [hc, ↓reduceIte]
      simp only [Verdict.mem, List.mem_filter, List.mem_range]
      constructor
      · intro h; exact ⟨Family.finite_bound hF hN hc h, (cycB_iff _).mpr h⟩
      · rintro ⟨-, h⟩; exact (cycB_iff _).mp h

/-- Use form: once `decideR1 F = v` is evaluated (by `decide +kernel`), the cycle set is `v`. -/
theorem decideR1_iff {F : Family} {v : Verdict} (hF : F.okB = true) (hv : decideR1 F = v) (a : ℕ) :
    IsCycleWord (F.word a) ↔ v.mem a := hv ▸ decideR1_correct hF a

/-- **Classification of r = 1 families.** Either the cycle set is a finite list (computed by
`decideR1`), or the fixed point `S/D` is the same rational number for every member. -/
theorem classification {F : Family} (hF : F.okB = true) (hN : 1 ≤ F.data.d) :
    (∃ l : List ℕ, ∀ a, IsCycleWord (F.word a) ↔ a ∈ l) ∨
      ∃ κ : ℚ, ∀ a, (Sz (F.word a) : ℚ) = κ * Dz (F.word a) := by
  by_cases hc : (trim F.δ').length ≤ 1
  · exact Or.inr (const_ratio hF hN hc)
  · refine Or.inl ⟨(List.range F.a₀).filter fun a => cycB (F.word a), fun a => ?_⟩
    have := decideR1_correct hF a
    unfold decideR1 at this
    simp only [show F.data.d ≠ 0 by omega, hc, ↓reduceIte] at this
    exact this

/-- **Infinite cycle families are powers of one cycle.** In the constant case, if some member
with `a ≥ 1` is a cycle word then one integer `x` starts all of them: every `W(b)`, `b ≥ 1`, is the
gap word of `x` for `len W(b)` odd steps. -/
theorem const_one_orbit {F : Family} (hF : F.okB = true) (hN : 1 ≤ F.data.d)
    (hc : (trim F.δ').length ≤ 1) {a : ℕ} (hcyc : IsCycleWord (F.word a)) :
    ∃ x : ℤ, ∀ b, 1 ≤ b → IsSyrCycle x (F.word b).length ∧
      gapWord x (F.word b).length = F.word b := by
  obtain ⟨κ, hκ⟩ := const_ratio hF hN hc
  obtain ⟨hne, k, hk⟩ := hcyc
  have hD0 := Dz_ne_zero (F.word_pos hF a) hne
  have hκk : κ = k := by
    have h1 := hκ a
    rw [hk] at h1; push_cast at h1
    have hDq : (Dz (F.word a) : ℚ) ≠ 0 := by exact_mod_cast hD0
    exact (mul_right_cancel₀ hDq (by rw [← h1]; ring) : (k : ℚ) = κ).symm
  refine ⟨k, fun b hb => ?_⟩
  have hneb := F.word_ne_nil hF hN hb
  have hDb := Dz_ne_zero (F.word_pos hF b) hneb
  have hSb : Sz (F.word b) = Dz (F.word b) * k := by
    have h1 := hκ b
    rw [hκk] at h1
    have : ((Sz (F.word b) : ℤ) : ℚ) = ((Dz (F.word b) * k : ℤ) : ℚ) := by push_cast; rw [h1]; ring
    exact_mod_cast this
  have hq : Sz (F.word b) / Dz (F.word b) = k := by
    rw [hSb, Int.mul_ediv_cancel_left _ hDb]
  have := CycleLiterature.isSyrCycle_of_dvd (F.word_pos hF b) hneb ⟨k, hSb⟩
  rw [hq] at this
  exact this

end Syracuse.R1
