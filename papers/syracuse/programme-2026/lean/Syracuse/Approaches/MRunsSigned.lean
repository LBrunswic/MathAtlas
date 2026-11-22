import Syracuse.Approaches.MRunsRhin

/-!
# Every number of runs, both signs, from Rhin's linear-form bound

`MRunsRhin` used Simons–de Weger's Lemma 12, which is stated for nontrivial positive cycles. Its source is
Rhin's bound on the linear form `|u₀ + u₁ log 2 + u₂ log 3| ≥ H^{-13.3}`, `H = max |u_i|` (Rhin 1987).
Rukhin (arXiv:1805.10496, eq. (3), with `u₀ = 0`) quotes it as `|-E log 2 + τ log 3| ≥ E^{-13.3}`, an
absolute value with no sign condition. It is stated here as `Rhin1987` for `2 ≤ E`, `1 ≤ o ≤ E`.
Rhin's original text was not available. The quoted form gives no range restriction, and the inequality is
far from tight for small `E`.

From it (`rhin_sep_signed`): `|2^E - 3^o| ≥ 2^{max(E, o log₂3) - 2 - 14ℓ}`, `ℓ = ⌊log₂ E⌋ + 1`, for
**every** word. In the near-critical case `1/2 < r = 2^E/3^o < 2`, `|r - 1| ≥ |log r|/2`. Hence
(`mruns_signed`):

> Given `Rhin1987`, a cycle **of either sign** on `p₀^{a₀} ⋯ p_{m-1}^{a_{m-1}}` (`m ≥ 1`, positive
> nonempty base blocks of total weight `B`) either has an orbit point on a base block's cycle, or
> satisfies `max(E, o log₂3)/σ_m ≤ 6B + 3 + 14ℓ + log₂ m`.

For negative cycles this is the first effective statement for four or more runs. There is no
verification bound for negative cycles, so it constrains them rather than excluding them.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| Rhin 1987, absolute linear form (as quoted by Rukhin) | `Rhin1987` | stated |
| `|r - 1| ≥ |log r|/2` for `1/2 ≤ r ≤ 2` | `abs_sub_one_ge` | proved |
| `E^{-13.3} ≥ 2^{-14ℓ}` | `rpow_neg_ge` | proved |
| separation for every word | `rhin_sep_signed` | proved (conditional on `Rhin1987`) |
| **all-`m` dichotomy, both signs** | `mruns_signed` | proved (conditional on `Rhin1987`) |
-/

namespace Syracuse.MRunsSigned

open Finset Syracuse.MRuns Syracuse.MRunsExplicit Syracuse.MRunsDichotomy

/-- **Rhin 1987** (G. Rhin, "Approximants de Padé et mesures effectives d'irrationalité", Sém. Théorie des
Nombres Paris 1985–86, Progress in Math. 71, Birkhäuser 1987, 155–164), as quoted by Rukhin
(arXiv:1805.10496, eq. (3)) and used by Simons–de Weger 2005 (Lemma 12): `|E log 2 - o log 3| ≥ E^{-13.3}`
for `H = max(E, o) = E`. -/
def Rhin1987 : Prop :=
  ∀ E o : ℕ, 2 ≤ E → 1 ≤ o → o ≤ E →
    (E : ℝ) ^ (-13.3 : ℝ) ≤ |(E : ℝ) * Real.log 2 - o * Real.log 3|

/-- `|r - 1| ≥ |log r|/2` for `1/2 ≤ r ≤ 2`. -/
lemma abs_sub_one_ge {r : ℝ} (h1 : 1 / 2 ≤ r) (h2 : r ≤ 2) : |Real.log r| / 2 ≤ |r - 1| := by
  have hr : 0 < r := by linarith
  rcases le_total 1 r with h | h
  · have hl : 0 ≤ Real.log r := Real.log_nonneg h
    have := Real.log_le_sub_one_of_pos hr
    rw [abs_of_nonneg hl, abs_of_nonneg (by linarith)]; linarith
  · have hl : Real.log r ≤ 0 := Real.log_nonpos hr.le h
    have hinv := Real.log_le_sub_one_of_pos (inv_pos.2 hr)
    rw [Real.log_inv] at hinv
    rw [abs_of_nonpos hl, abs_of_nonpos (by linarith)]
    -- `-log r ≤ 1/r - 1`, so `1 - r ≥ r·(-log r) ≥ (-log r)/2`
    have h3 : r * (-Real.log r) ≤ 1 - r := by
      have := mul_le_mul_of_nonneg_left hinv hr.le
      rw [mul_sub, mul_inv_cancel₀ hr.ne', mul_one] at this; linarith
    nlinarith

/-- `E^{-13.3} ≥ 2^{-14ℓ}` with `ℓ = ⌊log₂ E⌋ + 1`. -/
lemma rpow_neg_ge {E : ℕ} (hE : 1 ≤ E) :
    (2 : ℝ) ^ (-(14 * ((Nat.log 2 E + 1 : ℕ) : ℝ))) ≤ (E : ℝ) ^ (-13.3 : ℝ) := by
  set ℓ := Nat.log 2 E + 1
  have hlt : E < 2 ^ ℓ := Nat.lt_pow_succ_log_self (by norm_num) E
  have hEr : (0 : ℝ) < E := by exact_mod_cast hE
  have hle : (E : ℝ) ≤ (2 : ℝ) ^ (ℓ : ℝ) := by rw [Real.rpow_natCast]; exact_mod_cast hlt.le
  -- `E^{13.3} ≤ 2^{13.3 ℓ} ≤ 2^{14 ℓ}`
  have h1 : (E : ℝ) ^ (13.3 : ℝ) ≤ (2 : ℝ) ^ (14 * (ℓ : ℝ)) := by
    calc (E : ℝ) ^ (13.3 : ℝ) ≤ ((2 : ℝ) ^ (ℓ : ℝ)) ^ (13.3 : ℝ) :=
          Real.rpow_le_rpow hEr.le hle (by norm_num)
      _ = (2 : ℝ) ^ ((ℓ : ℝ) * 13.3) := by rw [← Real.rpow_mul (by norm_num)]
      _ ≤ (2 : ℝ) ^ (14 * (ℓ : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
            have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
            nlinarith)
  rw [Real.rpow_neg (by norm_num), Real.rpow_neg hEr.le]
  exact inv_anti₀ (by positivity) h1

/-- **Separation for every word, from Rhin.** -/
theorem rhin_sep_signed (hR : Rhin1987) {E o : ℕ} (hE : 2 ≤ E) (ho : 1 ≤ o) (hoE : o ≤ E) :
    (2 : ℝ) ^ (1 * max (E : ℝ) (Real.logb 2 3 * o) - (2 + 14 * ((Nat.log 2 E + 1 : ℕ) : ℝ))) ≤
      |(2 : ℝ) ^ E - 3 ^ o| := by
  set ℓ := Nat.log 2 E + 1
  rw [one_mul]
  have e3 : (3 : ℝ) ^ o = (2 : ℝ) ^ (Real.logb 2 3 * o) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num),
      Real.rpow_natCast]
  have e2 : (2 : ℝ) ^ E = (2 : ℝ) ^ (E : ℝ) := (Real.rpow_natCast 2 E).symm
  set lo := Real.logb 2 3 * o
  have mono : ∀ a b : ℝ, a ≤ b → (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
    fun a b hab => Real.rpow_le_rpow_of_exponent_le (by norm_num) hab
  have hℓ0 : (0 : ℝ) ≤ ((ℓ : ℕ) : ℝ) := Nat.cast_nonneg _
  have h3pos : (0 : ℝ) < 3 ^ o := by positivity
  have h2pos : (0 : ℝ) < 2 ^ E := by positivity
  by_cases A : 2 * (3 : ℝ) ^ o ≤ 2 ^ E
  · have hlo : lo ≤ E := by
      have : (2 : ℝ) ^ lo ≤ 2 ^ (E : ℝ) := by rw [← e3, ← e2]; linarith
      exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 this
    rw [max_eq_left hlo, abs_of_pos (by linarith)]
    calc (2 : ℝ) ^ ((E : ℝ) - (2 + 14 * ((ℓ : ℕ) : ℝ))) ≤ (2 : ℝ) ^ ((E : ℝ) - 1) := mono _ _ (by linarith)
      _ = 2 ^ E / 2 := by rw [Real.rpow_sub (by norm_num), Real.rpow_one, ← e2]
      _ ≤ 2 ^ E - 3 ^ o := by linarith
  by_cases B : 2 * (2 : ℝ) ^ E ≤ 3 ^ o
  · have hlo : (E : ℝ) ≤ lo := by
      have : (2 : ℝ) ^ (E : ℝ) ≤ 2 ^ lo := by rw [← e3, ← e2]; linarith
      exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 this
    rw [max_eq_right hlo, abs_of_neg (by linarith)]
    calc (2 : ℝ) ^ (lo - (2 + 14 * ((ℓ : ℕ) : ℝ))) ≤ (2 : ℝ) ^ (lo - 1) := mono _ _ (by linarith)
      _ = 3 ^ o / 2 := by rw [Real.rpow_sub (by norm_num), Real.rpow_one, ← e3]
      _ ≤ -(2 ^ E - 3 ^ o) := by linarith
  push_neg at A B
  -- near-critical: `r = 2^E/3^o ∈ (1/2, 2)`
  set r := (2 : ℝ) ^ E / 3 ^ o
  have hr1 : 1 / 2 ≤ r := by rw [le_div_iff₀ h3pos]; linarith
  have hr2 : r ≤ 2 := by rw [div_le_iff₀ h3pos]; linarith
  have hlogr : Real.log r = (E : ℝ) * Real.log 2 - o * Real.log 3 := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hRh := hR E o hE ho hoE
  rw [← hlogr] at hRh
  have hD : |(2 : ℝ) ^ E - 3 ^ o| = 3 ^ o * |r - 1| := by
    rw [show (2 : ℝ) ^ E - 3 ^ o = 3 ^ o * (r - 1) by simp only [r]; field_simp, abs_mul,
      abs_of_pos h3pos]
  have hsub := abs_sub_one_ge hr1 hr2
  have hneg := rpow_neg_ge (E := E) (by omega)
  have hmax : max (E : ℝ) lo ≤ lo + 1 := by
    have : (2 : ℝ) ^ (E : ℝ) < 2 ^ (lo + 1) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one, ← e3, ← e2]; linarith
    exact max_le ((Real.rpow_lt_rpow_left_iff (by norm_num)).1 this).le (by linarith)
  rw [hD]
  calc (2 : ℝ) ^ (max (E : ℝ) lo - (2 + 14 * ((ℓ : ℕ) : ℝ)))
      ≤ (2 : ℝ) ^ (lo - 1 + -(14 * ((ℓ : ℕ) : ℝ))) := mono _ _ (by linarith)
    _ = 3 ^ o / 2 * (2 : ℝ) ^ (-(14 * ((ℓ : ℕ) : ℝ))) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_sub (by norm_num), Real.rpow_one, ← e3]
    _ ≤ 3 ^ o / 2 * (E : ℝ) ^ (-13.3 : ℝ) := mul_le_mul_of_nonneg_left hneg (by positivity)
    _ ≤ 3 ^ o / 2 * |Real.log r| := mul_le_mul_of_nonneg_left hRh (by positivity)
    _ ≤ 3 ^ o * |r - 1| := by nlinarith [abs_nonneg (Real.log r)]

/-- **All-`m` dichotomy, both signs**, given Rhin's linear-form bound. -/
theorem mruns_signed (hR : Rhin1987) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    {p : ℕ → Word} {a : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hp : ∀ i, p (i + m) = p i) (ha : ∀ i, a (i + m) = a i) (hpos : ∀ i, (p i).Pos)
    (hne : ∀ i, p i ≠ []) (hne' : ∀ i, TwoBackground.bpow (p i) (a i) ≠ [])
    (hrot : gapWord x o ~r cat (fun i => TwoBackground.bpow (p i) (a i)) m)
    (hE2 : 2 ≤ (cat (fun i => TwoBackground.bpow (p i) (a i)) m).sum) :
    (∃ R : ℕ, ∃ y : ℤ, IsSyrCycle y o ∧ (∃ j, y = syr^[j] x) ∧ Dz (p R) * y = Sz (p R)) ∨
      (1 / Reach.σ (Real.logb 2 3) m) *
        max ((cat (fun i => TwoBackground.bpow (p i) (a i)) m).sum : ℝ)
          (Real.logb 2 3 * (cat (fun i => TwoBackground.bpow (p i) (a i)) m).length) ≤
        (6 * (∑ k ∈ range m, (p k).sum) + 1 : ℕ) +
          (2 + 14 * ((Nat.log 2 (cat (fun i => TwoBackground.bpow (p i) (a i)) m).sum + 1 : ℕ) : ℝ)) +
          Real.logb 2 m := by
  set Q : ℕ → Word := fun i => TwoBackground.bpow (p i) (a i)
  have hQ : ∀ i, Q (i + m) = Q i := fun i => by simp only [Q, hp, ha]
  have hQpos : ∀ i, (Q i).Pos := fun i => StdPairs.pos_bpow (hpos i) (a i)
  by_cases hall : ∀ R, T (2 : ℤ) 3 (fun k => Q (R + k)) (fun k => Acoef p m (R + k)) m ≠ 0
  · right
    have hm2 : 2 ≤ m := by
      by_contra hc
      obtain rfl : m = 1 := by omega
      apply hall 0
      simp [T, Nat.mod_one]
    have hpo : 1 ≤ (cat Q m).length := by
      have := List.length_pos_of_ne_nil (show cat Q m ≠ [] by
        intro h0; rw [h0] at hE2; simp at hE2)
      omega
    have hoE : (cat Q m).length ≤ (cat Q m).sum := by
      have := CycleLiterature.length_le_sum (CocycleCombine.IsSyrCycle.pos h)
      rwa [hrot.perm.length_eq, hrot.perm.sum_eq] at this
    have hsep := rhin_sep_signed hR hE2 hpo hoE
    have hsepD : (2 : ℝ) ^ (1 * max ((cat Q m).sum : ℝ) (Real.logb 2 3 * (cat Q m).length) -
        (2 + 14 * ((Nat.log 2 (cat Q m).sum + 1 : ℕ) : ℝ))) ≤ |((Dz (cat Q m) : ℤ) : ℝ)| := by
      have e : ((Dz (cat Q m) : ℤ) : ℝ) = (2 : ℝ) ^ (cat Q m).sum - 3 ^ (cat Q m).length := by
        simp [Dz, D]
      rw [e]; exact hsep
    have hb := mruns_bounded h hm hQ hQpos hne' hrot (fun i => Acoef_spec (a := a) hm hp i)
      (Acoef_period hp) (Acoef_diff_le hm2 hp hpos) hall hsepD
    have hσ : (1 : ℝ) - (1 - 1 / Reach.σ (Real.logb 2 3) m) = 1 / Reach.σ (Real.logb 2 3) m := by ring
    rw [hσ] at hb
    exact hb
  · left
    push_neg at hall
    obtain ⟨R, hR'⟩ := hall
    have hrotR : gapWord x o ~r cat (fun k => Q (R + k)) m := hrot.trans (rot_cat Q hm hQ R).symm
    exact ⟨R, T_zero_alt h hm hp hne hne' R hrotR hR'⟩

end Syracuse.MRunsSigned
