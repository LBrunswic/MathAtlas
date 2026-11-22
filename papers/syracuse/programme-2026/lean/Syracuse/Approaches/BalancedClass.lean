import Syracuse.Approaches.BalancedPow

/-!
# Classification of balanced cycles (both signs)

`BalancedPow.no_balanced_cycle_all` shows that no nontrivial *positive* cycle has a circularly balanced
parity vector. Every step of that argument except the last is sign-free, so the same method
**classifies all balanced cycles** of the accelerated `3x + 1` map on `ℤ` (`balanced_cycle_classification`):

> A Syracuse cycle (of either sign) has a circularly balanced parity vector only if it is the trivial
> cycle `1`, the cycle `-1`, or the cycle `-5 → -7`.

The proof:
* All gaps `1` (`E = o`): the gap word is `1^o` and `x = -1`.
* Otherwise, Knight for powers gives `2^{n'} - 3^{p'} = ±1`. The sign `+` forces `A = 10`, so
  `E = 2o`, so `D > 0`, so `x > 0`, and the positive result gives `x = 1`. The sign `-` forces
  `(p', n') = (2, 3)`, so `A = 110` (`three_pow_eq_two_pow_add_one`), and the parity vector is
  `(110)^g` or `(101)^g`. Decoding (`pv` is injective on positive words) gives the gap word `(1,2)^g`
  or `(2,1)^g`, hence `x = -5` or `-7`.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `3^p = 2^n + 1 ⇒ (p,n) ∈ {(1,1), (2,3)}` | `three_pow_eq_two_pow_add_one` | proved |
| `pv` is injective on positive words; `pv(u ++ v) = pv u ++ pv v` | `pv_injective`, `pv_append` | proved |
| balanced cycles (either sign) are `1`, `-1`, `-5`, `-7` | `balanced_cycle_classification` | proved (no literature input) |
-/

namespace Syracuse.BalancedClass

open Syracuse Syracuse.CocycleCombine Syracuse.Balanced Syracuse.Christoffel Syracuse.BalancedPow

/-! ## Arithmetic: `3^p = 2^n + 1` -/

lemma three_pow_mod_sixteen (p : ℕ) : 3 ^ p % 16 = 3 ^ (p % 4) % 16 := by
  conv_lhs => rw [← Nat.mod_add_div p 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod (3 ^ 4)]; norm_num

lemma three_pow_mod_five (p : ℕ) : 3 ^ p % 5 = 3 ^ (p % 4) % 5 := by
  conv_lhs => rw [← Nat.mod_add_div p 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod (3 ^ 4)]; norm_num

/-- **`3^p = 2^n + 1` only for `(p,n) = (1,1)` and `(2,3)`.** -/
theorem three_pow_eq_two_pow_add_one {p n : ℕ} (h : 3 ^ p = 2 ^ n + 1) :
    (p = 1 ∧ n = 1) ∨ (p = 2 ∧ n = 3) := by
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n
    · -- `3^p = 2` is impossible
      exfalso
      have h2 : 3 ^ p = 2 := by simpa using h
      rcases Nat.eq_zero_or_pos p with h0 | h0
      · subst h0; simp at h2
      · have : 3 ∣ 2 := by rw [← h2]; exact dvd_pow_self 3 h0.ne'
        omega
    · left; refine ⟨Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h), rfl⟩
    · exfalso
      have : 3 ^ p = 5 := by simpa using h
      have h1 : p ≤ 1 := by
        by_contra hc; have : 3 ^ 2 ≤ 3 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega); omega
      interval_cases p <;> simp at this
    · right; refine ⟨Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by simpa using h), rfl⟩
  · exfalso
    have h16 : 3 ^ p % 16 = 1 := by
      have : 16 ∣ 2 ^ n := by
        rw [show n = 4 + (n - 4) by omega, pow_add]; exact dvd_mul_right _ _
      omega
    have hp4 : p % 4 = 0 := by
      rw [three_pow_mod_sixteen] at h16
      have := Nat.mod_lt p (by norm_num : 0 < 4)
      interval_cases (p % 4) <;> simp_all
    have h5 : 3 ^ p % 5 = 1 := by rw [three_pow_mod_five, hp4]; norm_num
    have : 2 ^ n % 5 = 0 := by omega
    have h2 : ¬ 5 ∣ 2 ^ n := by
      intro hd
      have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) hd)
      omega
    exact h2 (Nat.dvd_of_mod_eq_zero this)

/-! ## Decoding parity vectors -/

/-- `pv(u ++ v) = pv u ++ pv v`. -/
theorem pv_append (u v : Word) : pv (u ++ v) = pv u ++ pv v := by
  induction u with
  | nil => rfl
  | cons d u ih => simp [pv, ih]

/-- Cancelling leading `false`s before lists that do not start with `false`. -/
lemma replicate_false_cancel {m m' : ℕ} {L L' : List Bool}
    (hL : L.head? ≠ some false) (hL' : L'.head? ≠ some false)
    (h : List.replicate m false ++ L = List.replicate m' false ++ L') : m = m' ∧ L = L' := by
  induction m generalizing m' with
  | zero =>
    rcases m' with _ | m'
    · simpa using h
    · exfalso; simp [List.replicate_succ] at h; subst h; simp at hL
  | succ m ih =>
    rcases m' with _ | m'
    · exfalso; simp [List.replicate_succ] at h; subst h; simp at hL'
    · simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih h; exact ⟨by omega, h2⟩

lemma pv_head (w : Word) : (pv w).head? ≠ some false := by
  cases w <;> simp [pv]

/-- **`pv` is injective on positive words.** -/
theorem pv_injective {w w' : Word} (hw : w.Pos) (hw' : w'.Pos) (h : pv w = pv w') : w = w' := by
  induction w generalizing w' with
  | nil => cases w' <;> simp_all [pv]
  | cons d w ih =>
    cases w' with
    | nil => simp [pv] at h
    | cons d' w' =>
      simp only [pv, List.cons.injEq, true_and] at h
      obtain ⟨e1, e2⟩ := replicate_false_cancel (pv_head w) (pv_head w') h
      have hd : 1 ≤ d := hw d (by simp)
      have hd' : 1 ≤ d' := hw' d' (by simp)
      have : d = d' := by omega
      rw [this, ih (fun e he => hw e (by simp [he])) (fun e he => hw' e (by simp [he])) e2]

/-- `pv` of a word power is the power of `pv`. -/
theorem pv_wpow (v : Word) (g : ℕ) : pv (wpow v g) = lpow (pv v) g := by
  induction g with
  | zero => simp [wpow, lpow, pv]
  | succ g ih =>
    rw [show wpow v (g + 1) = v ++ wpow v g by simp [wpow, List.replicate_succ], pv_append, ih,
      lpow_succ]

/-! ## The classification -/

/-- A positive word with sum equal to length is `1^n`. -/
lemma eq_replicate_one {w : Word} (hw : w.Pos) (h : w.sum = w.length) :
    w = List.replicate w.length 1 := by
  induction w with
  | nil => rfl
  | cons d w ih =>
    have hd : 1 ≤ d := hw d (by simp)
    have hl := CycleLiterature.length_le_sum (fun e he => hw e (List.mem_cons_of_mem d he))
    simp only [List.sum_cons, List.length_cons] at h
    have hd1 : d = 1 := by omega
    have hs : w.sum = w.length := by omega
    rw [List.length_cons, List.replicate_succ, hd1, ← ih (fun e he => hw e (List.mem_cons_of_mem d he)) hs]

/-- **Classification of balanced cycles.** A Syracuse cycle of either sign whose parity vector is
circularly balanced is the cycle through `1`, `-1`, `-5` or `-7`. -/
theorem balanced_cycle_classification {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    (hb : CircBalanced (pv (gapWord x o))) : x = 1 ∨ x = -1 ∨ x = -5 ∨ x = -7 := by
  have hp := IsSyrCycle.pos h
  have ho : 0 < o := h.1
  set w := gapWord x o with hw_def
  set E := w.sum
  have hlen : (pv w).length = E := pv_length hp
  have hcnt : (pv w).count true = o := by rw [pv_count, gapWord_length]
  have hwl : w.length = o := gapWord_length x o
  have hoE : o ≤ E := by have := CycleLiterature.length_le_sum hp; omega
  have hceq := h.cycle_equation
  rcases Nat.eq_or_lt_of_le hoE with heq | hlt
  · -- all gaps `1`: `x = -1`
    right; left
    have hrep : w = List.replicate o 1 := by
      have := eq_replicate_one hp (by rw [hwl]; exact heq.symm); rwa [hwl] at this
    have hS := BoundedDefectLever.S_replicate_mul (2 : ℤ) 3 1 o
    rw [← hw_def, hrep] at hceq
    simp only [Dz, Sz, D, List.sum_replicate, List.length_replicate, smul_eq_mul, mul_one] at hceq
    simp only [mul_one, pow_one] at hS
    have hD : (2 : ℤ) ^ o - 3 ^ o ≠ 0 := by
      have : (2 : ℤ) ^ o < 3 ^ o := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
      linarith
    have : ((2 : ℤ) ^ o - 3 ^ o) * (x + 1) = 0 := by linear_combination hceq - hS
    have := (mul_eq_zero.1 this).resolve_left hD
    linarith
  · -- reduce the slope and apply Knight for powers
    set gg := Nat.gcd o E
    have hg : 0 < gg := Nat.gcd_pos_of_pos_left _ ho
    set p' := o / gg
    set n' := E / gg
    have ho' : o = gg * p' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left o E)).symm
    have hE' : E = gg * n' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right o E)).symm
    have hcop : Nat.Coprime p' n' := Nat.coprime_div_gcd_div_gcd hg
    have hp'0 : 0 < p' := Nat.pos_of_ne_zero (by rintro h0; rw [h0, mul_zero] at ho'; omega)
    have hp'n' : p' < n' := by
      by_contra hc; replace hc := not_lt.mp hc
      have : gg * n' ≤ gg * p' := Nat.mul_le_mul_left _ hc
      omega
    have hn : 0 < (pv w).length := by omega
    have hrot := isRotated_upper' hb hn
    have hU : upper o E = lpow (upper p' n') gg := by
      rw [show upper o E = upper (gg * p') (gg * n') by rw [← ho', ← hE'], upper_mul hg (by omega)]
    rw [hcnt, hlen, hU] at hrot
    obtain ⟨u, hu, hl⟩ := christoffel_shape hp'0 hp'n' hcop
    have hlu := lower_isRotated_upper (by omega) hcop
    have hLU : lpow (lower p' n') gg ~r lpow (upper p' n') gg := by
      obtain ⟨j, hj⟩ := hlu; exact ⟨j, by rw [lpow_rotate, hj]⟩
    have hrotL : pv w ~r lpow (lower p' n') gg := hrot.trans hLU.symm
    rw [hu] at hrot; rw [hl] at hrotL
    have hk := knight_pow h u hg hrot hrotL
    set A := true :: (u ++ [false])
    have hAlen : A.length = n' := by
      have := congrArg List.length hu; simpa [upper, word] using this.symm
    have hAcnt : A.count true = p' := by
      have h1 := hrot.perm.count_eq true
      rw [hcnt, lpow_count] at h1
      exact Nat.eq_of_mul_eq_mul_left hg (h1.symm.trans ho')
    have hDA : Dpv (2 : ℤ) 3 A = 2 ^ n' - 3 ^ p' := by simp [Dpv, hAlen, hAcnt]
    rcases Int.natAbs_eq_iff.1 hk with hA1 | hA1
    · -- `2^{n'} = 3^{p'} + 1`: `E = 2o`, `D > 0`, `x > 0`, so `x = 1`
      left
      have hnat : 2 ^ n' = 3 ^ p' + 1 := by
        rw [hDA] at hA1; push_cast at hA1
        have : (2 : ℤ) ^ n' = 3 ^ p' + 1 := by linarith
        exact_mod_cast this
      rcases two_pow_eq_three_pow_add_one hnat with ⟨-, h0⟩ | ⟨hn2, hp1⟩
      · omega
      have hE2 : E = 2 * o := by rw [hE', ho', hn2, hp1]; ring
      have hDpos : 0 < Dz w := by
        simp only [Dz, D, hwl]
        rw [show w.sum = E from rfl, hE2, pow_mul]
        have : (3 : ℤ) ^ o < 4 ^ o := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
        norm_num; linarith
      have hSpos : 0 < Sz w := Program.Sz_pos (by intro h0; rw [h0] at hwl; simp at hwl; omega)
      have hxpos : 0 < x := by
        by_contra hneg; replace hneg := not_lt.mp hneg
        have : Dz w * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hDpos.le hneg
        linarith
      by_contra hx1
      have hcyc := BalancedPow.no_balanced_cycle_all h hxpos hb
      exact hx1 hcyc
    · -- `3^{p'} = 2^{n'} + 1`: `(p', n') = (2, 3)`, `A = 110`
      right; right
      have hnat : 3 ^ p' = 2 ^ n' + 1 := by
        rw [hDA] at hA1; push_cast at hA1
        have : (3 : ℤ) ^ p' = 2 ^ n' + 1 := by linarith
        exact_mod_cast this
      rcases three_pow_eq_two_pow_add_one hnat with ⟨hp1, hn1⟩ | ⟨hp2, hn3⟩
      · omega
      have hA : A = [true, true, false] := by
        rw [← hu, hp2, hn3]; decide
      rw [hA] at hrot
      -- `pv w` is a rotation of `(110)^g` that starts with `true`
      obtain ⟨j, hj⟩ := hrot.symm
      rw [lpow_rotate] at hj
      have hcase : [true, true, false].rotate j = [true, true, false] ∨
          [true, true, false].rotate j = [true, false, true] ∨
          [true, true, false].rotate j = [false, true, true] := by
        rw [← List.rotate_mod]
        have : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
        interval_cases (j % 3) <;> simp [List.rotate]
      have hgw : w = wpow [1, 2] gg ∨ w = wpow [2, 1] gg := by
        rcases hcase with hc | hc | hc
        · left; apply pv_injective hp (pos_wpow (fun d hd => by simp at hd; omega) gg)
          rw [← hj, hc, pv_wpow]; rfl
        · right; apply pv_injective hp (pos_wpow (fun d hd => by simp at hd; omega) gg)
          rw [← hj, hc, pv_wpow]; rfl
        · exfalso
          have hh := pv_head w
          rw [← hj, hc] at hh
          rcases Nat.eq_zero_or_pos gg with h0 | h0
          · omega
          · obtain ⟨k, hk⟩ : ∃ k, gg = k + 1 := ⟨gg - 1, by omega⟩
            rw [hk] at hh
            simp [lpow_succ] at hh
      -- the cycle equation on `v^g`: `D(v)·x = S(v)`
      have finish : ∀ v : Word, w = wpow v gg → D (2 : ℤ) 3 v * x = S (2 : ℤ) 3 v := by
        intro v hv
        rw [← hw_def, hv] at hceq
        simp only [Dz, Sz] at hceq
        rw [CocycleCombine.S_wpow, CocycleCombine.D_wpow] at hceq
        have hgeo : CocycleCombine.geo (2 : ℤ) 3 v gg ≠ 0 := by
          rw [CocycleCombine.geo_eq_sum (2 : ℤ) 3]
          exact (Finset.sum_pos (fun i _ => by positivity) (by simp; omega)).ne'
        have : CocycleCombine.geo (2 : ℤ) 3 v gg * (D 2 3 v * x - S 2 3 v) = 0 := by
          linear_combination hceq
        have := (mul_eq_zero.1 this).resolve_left hgeo
        linarith
      rcases hgw with hv | hv
      · have := finish _ hv; norm_num [D, S] at this; left; linarith
      · have := finish _ hv; norm_num [D, S] at this; right; linarith
  where
    pos_wpow {v : Word} (hv : v.Pos) (g : ℕ) : (wpow v g).Pos := by
      intro d hd
      simp only [wpow, List.mem_flatten, List.mem_replicate] at hd
      obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hd
      exact hv d hl

end Syracuse.BalancedClass
