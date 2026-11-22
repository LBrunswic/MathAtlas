import Syracuse.Approaches.Renormalize

/-!
# Near-standard pairs, and the frontier with the literature

**Near-standard pairs.** `StdPairs` uses that the wedge core `C(u,v)` of a standard pair is
`6`-smooth. The same argument works when the core is `6`-smooth **times a small integer `c`**. With
`D ∣ c·D(u^a)` and `D ∣ c·D(Z^b)`, we get `|D|² < c²·3^E`, while Ellison gives
`|D|² > (4e^{-1/5})^E ≥ (16/5)^E`. Hence there is no cycle once `c²·15^E ≤ 16^E`, i.e.
`E ≥ ln(c²)/ln(16/15) ≈ 31·ln|c|` (`no_cycle_near_std`). This makes the trade-off between the size
of a certificate and the word length explicit. Standard pairs are the case `c = ±1`. Letters
`(1), (d)` have `c = 2^{d-1} - 1`, which is why circuits needed the sandwich as well (`Circuits`).

**The frontier with the literature** (`frontier_lit`). On top of `Frontier.frontier`, the stated
literature Props of `CycleLiterature` add the following for a nontrivial positive cycle:
* `Hercher2023` (no `m`-cycle for `m ≤ 91`): its minimal period has at least `92` blocks (gaps
  `≥ 2`);
* `Hercher2023Cor29` with Barina: more than `1.375·10^11` odd steps.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| no cycle on `u^a Z^b` when `C(u,Z) = 2^i 3^j c` and `c² 15^E ≤ 16^E` | `no_cycle_near_std` | proved (conditional on `Ellison1971`) |
| frontier + Hercher (`≥ 92` blocks at minimal period, `o > 1.375·10^11`) | `frontier_lit` | proved (conditional on Ellison, Barina, Hercher) |
-/

namespace Syracuse.NearStd

open Syracuse Syracuse.TwoBackground Syracuse.StdPairs

/-- `(16/5)^E ≤ (2^E e^{-E/10})²`. -/
lemma sixteen_fifths_le (E : ℕ) :
    ((16 : ℝ) / 5) ^ E ≤ ((2 : ℝ) ^ E * Real.exp (-(E : ℝ) / 10)) ^ 2 := by
  have e1 : Real.exp (1 / 5) ≤ 5 / 4 := by
    have := Real.exp_bound_div_one_sub_of_interval (x := 1 / 5) (by norm_num) (by norm_num)
    linarith [show (1 : ℝ) / (1 - 1 / 5) = 5 / 4 by norm_num]
  have hexp : Real.exp ((E : ℝ) / 5) = Real.exp (1 / 5) ^ E := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hsq : ((2 : ℝ) ^ E * Real.exp (-(E : ℝ) / 10)) ^ 2 * Real.exp ((E : ℝ) / 5) = 4 ^ E := by
    rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    have : ((2 : ℕ) : ℝ) * (-(E : ℝ) / 10) + (E : ℝ) / 5 = 0 := by ring
    rw [this, Real.exp_zero, mul_one, ← pow_mul, mul_comm E 2, pow_mul]; norm_num
  have hb : ((16 : ℝ) / 5) ^ E * Real.exp ((E : ℝ) / 5) ≤ 4 ^ E := by
    rw [hexp, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) E
  rw [← hsq] at hb
  exact le_of_mul_le_mul_right hb (Real.exp_pos _)

/-- **Near-standard pairs.** If `C(u,Z) = 2^i 3^j c` (`c ≠ 0`) and `c²·15^E ≤ 16^E`, then no cycle (of
either sign) has a gap word that is a rotation of `u^a Z^b` (`a, b ≥ 1`), for `E` outside Ellison's
exceptions. -/
theorem no_cycle_near_std (hEl : CycleLiterature.Ellison1971) {u Z : Word} (hu : u.Pos) (hZ : Z.Pos)
    (hu0 : u ≠ []) (hZ0 : Z ≠ []) {i j : ℕ} {c : ℤ} (hc0 : c ≠ 0)
    (hc : core (2 : ℤ) 3 u Z = 2 ^ i * 3 ^ j * c) {x : ℤ} {o : ℕ} (h : IsSyrCycle x o)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hw : gapWord x o ~r bpow u a ++ bpow Z b)
    (hx : (gapWord x o).sum ∉ CycleLiterature.ellisonExceptions)
    (hbig : c ^ 2 * 15 ^ (gapWord x o).sum ≤ 16 ^ (gapWord x o).sum) : False := by
  set w := bpow u a ++ bpow Z b
  have hua : (bpow u a).Pos := pos_bpow hu a
  have hZb : (bpow Z b).Pos := pos_bpow hZ b
  have ne_pow : ∀ {y : Word}, y ≠ [] → ∀ {k : ℕ}, 1 ≤ k → bpow y k ≠ [] := by
    intro y hy k hk h0
    have := congrArg List.length h0
    simp [bpow, CocycleCombine.wpow_length] at this
    rcases this with h1 | h1
    · omega
    · exact hy h1
  have hua0 := ne_pow hu0 ha
  have hZb0 := ne_pow hZ0 hb
  have hne : w ≠ [] := by simp [w, hua0]
  have hwpos : w.Pos := fun d hd => by
    simp only [w, List.mem_append] at hd; rcases hd with hd | hd
    · exact hua d hd
    · exact hZb d hd
  have hsum0 : w.sum ≠ 0 := by
    have := CycleLiterature.length_le_sum hwpos
    have : 0 < w.length := List.length_pos_of_ne_nil hne
    omega
  obtain ⟨hV, hU⟩ := dvd_of_cycle_block h hw hne hsum0
  have hcop := isCoprime_six hne hsum0
  have strip : ∀ y : ℤ, Dz w ∣ core (2 : ℤ) 3 u Z * y → Dz w ∣ c * y := by
    intro y hdy
    rw [hc, mul_assoc] at hdy
    exact CocycleCombine.dvd_of_isCoprime_six_of_dvd hcop _ _ hdy
  have dU := strip _ hU
  have dV := strip _ hV
  have hU0 := Dz_ne_zero hua0
  have hV0 := Dz_ne_zero hZb0
  have leU : |Dz w| ≤ |c| * |Dz (bpow u a)| := by
    have := Int.natAbs_le_of_dvd_ne_zero dU (mul_ne_zero hc0 hU0)
    rw [Int.abs_eq_natAbs, ← abs_mul, Int.abs_eq_natAbs]; exact_mod_cast this
  have leV : |Dz w| ≤ |c| * |Dz (bpow Z b)| := by
    have := Int.natAbs_le_of_dvd_ne_zero dV (mul_ne_zero hc0 hV0)
    rw [Int.abs_eq_natAbs, ← abs_mul, Int.abs_eq_natAbs]; exact_mod_cast this
  have ltU := abs_Dz_lt hua
  have ltV := abs_Dz_lt hZb
  have hE : w.sum = (bpow u a).sum + (bpow Z b).sum := List.sum_append
  have hsw : (gapWord x o).sum = w.sum := hw.perm.sum_eq
  rw [hsw] at hx hbig
  set E := w.sum
  -- `|D|² < c²·3^E`
  have hsq : |Dz w| ^ 2 < c ^ 2 * 3 ^ E := by
    have hc2 : c ^ 2 = |c| * |c| := by rw [sq, ← abs_mul_abs_self]
    rw [hE, pow_add, sq, hc2]
    calc |Dz w| * |Dz w| ≤ (|c| * |Dz (bpow u a)|) * (|c| * |Dz (bpow Z b)|) :=
          mul_le_mul leU leV (abs_nonneg _) (by positivity)
      _ < (|c| * 3 ^ (bpow u a).sum) * (|c| * 3 ^ (bpow Z b).sum) := by
          have hcpos : 0 < |c| := abs_pos.mpr hc0
          apply mul_lt_mul'' (mul_lt_mul_of_pos_left ltU hcpos) (mul_lt_mul_of_pos_left ltV hcpos)
            (by positivity) (by positivity)
      _ = |c| * |c| * (3 ^ (bpow u a).sum * 3 ^ (bpow Z b).sum) := by ring
  -- Ellison
  have hEpos : 0 < E := Nat.pos_of_ne_zero hsum0
  have hopos : 0 < w.length := List.length_pos_of_ne_nil hne
  have hEl' := hEl E w.length hEpos hopos hx
  have hDr : |(2 : ℝ) ^ E - 3 ^ w.length| = ((|Dz w| : ℤ) : ℝ) := by
    simp only [Dz, D]; push_cast; rfl
  rw [hDr] at hEl'
  have hA0 : 0 ≤ (2 : ℝ) ^ E * Real.exp (-(E : ℝ) / 10) := by positivity
  have hlt := pow_lt_pow_left₀ hEl' hA0 (by norm_num : (2 : ℕ) ≠ 0)
  have h165 := sixteen_fifths_le E
  -- `c²·3^E ≤ (16/5)^E` from `c²·15^E ≤ 16^E`
  have hbigR : ((c ^ 2 : ℤ) : ℝ) * 3 ^ E ≤ ((16 : ℝ) / 5) ^ E := by
    have h1 : ((c ^ 2 * 15 ^ E : ℤ) : ℝ) ≤ ((16 ^ E : ℤ) : ℝ) := by exact_mod_cast hbig
    push_cast at h1
    have h5 : (0 : ℝ) < 5 ^ E := by positivity
    rw [div_pow, le_div_iff₀ h5]
    push_cast
    calc (c : ℝ) ^ 2 * 3 ^ E * 5 ^ E = (c : ℝ) ^ 2 * 15 ^ E := by
          rw [mul_assoc, ← mul_pow]; norm_num
      _ ≤ 16 ^ E := h1
  have hsqR : ((|Dz w| : ℤ) : ℝ) ^ 2 < ((c ^ 2 : ℤ) : ℝ) * 3 ^ E := by exact_mod_cast hsq
  linarith

/-- **The frontier with the literature.** Given Ellison, Barina, Hercher 2023 (no `m`-cycle for
`m ≤ 91`) and Hercher's Cor. 29, a nontrivial positive cycle satisfies all of `Frontier.frontier`, its
minimal period carries at least `92` blocks, and it has more than `1.375·10^11` odd steps. -/
theorem frontier_lit (hEl : CycleLiterature.Ellison1971) (hB : CycleLiterature.Barina2025)
    (hH : CycleLiterature.Hercher2023) (hH29 : CycleLiterature.Hercher2023Cor29)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x) (hx1 : x ≠ 1) :
    137500000000 < o ∧ (∃ m, 92 ≤ m ∧ CycleLiterature.IsMCycle x m) ∧
    ¬ Balanced.CircBalanced (CocycleCombine.pv (gapWord x o)) ∧
    (∀ u v : Word, ∀ a b : ℕ, StdPair u v → 1 ≤ a → 1 ≤ b → ¬ (gapWord x o ~r bpow u a ++ bpow v b)) ∧
    (∀ u v : Word, ∀ a₁ a₂ : ℕ, StdPair u v → 1 ≤ a₁ → 1 ≤ a₂ →
      ¬ (gapWord x o ~r (bpow u a₁ ++ v) ++ (bpow u a₂ ++ v))) := by
  have hf := Frontier.frontier hEl hB h hx hx1
  refine ⟨CycleLiterature.hercher_odd_steps_of_barina hH29 hB h hx hx1, ?_, hf.2.2.2.2.1,
    hf.2.2.2.2.2.2.1, fun u v a₁ a₂ hst h1 h2 hw => Renormalize.no_pos_two_cycle hEl hB hst h hx h1 h2 hw⟩
  obtain ⟨m, hm1, hmc⟩ := CycleLiterature.exists_isMCycle h hx
  refine ⟨m, ?_, hmc⟩
  by_contra hlt
  exact hx1 (hH x m hm1 (by omega) hmc)

end Syracuse.NearStd
