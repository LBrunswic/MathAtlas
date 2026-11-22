import Syracuse.Approaches.TwoBackground
import Syracuse.Approaches.CycleLiterature

/-!
# Two runs at any level of the Christoffel tree (renormalisation, review direction D4)

**Standard pairs** over the gap alphabet `{1, 2}` are generated from `((1), (2))` by the Stern–Brocot
moves `(u, v) ↦ (u, uv)` and `(u, v) ↦ (uv, v)` (`StdPair`). Their products are the Christoffel
words, and words `u^a v^b` are "two growing runs at some level of the continued fraction".

Key fact: the wedge core `C(u,v) = D(u)S(v) - D(v)S(u)` (structure.md C7) **is 6-smooth for every
standard pair**. It starts at `C((1),(2)) = -X(X-1)` and the moves only multiply it by monomials:
`C(u, uv) = X^{|u|} C(u,v)` and `C(uv, v) = Y^{len v} C(u,v)` (`core_left`, `core_right`). So
`C(u,v) = -2^{i+1}3^j` at `(2,3)` (`core_smooth`).

With the two-block identity (`TwoBackground.dvd_of_cycle_block`), a cycle (of **either** sign) on
`u^a v^b` has `D ∣ D(u^a)` and `D ∣ D(v^b)`. Hence `|D|² ≤ |D(u^a)|·|D(v^b)| < 3^{|u^a|}·3^{|v^b|} = 3^E`.
Ellison gives `|D| > 2^E e^{-E/10}`, so `|D|² > (4e^{-1/5})^E ≥ 3^E`, a contradiction
(`no_cycle_std_pair`). No ratio sandwich and no finite window are needed. This generalises
`TwoBackground.no_cycle_one_two`, which is the base pair.

The excluded `E` are Ellison's exceptional values `{1–11, 13, 14, 16, 19, 27}`. The one genuine cycle
there is the negative cycle `-5 → -7`, word `(1)(2)` with `E = 3`.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| `C(u, uv) = X^{|u|}C(u,v)`, `C(uv, v) = Y^{len v}C(u,v)` | `core_left`, `core_right` | proved (generic) |
| standard pairs have a `6`-smooth core `-2^{i+1}3^j` | `core_smooth` | proved |
| standard pairs are positive, nonempty words | `StdPair.pos` | proved |
| no cycle (either sign) on `u^a v^b`, `(u,v)` standard, `a, b ≥ 1`, `E` not exceptional | `no_cycle_std_pair` | proved (conditional on `Ellison1971`) |
-/

namespace Syracuse.StdPairs

open Syracuse Syracuse.TwoBackground

/-- Standard (Christoffel) pairs over the gap alphabet `{1, 2}`. -/
inductive StdPair : Word → Word → Prop
  | base : StdPair [1] [2]
  | left {u v : Word} : StdPair u v → StdPair u (u ++ v)
  | right {u v : Word} : StdPair u v → StdPair (u ++ v) v

section Generic

variable {R : Type*} [CommRing R] (X Y : R)

/-- `C(u, uv) = X^{|u|}·C(u, v)`. -/
theorem core_left (u v : Word) : core X Y u (u ++ v) = X ^ u.sum * core X Y u v := by
  simp only [core, S_append, D_append]; ring

/-- `C(uv, v) = Y^{len v}·C(u, v)`. -/
theorem core_right (u v : Word) : core X Y (u ++ v) v = Y ^ v.length * core X Y u v := by
  simp only [core, S_append, D_append]; ring

end Generic

/-- **The core of a standard pair is `6`-smooth**: `C(u,v) = -2^{i+1}3^j` at `(2,3)`. -/
theorem core_smooth {u v : Word} (h : StdPair u v) :
    ∃ i j : ℕ, core (2 : ℤ) 3 u v = -(2 ^ (i + 1) * 3 ^ j) := by
  induction h with
  | base => exact ⟨0, 0, by decide⟩
  | @left u v _ ih =>
    obtain ⟨i, j, hij⟩ := ih
    exact ⟨i + u.sum, j, by rw [core_left, hij]; ring⟩
  | @right u v _ ih =>
    obtain ⟨i, j, hij⟩ := ih
    exact ⟨i, j + v.length, by rw [core_right, hij]; ring⟩

/-- Standard pairs consist of positive, nonempty words. -/
theorem StdPair.pos {u v : Word} (h : StdPair u v) : u.Pos ∧ v.Pos ∧ u ≠ [] ∧ v ≠ [] := by
  induction h with
  | base => exact ⟨by simp [Word.Pos], by simp [Word.Pos], by simp, by simp⟩
  | @left u v _ ih =>
    obtain ⟨hu, hv, hu0, -⟩ := ih
    exact ⟨hu, fun d hd => by simp only [List.mem_append] at hd; rcases hd with hd | hd
                              · exact hu d hd
                              · exact hv d hd, hu0, by simp [hu0]⟩
  | @right u v _ ih =>
    obtain ⟨hu, hv, hu0, hv0⟩ := ih
    exact ⟨fun d hd => by simp only [List.mem_append] at hd; rcases hd with hd | hd
                          · exact hu d hd
                          · exact hv d hd, hv, by simp [hu0], hv0⟩

/-- Letters of a power are letters of the base word. -/
lemma pos_bpow {u : Word} (hu : u.Pos) (a : ℕ) : (bpow u a).Pos := by
  intro d hd
  simp only [bpow, CocycleCombine.wpow, List.mem_flatten, List.mem_replicate] at hd
  obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hd
  exact hu d hl

/-- `|D(w)| < 3^{|w|}` for a positive word. -/
lemma abs_Dz_lt {w : Word} (hw : w.Pos) : |Dz w| < 3 ^ w.sum := by
  have hl := CycleLiterature.length_le_sum hw
  have h3 : (3 : ℤ) ^ w.length ≤ 3 ^ w.sum := pow_le_pow_right₀ (by norm_num) hl
  have h2 : (2 : ℤ) ^ w.sum < 3 ^ w.sum ∨ w.sum = 0 := by
    rcases Nat.eq_zero_or_pos w.sum with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega))
  have hp2 : (0 : ℤ) < 2 ^ w.sum := by positivity
  have hp3 : (0 : ℤ) < 3 ^ w.length := by positivity
  simp only [Dz, D]
  rw [abs_lt]
  rcases h2 with h2 | h0
  · constructor <;> linarith
  · rw [h0] at h3 ⊢; simp at h3 ⊢
    have : w.length = 0 := by omega
    rw [this]; norm_num

/-- `D(w) ≠ 0` for a nonempty word (parity: `2^E` is even or `1`, `3^o` is odd and `> 1`). -/
lemma Dz_ne_zero {w : Word} (hne : w ≠ []) : Dz w ≠ 0 := by
  intro h0
  simp only [Dz, D, sub_eq_zero] at h0
  have hl : 0 < w.length := List.length_pos_of_ne_nil hne
  rcases Nat.eq_zero_or_pos w.sum with hs | hs
  · rw [hs, pow_zero] at h0
    have : (3 : ℤ) ^ 1 ≤ 3 ^ w.length := pow_le_pow_right₀ (by norm_num) hl
    linarith
  · have h2 : Even ((2 : ℤ) ^ w.sum) := (even_two).pow_of_ne_zero (by omega)
    have h3 : Odd ((3 : ℤ) ^ w.length) := Odd.pow (by decide)
    rw [h0] at h2
    exact (Int.not_even_iff_odd.mpr h3) h2

/-- **No cycle on two runs of a standard pair** (any level of the Christoffel tree, either sign),
conditional on Ellison, for `E` outside Ellison's finite exceptional set. -/
theorem no_cycle_std_pair (hEl : CycleLiterature.Ellison1971) {u v : Word} (hst : StdPair u v)
    {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hw : gapWord x o ~r bpow u a ++ bpow v b)
    (hx : (gapWord x o).sum ∉ CycleLiterature.ellisonExceptions) : False := by
  obtain ⟨hu, hv, hu0, hv0⟩ := hst.pos
  set w := bpow u a ++ bpow v b with hw_def
  have hua : (bpow u a).Pos := pos_bpow hu a
  have hvb : (bpow v b).Pos := pos_bpow hv b
  have hua0 : bpow u a ≠ [] := by
    intro h0; have := congrArg List.length h0
    simp [bpow, CocycleCombine.wpow_length] at this
    rcases this with h1 | h1
    · omega
    · exact hu0 h1
  have hvb0 : bpow v b ≠ [] := by
    intro h0; have := congrArg List.length h0
    simp [bpow, CocycleCombine.wpow_length] at this
    rcases this with h1 | h1
    · omega
    · exact hv0 h1
  have hne : w ≠ [] := by simp [w, hua0]
  have hwpos : w.Pos := fun d hd => by
    simp only [w, List.mem_append] at hd; rcases hd with hd | hd
    · exact hua d hd
    · exact hvb d hd
  have hsum0 : w.sum ≠ 0 := by
    have := CycleLiterature.length_le_sum hwpos
    have : 0 < w.length := List.length_pos_of_ne_nil hne
    omega
  obtain ⟨hV, hU⟩ := dvd_of_cycle_block h hw hne hsum0
  obtain ⟨i, j, hc⟩ := core_smooth hst
  have hcop := isCoprime_six hne hsum0
  have strip : ∀ c : ℤ, Dz w ∣ core (2 : ℤ) 3 u v * c → Dz w ∣ c := by
    intro c hdc
    rw [hc, show -(2 ^ (i + 1) * 3 ^ j) * c = 2 ^ (i + 1) * 3 ^ j * (-c) by ring] at hdc
    have := CocycleCombine.dvd_of_isCoprime_six_of_dvd hcop _ _ hdc
    rwa [dvd_neg] at this
  have dU := strip _ hU
  have dV := strip _ hV
  -- sizes
  have hDw0 := Dz_ne_zero hne
  have hU0 := Dz_ne_zero hua0
  have hV0 := Dz_ne_zero hvb0
  have leU : |Dz w| ≤ |Dz (bpow u a)| := by
    have := Int.natAbs_le_of_dvd_ne_zero dU hU0
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]; exact_mod_cast this
  have leV : |Dz w| ≤ |Dz (bpow v b)| := by
    have := Int.natAbs_le_of_dvd_ne_zero dV hV0
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]; exact_mod_cast this
  have ltU := abs_Dz_lt hua
  have ltV := abs_Dz_lt hvb
  have hE : w.sum = (bpow u a).sum + (bpow v b).sum := List.sum_append
  have hsq : |Dz w| ^ 2 < 3 ^ w.sum := by
    rw [hE, pow_add, sq]
    calc |Dz w| * |Dz w| ≤ |Dz (bpow u a)| * |Dz (bpow v b)| :=
          mul_le_mul leU leV (abs_nonneg _) (abs_nonneg _)
      _ < 3 ^ (bpow u a).sum * 3 ^ (bpow v b).sum := by
          apply mul_lt_mul'' ltU ltV (abs_nonneg _) (abs_nonneg _)
  -- Ellison
  have hsw : (gapWord x o).sum = w.sum := hw.perm.sum_eq
  have hlw : (gapWord x o).length = w.length := hw.perm.length_eq
  have hDeq : Dz (gapWord x o) = Dz w := by
    obtain ⟨n, hn⟩ := hw; rw [← hn]; exact (D_rotate _ _ _ _).symm
  set E := w.sum
  have hEpos : 0 < E := Nat.pos_of_ne_zero hsum0
  have hopos : 0 < w.length := List.length_pos_of_ne_nil hne
  rw [hsw] at hx
  have hEl' := hEl E w.length hEpos hopos hx
  have hDr : |(2 : ℝ) ^ E - 3 ^ w.length| = ((|Dz w| : ℤ) : ℝ) := by
    simp only [Dz, D]; push_cast; rfl
  rw [hDr] at hEl'
  have e1 : Real.exp (1 / 5) ≤ 4 / 3 := by
    have := Real.exp_bound_div_one_sub_of_interval (x := 1 / 5) (by norm_num) (by norm_num)
    linarith [show (1 : ℝ) / (1 - 1 / 5) = 5 / 4 by norm_num]
  -- `3^E ≤ (2^E e^{-E/10})²`
  have key : (3 : ℝ) ^ E ≤ ((2 : ℝ) ^ E * Real.exp (-(E : ℝ) / 10)) ^ 2 := by
    have hexp : Real.exp ((E : ℝ) / 5) = Real.exp (1 / 5) ^ E := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have hsq' : ((2 : ℝ) ^ E * Real.exp (-(E : ℝ) / 10)) ^ 2 * Real.exp ((E : ℝ) / 5) = 4 ^ E := by
      rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      have : ((2 : ℕ) : ℝ) * (-(E : ℝ) / 10) + (E : ℝ) / 5 = 0 := by ring
      rw [this, Real.exp_zero, mul_one, ← pow_mul, mul_comm E 2, pow_mul]; norm_num
    have hb : (3 : ℝ) ^ E * Real.exp ((E : ℝ) / 5) ≤ 4 ^ E := by
      rw [hexp, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith) E
    rw [← hsq'] at hb
    exact le_of_mul_le_mul_right hb (Real.exp_pos _)
  have hA0 : 0 ≤ (2 : ℝ) ^ E * Real.exp (-(E : ℝ) / 10) := by positivity
  have hlt := pow_lt_pow_left₀ hEl' hA0 (by norm_num : (2 : ℕ) ≠ 0)
  have hsqR : ((|Dz w| : ℤ) : ℝ) ^ 2 < 3 ^ E := by exact_mod_cast hsq
  linarith

end Syracuse.StdPairs
