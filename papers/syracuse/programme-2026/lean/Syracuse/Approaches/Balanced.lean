import Syracuse.Approaches.Christoffel

/-!
# Circularly balanced words are Christoffel conjugates (Lothaire 2.1.15), and no balanced cycle

A binary word `w` of length `n` with `p` ones is **circularly balanced** if any two cyclic factors of
the same length contain numbers of `1`s that differ by at most one. Lothaire (*Algebraic
Combinatorics on Words*, Lemma 2.1.15, after Tijdeman) and Berstel–Lauve–Reutenauer–Saliola
(Thm 6.9) show that such words are exactly the conjugates of Christoffel words. We prove the
direction the cycle problem needs, for coprime `(p, n)`: **a circularly balanced word is a rotation of
the upper Christoffel word** (`isRotated_upper`).

Proof (cycle lemma). Let `x` be the periodic extension of `w`, `P(i)` the number of ones among its
first `i` letters, and `F(i) = n·P(i) - i·p` (period `n`). A window of length `k` starting at `s`
contains `P(s+k) - P(s)` ones, and `n` times that is `F(s+k) - F(s) + kp`. Start at a minimiser `j`
of `F`. Balance applied at the maximiser `a`, together with coprimality (`F(i) ≡ -ip mod n`), gives
`max F - min F < n`. Hence every prefix count of the rotation at `j` lies in `[kp/n, kp/n + 1)`, so it
equals `⌈kp/n⌉`. That is the upper mechanical word.

Combined with `Christoffel.no_high_cycle`: **no nontrivial positive Syracuse cycle with coprime
`(o, E)` has a circularly balanced parity vector** (`no_balanced_cycle`). This closes the "balanced
half" of the covering dichotomy (review direction D2). Every remaining cycle has an unbalanced parity
word.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| window counts are prefix differences of the periodic extension | `count_take_rotate` | proved |
| `P(i + n) = P(i) + p`, `F` has period `n` | `P_add_length`, `F_add_length` | proved |
| cycle lemma: `F` has a minimiser and a maximiser on one period | `exists_min`, `exists_max` | proved |
| balanced and coprime ⇒ `max F - min F < n` | `F_range_lt` | proved |
| balanced and coprime ⇒ rotation of the upper Christoffel word (Lothaire 2.1.15, ⇒ direction) | `isRotated_upper` | proved |
| no nontrivial positive cycle with a balanced parity vector (coprime `(o, E)`) | `no_balanced_cycle` | proved |
| the converse (Christoffel words are balanced); the non-coprime case | — | not formalized |
-/

namespace Syracuse.Balanced

open Syracuse Syracuse.Christoffel

variable (w : List Bool)

/-- The periodic extension of `w`. -/
def xp (i : ℕ) : Bool := w.getD (i % w.length) false

/-- `P(i)`: the number of `true`s among the first `i` letters of the periodic extension. -/
def P : ℕ → ℕ
  | 0 => 0
  | i + 1 => P i + if xp w i then 1 else 0

/-- **Circularly balanced**: any two cyclic factors of the same length `k ≤ n` have numbers of
`true`s differing by at most one. -/
def CircBalanced : Prop :=
  ∀ s t k, k ≤ w.length →
    ((w.rotate s).take k).count true ≤ ((w.rotate t).take k).count true + 1

variable {w}

/-- Letters of a rotation are letters of the periodic extension. -/
lemma getElem_rotate_xp (s i : ℕ) (h : i < (w.rotate s).length) :
    (w.rotate s)[i] = xp w (s + i) := by
  have hl : i < w.length := by simpa using h
  rw [List.getElem_rotate, xp, List.getD_eq_getElem _ _ (Nat.mod_lt _ (by omega)), add_comm]

/-- **Window counts.** For `k ≤ n`, the cyclic factor of length `k` at `s` has `P(s+k) - P(s)` ones. -/
theorem count_take_rotate (s k : ℕ) (hk : k ≤ w.length) :
    ((w.rotate s).take k).count true + P w s = P w (s + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < (w.rotate s).length := by simp; omega
    have ih' := ih (by omega)
    rw [List.take_add_one, List.count_append, List.getElem?_eq_getElem hk', Option.toList_some,
      getElem_rotate_xp s k hk', show s + (k + 1) = (s + k) + 1 by omega, P]
    cases xp w (s + k) <;> simp <;> omega

/-- `P(n) = p`. -/
lemma P_length : P w w.length = w.count true := by
  have := count_take_rotate (w := w) 0 w.length le_rfl
  simpa [P] using this.symm

/-- `P` grows by `p` over each period. -/
theorem P_add_length (i : ℕ) : P w (i + w.length) = P w i + w.count true := by
  have := count_take_rotate (w := w) i w.length le_rfl
  rw [List.take_of_length_le (by simp), (List.rotate_perm w i).count_eq] at this
  omega

/-- The potential `F(i) = n·P(i) - i·p`. -/
def F (i : ℕ) : ℤ := (w.length : ℤ) * P w i - i * w.count true

/-- `F` has period `n`. -/
theorem F_add_length (i : ℕ) : F (w := w) (i + w.length) = F (w := w) i := by
  simp only [F, P_add_length]; push_cast; ring

/-- `F(i) = F(i mod n)`. -/
lemma F_mod (i : ℕ) : F (w := w) (i % w.length) = F (w := w) i := by
  conv_rhs => rw [← Nat.mod_add_div i w.length]
  generalize i / w.length = q
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← add_assoc, F_add_length, ih]

/-- `n` times a window count is a difference of `F`, plus `kp`. -/
lemma window_F (s k : ℕ) (hk : k ≤ w.length) :
    (w.length : ℤ) * ((w.rotate s).take k).count true = F (w := w) (s + k) - F (w := w) s + k * w.count true := by
  have := count_take_rotate (w := w) s k hk
  simp only [F]
  rw [← this]; push_cast; ring

/-- **Cycle lemma, minimiser.** -/
lemma exists_min (hn : 0 < w.length) : ∃ j < w.length, ∀ i, F (w := w) j ≤ F (w := w) i := by
  obtain ⟨j, hj, hmin⟩ := (Finset.range w.length).exists_min_image (F (w := w)) ⟨0, by simpa using hn⟩
  refine ⟨j, by simpa using hj, fun i => ?_⟩
  calc F (w := w) j ≤ F (w := w) (i % w.length) := hmin _ (by simpa using Nat.mod_lt i hn)
    _ = F (w := w) i := F_mod i

/-- **Cycle lemma, maximiser.** -/
lemma exists_max (hn : 0 < w.length) : ∃ a < w.length, ∀ i, F (w := w) i ≤ F (w := w) a := by
  obtain ⟨a, ha, hmax⟩ := (Finset.range w.length).exists_max_image (F (w := w)) ⟨0, by simpa using hn⟩
  refine ⟨a, by simpa using ha, fun i => ?_⟩
  calc F (w := w) i = F (w := w) (i % w.length) := (F_mod i).symm
    _ ≤ F (w := w) a := hmax _ (by simpa using Nat.mod_lt i hn)

/-- **Range bound.** For a circularly balanced word with coprime `(p, n)`, `max F - min F < n`. -/
theorem F_range_lt (hb : CircBalanced w) (hn : 0 < w.length) (hc : Nat.Coprime (w.count true) w.length)
    {j a : ℕ} (hj : j < w.length) (ha : a < w.length)
    (hjmin : ∀ i, F (w := w) j ≤ F (w := w) i) (hamax : ∀ i, F (w := w) i ≤ F (w := w) a) :
    F (w := w) a - F (w := w) j < w.length := by
  set n := w.length with hn_def
  set p := w.count true
  -- `k` is the forward distance from `j` to `a`
  set k := (a + n - j) % n with hk_def
  have hkn : k < n := Nat.mod_lt _ hn
  have hjk : F (w := w) (j + k) = F (w := w) a := by
    rw [← F_mod, show (j + k) % n = a by
      rw [hk_def, Nat.add_mod_mod, show j + (a + n - j) = a + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt ha]]
  have h1 := window_F (w := w) j k hkn.le
  have h2 := window_F (w := w) a k hkn.le
  have hbal := hb j a k hkn.le
  have h3 : F (w := w) (a + k) ≤ F (w := w) a := hamax _
  -- `n·(h_j - h_a) ≤ n`, and `n·h_j - n·h_a = (F a - F j) + (F a - F(a+k))`
  have hle : F (w := w) a - F (w := w) j ≤ n := by
    have : (n : ℤ) * ((w.rotate j).take k).count true ≤ n * (((w.rotate a).take k).count true + 1) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hbal) (by positivity)
    rw [hjk] at h1
    nlinarith
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    -- `F a - F j = n` gives `n ∣ (a - j)·p`, so `a = j` by coprimality, so `n = 0`
    have hdiv : (n : ℤ) ∣ ((a : ℤ) - j) * p :=
      ⟨(P w a : ℤ) - P w j - 1, by simp only [F] at heq; linear_combination (-1 : ℤ) * heq⟩
    have hcop : IsCoprime (n : ℤ) p := Nat.isCoprime_iff_coprime.mpr hc.symm
    have hd := hcop.dvd_of_dvd_mul_right hdiv
    have h0 : (a : ℤ) - j = 0 :=
      Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> omega)
    have : a = j := by omega
    subst this
    have : (n : ℤ) = 0 := by linarith
    omega

/-- **Every prefix count of the minimising rotation is `⌈kp/n⌉`.** -/
theorem prefix_count_eq (hb : CircBalanced w) (hn : 0 < w.length)
    (hc : Nat.Coprime (w.count true) w.length) {j : ℕ} (hj : j < w.length)
    (hjmin : ∀ i, F (w := w) j ≤ F (w := w) i) (k : ℕ) (hk : k ≤ w.length) :
    ((w.rotate j).take k).count true = (k * w.count true + (w.length - 1)) / w.length := by
  obtain ⟨a, ha, hamax⟩ := exists_max (w := w) hn
  have hr := F_range_lt hb hn hc hj ha hjmin hamax
  have hw := window_F (w := w) j k hk
  have hlo : F (w := w) j ≤ F (w := w) (j + k) := hjmin _
  have hhi : F (w := w) (j + k) ≤ F (w := w) a := hamax _
  set h := ((w.rotate j).take k).count true
  symm
  apply Nat.div_eq_of_lt_le
  · -- `n·h ≤ kp + n - 1`
    have : (w.length : ℤ) * h < k * w.count true + w.length := by linarith
    have : w.length * h < k * w.count true + w.length := by exact_mod_cast this
    rw [mul_comm]; omega
  · -- `kp + n - 1 < n·(h+1)`
    have : (k * w.count true : ℤ) ≤ w.length * h := by linarith
    have : k * w.count true ≤ w.length * h := by exact_mod_cast this
    rw [Nat.succ_mul, mul_comm h]; omega

/-- **Lothaire 2.1.15 (⇒ direction).** A circularly balanced binary word with coprime numbers of
ones and letters is a rotation of the upper Christoffel word. -/
theorem isRotated_upper (hb : CircBalanced w) (hn : 0 < w.length)
    (hc : Nat.Coprime (w.count true) w.length) : w ~r upper (w.count true) w.length := by
  obtain ⟨j, hj, hjmin⟩ := exists_min (w := w) hn
  refine ⟨j, List.ext_getElem (by simp [upper]) fun i h1 h2 => ?_⟩
  have hi : i < w.length := by simpa using h1
  have e1 := prefix_count_eq hb hn hc hj hjmin i hi.le
  have e2 := prefix_count_eq hb hn hc hj hjmin (i + 1) hi
  have hstep : ((w.rotate j).take (i + 1)).count true =
      ((w.rotate j).take i).count true + if (w.rotate j)[i]'h1 then 1 else 0 := by
    rw [List.take_add_one, List.count_append, List.getElem?_eq_getElem h1, Option.toList_some]
    cases (w.rotate j)[i] <;> simp
  simp only [upper, word, List.getElem_map, List.getElem_range, mech]
  rw [e1, e2] at hstep
  rcases hx : (w.rotate j)[i] with _ | _ <;> rw [hx] at hstep <;> simp at hstep ⊢ <;> omega

/-- **No balanced cycle.** A positive Syracuse cycle with coprime `(o, E)` whose parity vector is
circularly balanced is the trivial cycle. -/
theorem no_balanced_cycle {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hcop : Nat.Coprime o (gapWord x o).sum)
    (hb : CircBalanced (CocycleCombine.pv (gapWord x o))) : x = 1 := by
  have hp := CocycleCombine.IsSyrCycle.pos h
  have hlen := CocycleCombine.pv_length hp
  have hcnt := CocycleCombine.pv_count (gapWord x o)
  rw [gapWord_length] at hcnt
  have hn : 0 < (CocycleCombine.pv (gapWord x o)).length := by
    rw [hlen]
    by_contra h0
    have hE : (gapWord x o).sum = 0 := by omega
    have h32 := Program.three_pow_lt_two_pow h hx
    rw [hE, pow_zero] at h32
    have := one_le_pow₀ (by norm_num : (1 : ℤ) ≤ 3) (n := o)
    linarith
  have hrot := isRotated_upper hb hn (by rw [hcnt, hlen]; exact hcop)
  rw [hcnt, hlen] at hrot
  exact no_high_cycle h hx hcop hrot

end Syracuse.Balanced
