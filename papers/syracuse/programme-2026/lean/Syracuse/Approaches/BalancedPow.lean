import Syracuse.Approaches.Balanced
import Syracuse.Approaches.Limits

/-!
# No balanced cycle, without coprimality

`Balanced.no_balanced_cycle` excludes positive cycles with a circularly balanced parity vector when
`gcd(o, E) = 1`. Here the coprimality hypothesis is removed (`no_balanced_cycle_all`).

1. **Averaging** (`sum_window`): the counts of ones in the `n` cyclic windows of length `k` sum to
   `k·p`. With balance, this gives `max F - min F < n` for *every* balanced word (`F_range_lt'`). So a
   balanced word is a rotation of the (possibly non-reduced) upper mechanical word
   (`isRotated_upper'`).
2. **Non-reduced mechanical words are powers** (`word_mul`): with `g = gcd(p, n)`, the upper/lower
   word of slope `p/n` is the `g`-th power of the primitive Christoffel word of slope `(p/g)/(n/g)`.
3. **Knight for powers** (`knight_pow`): for `A = 1u0`, `B = 0u1`,
   `Y·g(A^k) - g(B^k) + D(A^k) = geo_k·X^{|A|-1}(X - 1)` and `D(A^k) = geo_k·D(A)`. On a cycle whose
   parity vector is a rotation of both `A^k` and `B^k`, this forces `|D(A)| = 1`.
4. **Finish.** Gersonides forces `A = 10`, so `E = 2o`, which contradicts the sandwich
   `2^E 3^o ≤ 10^o` (`12^o > 10^o`) unless the cycle is trivial.

## Coverage

| Claim | Lean name | Status |
|---|---|---|
| window counts average to `kp/n` | `sum_window` | proved |
| balanced ⇒ `max F - min F < n` (no coprimality) | `F_range_lt'` | proved |
| balanced ⇒ rotation of the upper mechanical word (Lothaire 2.1.15 ⇒, any gcd) | `isRotated_upper'` | proved |
| non-reduced mechanical words are powers of the primitive one | `word_mul` | proved |
| Knight's C9 for powers | `knight_pow` | proved |
| no nontrivial positive cycle with a circularly balanced parity vector (any `gcd(o, E)`) | `no_balanced_cycle_all` | proved |
-/

namespace Syracuse.BalancedPow

open Syracuse Syracuse.Balanced Syracuse.Christoffel Syracuse.CocycleCombine

/-! ## 1. Averaging -/

section Avg

variable {w : List Bool}

/-- Shifting the summation window of the periodic `F` does not change its sum over a period. -/
lemma sum_F_shift (k : ℕ) :
    ∑ s ∈ Finset.range w.length, F (w := w) (s + k) = ∑ s ∈ Finset.range w.length, F (w := w) s := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := Finset.sum_range_succ' (fun i => F (w := w) (i + k)) w.length
    have h2 := Finset.sum_range_succ (fun i => F (w := w) (i + k)) w.length
    have hp : F (w := w) (w.length + k) = F (w := w) (0 + k) := by
      rw [zero_add, add_comm, F_add_length]
    simp only [show ∀ i, i + 1 + k = i + (k + 1) by intro i; ring] at h1
    linarith

/-- **Averaging.** The `n` cyclic windows of length `k ≤ n` contain `k·p` ones in total. -/
theorem sum_window (k : ℕ) (hk : k ≤ w.length) :
    ∑ s ∈ Finset.range w.length, (((w.rotate s).take k).count true : ℤ) = k * w.count true := by
  have hn : (0 : ℤ) ≤ w.length := by positivity
  rcases Nat.eq_zero_or_pos w.length with h0 | hpos
  · have : k = 0 := by omega
    subst this; simp [h0]
  have key : (w.length : ℤ) * ∑ s ∈ Finset.range w.length, (((w.rotate s).take k).count true : ℤ) =
      w.length * (k * w.count true) := by
    rw [Finset.mul_sum]
    simp_rw [window_F (w := w) _ k hk]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_F_shift, sub_self, zero_add,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_left_cancel₀ (by exact_mod_cast hpos.ne') key

/-- **Range bound without coprimality.** For a circularly balanced word, `max F - min F < n`. -/
theorem F_range_lt' (hb : CircBalanced w) (hn : 0 < w.length)
    {j a : ℕ} (hj : j < w.length) (ha : a < w.length)
    (_hjmin : ∀ i, F (w := w) j ≤ F (w := w) i) (_hamax : ∀ i, F (w := w) i ≤ F (w := w) a) :
    F (w := w) a - F (w := w) j < w.length := by
  by_contra hge
  replace hge := not_lt.mp hge
  set n := w.length with hn_def
  set p := w.count true
  set k := (a + n - j) % n with hk_def
  have hkn : k < n := Nat.mod_lt _ hn
  have hjk : F (w := w) (j + k) = F (w := w) a := by
    rw [← F_mod, show (j + k) % n = a by
      rw [hk_def, Nat.add_mod_mod, show j + (a + n - j) = a + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt ha]]
  have hwj := window_F (w := w) j k hkn.le
  rw [hjk] at hwj
  -- every window of length `k` has `n·h ≥ kp`
  have hall : ∀ s ∈ Finset.range n,
      (0 : ℤ) ≤ n * (((w.rotate s).take k).count true : ℤ) - k * p := by
    intro s _
    have hbal := hb j s k hkn.le
    have : (n : ℤ) * ((w.rotate j).take k).count true ≤ n * (((w.rotate s).take k).count true + 1) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hbal) (by positivity)
    nlinarith
  have hsum : ∑ s ∈ Finset.range n, ((n : ℤ) * (((w.rotate s).take k).count true : ℤ) - k * p) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_window k hkn.le, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]; ring
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hall).1 hsum j (by simpa using hj)
  have : (0 : ℤ) < n := by exact_mod_cast hn
  linarith

/-- Prefix counts of the minimising rotation are `⌈kp/n⌉` (any balanced word). -/
theorem prefix_count_eq' (hb : CircBalanced w) (hn : 0 < w.length) {j : ℕ} (hj : j < w.length)
    (hjmin : ∀ i, F (w := w) j ≤ F (w := w) i) (k : ℕ) (hk : k ≤ w.length) :
    ((w.rotate j).take k).count true = (k * w.count true + (w.length - 1)) / w.length := by
  obtain ⟨a, ha, hamax⟩ := exists_max (w := w) hn
  have hr := F_range_lt' hb hn hj ha hjmin hamax
  have hw := window_F (w := w) j k hk
  have hlo : F (w := w) j ≤ F (w := w) (j + k) := hjmin _
  have hhi : F (w := w) (j + k) ≤ F (w := w) a := hamax _
  set h := ((w.rotate j).take k).count true
  symm
  apply Nat.div_eq_of_lt_le
  · have : (w.length : ℤ) * h < k * w.count true + w.length := by linarith
    have : w.length * h < k * w.count true + w.length := by exact_mod_cast this
    rw [mul_comm]; omega
  · have : (k * w.count true : ℤ) ≤ w.length * h := by linarith
    have : k * w.count true ≤ w.length * h := by exact_mod_cast this
    rw [Nat.succ_mul, mul_comm h]; omega

/-- **Lothaire 2.1.15 (⇒), any gcd.** A circularly balanced binary word is a rotation of the upper
mechanical word of slope `p/n` (not necessarily reduced). -/
theorem isRotated_upper' (hb : CircBalanced w) (hn : 0 < w.length) :
    w ~r upper (w.count true) w.length := by
  obtain ⟨j, hj, hjmin⟩ := exists_min (w := w) hn
  refine ⟨j, List.ext_getElem (by simp [upper]) fun i h1 h2 => ?_⟩
  have hi : i < w.length := by simpa using h1
  have e1 := prefix_count_eq' hb hn hj hjmin i hi.le
  have e2 := prefix_count_eq' hb hn hj hjmin (i + 1) hi
  have hstep : ((w.rotate j).take (i + 1)).count true =
      ((w.rotate j).take i).count true + if (w.rotate j)[i]'h1 then 1 else 0 := by
    rw [List.take_add_one, List.count_append, List.getElem?_eq_getElem h1, Option.toList_some]
    cases (w.rotate j)[i] <;> simp
  simp only [upper, word, List.getElem_map, List.getElem_range, mech]
  rw [e1, e2] at hstep
  rcases hx : (w.rotate j)[i] with _ | _ <;> rw [hx] at hstep <;> simp at hstep ⊢ <;> omega

end Avg

/-! ## 2. Powers of lists and non-reduced mechanical words -/

/-- The `k`-th power of a list. -/
def lpow (l : List Bool) (k : ℕ) : List Bool := (List.replicate k l).flatten

@[simp] lemma lpow_length (l : List Bool) (k : ℕ) : (lpow l k).length = k * l.length := by
  simp [lpow, List.length_flatten, List.sum_replicate]

lemma lpow_succ (l : List Bool) (k : ℕ) : lpow l (k + 1) = l ++ lpow l k := by
  simp [lpow, List.replicate_succ]

/-- Letters of a power. -/
lemma getElem_lpow (l : List Bool) (k i : ℕ) (h : i < (lpow l k).length) :
    (lpow l k)[i] = l[i % l.length]'(Nat.mod_lt _ (by
      rcases Nat.eq_zero_or_pos l.length with h0 | h0
      · simp [h0] at h
      · exact h0)) := by
  induction k generalizing i with
  | zero => simp at h
  | succ k ih =>
    simp only [lpow_succ]
    by_cases hi : i < l.length
    · rw [List.getElem_append_left hi]; congr 1; exact (Nat.mod_eq_of_lt hi).symm
    · have hi' : i - l.length < (lpow l k).length := by
        simp only [lpow_succ, List.length_append, lpow_length] at h ⊢; omega
      rw [List.getElem_append_right (by omega), ih _ hi']
      congr 1
      conv_rhs => rw [show i = i - l.length + l.length by omega]
      rw [Nat.add_mod_right]

/-- Rotating a power rotates each factor. -/
lemma lpow_rotate (l : List Bool) (k j : ℕ) : (lpow l k).rotate j = lpow (l.rotate j) k := by
  rcases Nat.eq_zero_or_pos l.length with h0 | hl
  · have : l = [] := List.eq_nil_of_length_eq_zero h0
    subst this; simp [lpow]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_rotate, getElem_lpow, getElem_lpow, List.getElem_rotate]
  congr 1
  simp only [lpow_length, List.length_rotate]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp at h1
  rw [Nat.mod_mod_of_dvd _ (Dvd.intro_left k rfl), Nat.mod_add_mod]

/-- Ceiling scaling: `⌈gm/gN⌉ = ⌈m/N⌉` in the form `(gm + gN - 1)/(gN) = (m + N - 1)/N`. -/
lemma ceil_scale {g m N : ℕ} (hg : 0 < g) (hN : 0 < N) :
    (g * m + (g * N - 1)) / (g * N) = (m + (N - 1)) / N := by
  set q := (m + (N - 1)) / N
  have h1 : N * q ≤ m + (N - 1) := Nat.mul_div_le _ _
  have h2 : m + (N - 1) < N * (q + 1) := Nat.lt_mul_div_succ (m + (N - 1)) hN
  apply Nat.div_eq_of_lt_le
  · -- `gN·q ≤ gm + gN - 1`
    have : g * (N * q) ≤ g * (m + (N - 1)) := Nat.mul_le_mul_left g h1
    have hgN : 1 ≤ g * N := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith [Nat.sub_add_cancel hgN, Nat.sub_add_cancel (show 1 ≤ N by omega)]
  · have : g * (m + (N - 1)) < g * (N * (q + 1)) := Nat.mul_lt_mul_of_pos_left h2 hg
    have hgN : 1 ≤ g * N := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith [Nat.sub_add_cancel hgN, Nat.sub_add_cancel (show 1 ≤ N by omega)]

/-- **Non-reduced upper words are powers.** -/
theorem upper_mul {g p n : ℕ} (hg : 0 < g) (hn : 0 < n) :
    upper (g * p) (g * n) = lpow (upper p n) g := by
  apply List.ext_getElem (by simp [upper, word])
  intro i h1 h2
  rw [getElem_lpow]
  simp only [upper, word, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
  rw [mech_index_mod hn i]
  simp only [mech]
  rw [show i * (g * p) + (g * n - 1) = g * (i * p) + (g * n - 1) by ring,
    show (i + 1) * (g * p) + (g * n - 1) = g * ((i + 1) * p) + (g * n - 1) by ring,
    ceil_scale hg hn, ceil_scale hg hn]

/-- **Non-reduced lower words are powers.** -/
theorem lower_mul {g p n : ℕ} (hg : 0 < g) (hn : 0 < n) :
    lower (g * p) (g * n) = lpow (lower p n) g := by
  apply List.ext_getElem (by simp [lower, word])
  intro i h1 h2
  rw [getElem_lpow]
  simp only [lower, word, List.getElem_map, List.getElem_range, List.length_map, List.length_range]
  rw [mech_index_mod hn i]
  simp only [mech, add_zero]
  rw [show i * (g * p) = g * (i * p) by ring, show (i + 1) * (g * p) = g * ((i + 1) * p) by ring,
    Nat.mul_div_mul_left _ _ hg, Nat.mul_div_mul_left _ _ hg]


/-! ## 3. Knight's C9 for powers -/

section Pow

variable {R : Type*} [CommRing R] (X Y : R)

/-- The common geometric factor `geo_k = Σ_{i<k} Y^{c(k-1-i)} X^{n i}`, by recursion. -/
def geoP (n c : ℕ) : ℕ → R
  | 0 => 0
  | k + 1 => Y ^ (c * k) + X ^ n * geoP n c k

lemma lpow_count (A : List Bool) (k : ℕ) : (lpow A k).count true = k * A.count true := by
  induction k with
  | zero => simp [lpow]
  | succ k ih => rw [lpow_succ, List.count_append, ih, Nat.succ_mul]; ring

/-- `D(A^k) = geo_k·D(A)`. -/
theorem Dpv_lpow (A : List Bool) (k : ℕ) :
    Dpv X Y (lpow A k) = geoP X Y A.length (A.count true) k * Dpv X Y A := by
  induction k with
  | zero => simp [lpow, Dpv, geoP]
  | succ k ih =>
    have e : Dpv X Y (lpow A (k + 1)) =
        Y ^ (A.count true * k) * Dpv X Y A + X ^ A.length * Dpv X Y (lpow A k) := by
      simp only [Dpv, lpow_succ, List.length_append, List.count_append, lpow_length, lpow_count,
        pow_add]
      rw [mul_comm k A.length, mul_comm k (A.count true)]
      ring
    rw [e, ih, geoP]; ring

/-- **C9 for powers.** If `|A| = |B|` and `#₁A = #₁B`, then
`Y·g(A^k) - g(B^k) + D(A^k) = geo_k·(Y·g(A) - g(B) + D(A))`. -/
theorem C9_lpow (A B : List Bool) (hl : A.length = B.length) (hc : A.count true = B.count true)
    (k : ℕ) :
    Y * g X Y (lpow A k) - g X Y (lpow B k) + Dpv X Y (lpow A k) =
      geoP X Y A.length (A.count true) k * (Y * g X Y A - g X Y B + Dpv X Y A) := by
  induction k with
  | zero => simp [lpow, Dpv, geoP]
  | succ k ih =>
    have eA : g X Y (lpow A (k + 1)) = Y ^ (A.count true * k) * g X Y A + X ^ A.length * g X Y (lpow A k) := by
      rw [lpow_succ, g_append, lpow_count, mul_comm k]
    have eB : g X Y (lpow B (k + 1)) = Y ^ (A.count true * k) * g X Y B + X ^ A.length * g X Y (lpow B k) := by
      rw [lpow_succ, g_append, lpow_count, mul_comm k, hl, hc]
    have eD : Dpv X Y (lpow A (k + 1)) =
        Y ^ (A.count true * k) * Dpv X Y A + X ^ A.length * Dpv X Y (lpow A k) := by
      simp only [Dpv, lpow_succ, List.length_append, List.count_append, lpow_length, lpow_count,
        pow_add]
      rw [mul_comm k A.length, mul_comm k (A.count true)]
      ring
    rw [eA, eB, eD, geoP]
    linear_combination X ^ A.length * ih

end Pow

/-- `geo_k > 0` at `(2,3)` for `k ≥ 1`. -/
lemma geoP_pos (n c k : ℕ) (hk : 1 ≤ k) : (0 : ℤ) < geoP (2 : ℤ) 3 n c k := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [geoP]
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp [geoP]
    · have := ih h0; positivity

/-- **Knight for powers.** If the parity vector of a genuine cycle is a rotation of both `(1u0)^k`
and `(0u1)^k` (`k ≥ 1`), then `|2^{|1u0|} - 3^{#₁(1u0)}| = 1`. -/
theorem knight_pow {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (u : List Bool) {k : ℕ} (hk : 1 ≤ k)
    (h1 : pv (gapWord x o) ~r lpow (true :: (u ++ [false])) k)
    (h2 : pv (gapWord x o) ~r lpow (false :: (u ++ [true])) k) :
    (Dpv (2 : ℤ) 3 (true :: (u ++ [false]))).natAbs = 1 := by
  set A := true :: (u ++ [false])
  set B := false :: (u ++ [true])
  have hp := IsSyrCycle.pos h
  set w := gapWord x o
  have hD : Dpv (2 : ℤ) 3 (pv w) = Dz w := Dpv_pv _ _ hp
  have hodd : Odd (Dpv (2 : ℤ) 3 (pv w)) := hD ▸ IsSyrCycle.Dz_odd h
  have h0 : Dpv (2 : ℤ) 3 (pv w) ∣ g 2 3 (pv w) := by
    rw [hD, g_pv _ _ hp]; simpa using IsSyrCycle.Dz_dvd_S_rotate h 0
  obtain ⟨n1, hn1⟩ := h1
  obtain ⟨n2, hn2⟩ := h2
  have e1 := dvd_g_rotate hodd h0 n1
  have e2 := dvd_g_rotate hodd h0 n2
  rw [hn1] at e1; rw [hn2] at e2
  have hDA : Dpv (2 : ℤ) 3 (pv w) = Dpv (2 : ℤ) 3 (lpow A k) := by rw [← hn1, Dpv_rotate]
  rw [hDA] at e1 e2 hodd
  have hl : A.length = B.length := by simp [A, B]
  have hc : A.count true = B.count true := by simp [A, B, List.count_append]
  have hcomb := C9_lpow (2 : ℤ) 3 A B hl hc k
  have hC9 : 3 * g (2 : ℤ) 3 A - g 2 3 B + Dpv 2 3 A = 2 ^ (A.length - 1) * (2 - 1) := C9a (2 : ℤ) 3 u
  have hdvd : Dpv (2 : ℤ) 3 (lpow A k) ∣
      geoP (2 : ℤ) 3 A.length (A.count true) k * (2 ^ (A.length - 1) * (2 - 1)) := by
    rw [← hC9, ← hcomb]
    exact dvd_add (dvd_sub (dvd_mul_of_dvd_right e1 _) e2) dvd_rfl
  rw [Dpv_lpow] at hdvd hodd
  have hgeo := geoP_pos A.length (A.count true) k hk
  have hdvd' : Dpv (2 : ℤ) 3 A ∣ 2 ^ (A.length - 1) * 1 := by
    rw [show (2 : ℤ) - 1 = 1 by norm_num] at hdvd
    exact (mul_dvd_mul_iff_left hgeo.ne').1 hdvd
  have hoddA : Odd (Dpv (2 : ℤ) 3 A) := (Int.odd_mul.1 hodd).2
  have := dvd_of_odd_of_dvd_two_pow_mul hoddA _ hdvd'
  exact Int.isUnit_iff_natAbs_eq.1 (isUnit_of_dvd_one this)

/-! ## 4. No balanced cycle, any gcd -/

/-- **No balanced cycle.** No nontrivial positive Syracuse cycle has a circularly balanced parity
vector, whatever `gcd(o, E)` is. -/
theorem no_balanced_cycle_all {x : ℤ} {o : ℕ} (h : IsSyrCycle x o) (hx : 0 < x)
    (hb : CircBalanced (pv (gapWord x o))) : x = 1 := by
  by_contra hx1
  have hp := IsSyrCycle.pos h
  set E := (gapWord x o).sum
  have hlen : (pv (gapWord x o)).length = E := pv_length hp
  have hcnt : (pv (gapWord x o)).count true = o := by rw [pv_count, gapWord_length]
  have ho : 0 < o := h.1
  have h32 := Program.three_pow_lt_two_pow h hx
  have hoE : o < E := by
    by_contra hle; replace hle := not_lt.mp hle
    have : (2 : ℤ) ^ E ≤ 2 ^ o := pow_le_pow_right₀ (by norm_num) hle
    have : (2 : ℤ) ^ o ≤ 3 ^ o := pow_le_pow_left₀ (by norm_num) (by norm_num) o
    linarith
  -- reduce the slope
  set gg := Nat.gcd o E with hgg
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
  -- balanced ⇒ rotation of `(upper p' n')^gg`
  have hn : 0 < (pv (gapWord x o)).length := by omega
  have hrot := isRotated_upper' hb hn
  have hU : upper o E = lpow (upper p' n') gg := by
    rw [show upper o E = upper (gg * p') (gg * n') by rw [← ho', ← hE'], upper_mul hg (by omega)]
  rw [hcnt, hlen, hU] at hrot
  obtain ⟨u, hu, hl⟩ := christoffel_shape hp'0 hp'n' hcop
  have hlu := lower_isRotated_upper (by omega) hcop
  have hLU : lpow (lower p' n') gg ~r lpow (upper p' n') gg := by
    obtain ⟨j, hj⟩ := hlu
    exact ⟨j, by rw [lpow_rotate, hj]⟩
  have hrotL : pv (gapWord x o) ~r lpow (lower p' n') gg := hrot.trans hLU.symm
  rw [hu] at hrot; rw [hl] at hrotL
  have hk := knight_pow h u hg hrot hrotL
  -- sizes of `A = 1u0`
  set A := true :: (u ++ [false])
  have hAlen : A.length = n' := by
    have := congrArg List.length hu; simpa [upper, word] using this.symm
  have hAcnt : A.count true = p' := by
    have h1 := hrot.perm.count_eq true
    rw [hcnt, lpow_count] at h1
    exact Nat.eq_of_mul_eq_mul_left hg (h1.symm.trans ho')
  -- sign: `D(w) = geo·D(A) > 0`
  have hDw : Dz (gapWord x o) = geoP (2 : ℤ) 3 A.length (A.count true) gg * Dpv (2 : ℤ) 3 A := by
    show D (2 : ℤ) 3 (gapWord x o) = _
    rw [← Dpv_pv _ _ hp, ← Dpv_lpow]
    obtain ⟨j, hj⟩ := hrot
    rw [← hj, Dpv_rotate]
  have hDpos := CycleLiterature.cycle_Dz_pos h hx
  rw [hDw] at hDpos
  have hApos : 0 < Dpv (2 : ℤ) 3 A := pos_of_mul_pos_right hDpos (geoP_pos _ _ _ hg).le
  have hA1 : Dpv (2 : ℤ) 3 A = 1 := by have := hk; omega
  have hnat : 2 ^ n' = 3 ^ p' + 1 := by
    simp only [Dpv, hAlen, hAcnt] at hA1
    have : (2 : ℤ) ^ n' = 3 ^ p' + 1 := by linarith
    exact_mod_cast this
  rcases two_pow_eq_three_pow_add_one hnat with ⟨-, h0⟩ | ⟨hn2, hp1⟩
  · omega
  -- `E = 2o` contradicts the sandwich for a nontrivial cycle
  have hE2 : E = 2 * o := by rw [hE', ho', hn2, hp1]; ring
  have hs := Limits.two_pow_mul_three_pow_le h hx hx1
  have hE2' : (gapWord x o).sum = 2 * o := hE2
  rw [hE2', pow_mul, ← mul_pow] at hs
  norm_num at hs
  have h12 : 10 ^ o < 12 ^ o := Nat.pow_lt_pow_left (by norm_num) (by omega)
  exact absurd hs (not_le.mpr h12)

end Syracuse.BalancedPow
