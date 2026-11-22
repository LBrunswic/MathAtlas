import Syracuse.Basic

/-!
# Cycle sums, rotations, the gcd of shifts, and eventually periodic words (`approaches/cycle-gcd`)

Formalisation of `approaches/cycle-gcd/{theorems.md, periodic-words.md, STATUS.md,
eventually-periodic.tex}`. Generic identities are proved for arbitrary `X, Y` in an arbitrary
commutative ring (= `ℤ[X,Y]` identities), then specialised to `(2, 3)` in `ℤ`. Notation as in
`Syracuse.Basic`: `S^{(j)} = Sz (w.rotate j)`, `D = Dz w = 2^E - 3^o`, `E = w.sum`,
`o = w.length`; `u^q = upow u q`; `C(u,v) = D(u)S(v) - D(v)S(u)`; `G w = gcd_{j<o} S^{(j)}`.
"Cycle" means `Follows 2 3 w a a` with `a : ℤ` (any closed integer orbit of the recurrence),
which covers every genuine cycle `IsSyrCycle a o` (corollaries `IsSyrCycle.*`).
`eventually-periodic.tex` numbering is the compiled one (Thm 2.2 telescoping, …, Thm 2.13).

## Coverage

| Note claim (file) | Lean name | Status |
|---|---|---|
| `D ≠ 0` for `o ≥ 1`, `o log₂3 ∉ ℤ` (theorems 1.5; tex 1.5) | `two_pow_ne_three_pow`, `Dz_ne_zero`, `logb_not_int` | proved |
| Closed form, cycle equation (theorems 2.1–2.2; tex 1.3, 1.6) | `Syracuse.Follows.closed_form`, `Follows.cycle_equation` (Basic) | proved (Basic; notes' notation in `Diophantine`) |
| Characters, cocycle, transfer-matrix hom (tex 1.8–1.10; periodic 1.2) | `List.length_append`, `List.sum_append`, `S_append`, `Mw_eq`, `Mw_append` (Basic) | proved (Basic) |
| Antisymmetry `S(uv) - S(vu) = D(u)S(v) - D(v)S(u)` (periodic 1.3; tex 1.11) | `S_append_sub_S_append`, `C`, `C_eq` | proved |
| Rotation recursion `2^{d₀} S(w') = 3S(w) + D`, any word (theorems 3.1; tex 1.12) | `rotation_recursion` (Basic), `rotation_recursion_rotate` (every `j`), `rotation_recursion_two_three` | proved |
| `gcd_j S^{(j)} ∣ D` for every word (theorems 3.2; tex 1.13) | `dvd_D_of_dvd`, `dvd_D_of_forall_dvd` (any ring), `G_dvd_D` | proved |
| Exact gcd `= \|2^E - 3^o\|` on cycles (theorems 3.3; tex 1.14) | `G_eq_abs_D_of_follows`, `IsSyrCycle.G_eq` | proved |
| `E_* = min{E : 2^E > 3^o} = ⌈o log₂3⌉`, critical (theorems 4.1) | `Ecrit`, `Critical`, `critical_iff`, `Ecrit_eq_ceil` | proved |
| Dichotomy & gap bound (theorems 4.2(1)–(3)) | `critical_iff_real`, `not_critical_iff_real`, `not_critical_iff_pow`, `gap_bound` | proved |
| Positive cycle: `2^E > 3^o`; critical `⟺ 2^E < 2·3^o ⟺ ∏(1+1/(3a_k)) < 2`; (4.1) (theorems 4.3) | `three_pow_lt_two_pow_of_follows`, `IsSyrCycle.three_pow_lt`, `IsSyrCycle.critical_iff`, `IsSyrCycle.critical_iff_prod`, `IsSyrCycle.two_pow_eq_prod` | proved |
| `(9,5)` witness `(1,2,2,2,2)`: sums `431,781,653,557,485`, `min = 431 > D = 269 > 256`, primitive, non-critical, gcd `1`, not a cycle (theorems 4.4; STATUS) | `w95_data`, `w95_rotations`, `w95_min`, `w95_min_gt`, `w95_primitive`, `w95_noncritical`, `w95_G`, `w95_prime_431`, `w95_not_cycle` | proved (by computation) |
| Imprimitive `(2,2,2)` non-critical (STATUS) | `imprimitive_noncritical` | corrected: STATUS writes `3×(2,1)`, it is `3×(2)` |
| Worked checks `1→1`, `-5→-7` (STATUS) | `trivial_cycle_check`, `neg_five_cycle_check` | proved |
| Block telescoping `S(u^q v) - S(u^{q-1} v u) = X^{(q-1)\|u\|} C(u,v)` (periodic 2.1; tex 2.2) | `telescoping`, `telescoping'`, `telescoping_rotate`, `upow_rotate` | proved (sign and form as in the notes) |
| `G(u^q v) ∣ C(u,v)`, `q`-free (periodic 3.1; tex 2.3 (8)) | `G_dvd_C` | proved (uses the standing `d_k ≥ 1`, which makes `D` odd) |
| On a cycle `\|D\| ∣ C`, so `C = 0 ∨ \|D\| ≤ \|C\|` (periodic 3.2; tex 2.3 (9)) | `D_dvd_C_of_follows`, `IsSyrCycle.D_dvd_C`, `C_eq_zero_or_abs_D_le` | proved |
| Finitely many `q` per `(u,v)` unless `C = 0` (periodic 3.2; tex after 2.3) | `finite_q` | proved (unconditional) |
| Numerical table, `q ≤ 6` (periodic §3) | `table_values`, `table_G` | proved (by computation) |
| `C = 0 ⟺ S(u)/D(u) = S(v)/D(v)`; contains `v = u^k` (periodic §4; tex 2.4) | `C_eq_zero_iff` (field), `Cz_eq_zero_iff`, `C_upow_self` | proved; "= bounded-circuit cases (Steiner, Simons–de Weger)": literature, not formalized |
| `S(r) < 2^{σ-1}3^ℓ`, `S(r) < 2^{σ-2}3^ℓ`, `\|C\| < 2^{a+b}3^{m+ℓ}` (tex 2.5; periodic §5.1) | `two_mul_Sz_lt`, `four_mul_Sz_le`, `four_mul_Sz_lt`, `abs_Cz_lt`, `two_mul_abs_Cz_lt` (sharper `2\|C\| < …`) | proved (positive words) |
| Smaller guess `2^{\|v\|}3^{m+ℓ}` false, `u=(3,3), v=(1)`: `66 > 54` (tex 2.6; periodic §5.1) | `smaller_guess_false` | proved |
| Matveev's theorem (tex 2.7) | `MatveevTwoThree c` (specialised to `n = 2`, `α = (2,3)`), `c₀` | stated only (a `Prop`, never assumed) |
| `2^E - 3^o > 3^o e^{-c₀(1+log E)}` (tex 2.8) | `lower_bound` | proved (conditional on `MatveevTwoThree c`); the note's `E, o ≥ 2` is not needed |
| Periodic §5.2 form `\|D\| ≥ 2^E exp(-c log E)` | — | imprecise (unspecified `c`); tex 2.8 form formalized instead |
| Exclusion `(q-1) m log3 < (a+b) log2 + c₀(1 + log E)` (tex 2.9; periodic §5.3) | `exclusion` | proved (conditional on `MatveevTwoThree c`) |
| Effective `q ≤ Q(u,v)` (tex 2.9) | `Qbound`, `q_lt_Qbound`, `q_lt_Qbound_c₀`, `IsSyrCycle.q_lt_Qbound` | proved (conditional on `MatveevTwoThree`), explicit `Q` |
| `Q(u,v) ~ (c₀/m) log(c₀/m)`; Remark 2.10 | — | not formalized (asymptotic remark) |
| Positive cycle: `3^o < 2^E` and `2^E ≤ 4^o` (tex §2.7 preamble, which writes `< 4^o`) | `three_pow_lt_two_pow_of_follows`, `follows_pos_bound`, `sum_le_two_mul_length` | corrected: `2^E ≤ 4^o` (equality on `1→1`) |
| Critical band; Prop 2.12 (i)–(iii) (tex 2.11–2.12) | `InBand`, `InBand.Lambda`, `InBand.D_lt`, `InBand.E_eq`, `InBand.bounds`, `InBand.E_le` | proved |
| "A positive cycle necessarily inhabits the band" (tex abstract, Thm 2.13 proof) | `positive_cycle_not_in_band` | **false**: `1→1` traversed 4 times, `2^8 = 256 > 243 = 3^5` |
| Thm 2.13: inequality (14) | `band_exclusion` | corrected: holds (conditional on Matveev) for every positive cycle via `E ≤ 2o`, no band needed; "`E` pinned to ≤ 2 values" only under `InBand` (`InBand.E_eq`) |
| A-priori bound on `gcd_j S^{(j)}`; criticality of primitive cycles (theorems 4.5; STATUS open) | — | open problems, not formalized |
-/

namespace Syracuse.CycleGcd

open Finset

section Generic

variable {R : Type*} [CommRing R] (X Y : R)

/-- **Rotation recursion at every position.** For a nonempty word `w` and `j < o`,
`X^{d_j} S(w^{(j+1)}) = Y S(w^{(j)}) + D(w)`. -/
theorem rotation_recursion_rotate (w : Word) {j : ℕ} (hj : j < w.length) :
    X ^ w[j] * S X Y (w.rotate (j + 1)) = Y * S X Y (w.rotate j) + D X Y w := by
  obtain ⟨d, t, ht⟩ : ∃ d t, w.rotate j = d :: t := by
    rcases h : w.rotate j with _ | ⟨d, t⟩
    · simp only [List.rotate_eq_nil_iff] at h; subst h; simp at hj
    · exact ⟨d, t, rfl⟩
  have hd : w[j] = d := by
    have h0 : 0 < (w.rotate j).length := by simp; omega
    have := List.getElem_rotate w j 0 h0
    simp only [ht, List.getElem_cons_zero, zero_add, Nat.mod_eq_of_lt hj] at this
    exact this.symm
  rw [← List.rotate_rotate, ht, rotate_one_cons, hd, rotation_recursion, ← ht, D_rotate]

/-- Any common divisor of `S(w)` and of its left rotation `S(w')` divides `D(w)`. -/
theorem dvd_D_of_dvd {w : Word} {g : R} (h0 : g ∣ S X Y w) (h1 : g ∣ S X Y (w.rotate 1)) :
    g ∣ D X Y w := by
  cases w with
  | nil => simp
  | cons d t =>
    rw [rotate_one_cons] at h1
    have : D X Y (d :: t) = X ^ d * S X Y (t ++ [d]) - Y * S X Y (d :: t) := by
      rw [rotation_recursion]; ring
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h0 _)

/-- **`gcd_j S^{(j)} ∣ D`, generic form.** A common divisor of all rotation sums divides `D`. -/
theorem dvd_D_of_forall_dvd {w : Word} {g : R} (h : ∀ j, g ∣ S X Y (w.rotate j)) :
    g ∣ D X Y w :=
  dvd_D_of_dvd X Y (by simpa using h 0) (h 1)

/-- **Antisymmetry** (`periodic-words.md` Lemma 1.3, `eventually-periodic.tex` Lemma 1.11):
`S(uv) - S(vu) = D(u) S(v) - D(v) S(u)`. -/
theorem S_append_sub_S_append (u v : Word) :
    S X Y (u ++ v) - S X Y (v ++ u) = D X Y u * S X Y v - D X Y v * S X Y u := by
  rw [S_append, S_append, D, D]; ring

/-- The **core** `C(u, v) = D(u) S(v) - D(v) S(u)`. -/
def C (u v : Word) : R := D X Y u * S X Y v - D X Y v * S X Y u

/-- `C(u, v) = S(uv) - S(vu)`. -/
theorem C_eq (u v : Word) : C X Y u v = S X Y (u ++ v) - S X Y (v ++ u) :=
  (S_append_sub_S_append X Y u v).symm

/-- The power `u^q` of a word (concatenation of `q` copies of `u`). -/
def upow (u : Word) (q : ℕ) : Word := (List.replicate q u).flatten

@[simp] lemma upow_zero (u : Word) : upow u 0 = [] := rfl

/-- `u^{q+1} = u · u^q`. -/
lemma upow_succ (u : Word) (q : ℕ) : upow u (q + 1) = u ++ upow u q := by
  simp [upow, List.replicate_succ]

/-- `u^{q+1} = u^q · u`. -/
lemma upow_succ' (u : Word) (q : ℕ) : upow u (q + 1) = upow u q ++ u := by
  simp [upow, List.replicate_succ', List.flatten_append]

@[simp] lemma upow_length (u : Word) (q : ℕ) : (upow u q).length = q * u.length := by
  induction q with
  | zero => simp
  | succ q ih => rw [upow_succ, List.length_append, ih]; ring

@[simp] lemma upow_sum (u : Word) (q : ℕ) : (upow u q).sum = q * u.sum := by
  induction q with
  | zero => simp
  | succ q ih => rw [upow_succ, List.sum_append, ih]; ring

/-- Powers of a positive word are positive. -/
lemma upow_pos {u : Word} (hu : u.Pos) (q : ℕ) : (upow u q).Pos := by
  intro d hd
  simp only [upow, List.mem_flatten, List.mem_replicate] at hd
  obtain ⟨l, ⟨_, rfl⟩, hl⟩ := hd
  exact hu d hl

/-- Two words with a common prefix `u` and tails of equal length:
`S(uA) - S(uB) = X^{|u|} (S(A) - S(B))`. -/
theorem S_append_sub_S_append_left (u : Word) {A B : Word} (h : A.length = B.length) :
    S X Y (u ++ A) - S X Y (u ++ B) = X ^ u.sum * (S X Y A - S X Y B) := by
  rw [S_append, S_append, h]; ring

/-- Rotating `u^{q+1} v` by `len u` moves the leading block to the tail: `u^q v u`. -/
theorem upow_rotate (u v : Word) (q : ℕ) :
    (upow u (q + 1) ++ v).rotate u.length = upow u q ++ v ++ u := by
  rw [upow_succ, List.append_assoc, List.rotate_append_length_eq]

/-- **Block telescoping** (`periodic-words.md` Thm 2.1, `eventually-periodic.tex` Thm 2.2),
indexed by `q + 1 ≥ 1`: `S(u^{q+1} v) - S(u^q v u) = X^{q|u|} C(u, v)`. -/
theorem telescoping' (u v : Word) (q : ℕ) :
    S X Y (upow u (q + 1) ++ v) - S X Y (upow u q ++ v ++ u) = X ^ (q * u.sum) * C X Y u v := by
  induction q with
  | zero => simp [C_eq, upow]
  | succ q ih =>
    have e1 : upow u (q + 1 + 1) ++ v = u ++ (upow u (q + 1) ++ v) := by
      rw [upow_succ u (q + 1), List.append_assoc]
    have e2 : upow u (q + 1) ++ v ++ u = u ++ (upow u q ++ v ++ u) := by
      rw [upow_succ u q]; simp
    rw [e1, e2, S_append_sub_S_append_left X Y u (by simp; ring), ih, ← mul_assoc, ← pow_add]
    ring_nf

/-- **Block telescoping**, in the notes' indexing (`q ≥ 1`):
`S(u^q v) - S(u^{q-1} v u) = X^{(q-1)|u|} C(u, v)`; the prefactor is a bare power of `X`. -/
theorem telescoping (u v : Word) {q : ℕ} (hq : 1 ≤ q) :
    S X Y (upow u q ++ v) - S X Y (upow u (q - 1) ++ v ++ u) =
      X ^ ((q - 1) * u.sum) * C X Y u v := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hq
  simpa using telescoping' X Y u v q

/-- Telescoping as a difference of two rotation sums of `w = u^q v`:
`S^{(0)}(w) - S^{(len u)}(w) = X^{(q-1)|u|} C(u, v)`. -/
theorem telescoping_rotate (u v : Word) {q : ℕ} (hq : 1 ≤ q) :
    S X Y (upow u q ++ v) - S X Y ((upow u q ++ v).rotate u.length) =
      X ^ ((q - 1) * u.sum) * C X Y u v := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hq
  rw [upow_rotate]
  simpa using telescoping' X Y u v q

/-- The degenerate locus contains `v = u^k` (pure powers: the single-circuit case). -/
theorem C_upow_self (u : Word) (k : ℕ) : C X Y u (upow u k) = 0 := by
  rw [C_eq, ← upow_succ, ← upow_succ', sub_self]

/-- `C(u, v) = 0` iff `u, v` share the fixed point `S/D` (when `D(u), D(v) ≠ 0`), in a field. -/
theorem C_eq_zero_iff {K : Type*} [Field K] (X Y : K) (u v : Word) (hu : D X Y u ≠ 0)
    (hv : D X Y v ≠ 0) : C X Y u v = 0 ↔ S X Y u / D X Y u = S X Y v / D X Y v := by
  rw [C, sub_eq_zero, div_eq_div_iff hu hv]
  constructor <;> intro h <;> linear_combination -h

end Generic


/-! ## The integer specialisation `(X, Y) = (2, 3)` -/

/-- The integer core `C(u, v) = D(u) S(v) - D(v) S(u)` at `(2, 3)`. -/
abbrev Cz (u v : Word) : ℤ := C (2 : ℤ) 3 u v

/-- `G(w) = gcd_{0 ≤ j < o} S^{(j)}`, the gcd of the rotation sums (normalised: `G ≥ 0`). -/
def G (w : Word) : ℤ := (range w.length).gcd fun j => Sz (w.rotate j)

/-- `G ≥ 0` (the gcd is normalised). -/
lemma G_nonneg (w : Word) : 0 ≤ G w := by
  rw [G, ← Finset.normalize_gcd, ← Int.abs_eq_normalize]; exact abs_nonneg _

/-- `G(w)` divides every rotation sum `S^{(j)}` (for every `j`, rotations being periodic). -/
theorem G_dvd_S_rotate (w : Word) (j : ℕ) : G w ∣ Sz (w.rotate j) := by
  rcases eq_or_ne w [] with rfl | hw
  · simp
  · rw [← List.rotate_mod]
    exact Finset.gcd_dvd (mem_range.2 (Nat.mod_lt _ (List.length_pos_iff.2 hw)))

/-- A common divisor of the `o` rotation sums divides `G`. -/
lemma dvd_G {w : Word} {g : ℤ} (h : ∀ j < w.length, g ∣ Sz (w.rotate j)) : g ∣ G w :=
  Finset.dvd_gcd fun j hj => h j (mem_range.1 hj)

/-- **`gcd_j S^{(j)} ∣ D` for every word** (`theorems.md` Cor. 3.2). -/
theorem G_dvd_D (w : Word) : G w ∣ Dz w := dvd_D_of_forall_dvd _ _ (G_dvd_S_rotate w)

/-- **Exact gcd on cycles** (`theorems.md` Thm 3.3): along any closed integer orbit of the
recurrence, `gcd_j S^{(j)} = |2^E - 3^o|`. -/
theorem G_eq_abs_D_of_follows {w : Word} {a : ℤ} (h : Follows (2 : ℤ) 3 w a a) :
    G w = |Dz w| :=
  Int.dvd_antisymm (G_nonneg w) (abs_nonneg _) ((dvd_abs _ _).2 (G_dvd_D w))
    ((abs_dvd _ _).2 (dvd_G fun j _ => Follows.D_dvd_S_rotate 2 3 h j))

/-- **Exact gcd on genuine Syracuse cycles.** -/
theorem IsSyrCycle.G_eq {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    G (gapWord a o) = |Dz (gapWord a o)| := by
  have hf := follows_gapWord a o
  rw [h.2.2] at hf
  exact G_eq_abs_D_of_follows hf

/-- The rotation recursion at `(2, 3)`: `2^{d_j} S^{(j+1)} = 3 S^{(j)} + D`. -/
theorem rotation_recursion_two_three (w : Word) {j : ℕ} (hj : j < w.length) :
    2 ^ w[j] * Sz (w.rotate (j + 1)) = 3 * Sz (w.rotate j) + Dz w :=
  rotation_recursion_rotate 2 3 w hj

/-- `2^E ≠ 3^o` for `o ≥ 1` (`theorems.md` Remark 1.5). -/
theorem two_pow_ne_three_pow (E : ℕ) {o : ℕ} (ho : 0 < o) : (2 : ℤ) ^ E ≠ 3 ^ o := by
  intro h
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · have : (3 : ℤ) ≤ 3 ^ o := le_self_pow₀ (by norm_num) ho.ne'
    rw [← h] at this; norm_num at this
  · have h2 : (2 : ℤ) ∣ 3 ^ o := h ▸ dvd_pow_self 2 hE.ne'
    have := Int.Prime.dvd_pow' (p := 2) Nat.prime_two (n := 3) (k := o) (by exact_mod_cast h2)
    norm_num at this

/-- `D(w) ≠ 0` for every nonempty word (`theorems.md` Remark 1.5). -/
theorem Dz_ne_zero {w : Word} (hw : w ≠ []) : Dz w ≠ 0 :=
  sub_ne_zero.2 (two_pow_ne_three_pow _ (List.length_pos_iff.2 hw))

/-- `D(w) = 2^E - 3^o` is odd as soon as `E ≥ 1`. -/
theorem Dz_odd {w : Word} (hw : 0 < w.sum) : Odd (Dz w) :=
  Even.sub_odd ((Int.even_pow).2 ⟨even_two, hw.ne'⟩) (Odd.pow (by decide))

/-- A positive word has `E ≥ o`. -/
theorem Word.Pos.length_le_sum {w : Word} (hw : w.Pos) : w.length ≤ w.sum := by
  induction w with
  | nil => simp
  | cons d t ih =>
    have hd := hw d (by simp)
    have := ih fun x hx => hw x (by simp [hx])
    simp; omega

/-- Concatenation of positive words is positive. -/
lemma Word.Pos.append {u v : Word} (hu : u.Pos) (hv : v.Pos) : (u ++ v).Pos := by
  intro d hd; rcases List.mem_append.1 hd with h | h; exacts [hu d h, hv d h]

/-- A divisor of an odd integer is coprime to every power of `2`. -/
lemma isCoprime_two_pow_of_dvd_odd {g d : ℤ} (hg : g ∣ d) (hd : Odd d) (n : ℕ) :
    IsCoprime g (2 ^ n) := by
  refine IsCoprime.pow_right (IsCoprime.symm ?_)
  refine (Irreducible.coprime_iff_not_dvd Int.prime_two.irreducible).2 fun h2 => ?_
  exact (Int.not_even_iff_odd.2 hd) (even_iff_two_dvd.2 (h2.trans hg))

/-- **The uniform a priori obstruction** (`eventually-periodic.tex` Thm 2.3,
`periodic-words.md` Prop. 3.1): for `w = u^q v` with `q ≥ 1` and `u` a positive word,
`gcd_j S^{(j)}(w) ∣ C(u, v)`, an integer independent of `q`. -/
theorem G_dvd_C {u : Word} (hu : u.Pos) (v : Word) {q : ℕ} (hq : 1 ≤ q) :
    G (upow u q ++ v) ∣ Cz u v := by
  rcases eq_or_ne u [] with rfl | hne
  · simp [C]
  have hsum : 0 < (upow u q ++ v).sum := by
    have h1 := (Word.Pos.length_le_sum hu)
    have h2 : 0 < u.length := List.length_pos_iff.2 hne
    have : 0 < q * u.sum := Nat.mul_pos (by omega) (by omega)
    simp only [List.sum_append, upow_sum]
    omega
  have hdiff : G (upow u q ++ v) ∣ 2 ^ ((q - 1) * u.sum) * Cz u v := by
    rw [← telescoping_rotate _ _ u v hq]
    exact dvd_sub (by simpa using G_dvd_S_rotate _ 0) (G_dvd_S_rotate _ _)
  exact (isCoprime_two_pow_of_dvd_odd (G_dvd_D _) (Dz_odd hsum) _).dvd_of_dvd_mul_left hdiff

/-- **`|2^E - 3^o| ∣ C(u, v)` on a cycle** (`eventually-periodic.tex` (9), `periodic-words.md`
Cor. 3.2): if `u^q v` (`q ≥ 1`, `u` positive) carries a closed integer orbit, `D(w) ∣ C(u, v)`. -/
theorem D_dvd_C_of_follows {u : Word} (hu : u.Pos) (v : Word) {q : ℕ} (hq : 1 ≤ q) {a : ℤ}
    (h : Follows (2 : ℤ) 3 (upow u q ++ v) a a) : Dz (upow u q ++ v) ∣ Cz u v :=
  (abs_dvd _ _).1 (G_eq_abs_D_of_follows h ▸ G_dvd_C hu v hq)

/-- Hence on a cycle `C(u, v) = 0` or `|2^E - 3^o| ≤ |C(u, v)|`. -/
theorem C_eq_zero_or_abs_D_le {u : Word} (hu : u.Pos) (v : Word) {q : ℕ} (hq : 1 ≤ q) {a : ℤ}
    (h : Follows (2 : ℤ) 3 (upow u q ++ v) a a) :
    Cz u v = 0 ∨ |Dz (upow u q ++ v)| ≤ |Cz u v| := by
  by_cases hC : Cz u v = 0
  · exact Or.inl hC
  · exact Or.inr (Int.le_of_dvd (abs_pos.2 hC)
      ((abs_dvd_abs _ _).2 (D_dvd_C_of_follows hu v hq h)))

/-- The blocks of a genuine gap word `u^q v` (`q ≥ 1`) are positive words. -/
lemma IsSyrCycle.blocks_pos {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {u v : Word}
    {q : ℕ} (hq : 1 ≤ q) (hw : gapWord a o = upow u q ++ v) : u.Pos ∧ v.Pos := by
  have hpos := gapWord_pos h.2.1 o
  rw [hw] at hpos
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hq
  refine ⟨fun d hd => hpos d ?_, fun d hd => hpos d (List.mem_append_right _ hd)⟩
  exact List.mem_append_left _ (by rw [upow_succ]; exact List.mem_append_left _ hd)

/-- A genuine cycle is a closed orbit along its gap word. -/
lemma IsSyrCycle.follows {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    Follows (2 : ℤ) 3 (gapWord a o) a a := by
  have hf := follows_gapWord a o; rwa [h.2.2] at hf

/-- The obstruction for a genuine Syracuse cycle whose gap word is `u^q v`. -/
theorem IsSyrCycle.D_dvd_C {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {u v : Word}
    {q : ℕ} (hq : 1 ≤ q) (hw : gapWord a o = upow u q ++ v) :
    Dz (gapWord a o) ∣ Cz u v := by
  have hf := (IsSyrCycle.follows h)
  rw [hw] at hf ⊢
  exact D_dvd_C_of_follows (IsSyrCycle.blocks_pos h hq hw).1 v hq hf

/-! ### A `q`-free upper bound on the core (`eventually-periodic.tex` Lemma 2.5) -/

/-- `S(w) ≥ 0` at `(2, 3)`. -/
lemma Sz_nonneg (w : Word) : 0 ≤ Sz w := by
  induction w with
  | nil => simp
  | cons d t ih => simp only [S_cons]; positivity

/-- `S(w) > 0` at `(2, 3)` for a nonempty word. -/
lemma Sz_pos {w : Word} (hw : w ≠ []) : 0 < Sz w := by
  cases w with
  | nil => exact absurd rfl hw
  | cons d t => simp only [S_cons]; have := Sz_nonneg t; positivity

/-- `4 S(r) ≤ 2^σ (3^ℓ - 1)` for a nonempty positive word `r` of length `ℓ` and gap-sum `σ`,
i.e. `S(r) ≤ 2^{σ-1}(3^ℓ - 1)/2` (`periodic-words.md` §5.1). -/
theorem four_mul_Sz_le {r : Word} (hr : r.Pos) (hne : r ≠ []) :
    4 * Sz r ≤ 2 ^ r.sum * (3 ^ r.length - 1) := by
  induction r with
  | nil => exact absurd rfl hne
  | cons d t ih =>
    have hd : 1 ≤ d := hr d (by simp)
    have ht : Word.Pos t := fun x hx => hr x (by simp [hx])
    have hP : (2 : ℤ) ≤ 2 ^ d := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
    simp only [S_cons, List.sum_cons, List.length_cons, pow_add, pow_succ]
    rcases eq_or_ne t [] with rfl | htne
    · simp; linarith
    have ih := ih ht htne
    have hQ : (2 : ℤ) ≤ 2 ^ t.sum := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ t.sum := pow_le_pow_right₀ (by norm_num)
            (le_trans (List.length_pos_iff.2 htne) (Word.Pos.length_le_sum ht))
    have hT : (1 : ℤ) ≤ 3 ^ t.length := one_le_pow₀ (by norm_num)
    have h1 : 2 ^ d * (4 * Sz t) ≤ 2 ^ d * (2 ^ t.sum * (3 ^ t.length - 1)) :=
      mul_le_mul_of_nonneg_left ih (by positivity)
    nlinarith [mul_le_mul hP hQ (by norm_num) (by positivity)]

/-- **`S(r) < 2^{σ-1} 3^ℓ`** for every positive word (`eventually-periodic.tex` Lemma 2.5),
written `2 S(r) < 2^σ 3^ℓ`. -/
theorem two_mul_Sz_lt {r : Word} (hr : r.Pos) : 2 * Sz r < 2 ^ r.sum * 3 ^ r.length := by
  rcases eq_or_ne r [] with rfl | hne
  · simp
  · have h := four_mul_Sz_le hr hne
    have : (0 : ℤ) < 2 ^ r.sum := by positivity
    have := Sz_nonneg r
    rw [mul_sub, mul_one] at h
    linarith

/-- `periodic-words.md` §5.1's form `S(r) < 2^{σ-2} 3^ℓ`, written `4 S(r) < 2^σ 3^ℓ`. -/
theorem four_mul_Sz_lt {r : Word} (hr : r.Pos) : 4 * Sz r < 2 ^ r.sum * 3 ^ r.length := by
  rcases eq_or_ne r [] with rfl | hne
  · simp
  · have h := four_mul_Sz_le hr hne
    have : (0 : ℤ) < 2 ^ r.sum := by positivity
    have := Sz_nonneg r
    rw [mul_sub, mul_one] at h
    linarith

/-- The sharp form of the core bound: `2 |C(u, v)| < 2^{a+b} 3^{m+ℓ}`. -/
theorem two_mul_abs_Cz_lt {u v : Word} (hu : u.Pos) (hv : v.Pos) :
    2 * |Cz u v| < 2 ^ (u.sum + v.sum) * 3 ^ (u.length + v.length) := by
  have h1 := two_mul_Sz_lt (Word.Pos.append hu hv)
  have h2 := two_mul_Sz_lt (Word.Pos.append hv hu)
  have h3 := Sz_nonneg (u ++ v)
  have h4 := Sz_nonneg (v ++ u)
  simp only [List.sum_append, List.length_append] at h1 h2
  rw [add_comm v.sum, add_comm v.length] at h2
  rw [show Cz u v = Sz (u ++ v) - Sz (v ++ u) from C_eq 2 3 u v]
  rcases abs_cases (Sz (u ++ v) - Sz (v ++ u)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

/-- **`q`-free upper bound** (`eventually-periodic.tex` (10), `periodic-words.md` §5.1):
`|C(u, v)| < 2^{a+b} 3^{m+ℓ}` with `a = |u|, b = |v|, m = len u, ℓ = len v`. -/
theorem abs_Cz_lt {u v : Word} (hu : u.Pos) (hv : v.Pos) :
    |Cz u v| < 2 ^ (u.sum + v.sum) * 3 ^ (u.length + v.length) := by
  have := two_mul_abs_Cz_lt hu hv
  have := abs_nonneg (Cz u v)
  linarith

/-- The smaller guess `|C(u, v)| < 2^{|v|} 3^{m+ℓ}` is false: `u = (3,3), v = (1)` gives
`C = 66 > 54` (`eventually-periodic.tex` Remark 2.6). -/
theorem smaller_guess_false :
    Cz [3, 3] [1] = 66 ∧ (2 : ℤ) ^ [1].sum * 3 ^ ([3, 3].length + [1].length) = 54 := by
  decide

/-- **Prop. 2.4 at `(2, 3)`** (`eventually-periodic.tex`, `periodic-words.md` §4): for nonempty
`u, v`, `C(u, v) = 0` iff `u, v` force the same rational fixed point `S/D`. -/
theorem Cz_eq_zero_iff {u v : Word} (hu : u ≠ []) (hv : v ≠ []) :
    Cz u v = 0 ↔ (Sz u : ℚ) / Dz u = (Sz v : ℚ) / Dz v := by
  have hu' : (Dz u : ℚ) ≠ 0 := by exact_mod_cast Dz_ne_zero hu
  have hv' : (Dz v : ℚ) ≠ 0 := by exact_mod_cast Dz_ne_zero hv
  rw [div_eq_div_iff hu' hv', show Cz u v = Dz u * Sz v - Dz v * Sz u from rfl, sub_eq_zero]
  constructor
  · intro h
    have := congrArg (Int.cast : ℤ → ℚ) h
    push_cast at this
    linarith
  · intro h
    have : ((Dz u * Sz v : ℤ) : ℚ) = ((Dz v * Sz u : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this

/-- The numerical table of `periodic-words.md` §3: cores `C(w, w')` and `|D(w^q w')|` at
`q = 1, 6`. -/
theorem table_values :
    Cz [1, 2] [3] = -26 ∧ Cz [2, 1, 1] [4, 1] = -876 ∧ Cz [1, 3] [2] = 2 ∧
      |Dz (upow [1, 2] 1 ++ [3])| = 37 ∧ |Dz (upow [1, 2] 6 ++ [3])| = 502829 ∧
      |Dz (upow [2, 1, 1] 1 ++ [4, 1])| = 269 ∧
      |Dz (upow [2, 1, 1] 6 ++ [4, 1])| = 2949913489 ∧
      |Dz (upow [1, 3] 1 ++ [2])| = 37 ∧ |Dz (upow [1, 3] 6 ++ [2])| = 65514541 := by
  decide

/-- … and in every row `gcd_j S^{(j)} = 1` for `q = 1, …, 6` (no cycle). -/
theorem table_G : ∀ q ∈ Finset.Icc 1 6,
    G (upow [1, 2] q ++ [3]) = 1 ∧ G (upow [2, 1, 1] q ++ [4, 1]) = 1 ∧
      G (upow [1, 3] q ++ [2]) = 1 := by
  decide

/-! ### Finitely many `q` per block pair (`periodic-words.md` Cor. 3.2) -/

open Filter in
/-- `|A α^q - B β^q| → ∞` for `A, B > 0`, `α, β ≥ 1`, `α ≠ β`. -/
lemma tendsto_abs_sub_pow {A B α β : ℝ} (hA : 0 < A) (hB : 0 < B) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hne : α ≠ β) : Tendsto (fun q : ℕ => |A * α ^ q - B * β ^ q|) atTop atTop := by
  wlog hlt : β < α generalizing A B α β
  · have := this hB hA hβ hα hne.symm (lt_of_le_of_ne (not_lt.1 hlt) hne)
    simpa [abs_sub_comm] using this
  have hβ0 : 0 < β := by linarith
  have hr : 1 < α / β := (one_lt_div hβ0).2 hlt
  have h1 : Tendsto (fun q : ℕ => A * (α / β) ^ q + -B) atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_pow_atTop_atTop_of_one_lt hr).const_mul_atTop hA)
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [h1.eventually_ge_atTop 0] with q hq
  have hβq : 1 ≤ β ^ q := one_le_pow₀ hβ
  have : A * α ^ q - B * β ^ q = β ^ q * (A * (α / β) ^ q + -B) := by
    rw [div_pow]; field_simp; ring
  rw [this, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg hq]
  nlinarith

open Filter in
/-- **Finitely many `q` unless `C = 0`** (`periodic-words.md` Cor. 3.2,
`eventually-periodic.tex` after Thm 2.3): for a nonempty positive block `u` and any tail `v`
with `C(u, v) ≠ 0`, only finitely many `q` make `u^q v` carry a closed integer orbit. -/
theorem finite_q {u : Word} (hu : u.Pos) (hne : u ≠ []) (v : Word) (hC : Cz u v ≠ 0) :
    {q | ∃ a : ℤ, Follows (2 : ℤ) 3 (upow u q ++ v) a a}.Finite := by
  have hD : ∀ q, ((Dz (upow u q ++ v) : ℤ) : ℝ) =
      2 ^ v.sum * ((2 : ℝ) ^ u.sum) ^ q - 3 ^ v.length * ((3 : ℝ) ^ u.length) ^ q := by
    intro q
    simp only [D, List.sum_append, List.length_append, upow_sum, upow_length]
    push_cast; ring
  have hne' : (2 : ℝ) ^ u.sum ≠ 3 ^ u.length := by
    exact_mod_cast two_pow_ne_three_pow u.sum (List.length_pos_iff.2 hne)
  have ht := tendsto_abs_sub_pow (A := 2 ^ v.sum) (B := 3 ^ v.length) (by positivity)
    (by positivity) (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) hne'
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually_gt_atTop ((|Cz u v| : ℤ) : ℝ))
  refine (Set.finite_Iio (max N 1)).subset fun q ⟨a, ha⟩ => ?_
  by_contra hq
  simp only [Set.mem_Iio, not_lt, max_le_iff] at hq
  have h1 := hN q hq.1
  rcases C_eq_zero_or_abs_D_le hu v hq.2 ha with h | h
  · exact hC h
  · rw [← hD, ← Int.cast_abs] at h1
    have : ((|Dz (upow u q ++ v)| : ℤ) : ℝ) ≤ ((|Cz u v| : ℤ) : ℝ) := by exact_mod_cast h
    linarith

/-! ## Positive cycles -/

/-- Along an integer orbit with positive start, `a_k > 0` and `2^E b ≤ 4^o a` (each step has
`2^d a' = 3a + 1 ≤ 4a`). -/
theorem follows_pos_bound {w : Word} {a b : ℤ} (h : Follows (2 : ℤ) 3 w a b) :
    0 < a → 0 < b ∧ 2 ^ w.sum * b ≤ 4 ^ w.length * a := by
  induction h with
  | nil a => intro ha; simpa using ha
  | @cons d w a a' b hstep _ ih =>
    intro ha
    have ha' : 0 < a' :=
      pos_of_mul_pos_right (show (0 : ℤ) < 2 ^ d * a' by rw [hstep]; linarith) (by positivity)
    obtain ⟨hb, hle⟩ := ih ha'
    refine ⟨hb, ?_⟩
    simp only [List.sum_cons, List.length_cons, pow_add, pow_succ]
    have h4 : (0 : ℤ) ≤ 4 ^ w.length := by positivity
    calc 2 ^ d * 2 ^ w.sum * b = 2 ^ d * (2 ^ w.sum * b) := by ring
      _ ≤ 2 ^ d * (4 ^ w.length * a') := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 4 ^ w.length * (3 * a + 1) := by rw [← hstep]; ring
      _ ≤ 4 ^ w.length * 4 * a := by nlinarith

/-- A positive cycle has `E ≤ 2o` (`2^E = ∏(3 + 1/a_k) ≤ 4^o`). -/
theorem sum_le_two_mul_length {w : Word} {a : ℤ} (h : Follows (2 : ℤ) 3 w a a) (ha : 0 < a) :
    w.sum ≤ 2 * w.length := by
  have h1 := (follows_pos_bound h ha).2
  have h2 : (2 : ℤ) ^ w.sum ≤ 2 ^ (2 * w.length) := by
    rw [pow_mul]; norm_num
    exact le_of_mul_le_mul_right h1 ha
  exact (pow_le_pow_iff_right₀ (by norm_num)).1 h2

/-- **A positive cycle has `2^E > 3^o`**, i.e. `D > 0` (`theorems.md` Thm 4.3(1)): `D a = S > 0`. -/
theorem three_pow_lt_two_pow_of_follows {w : Word} (hw : w ≠ []) {a : ℤ} (ha : 0 < a)
    (h : Follows (2 : ℤ) 3 w a a) : (3 : ℤ) ^ w.length < 2 ^ w.sum := by
  have h1 := Follows.cycle_equation 2 3 h
  have h2 := Sz_pos hw
  have : 0 < Dz w := by
    by_contra hD
    have : Dz w * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hD) ha.le
    linarith
  simpa [D] using this

/-! ## The critical exponent (`theorems.md` §4) -/

/-- Some power of `2` exceeds `3^o` (e.g. `2^{2o+1}`). -/
lemma exists_three_pow_lt (o : ℕ) : ∃ E, 3 ^ o < 2 ^ E :=
  ⟨2 * o + 1, by
    rw [pow_succ, pow_mul]
    calc 3 ^ o ≤ (2 ^ 2) ^ o := Nat.pow_le_pow_left (by norm_num) o
      _ < (2 ^ 2) ^ o * 2 := by have : 0 < (2 ^ 2) ^ o := by positivity
                                omega⟩

/-- `E_*(o) = min {E : 2^E > 3^o}`. -/
def Ecrit (o : ℕ) : ℕ := Nat.find (exists_three_pow_lt o)

/-- `(E, o)` is **critical** when `E = E_*(o)` (`theorems.md` Def. 4.1); for `2^E > 3^o` the
alternative is *non-critical*, `E > E_*(o)`. -/
def Critical (E o : ℕ) : Prop := E = Ecrit o

/-- Critical `⟺ 2^E > 3^o ≥ 2^{E-1}`. -/
lemma critical_iff {E o : ℕ} : Critical E o ↔ 3 ^ o < 2 ^ E ∧ 2 ^ (E - 1) ≤ 3 ^ o := by
  unfold Critical Ecrit
  rw [eq_comm, Nat.find_eq_iff]
  refine and_congr_right fun hE => ⟨fun h => not_lt.1 (h _ ?_), fun h n hn => ?_⟩
  · rcases Nat.eq_zero_or_pos E with rfl | hE0
    · simp at hE
    · omega
  · exact not_lt.2 (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h)

/-- `2^E ≠ 3^o` in `ℕ` for `o ≥ 1`. -/
lemma two_pow_ne_three_pow_nat (E : ℕ) {o : ℕ} (ho : 0 < o) : 2 ^ E ≠ 3 ^ o := by
  have := two_pow_ne_three_pow E ho
  exact_mod_cast this

/-- `2^E > 3^o ⟺ E > o log₂ 3`. -/
theorem three_pow_lt_two_pow_iff {E o : ℕ} : 3 ^ o < 2 ^ E ↔ (o : ℝ) * Real.logb 2 3 < E := by
  rw [← Real.logb_pow, Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity), Real.rpow_natCast]
  exact_mod_cast Iff.rfl

/-- `o log₂ 3 ∉ ℤ` for `o ≥ 1` (`theorems.md` Remark 1.5). -/
theorem logb_not_int {o : ℕ} (ho : 0 < o) (n : ℤ) : (o : ℝ) * Real.logb 2 3 ≠ n := by
  intro h
  have hpos : (0 : ℝ) < o * Real.logb 2 3 := by
    have : (0 : ℝ) < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)
    have : (0 : ℝ) < o := by exact_mod_cast ho
    positivity
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ n by
    have : (0 : ℝ) < n := h ▸ hpos
    exact_mod_cast this.le)
  have : (3 : ℝ) ^ o = 2 ^ k := by
    rw [← Real.logb_pow] at h
    have := Real.rpow_logb (b := 2) (x := 3 ^ o) (by norm_num) (by norm_num) (by positivity)
    rw [h] at this
    simpa using this.symm
  exact two_pow_ne_three_pow_nat k ho (by exact_mod_cast this.symm)

/-- `E_*(o) = ⌈o log₂ 3⌉` for `o ≥ 1`. -/
theorem Ecrit_eq_ceil {o : ℕ} (ho : 0 < o) : Ecrit o = ⌈(o : ℝ) * Real.logb 2 3⌉₊ := by
  unfold Ecrit
  rw [Nat.find_eq_iff]
  have hx := logb_not_int ho
  constructor
  · rw [three_pow_lt_two_pow_iff]
    exact lt_of_le_of_ne (Nat.le_ceil _) (by exact_mod_cast hx ⌈(o : ℝ) * Real.logb 2 3⌉₊)
  · intro n hn h
    rw [three_pow_lt_two_pow_iff] at h
    have := Nat.ceil_le.2 h.le
    omega

/-- `log₂ 3 > 0`. -/
lemma logb_two_three_pos : 0 < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)

/-- **Lemma 4.2(1)**: for `o ≥ 1` and `2^E > 3^o`, critical `⟺ o log₂3 < E < o log₂3 + 1`. -/
theorem critical_iff_real {E o : ℕ} (ho : 0 < o) (hE : 3 ^ o < 2 ^ E) :
    Critical E o ↔ (o : ℝ) * Real.logb 2 3 < E ∧ (E : ℝ) < o * Real.logb 2 3 + 1 := by
  have hx := three_pow_lt_two_pow_iff.1 hE
  have h0 : (0 : ℝ) ≤ o * Real.logb 2 3 := by have := logb_two_three_pos; positivity
  rw [Critical, Ecrit_eq_ceil ho]
  refine ⟨fun h => ⟨hx, h ▸ Nat.ceil_lt_add_one h0⟩, fun ⟨_, h⟩ =>
    le_antisymm ?_ (Nat.ceil_le.2 hx.le)⟩
  have := Nat.le_ceil ((o : ℝ) * Real.logb 2 3)
  have h' : (E : ℝ) < ⌈(o : ℝ) * Real.logb 2 3⌉₊ + 1 := by linarith
  exact Nat.lt_succ_iff.1 (by exact_mod_cast h')

/-- **Lemma 4.2(2), real form**: for `o ≥ 1` and `2^E > 3^o`, non-critical `⟺ E > o log₂3 + 1`. -/
theorem not_critical_iff_real {E o : ℕ} (ho : 0 < o) (hE : 3 ^ o < 2 ^ E) :
    ¬ Critical E o ↔ (o : ℝ) * Real.logb 2 3 + 1 < E := by
  have hx := three_pow_lt_two_pow_iff.1 hE
  rw [critical_iff_real ho hE]
  constructor
  · intro h
    have hle : (o : ℝ) * Real.logb 2 3 + 1 ≤ E := by by_contra h'; exact h ⟨hx, not_le.1 h'⟩
    refine lt_of_le_of_ne hle fun heq => logb_not_int ho ((E : ℤ) - 1) ?_
    push_cast; linarith
  · rintro h ⟨_, h'⟩; linarith

/-- **Lemma 4.2(2), power form**: for `2^E > 3^o`, non-critical `⟺ 2^{E-1} > 3^o`. -/
theorem not_critical_iff_pow {E o : ℕ} (hE : 3 ^ o < 2 ^ E) :
    ¬ Critical E o ↔ 3 ^ o < 2 ^ (E - 1) := by
  rw [critical_iff]; simp [hE]

/-- `2^E > 3^o` forces `E ≥ 1`. -/
lemma one_le_of_three_pow_lt {E o : ℕ} (hE : 3 ^ o < 2 ^ E) : 1 ≤ E := by
  rcases Nat.eq_zero_or_pos E with rfl | h
  · simp at hE
  · exact h

/-- **Lemma 4.2(3), gap bound**: non-critical `(E, o)` has `2^E - 3^o > 2^{E-1}`. -/
theorem gap_bound {E o : ℕ} (hE : 3 ^ o < 2 ^ E) (hnc : ¬ Critical E o) :
    (2 : ℤ) ^ (E - 1) < 2 ^ E - 3 ^ o := by
  have h : (3 : ℤ) ^ o < 2 ^ (E - 1) := by exact_mod_cast (not_critical_iff_pow hE).1 hnc
  have : (2 : ℤ) ^ E = 2 * 2 ^ (E - 1) := by
    rw [← pow_succ']; congr 1; have := one_le_of_three_pow_lt hE; omega
  linarith

/-! ### Reduction of criticality for positive cycles (`theorems.md` Thm 4.3) -/

/-- `E = Σ_k ν₂(3a_k + 1)` along the trajectory. -/
lemma gapWord_sum (a : ℤ) (o : ℕ) : (gapWord a o).sum = ∑ k ∈ range o, gap (syr^[k] a) := by
  induction o generalizing a with
  | zero => simp [gapWord]
  | succ o ih =>
    rw [gapWord, List.sum_cons, ih, sum_range_succ', add_comm]
    simp [Function.iterate_succ_apply]

/-- The odd terms of an odd trajectory are nonzero. -/
lemma iterate_syr_ne_zero {a : ℤ} (ha : Odd a) (k : ℕ) : syr^[k] a ≠ 0 := by
  have : Odd (syr^[k] a) := by
    cases k with
    | zero => exact ha
    | succ k => rw [Function.iterate_succ_apply']; exact syr_odd _
  rintro h; rw [h] at this; simp at this

/-- **(4.1)** On a cycle (any sign), `2^E = ∏_{k<o} (3 + 1/a_k)` in `ℚ`. -/
theorem IsSyrCycle.two_pow_eq_prod {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    (2 : ℚ) ^ (gapWord a o).sum = ∏ k ∈ range o, (3 + 1 / ((syr^[k] a : ℤ) : ℚ)) := by
  have hne : ∀ k, ((syr^[k] a : ℤ) : ℚ) ≠ 0 := fun k => by
    exact_mod_cast iterate_syr_ne_zero h.2.1 k
  have hstep : ∀ k, (2 : ℚ) ^ gap (syr^[k] a) * ((syr^[k + 1] a : ℤ) : ℚ) =
      3 * ((syr^[k] a : ℤ) : ℚ) + 1 := fun k => by
    rw [Function.iterate_succ_apply']; exact_mod_cast two_pow_gap_mul_syr _
  have hshift :
      ∏ k ∈ range o, ((syr^[k + 1] a : ℤ) : ℚ) = ∏ k ∈ range o, ((syr^[k] a : ℤ) : ℚ) := by
    have h1 := prod_range_succ (fun k => ((syr^[k] a : ℤ) : ℚ)) o
    have h2 := prod_range_succ' (fun k => ((syr^[k] a : ℤ) : ℚ)) o
    simp only [h.2.2, Function.iterate_zero, id_eq] at h1 h2
    exact mul_right_cancel₀ (hne 0) (h2.symm.trans h1)
  have hP : ∏ k ∈ range o, ((syr^[k] a : ℤ) : ℚ) ≠ 0 := prod_ne_zero_iff.2 fun k _ => hne k
  have key : (∏ k ∈ range o, (2 : ℚ) ^ gap (syr^[k] a)) * ∏ k ∈ range o, ((syr^[k] a : ℤ) : ℚ) =
      ∏ k ∈ range o, (3 * ((syr^[k] a : ℤ) : ℚ) + 1) := by
    rw [← hshift, ← prod_mul_distrib]; exact prod_congr rfl fun k _ => hstep k
  rw [gapWord_sum, ← prod_pow_eq_pow_sum, eq_div_of_mul_eq hP key, ← prod_div_distrib]
  exact prod_congr rfl fun k _ => by field_simp [hne k]

/-- `2^E / 3^o = ∏_{k<o} (1 + 1/(3a_k))` on a cycle. -/
theorem IsSyrCycle.two_pow_div_eq_prod {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    (2 : ℚ) ^ (gapWord a o).sum / 3 ^ o = ∏ k ∈ range o, (1 + 1 / (3 * ((syr^[k] a : ℤ) : ℚ))) := by
  rw [IsSyrCycle.two_pow_eq_prod h, div_eq_iff (by positivity)]
  have : (3 : ℚ) ^ o = ∏ k ∈ range o, (3 : ℚ) := by simp
  rw [this, ← prod_mul_distrib]
  refine prod_congr rfl fun k _ => ?_
  have := iterate_syr_ne_zero h.2.1 k
  have : ((syr^[k] a : ℤ) : ℚ) ≠ 0 := by exact_mod_cast this
  field_simp

/-- A positive Syracuse cycle has `3^o < 2^E` (`theorems.md` Thm 4.3(1)). -/
theorem IsSyrCycle.three_pow_lt {a : ℤ} {o : ℕ} (h : IsSyrCycle a o)
    (ha : 0 < a) : 3 ^ o < 2 ^ (gapWord a o).sum := by
  have hf := follows_gapWord a o
  rw [h.2.2] at hf
  have hne : gapWord a o ≠ [] := by
    intro h'; have := congrArg List.length h'; simp at this; exact h.1.ne' this
  have := three_pow_lt_two_pow_of_follows hne ha hf
  simp only [gapWord_length] at this
  exact_mod_cast this

/-- **Reduction of criticality** (`theorems.md` Thm 4.3(2)): a positive cycle is critical
`⟺ 2^E < 2·3^o`. -/
theorem IsSyrCycle.critical_iff {a : ℤ} {o : ℕ} (h : IsSyrCycle a o)
    (ha : 0 < a) : Critical (gapWord a o).sum o ↔ 2 ^ (gapWord a o).sum < 2 * 3 ^ o := by
  have hE := IsSyrCycle.three_pow_lt h ha
  set E := (gapWord a o).sum
  have hE1 := one_le_of_three_pow_lt hE
  have h2 : 2 ^ E = 2 * 2 ^ (E - 1) := by rw [← pow_succ']; congr 1; omega
  have hne := two_pow_ne_three_pow_nat (E - 1) h.1
  rw [_root_.Syracuse.CycleGcd.critical_iff]
  simp only [hE, true_and]
  constructor
  · intro h'; have := lt_of_le_of_ne h' hne; omega
  · intro h'; omega

/-- **Reduction of criticality, product form** (`theorems.md` Thm 4.3(2)): a positive cycle is
critical `⟺ ∏_{k<o} (1 + 1/(3a_k)) < 2`. -/
theorem IsSyrCycle.critical_iff_prod {a : ℤ} {o : ℕ} (h : IsSyrCycle a o)
    (ha : 0 < a) : Critical (gapWord a o).sum o ↔
      ∏ k ∈ range o, (1 + 1 / (3 * ((syr^[k] a : ℤ) : ℚ))) < 2 := by
  rw [IsSyrCycle.critical_iff h ha, ← IsSyrCycle.two_pow_div_eq_prod h, div_lt_iff₀ (by positivity)]
  exact_mod_cast Iff.rfl

/-! ## The critical band (`eventually-periodic.tex` Def. 2.11–Thm 2.13) -/

/-- `(E, o)` lies in the **critical band** `3^o < 2^E < 3^{o+1}` (Def. 2.11). -/
def InBand (E o : ℕ) : Prop := 3 ^ o < 2 ^ E ∧ 2 ^ E < 3 ^ (o + 1)

/-- `2^E < 3^o ⟺ E < o log₂ 3`. -/
theorem two_pow_lt_three_pow_iff {E o : ℕ} : 2 ^ E < 3 ^ o ↔ (E : ℝ) < o * Real.logb 2 3 := by
  rw [← Real.logb_pow, Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity), Real.rpow_natCast]
  exact_mod_cast Iff.rfl

/-- **Prop. 2.12(i)**: in the band, `0 < Λ = E log 2 - o log 3 < log 3` and
`2^E - 3^o < 2·3^o`. -/
theorem InBand.Lambda {E o : ℕ} (h : InBand E o) :
    0 < (E : ℝ) * Real.log 2 - o * Real.log 3 ∧
      (E : ℝ) * Real.log 2 - o * Real.log 3 < Real.log 3 := by
  have h1 := Real.log_lt_log (by positivity) (show ((3 : ℝ) ^ o) < 2 ^ E by exact_mod_cast h.1)
  have h2 := Real.log_lt_log (by positivity) (show ((2 : ℝ) ^ E) < 3 ^ (o + 1) by
    exact_mod_cast h.2)
  rw [Real.log_pow, Real.log_pow] at h1 h2
  push_cast at h2
  constructor <;> linarith

/-- **Prop. 2.12(i)**, second part: in the band `2^E - 3^o < 2·3^o`. -/
theorem InBand.D_lt {E o : ℕ} (h : InBand E o) : (2 : ℤ) ^ E - 3 ^ o < 2 * 3 ^ o := by
  have : (2 : ℤ) ^ E < 3 ^ (o + 1) := by exact_mod_cast h.2
  rw [pow_succ] at this; linarith

/-- **Prop. 2.12(ii)**: in the band, `E ∈ {E_*(o), E_*(o) + 1}` — at most two values per `o`. -/
theorem InBand.E_eq {E o : ℕ} (h : InBand E o) : E = Ecrit o ∨ E = Ecrit o + 1 := by
  have h1 : Ecrit o ≤ E := Nat.find_min' _ h.1
  have h2 : 3 ^ o < 2 ^ Ecrit o := Nat.find_spec (exists_three_pow_lt o)
  by_contra hne
  have h3 : 2 ^ (Ecrit o + 2) ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 := h.2
  rw [pow_add] at h3
  rw [pow_succ] at h4
  omega

/-- **Prop. 2.12(iii)**: in the band, `o log₂3 < E < (o+1) log₂3` and `E ≤ 2o + 1`. -/
theorem InBand.bounds {E o : ℕ} (h : InBand E o) :
    (o : ℝ) * Real.logb 2 3 < E ∧ (E : ℝ) < (o + 1) * Real.logb 2 3 := by
  refine ⟨three_pow_lt_two_pow_iff.1 h.1, ?_⟩
  have := two_pow_lt_three_pow_iff.1 h.2
  push_cast at this; exact this

/-- **Prop. 2.12(iii)**, second part: in the band `E ≤ 2o + 1`. -/
theorem InBand.E_le {E o : ℕ} (h : InBand E o) : E ≤ 2 * o + 1 := by
  have h1 : 2 ^ E < 2 ^ (2 * o + 2) := by
    calc 2 ^ E < 3 ^ (o + 1) := h.2
      _ ≤ 4 ^ (o + 1) := Nat.pow_le_pow_left (by norm_num) _
      _ = 2 ^ (2 * o + 2) := by rw [show 2 * o + 2 = 2 * (o + 1) by ring, pow_mul]; norm_num
  have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
  omega

/-! ## The Matveev lower bound, as a hypothesis

`eventually-periodic.tex` Thm 2.7, Prop. 2.8, Thm 2.9. -/

/-- **Matveev's theorem** (Bugeaud–Mignotte–Siksek form, Thm 2.7) specialised to `n = 2`,
`α = (2, 3)`, `D₀ = 1`, `A = (log 2, log 3)`, `b = (E, -o)`, `B = max(E, o)`, with constant `c`:
whenever `Λ = E log 2 - o log 3 ≠ 0`, `log |Λ| > -c (1 + log B)`.
This is **stated only**: it is neither proved nor assumed as an axiom here. For `c = c₀` it is
the published theorem. -/
def MatveevTwoThree (c : ℝ) : Prop :=
  ∀ E o : ℕ, (E : ℝ) * Real.log 2 - o * Real.log 3 ≠ 0 →
    -c * (1 + Real.log (max E o : ℕ)) < Real.log |(E : ℝ) * Real.log 2 - o * Real.log 3|

/-- Matveev's constant for two logarithms: `c₀ = 1.4 · 30⁵ · 2^{4.5} · log 2 · log 3 ≈ 5.86·10⁸`. -/
noncomputable def c₀ : ℝ := 1.4 * 30 ^ 5 * (2 : ℝ) ^ (4.5 : ℝ) * Real.log 2 * Real.log 3

/-- `c₀ > 0`. -/
lemma c₀_pos : 0 < c₀ := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  unfold c₀; positivity

/-- **Prop. 2.8, conditional on `MatveevTwoThree c`**: if `2^E > 3^o` then
`2^E - 3^o > 3^o exp(-c (1 + log E))`. (The note also assumes `E, o ≥ 2`; not needed.) -/
theorem lower_bound {c : ℝ} (hM : MatveevTwoThree c) {E o : ℕ} (h : 3 ^ o < 2 ^ E) :
    (3 : ℝ) ^ o * Real.exp (-c * (1 + Real.log E)) < 2 ^ E - 3 ^ o := by
  set Λ := (E : ℝ) * Real.log 2 - o * Real.log 3 with hΛ
  have hlog : (o : ℝ) * Real.log 3 < E * Real.log 2 := by
    have := Real.log_lt_log (by positivity) (show ((3 : ℝ) ^ o) < 2 ^ E by exact_mod_cast h)
    rwa [Real.log_pow, Real.log_pow] at this
  have hΛpos : 0 < Λ := by rw [hΛ]; linarith
  have hoE : o ≤ E := by
    have : 2 ^ o < 2 ^ E := lt_of_le_of_lt (Nat.pow_le_pow_left (by norm_num) o) h
    exact ((Nat.pow_lt_pow_iff_right (by norm_num)).1 this).le
  have hM' := hM E o hΛpos.ne'
  rw [max_eq_left hoE, abs_of_pos hΛpos] at hM'
  have h1 : Real.exp (-c * (1 + Real.log E)) < Λ := (Real.lt_log_iff_exp_lt hΛpos).1 hM'
  have h2 : (2 : ℝ) ^ E = 3 ^ o * Real.exp Λ := by
    have e2 : (2 : ℝ) ^ E = Real.exp (E * Real.log 2) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    have e3 : (3 : ℝ) ^ o = Real.exp (o * Real.log 3) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [e2, e3, ← Real.exp_add, hΛ]; congr 1; ring
  have h3 := Real.add_one_le_exp Λ
  have h4 : (0 : ℝ) < 3 ^ o := by positivity
  rw [h2]
  nlinarith

/-- **Thm 2.9 (effective exclusion), conditional on `MatveevTwoThree c`.** If `w = u^q v`
(`q ≥ 1`, `u, v` positive, `C(u, v) ≠ 0`) carries a positive closed integer orbit, then
`(q-1) m log 3 < (a+b) log 2 + c (1 + log E)` with `E = qa + b`. -/
theorem exclusion {c : ℝ} (hM : MatveevTwoThree c) {u v : Word} (hu : u.Pos) (hv : v.Pos)
    {q : ℕ} (hq : 1 ≤ q) (hC : Cz u v ≠ 0) {a : ℤ} (ha : 0 < a)
    (h : Follows (2 : ℤ) 3 (upow u q ++ v) a a) :
    ((q : ℝ) - 1) * u.length * Real.log 3 <
      (u.sum + v.sum) * Real.log 2 + c * (1 + Real.log (q * u.sum + v.sum : ℕ)) := by
  have hune : u ≠ [] := by rintro rfl; exact hC (by simp [C])
  have hwne : upow u q ++ v ≠ [] := by
    obtain ⟨q', rfl⟩ := Nat.exists_eq_add_of_le' hq; simp [upow_succ, hune]
  have hlt := three_pow_lt_two_pow_of_follows hwne ha h
  have hDC : Dz (upow u q ++ v) ≤ |Cz u v| :=
    le_trans (le_abs_self _) (Int.le_of_dvd (abs_pos.2 hC)
      ((abs_dvd_abs _ _).2 (D_dvd_C_of_follows hu v hq h)))
  have hCb := abs_Cz_lt hu hv
  have hE : (upow u q ++ v).sum = q * u.sum + v.sum := by simp
  have ho : (upow u q ++ v).length = q * u.length + v.length := by simp
  have hlow := lower_bound hM (show 3 ^ (upow u q ++ v).length < 2 ^ (upow u q ++ v).sum by
    exact_mod_cast hlt)
  rw [hE, ho] at hlow
  have hDr : ((Dz (upow u q ++ v) : ℤ) : ℝ) < 2 ^ (u.sum + v.sum) * 3 ^ (u.length + v.length) := by
    exact_mod_cast lt_of_le_of_lt hDC hCb
  have hDe : ((Dz (upow u q ++ v) : ℤ) : ℝ) =
      2 ^ (q * u.sum + v.sum) - 3 ^ (q * u.length + v.length) := by
    simp only [D, hE, ho]; push_cast; ring
  have hchain : (3 : ℝ) ^ (q * u.length + v.length) * Real.exp (-c * (1 + Real.log
      (q * u.sum + v.sum : ℕ))) < 2 ^ (u.sum + v.sum) * 3 ^ (u.length + v.length) := by
    linarith
  have hl := Real.log_lt_log (by positivity) hchain
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_pow, Real.log_pow, Real.log_pow] at hl
  push_cast at hl ⊢
  nlinarith

/-- The explicit threshold `Q(u, v)` of Thm 2.9, as a function of `c` and
`m = len u, a = |u|, b = |v|`: with `K = max(1, 2ca/(m log 3))`,
`Q = 2 + 2((a+b) log 2 + c log K + cb/K)/(m log 3)`. -/
noncomputable def Qbound (c : ℝ) (m a b : ℕ) : ℝ :=
  2 + 2 * ((a + b) * Real.log 2 + c * Real.log (max 1 (2 * c * a / (m * Real.log 3))) +
    c * b / max 1 (2 * c * a / (m * Real.log 3))) / (m * Real.log 3)

/-- **Effective `q ≤ Q(u, v)`, conditional on `MatveevTwoThree c`** (Thm 2.9, last part):
under the hypotheses of `exclusion` (and `c ≥ 0`), `q < Q(u, v)`. -/
theorem q_lt_Qbound {c : ℝ} (hM : MatveevTwoThree c) (hc : 0 ≤ c) {u v : Word} (hu : u.Pos)
    (hv : v.Pos) {q : ℕ} (hq : 1 ≤ q) (hC : Cz u v ≠ 0) {a : ℤ} (ha : 0 < a)
    (h : Follows (2 : ℤ) 3 (upow u q ++ v) a a) :
    (q : ℝ) < Qbound c u.length u.sum v.sum := by
  have hx := exclusion hM hu hv hq hC ha h
  simp only [Nat.cast_add, Nat.cast_mul] at hx
  have hune : u ≠ [] := by rintro rfl; exact hC (by simp [C])
  have hm : (1 : ℝ) ≤ u.length := by exact_mod_cast List.length_pos_iff.2 hune
  have ha0 : 0 < u.sum := lt_of_lt_of_le (List.length_pos_iff.2 hune) (Word.Pos.length_le_sum hu)
  have ha1 : (1 : ℝ) ≤ u.sum := by exact_mod_cast ha0
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hL3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hmL : 0 < (u.length : ℝ) * Real.log 3 := by positivity
  set m : ℝ := (u.length : ℝ)
  set A : ℝ := (u.sum : ℝ)
  set B : ℝ := (v.sum : ℝ)
  set L3 := Real.log 3
  set K := max 1 (2 * c * A / (m * L3)) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK0 : 0 < K := by linarith
  have hK2 : 2 * c * A ≤ K * (m * L3) := (div_le_iff₀ hmL).1 (le_max_right _ _)
  set x : ℝ := q * A + B
  have hx0 : 0 < x := by have : (0 : ℝ) ≤ B := by positivity
                         nlinarith
  -- `log x ≤ log K + x/K - 1`
  have hlog : Real.log x ≤ Real.log K + x / K - 1 := by
    have := Real.log_le_sub_one_of_pos (div_pos hx0 hK0)
    rw [Real.log_div hx0.ne' hK0.ne'] at this
    linarith
  have hcx : c * (x / K) ≤ q * (m * L3) / 2 + c * B / K := by
    have e : c * (x / K) = c * q * A / K + c * B / K := by rw [show x = q * A + B from rfl]; ring
    rw [e]
    have : c * q * A / K ≤ q * (m * L3) / 2 := by
      rw [div_le_iff₀ hK0]; nlinarith
    linarith
  have hmain :
      ((q : ℝ) - 2) * (m * L3) < 2 * ((A + B) * Real.log 2 + c * Real.log K + c * B / K) := by
    have : c * Real.log x ≤ c * (Real.log K + x / K - 1) := mul_le_mul_of_nonneg_left hlog hc
    nlinarith
  have : (q : ℝ) - 2 < 2 * ((A + B) * Real.log 2 + c * Real.log K + c * B / K) / (m * L3) :=
    (lt_div_iff₀ hmL).2 hmain
  unfold Qbound
  linarith

/-- With Matveev's constant: `q < Q(u, v)` for `c = c₀`, conditional on `MatveevTwoThree c₀`. -/
theorem q_lt_Qbound_c₀ (hM : MatveevTwoThree c₀) {u v : Word} (hu : u.Pos) (hv : v.Pos) {q : ℕ}
    (hq : 1 ≤ q) (hC : Cz u v ≠ 0) {a : ℤ} (ha : 0 < a)
    (h : Follows (2 : ℤ) 3 (upow u q ++ v) a a) : (q : ℝ) < Qbound c₀ u.length u.sum v.sum :=
  q_lt_Qbound hM c₀_pos.le hu hv hq hC ha h

/-- **Effective `q ≤ Q(u, v)` for genuine positive Syracuse cycles**, conditional on
`MatveevTwoThree c₀`: if the gap word of a positive cycle is `u^q v` with `q ≥ 1` and
`C(u, v) ≠ 0`, then `q < Q(u, v)`. -/
theorem IsSyrCycle.q_lt_Qbound (hM : MatveevTwoThree c₀) {a : ℤ} {o : ℕ}
    (h : IsSyrCycle a o) (ha : 0 < a) {u v : Word} {q : ℕ} (hq : 1 ≤ q)
    (hw : gapWord a o = upow u q ++ v) (hC : Cz u v ≠ 0) :
    (q : ℝ) < Qbound c₀ u.length u.sum v.sum := by
  have hf := (IsSyrCycle.follows h)
  rw [hw] at hf
  obtain ⟨hu, hv⟩ := IsSyrCycle.blocks_pos h hq hw
  exact q_lt_Qbound_c₀ hM hu hv hq hC ha hf

/-- **Thm 2.13, corrected** (conditional on `MatveevTwoThree c`, `c ≥ 0`): the `E`-free
inequality `(q-1) m log 3 < (a+b) log 2 + c (1 + log(2qm + 2ℓ + 1))`. It holds because a positive
cycle has `E ≤ 2o` (`sum_le_two_mul_length`); band membership is *not* used (and not implied,
see `positive_cycle_not_in_band`). -/
theorem band_exclusion {c : ℝ} (hM : MatveevTwoThree c) (hc : 0 ≤ c) {u v : Word} (hu : u.Pos)
    (hv : v.Pos) {q : ℕ} (hq : 1 ≤ q) (hC : Cz u v ≠ 0) {a : ℤ} (ha : 0 < a)
    (h : Follows (2 : ℤ) 3 (upow u q ++ v) a a) :
    ((q : ℝ) - 1) * u.length * Real.log 3 <
      (u.sum + v.sum) * Real.log 2 +
        c * (1 + Real.log (2 * q * u.length + 2 * v.length + 1 : ℕ)) := by
  have hx := exclusion hM hu hv hq hC ha h
  have hE := sum_le_two_mul_length h ha
  simp only [List.sum_append, List.length_append, upow_sum, upow_length] at hE
  have hune : u ≠ [] := by rintro rfl; exact hC (by simp [C])
  have hpos : 0 < q * u.sum + v.sum := by
    have := Nat.mul_pos (show 0 < q by omega)
      (lt_of_lt_of_le (List.length_pos_iff.2 hune) (Word.Pos.length_le_sum hu))
    omega
  have hlog :
      Real.log (q * u.sum + v.sum : ℕ) ≤ Real.log (2 * q * u.length + 2 * v.length + 1 : ℕ) :=
    Real.log_le_log (by exact_mod_cast hpos) (by
      have : 2 * q * u.length = 2 * (q * u.length) := by ring
      exact_mod_cast (by omega))
  have := mul_le_mul_of_nonneg_left hlog hc
  linarith

/-! ## Witnesses and worked checks -/

/-- `gap a = k` when `3a + 1 = 2^k m` with `m` odd. -/
lemma gap_eq {a m : ℤ} {k : ℕ} (h : 3 * a + 1 = 2 ^ k * m) (hm : Odd m) : gap a = k := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have h2 : ¬ ((2 : ℕ) : ℤ) ∣ m := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd] at hm; exact_mod_cast hm
  rw [gap, h, padicValInt.mul (by positivity) hm0, padicValInt.eq_zero_of_not_dvd h2,
    show (2 : ℤ) ^ k = ((2 ^ k : ℕ) : ℤ) by push_cast; rfl, padicValInt.of_nat,
    padicValNat.prime_pow, add_zero]

/-- `syr a = m` when `3a + 1 = 2^k m` with `m` odd. -/
lemma syr_eq {a m : ℤ} {k : ℕ} (h : 3 * a + 1 = 2 ^ k * m) (hm : Odd m) : syr a = m := by
  rw [syr, gap_eq h hm, h, Int.mul_ediv_cancel_left _ (by positivity)]

/-- `ν₂(3·1 + 1) = 2`. -/
lemma gap_one : gap 1 = 2 := gap_eq (m := 1) (by norm_num) odd_one
/-- `1` is a fixed point of the accelerated map. -/
lemma syr_one : syr 1 = 1 := syr_eq (k := 2) (by norm_num) odd_one

/-- The gap word of `1` is `(2, 2, …, 2)`. -/
lemma gapWord_one (n : ℕ) : gapWord 1 n = List.replicate n 2 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [gapWord, gap_one, syr_one, ih, List.replicate_succ]

/-- `1 → 1` traversed `n ≥ 1` times is a cycle of length `n`. -/
lemma isSyrCycle_one_iter {n : ℕ} (hn : 0 < n) : IsSyrCycle 1 n :=
  ⟨hn, odd_one, Function.iterate_fixed syr_one n⟩

/-- The trivial cycle `1 → 1`: word `(2)`, `D = 1`, `S = 1`, `a₀ = S/D = 1` (`STATUS.md`). -/
theorem trivial_cycle_check : gapWord 1 1 = [2] ∧ Dz [2] = 1 ∧ Sz [2] = 1 :=
  ⟨gapWord_one 1, by decide, by decide⟩

/-- The negative cycle `-5 → -7 → -5`: word `(1, 2)`, `E = 3`, `o = 2`, `D = -1`,
`S^{(0)} = 5`, `S^{(1)} = 7`, `2·7 = 3·5 + (-1)`, `gcd = 1 = |D|` (`STATUS.md` worked checks). -/
theorem neg_five_cycle_check :
    IsSyrCycle (-5) 2 ∧ gapWord (-5) 2 = [1, 2] ∧ Dz [1, 2] = -1 ∧ Sz [1, 2] = 5 ∧
      Sz ([1, 2].rotate 1) = 7 ∧ 2 ^ 1 * Sz ([1, 2].rotate 1) = 3 * Sz [1, 2] + Dz [1, 2] ∧
      G [1, 2] = 1 := by
  have h1 : syr (-5) = -7 := syr_eq (k := 1) (by norm_num) (by decide)
  have h2 : syr (-7) = -5 := syr_eq (k := 2) (by norm_num) (by decide)
  have g1 : gap (-5) = 1 := gap_eq (m := -7) (by norm_num) (by decide)
  have g2 : gap (-7) = 2 := gap_eq (m := -5) (by norm_num) (by decide)
  have hc : IsSyrCycle (-5) 2 := ⟨by norm_num, by decide, by simp [h1, h2]⟩
  have hw : gapWord (-5) 2 = [1, 2] := by simp [gapWord, g1, g2, h1]
  refine ⟨hc, hw, by decide, by decide, by decide, by decide, ?_⟩
  have := IsSyrCycle.G_eq hc; rw [hw] at this; rw [this]; decide

/-- **Imprimitive cycles need not be critical** (`STATUS.md`): the trivial cycle traversed three
times has word `(2,2,2)` and non-critical `(E, o) = (6, 3)`. (`STATUS.md` writes
`(2,2,2) = 3×(2,1)`; it is `3×(2)`.) -/
theorem imprimitive_noncritical :
    IsSyrCycle 1 3 ∧ gapWord 1 3 = [2, 2, 2] ∧ ¬ Critical (gapWord 1 3).sum 3 := by
  refine ⟨isSyrCycle_one_iter (by norm_num), gapWord_one 3, ?_⟩
  rw [gapWord_one, critical_iff]; decide

/-- **A positive cycle need not lie in the critical band** (contra the abstract and the proof of
Thm 2.13 of `eventually-periodic.tex`): the trivial cycle traversed four times,
word `(2,2,2,2)`, has `2^8 = 256 > 243 = 3^5`. -/
theorem positive_cycle_not_in_band :
    IsSyrCycle 1 4 ∧ gapWord 1 4 = [2, 2, 2, 2] ∧ ¬ InBand (gapWord 1 4).sum 4 := by
  refine ⟨isSyrCycle_one_iter (by norm_num), gapWord_one 4, ?_⟩
  rw [gapWord_one, InBand]; decide

/-! ### The `(9, 5)` witness (`theorems.md` Prop. 4.4) -/

/-- The primitive non-critical word `(1, 2, 2, 2, 2)`, `E = 9`, `o = 5`. -/
def w95 : Word := [1, 2, 2, 2, 2]

/-- `E = 9`, `o = 5`, `D = 512 - 243 = 269`. -/
theorem w95_data : w95.sum = 9 ∧ w95.length = 5 ∧ Dz w95 = 269 := by decide

/-- The rotation sums `431, 781, 653, 557, 485` (the table of Prop. 4.4). -/
theorem w95_rotations :
    Sz (w95.rotate 0) = 431 ∧ Sz (w95.rotate 1) = 781 ∧ Sz (w95.rotate 2) = 653 ∧
      Sz (w95.rotate 3) = 557 ∧ Sz (w95.rotate 4) = 485 := by decide

/-- A property of all five rotation sums holds for every `j` (rotations are `5`-periodic). -/
lemma w95_forall {P : ℤ → Prop} (h : ∀ j < 5, P (Sz (w95.rotate j))) (j : ℕ) :
    P (Sz (w95.rotate j)) := by
  rw [← List.rotate_mod, show w95.length = 5 from rfl]; exact h _ (Nat.mod_lt _ (by norm_num))

/-- `min_j S^{(j)} = 431`. -/
theorem w95_min : (∀ j, 431 ≤ Sz (w95.rotate j)) ∧ Sz (w95.rotate 0) = 431 :=
  ⟨w95_forall (P := fun s => 431 ≤ s) (by decide), by decide⟩

/-- `(9, 5)` is non-critical: `2^{E-1} = 256 > 243 = 3^5`. -/
theorem w95_noncritical : 3 ^ 5 < 2 ^ 9 ∧ ¬ Critical 9 5 := by
  rw [critical_iff]; decide

/-- The word is primitive: its five rotations are pairwise distinct. -/
theorem w95_primitive : ((List.range 5).map w95.rotate).Nodup := by decide

/-- **The size route fails** (Prop. 4.4): every rotation sum exceeds `2^{E-1} = 256` and even
`D = 269`, so every `a_j = S^{(j)}/D` would exceed `1`. -/
theorem w95_min_gt : ∀ j, 2 ^ (9 - 1) < Sz (w95.rotate j) ∧ Dz w95 < Sz (w95.rotate j) :=
  w95_forall (P := fun s => 2 ^ (9 - 1) < s ∧ Dz w95 < s) (by decide)

/-- `431 = S^{(0)}` is prime, as the note remarks. -/
theorem w95_prime_431 : Nat.Prime 431 := by norm_num

/-- `gcd_j S^{(j)} = 1` for the witness. -/
theorem w95_G : G w95 = 1 := by
  have h1 : G w95 ∣ 431 := by have := G_dvd_S_rotate w95 0; rwa [w95_rotations.1] at this
  have h2 : G w95 ∣ 485 := by
    have := G_dvd_S_rotate w95 4; rwa [w95_rotations.2.2.2.2] at this
  have h3 : G w95 ∣ ((Int.gcd 431 485 : ℕ) : ℤ) := by
    rw [← Int.natAbs_of_nonneg (G_nonneg w95)]
    exact Int.natCast_dvd_natCast.2 (Int.dvd_gcd (by simpa using h1) (by simpa using h2))
  rw [show Int.gcd 431 485 = 1 by decide] at h3
  exact Int.eq_one_of_dvd_one (G_nonneg _) (by exact_mod_cast h3)

/-- The witness is **not a cycle** (excluded arithmetically: `269 ∤ 431`). -/
theorem w95_not_cycle : ¬ ∃ a : ℤ, Follows (2 : ℤ) 3 w95 a a := by
  rintro ⟨a, h⟩
  have := Follows.cycle_equation 2 3 h
  have hd : (269 : ℤ) ∣ 431 := ⟨a, by rw [← w95_rotations.1]; simpa [w95_data.2.2] using this.symm⟩
  exact absurd hd (by decide)

end Syracuse.CycleGcd
