import Syracuse.Basic

/-!
# The exclusion squeeze (`PROGRAM.md`)

Formalises the program overview `PROGRAM.md`: the floor (§1), the squeeze as a conditional theorem
(§2), the controlled lower bound stated as hypotheses (§3), the "below `3^o` hence critical"
implication (§5) and the AM–GM estimator (§7). The move calculus (§4) and the bounded-defect lever
(§6) are in `Syracuse/Approaches/BoundedDefectLever.lean` (not imported: approach files are
independent). Transcendence inputs are `def … : Prop`, never axioms.

## Coverage

| Note claim (`PROGRAM.md` §) | Lean name | Status |
|---|---|---|
| §1 rotations share `D` | `D_rotate` (Basic) | proved (Basic) |
| §1 `G = gcd_j S^{(j)} = \|2^E-3^o\|` on a genuine cycle (boxed) | `rotGcd_cycle`, `rotIdeal_cycle` | proved |
| §1 `G` odd and prime to `3` "(each `S^{(j)}` is)" | `Sz_odd`, `Sz_not_three_dvd`, `rotGcd_odd`, `rotGcd_not_three_dvd` | proved (oddness needs a positive word; true for any positive word, cycle or not) |
| `D` itself is a representative, `G ∣ D` for every word | `Dz_mem_rotIdeal`, `rotGcd_dvd_Dz` | proved (used for `G = \|D\|`) |
| §1 floor `\|C\| ≥ G`; §2 `G ≤ sixfree C` for every nonzero `ℤ`-combination | `floor` (also `G ∣ sixfree C`), `floor_unit` (`ℤ[1/6]`-unit form) | proved |
| §2 the squeeze: lower bound `B(o)` + family ceiling `c < B(o)` ⇒ no cycle | `LowerBound`, `squeeze`, `no_cycle_of_ceiling_lt` | proved (conditional on `LowerBound B`) |
| §3 Rhin / Simons–de Weger Lemma 12 `Λ > e^{-13.3(0.46057+ln o)}` | `RhinBound` (as used in §3), `SdWLemma12` (paper's Lemma 8 regime), `sdwLemma12_of_rhinBound` | stated only (not assumed) |
| §3 "`⟹ \|2^E-3^o\| > 0.00219·3^o/o^{13.3}`" | `abs_two_pow_sub_three_pow_ge`, `lowerBound_of_rhinBound` | corrected: `\|2^E-3^o\| ≥ 3^o(1-e^{-Λ})` (the step `> 3^oΛ` holds only when `2^E > 3^o`); and `e^{-13.3·0.46057} ≈ 0.0021862`, so `0.00219` is rounded up |
| §3 threshold `o ≈ 60` for `c = 5`; conjectural `μ = 2`; trivial regime | — | not formalized (numerical / conjectural) |
| §5 positive cycle ⇒ `2^E > 3^o` | `three_pow_lt_two_pow` | proved |
| §5 nonzero rep `\|C\| < 3^o` ⇒ `3^o < 2^E < 2·3^o` ⇒ `E = ⌈o log₂ 3⌉` | `critical_of_small_rep`, `clog_eq_of_critical`, `E_eq_clog_of_small_rep` | proved (positive cycles; ceiling as `Nat.clog 2 (3^o)`) |
| §5 "honest status": rep `< 3^o` ⟺ critical | `small_rep_iff_critical` | proved |
| §5 cycle equation alone: `2^E/3^o ≤ (4/3)^o` | `two_pow_le_four_pow` | proved (the bound; the product formula itself is not stated) |
| §5 de Weger Lemma 8 (`δo < E < 1.000001δo`), `x_min` bound; explicit `f(w)` | — | not formalized (computational input) / open |
| §6 bounded-defect lever | `Syracuse.BoundedDefectLever.ceiling` | proved there |
| §6 Layer-1 closure (McMullen, Boden–Friedl) | — | not formalized |
| §7 partial characters, `A(w) = S/(n3^{n-1}) = mean χ_k` | `chiPart`, `amean`, `amean_eq` | proved |
| §7 `G_*(w) = 2^{ē}/3^{(n-1)/2}` | `gmean`, `gmean_eq` | proved |
| §7 `G_* ≤ A ≤ C·G_*`, AM/GM gap `≥ 0` | `amgm_sandwich` (`stark`), `amean_le_of_bounds`, `amgm_gap_nonneg` | proved |
| §8 tool; §9 open problems | — | not formalized / open |
-/

namespace Syracuse.Program

open Syracuse

/-! ## Local helpers (re-proved; approach files do not import each other) -/

/-- `sixFree` ignores the sign. -/
@[simp] lemma sixFree_neg (c : ℤ) : sixFree (-c) = sixFree c := by simp [sixFree]

/-- `sixFree` ignores powers of `2` and `3`. -/
lemma sixFree_pow_mul (i j : ℕ) (c : ℤ) : sixFree (2 ^ i * 3 ^ j * c) = sixFree c := by
  have h3 : ordCompl[2] (3 ^ j) = 3 ^ j := by
    rw [Nat.factorization_eq_zero_of_not_dvd, pow_zero, Nat.div_one]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).1
      (Nat.prime_two.dvd_of_dvd_pow h)
    omega
  simp only [sixFree, Int.natAbs_mul, Int.natAbs_pow, Int.reduceAbs]
  rw [mul_assoc, Nat.ordCompl_self_pow_mul _ _ Nat.prime_two, Nat.ordCompl_mul, h3,
    Nat.ordCompl_self_pow_mul _ _ Nat.prime_three]

/-- A nonzero integer has a positive `6`-free part. -/
lemma sixFree_pos {c : ℤ} (hc : c ≠ 0) : 0 < sixFree c :=
  Nat.ordCompl_pos 3 (Nat.ordCompl_pos 2 (Int.natAbs_ne_zero.2 hc)).ne'

/-- The `6`-free part is at most the absolute value. -/
lemma sixFree_le_natAbs (c : ℤ) : sixFree c ≤ c.natAbs :=
  (Nat.ordCompl_le _ 3).trans (Nat.ordCompl_le _ 2)

/-- `D = 2^E - 3^o` is coprime to `6` once `E ≥ 1` and `o ≥ 1`. -/
lemma Dz_coprime_six {w : Word} (hE : 1 ≤ w.sum) (ho : 1 ≤ w.length) :
    Nat.Coprime (Dz w).natAbs 6 := by
  have h2 : ¬ (2 : ℤ) ∣ Dz w := by
    have hodd : Odd (Dz w) := Even.sub_odd ((Int.even_pow).2 ⟨even_two, by omega⟩)
      (Odd.pow (by decide))
    exact fun h => (Int.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  have h3 : ¬ (3 : ℤ) ∣ Dz w := by
    intro h
    have h' : (3 : ℤ) ∣ 2 ^ w.sum := by
      have := dvd_add h (dvd_pow_self (3 : ℤ) (by omega : w.length ≠ 0))
      simpa [D] using this
    have := Int.prime_three.dvd_of_dvd_pow h'
    norm_num at this
  rw [show (6 : ℕ) = 2 * 3 from rfl]
  refine Nat.Coprime.mul_right ?_ ?_
  · exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      fun h => h2 (Int.natCast_dvd.2 h))
  · exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      fun h => h3 (Int.natCast_dvd.2 h))

/-- The gap word of a genuine cycle has `E ≥ 1`. -/
lemma one_le_sum_gapWord {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) : 1 ≤ (gapWord a o).sum := by
  obtain ⟨o, rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by have := h.1; omega⟩
  simp only [gapWord, List.sum_cons]
  have := one_le_gap h.2.1
  omega

/-- The closed orbit of a genuine cycle along its own gap word. -/
lemma follows_cycle {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) : Follows (2 : ℤ) 3 (gapWord a o) a a := by
  have hf := follows_gapWord a o
  rwa [h.2.2] at hf

/-- The gap word of a genuine cycle is nonempty. -/
lemma gapWord_ne_nil {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) : gapWord a o ≠ [] := by
  intro h0
  have := congrArg List.length h0
  simp only [gapWord_length, List.length_nil] at this
  exact h.1.ne' this

/-! ## §1 The cocycle and the floor -/

/-- **Each rotation sum is odd** on a positive word (`PROGRAM.md` §1): the `k = 0` term `3^{o-1}` is
the only odd term of `S(w) = Σ_k 2^{e_k} 3^{o-1-k}`. -/
theorem Sz_odd {w : Word} (hw : w.Pos) (hne : w ≠ []) : Odd (Sz w) := by
  cases w with
  | nil => exact absurd rfl hne
  | cons d w =>
    show Odd (S (2 : ℤ) 3 (d :: w))
    rw [S_cons]
    have hd : 1 ≤ d := hw d List.mem_cons_self
    exact (Odd.pow (by decide)).add_even
      ((Int.even_pow.2 ⟨even_two, by omega⟩).mul_right _)

/-- **No rotation sum is divisible by `3`** (`PROGRAM.md` §1): the last term `2^{e_{o-1}}` is the only
term of `S(w)` prime to `3`. -/
theorem Sz_not_three_dvd {w : Word} (hne : w ≠ []) : ¬ (3 : ℤ) ∣ Sz w := by
  induction w with
  | nil => exact absurd rfl hne
  | cons d w ih =>
    cases w with
    | nil => simp
    | cons d' w' =>
      intro h
      have h' : (3 : ℤ) ∣ S (2 : ℤ) 3 (d :: d' :: w') := h
      rw [S_cons] at h'
      have h3 : (3 : ℤ) ∣ 3 ^ (d' :: w').length := dvd_pow_self _ (by simp)
      have h2 : (3 : ℤ) ∣ 2 ^ d * Sz (d' :: w') := (Int.dvd_add_right h3).1 h'
      rcases Int.prime_three.dvd_or_dvd h2 with h4 | h4
      · have := Int.prime_three.dvd_of_dvd_pow h4
        norm_num at this
      · exact ih (by simp) h4

/-- The **rotation ideal** of `w`: all `ℤ`-linear combinations `Σ_j c_j S^{(j)}` of rotation sums. -/
def rotIdeal (w : Word) : Ideal ℤ := Ideal.span (Set.range fun j : ℕ => Sz (w.rotate j))

/-- Each rotation sum is a representative. -/
lemma Sz_rotate_mem (w : Word) (j : ℕ) : Sz (w.rotate j) ∈ rotIdeal w :=
  Ideal.subset_span ⟨j, rfl⟩

/-- `D` is itself a representative: `D(w) = 2^{d₀} S^{(1)} - 3 S^{(0)}` (rotation recursion). Holds for
every nonempty word, cycle or not. -/
theorem Dz_mem_rotIdeal {w : Word} (hne : w ≠ []) : Dz w ∈ rotIdeal w := by
  obtain ⟨d, w', rfl⟩ := List.exists_cons_of_ne_nil hne
  have h := rotation_recursion (2 : ℤ) 3 d w'
  rw [← rotate_one_cons] at h
  have : Dz (d :: w') = 2 ^ d * Sz ((d :: w').rotate 1) - 3 * Sz ((d :: w').rotate 0) := by
    rw [List.rotate_zero, h]; ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Sz_rotate_mem _ 1))
    (Ideal.mul_mem_left _ _ (Sz_rotate_mem _ 0))

/-- On a closed orbit every representative is a multiple of `D`. -/
theorem rotIdeal_le_of_follows {w : Word} {x : ℤ} (h : Follows (2 : ℤ) 3 w x x) :
    rotIdeal w ≤ Ideal.span {Dz w} := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  exact Ideal.mem_span_singleton.2 (Follows.D_dvd_S_rotate _ _ h j)

/-- **On a genuine cycle the rotation ideal is `(2^E - 3^o)`.** -/
theorem rotIdeal_cycle {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    rotIdeal (gapWord a o) = Ideal.span {Dz (gapWord a o)} :=
  le_antisymm (rotIdeal_le_of_follows (follows_cycle h))
    ((Ideal.span_singleton_le_iff_mem _).2 (Dz_mem_rotIdeal (gapWord_ne_nil h)))

/-- The shift-gcd `G(w) = gcd_{0 ≤ j < o} S^{(j)}(w)` (normalised, so `G ≥ 0`). -/
def rotGcd (w : Word) : ℤ := (Finset.range w.length).gcd fun j => Sz (w.rotate j)

/-- `G` divides every rotation sum (all `j`, reduced mod `o`). -/
lemma rotGcd_dvd_Sz (w : Word) (j : ℕ) : rotGcd w ∣ Sz (w.rotate j) := by
  rcases Nat.eq_zero_or_pos w.length with h0 | hpos
  · rw [List.length_eq_zero_iff.1 h0]; simp [rotGcd]
  · rw [← List.rotate_mod]
    exact Finset.gcd_dvd (Finset.mem_range.2 (Nat.mod_lt _ hpos))

/-- `G ∣ D` for every nonempty word. -/
theorem rotGcd_dvd_Dz {w : Word} (hne : w ≠ []) : rotGcd w ∣ Dz w := by
  have hmem := Dz_mem_rotIdeal hne
  have : rotIdeal w ≤ Ideal.span {rotGcd w} :=
    Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Ideal.mem_span_singleton.2 (rotGcd_dvd_Sz w j))
  exact Ideal.mem_span_singleton.1 (this hmem)

/-- **The floor identity** `G = |2^E - 3^o|` on a genuine cycle (`PROGRAM.md` §1, boxed). -/
theorem rotGcd_cycle {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) :
    rotGcd (gapWord a o) = |Dz (gapWord a o)| := by
  have h1 := rotGcd_dvd_Dz (gapWord_ne_nil h)
  have h2 : Dz (gapWord a o) ∣ rotGcd (gapWord a o) :=
    Finset.dvd_gcd fun j _ => Follows.D_dvd_S_rotate _ _ (follows_cycle h) j
  have hnn : 0 ≤ rotGcd (gapWord a o) :=
    Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
  rw [← Int.natAbs_of_nonneg hnn, Int.natAbs_eq_of_dvd_dvd h1 h2, Int.natCast_natAbs]

/-- **`G` is odd** for every positive nonempty word. -/
theorem rotGcd_odd {w : Word} (hw : w.Pos) (hne : w ≠ []) : Odd (rotGcd w) := by
  have h := rotGcd_dvd_Sz w 0
  rw [List.rotate_zero] at h
  rw [← Int.not_even_iff_odd]
  intro he
  exact Int.not_even_iff_odd.2 (Sz_odd hw hne) (he.two_dvd.trans h |> even_iff_two_dvd.2)

/-- **`G` is prime to `3`** for every nonempty word. -/
theorem rotGcd_not_three_dvd {w : Word} (hne : w ≠ []) : ¬ (3 : ℤ) ∣ rotGcd w := by
  have h := rotGcd_dvd_Sz w 0
  rw [List.rotate_zero] at h
  exact fun h3 => Sz_not_three_dvd hne (h3.trans h)

/-- **The floor** (`PROGRAM.md` §1–§2). On a genuine cycle every nonzero `ℤ`-combination `C` of
rotation sums satisfies `|2^E - 3^o| ∣ sixFree C`, hence `|2^E - 3^o| ≤ sixFree C ≤ |C|`. -/
theorem floor {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {C : ℤ} (hC : C ∈ rotIdeal (gapWord a o))
    (hC0 : C ≠ 0) :
    ((2 : ℤ) ^ (gapWord a o).sum - 3 ^ o).natAbs ∣ sixFree C ∧
      ((2 : ℤ) ^ (gapWord a o).sum - 3 ^ o).natAbs ≤ sixFree C ∧
      |(2 : ℤ) ^ (gapWord a o).sum - 3 ^ o| ≤ |C| := by
  have hD : (2 : ℤ) ^ (gapWord a o).sum - 3 ^ o = Dz (gapWord a o) := by simp [D]
  rw [hD]
  have hdvd : Dz (gapWord a o) ∣ C :=
    Ideal.mem_span_singleton.1 (rotIdeal_cycle h ▸ hC)
  have hcop := Dz_coprime_six (one_le_sum_gapWord h) (by rw [gapWord_length]; exact h.1)
  have h1 := dvd_sixFree hcop (Int.natAbs_dvd.2 hdvd)
  have h2 := Nat.le_of_dvd (sixFree_pos hC0) h1
  refine ⟨h1, h2, ?_⟩
  have h3 := h2.trans (sixFree_le_natAbs C)
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  exact_mod_cast h3

/-- **The floor, `ℤ[1/6]`-unit form.** If `2^i 3^j C` is a representative (i.e. `C` is a
representative up to a `6`-unit) and `C ≠ 0`, then still `|2^E - 3^o| ≤ sixFree C`. -/
theorem floor_unit {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {i j : ℕ} {C : ℤ}
    (hC : 2 ^ i * 3 ^ j * C ∈ rotIdeal (gapWord a o)) (hC0 : C ≠ 0) :
    ((2 : ℤ) ^ (gapWord a o).sum - 3 ^ o).natAbs ≤ sixFree C := by
  have := (floor h hC (by positivity)).2.1
  rwa [sixFree_pow_mul] at this

/-! ## §2–§3 The exclusion squeeze and the controlled lower bound -/

/-- A **lower-bound hypothesis** `B(o) ≤ |2^E - 3^o|` for all `E` and all `o ≥ 1` (the
"their job" side of the squeeze). -/
def LowerBound (B : ℕ → ℝ) : Prop := ∀ E o : ℕ, 0 < o → B o ≤ |(2 : ℝ) ^ E - 3 ^ o|

/-- **Rhin / Simons–de Weger Lemma 12, in the unrestricted form `PROGRAM.md` §3 uses**:
`Λ = |E ln 2 - o ln 3| > e^{-13.3 (0.46057 + ln o)}` for all `E` and `o ≥ 1`. Stated, **not assumed**.
(The paper proves it only in the Lemma 8 regime; see `SdWLemma12`.) -/
def RhinBound : Prop :=
  ∀ E o : ℕ, 1 ≤ o →
    Real.exp (-(13.3 * (0.46057 + Real.log o))) < |(E : ℝ) * Real.log 2 - o * Real.log 3|

/-- **Simons–de Weger (2005) Lemma 12 in the paper's own scope**: with `K = o` odd steps and
`K + L = E`, inside the Lemma 8 regime `δ o < E < 1.000001 δ o` (`δ = log₂ 3`), where
`Λ = E ln 2 - o ln 3 > 0`, one has `Λ > e^{-13.3 (0.46057 + ln o)}`. Stated, **not assumed**. -/
def SdWLemma12 : Prop :=
  ∀ E o : ℕ, 1 ≤ o → (o : ℝ) * Real.log 3 < E * Real.log 2 →
    (E : ℝ) * Real.log 2 < 1.000001 * (o * Real.log 3) →
    Real.exp (-(13.3 * (0.46057 + Real.log o))) < E * Real.log 2 - o * Real.log 3

/-- The unrestricted form implies the paper's form. -/
theorem sdwLemma12_of_rhinBound (h : RhinBound) : SdWLemma12 := by
  intro E o ho h1 _
  have := h E o ho
  rwa [abs_of_pos (by linarith)] at this

/-- **From `Λ` to `|2^E - 3^o|` (corrected passage).** `|2^E - 3^o| ≥ 3^o (1 - e^{-Λ})` with
`Λ = |E ln 2 - o ln 3|`. (The `PROGRAM.md` step `|2^E - 3^o| > 3^o Λ` is only valid when
`2^E > 3^o`; in general one loses the factor `(1 - e^{-Λ})/Λ < 1`.) -/
theorem abs_two_pow_sub_three_pow_ge (E o : ℕ) :
    (3 : ℝ) ^ o * (1 - Real.exp (-|(E : ℝ) * Real.log 2 - o * Real.log 3|)) ≤
      |(2 : ℝ) ^ E - 3 ^ o| := by
  set t := (E : ℝ) * Real.log 2 - o * Real.log 3
  have h2 : (2 : ℝ) ^ E = Real.exp t * 3 ^ o := by
    rw [show t = E * Real.log 2 - o * Real.log 3 from rfl, Real.exp_sub, Real.exp_nat_mul,
      Real.exp_nat_mul, Real.exp_log two_pos, Real.exp_log three_pos]
    field_simp
  have key : 1 - Real.exp (-|t|) ≤ |Real.exp t - 1| := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht, abs_of_nonneg (by linarith [Real.add_one_le_exp t])]
      linarith [Real.add_one_le_exp t, Real.add_one_le_exp (-t)]
    · rw [abs_of_nonpos ht, neg_neg, abs_sub_comm, abs_of_nonneg
        (by linarith [Real.exp_le_one_iff.2 ht])]
  have h3 : (0 : ℝ) < 3 ^ o := pow_pos three_pos o
  rw [h2, show Real.exp t * 3 ^ o - 3 ^ o = 3 ^ o * (Real.exp t - 1) by ring, abs_mul,
    abs_of_pos h3]
  exact mul_le_mul_of_nonneg_left key h3.le

/-- **The controlled lower bound.** Under `RhinBound`,
`|2^E - 3^o| ≥ 3^o (1 - exp(-e^{-13.3 (0.46057 + ln o)}))` for all `E` and `o ≥ 1`
(`≈ 0.0021862 · 3^o / o^{13.3}`). -/
theorem lowerBound_of_rhinBound (h : RhinBound) :
    LowerBound fun o => (3 : ℝ) ^ o * (1 - Real.exp (-Real.exp (-(13.3 * (0.46057 + Real.log o))))) := by
  intro E o ho
  refine le_trans ?_ (abs_two_pow_sub_three_pow_ge E o)
  have hlt := h E o ho
  dsimp only
  gcongr

/-- **The exclusion squeeze** (`PROGRAM.md` §2). Given any lower bound `B`, every nonzero
representative `C` of the rotation ideal of a genuine cycle satisfies `B(o) ≤ sixFree C`. -/
theorem squeeze {B : ℕ → ℝ} (hB : LowerBound B) {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) {C : ℤ}
    (hC : C ∈ rotIdeal (gapWord a o)) (hC0 : C ≠ 0) : B o ≤ sixFree C := by
  refine (hB (gapWord a o).sum o h.1).trans ?_
  have := (floor h hC hC0).2.1
  have h' : (((2 : ℤ) ^ (gapWord a o).sum - 3 ^ o).natAbs : ℝ) =
      |(2 : ℝ) ^ (gapWord a o).sum - 3 ^ o| := by
    rw [Nat.cast_natAbs]; push_cast; rfl
  rw [← h']
  exact_mod_cast this

/-- **The squeeze excludes a family** (`PROGRAM.md` §2): if every word of a family `F` has a nonzero
representative with `6`-free part `≤ c`, then a genuine cycle in `F` has `B(o) ≤ c`; so there is
no cycle in `F` with `c < B(o)`. -/
theorem no_cycle_of_ceiling_lt {B : ℕ → ℝ} (hB : LowerBound B) (F : Word → Prop) (c : ℕ)
    (hF : ∀ w, F w → ∃ C ∈ rotIdeal w, C ≠ 0 ∧ sixFree C ≤ c) {a : ℤ} {o : ℕ}
    (hlt : (c : ℝ) < B o) : ¬ (IsSyrCycle a o ∧ F (gapWord a o)) := by
  rintro ⟨h, hFw⟩
  obtain ⟨C, hC, hC0, hc⟩ := hF _ hFw
  have := squeeze hB h hC hC0
  have hc' : (sixFree C : ℝ) ≤ c := by exact_mod_cast hc
  linarith

/-! ## §5 Below `3^o`, hence critical -/

/-- `S > 0` at `(2, 3)` for a nonempty word. -/
lemma Sz_pos {w : Word} (hw : w ≠ []) : 0 < Sz w := by
  have hnn : ∀ v : Word, 0 ≤ Sz v := by
    intro v
    induction v with
    | nil => simp
    | cons d v ih =>
      show 0 ≤ S (2 : ℤ) 3 (d :: v)
      rw [S_cons]
      exact add_nonneg (by positivity) (mul_nonneg (by positivity) ih)
  obtain ⟨d, v, rfl⟩ := List.exists_cons_of_ne_nil hw
  show 0 < S (2 : ℤ) 3 (d :: v)
  rw [S_cons]
  exact add_pos_of_pos_of_nonneg (by positivity) (mul_nonneg (by positivity) (hnn v))

/-- **On a positive cycle `2^E > 3^o`** (from `D a = S > 0` with `a > 0`). -/
theorem three_pow_lt_two_pow {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) :
    (3 : ℤ) ^ o < 2 ^ (gapWord a o).sum := by
  have hS := Sz_pos (gapWord_ne_nil h)
  have := h.cycle_equation
  have hD : 0 < Dz (gapWord a o) := by
    by_contra hD
    nlinarith
  simpa [D] using hD

/-- **§5, the exact implication.** On a positive cycle, a nonzero representative `C` with
`|C| < 3^o` forces `3^o < 2^E < 2·3^o`. -/
theorem critical_of_small_rep {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) {C : ℤ}
    (hC : C ∈ rotIdeal (gapWord a o)) (hC0 : C ≠ 0) (hlt : |C| < 3 ^ o) :
    (3 : ℤ) ^ o < 2 ^ (gapWord a o).sum ∧ (2 : ℤ) ^ (gapWord a o).sum < 2 * 3 ^ o := by
  have h1 := three_pow_lt_two_pow h ha
  have h2 := (floor h hC hC0).2.2
  rw [abs_of_pos (by linarith)] at h2
  exact ⟨h1, by linarith⟩

/-- **§5 "honest status": a representative below `3^o` exists iff the cycle is critical.** On a
positive cycle, some nonzero representative has `|C| < 3^o` iff `2^E < 2·3^o` (take `C = D`). -/
theorem small_rep_iff_critical {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) :
    (∃ C ∈ rotIdeal (gapWord a o), C ≠ 0 ∧ |C| < 3 ^ o) ↔
      (2 : ℤ) ^ (gapWord a o).sum < 2 * 3 ^ o := by
  constructor
  · rintro ⟨C, hC, hC0, hlt⟩
    exact (critical_of_small_rep h ha hC hC0 hlt).2
  · intro hcrit
    have h1 := three_pow_lt_two_pow h ha
    refine ⟨Dz (gapWord a o), Dz_mem_rotIdeal (gapWord_ne_nil h), ?_, ?_⟩
    · simp only [D, gapWord_length]; linarith
    · simp only [D, gapWord_length]
      rw [abs_of_pos (by linarith)]
      linarith

/-- `3^o < 2^E < 2·3^o` pins `E = ⌈log₂ 3^o⌉ = ⌈o log₂ 3⌉` (**critical**). -/
theorem clog_eq_of_critical {E o : ℕ} (h1 : 3 ^ o < 2 ^ E) (h2 : 2 ^ E < 2 * 3 ^ o) :
    Nat.clog 2 (3 ^ o) = E := by
  have hE : 1 ≤ E := by
    rcases Nat.eq_zero_or_pos E with rfl | hE
    · simp at h1
    · exact hE
  refine le_antisymm (Nat.clog_le_of_le_pow h1.le) ?_
  have : E - 1 < Nat.clog 2 (3 ^ o) := by
    rw [Nat.lt_clog_iff_pow_lt (by norm_num)]
    have : 2 ^ E = 2 * 2 ^ (E - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  omega

/-- **§5 milestone in full.** On a positive cycle, a nonzero representative `|C| < 3^o` forces
`E = ⌈o log₂ 3⌉`. -/
theorem E_eq_clog_of_small_rep {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) {C : ℤ}
    (hC : C ∈ rotIdeal (gapWord a o)) (hC0 : C ≠ 0) (hlt : |C| < 3 ^ o) :
    (gapWord a o).sum = Nat.clog 2 (3 ^ o) := by
  obtain ⟨h1, h2⟩ := critical_of_small_rep h ha hC hC0 hlt
  exact (clog_eq_of_critical (by exact_mod_cast h1) (by exact_mod_cast h2)).symm

/-- Along a positive orbit each step has `2^{d} a' = 3a + 1 ≤ 4a`, so `2^{|w|} b ≤ 4^{len w} a`. -/
lemma follows_bound {w : Word} {x y : ℤ} (h : Follows (2 : ℤ) 3 w x y) (hx : 0 < x) :
    0 < y ∧ 2 ^ w.sum * y ≤ 4 ^ w.length * x := by
  induction h with
  | nil => exact ⟨hx, by simp⟩
  | @cons d w x x' y hstep _ ih =>
    have hx' : 0 < x' := by
      have : 0 < (2 : ℤ) ^ d * x' := by rw [hstep]; linarith
      exact pos_of_mul_pos_right this (by positivity)
    obtain ⟨hy, hb⟩ := ih hx'
    refine ⟨hy, ?_⟩
    simp only [List.sum_cons, List.length_cons, pow_add, pow_succ]
    have h2d : (0 : ℤ) < 2 ^ d := by positivity
    have h4 : (0 : ℤ) ≤ 4 ^ w.length := by positivity
    calc 2 ^ d * 2 ^ w.sum * y = 2 ^ d * (2 ^ w.sum * y) := by ring
      _ ≤ 2 ^ d * (4 ^ w.length * x') := mul_le_mul_of_nonneg_left hb h2d.le
      _ = 4 ^ w.length * (3 * x + 1) := by rw [← hstep]; ring
      _ ≤ 4 ^ w.length * 4 * x := by nlinarith

/-- **The cycle equation alone only gives `2^E ≤ 4^o`** on a positive cycle (`2^E/3^o =
∏(1 + 1/(3x_i)) ≤ (4/3)^o`), i.e. `E ≤ 2o`: criticality is not forced by the algebra. -/
theorem two_pow_le_four_pow {a : ℤ} {o : ℕ} (h : IsSyrCycle a o) (ha : 0 < a) :
    (2 : ℤ) ^ (gapWord a o).sum ≤ 4 ^ o := by
  have := (follows_bound (follows_cycle h) ha).2
  rw [gapWord_length] at this
  exact le_of_mul_le_mul_right this ha

/-! ## §7 The abelian (AM–GM) estimator -/

/-- The **partial character** `χ_k(w) = 2^{e_k} / 3^k`. -/
noncomputable def chiPart (w : Word) (k : ℕ) : ℝ := 2 ^ e w k / 3 ^ k

/-- The **arithmetic mean** `A(w) = S(w) / (n 3^{n-1})`. -/
noncomputable def amean (w : Word) : ℝ := Sz w / (w.length * 3 ^ (w.length - 1))

/-- The **geometric mean** `G_*(w) = (∏_{k<n} χ_k)^{1/n}`. -/
noncomputable def gmean (w : Word) : ℝ :=
  (∏ k ∈ Finset.range w.length, chiPart w k) ^ ((1 : ℝ) / w.length)

/-- `χ_k > 0`. -/
lemma chiPart_pos (w : Word) (k : ℕ) : 0 < chiPart w k := by unfold chiPart; positivity

/-- `S(w) = 3^{n-1} Σ_k χ_k`, i.e. `A(w)` is the arithmetic mean of the partial characters. -/
theorem amean_eq {w : Word} (hw : w ≠ []) :
    amean w = (∑ k ∈ Finset.range w.length, chiPart w k) / w.length := by
  have hn : 0 < w.length := List.length_pos_of_ne_nil hw
  have hS : (Sz w : ℝ) = ∑ k ∈ Finset.range w.length, (2 : ℝ) ^ e w k * 3 ^ (w.length - 1 - k) := by
    show ((S (2 : ℤ) 3 w : ℤ) : ℝ) = _
    rw [S_eq_sum]; push_cast; rfl
  rw [amean, hS, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have h3 : (3 : ℝ) ^ (w.length - 1) = 3 ^ (w.length - 1 - k) * 3 ^ k := by
    rw [← pow_add]; congr 1; omega
  rw [chiPart, h3]
  field_simp

/-- `G_*(w) = 2^{ē} / 3^{(n-1)/2}` with `ē = (Σ_k e_k)/n`: it depends only on `Σ_k e_k` and `n`. -/
theorem gmean_eq {w : Word} (hw : w ≠ []) :
    gmean w = (2 : ℝ) ^ ((∑ k ∈ Finset.range w.length, (e w k : ℝ)) / w.length) /
      (3 : ℝ) ^ (((w.length : ℝ) - 1) / 2) := by
  have hn : (0 : ℝ) < w.length := by exact_mod_cast List.length_pos_of_ne_nil hw
  have hsum : (∑ k ∈ Finset.range w.length, (k : ℝ)) = w.length * ((w.length : ℝ) - 1) / 2 := by
    have := Finset.sum_range_id_mul_two w.length
    have h' : ((∑ k ∈ Finset.range w.length, k : ℕ) : ℝ) * 2 = w.length * ((w.length - 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [Nat.cast_sub (Nat.succ_le_of_lt (List.length_pos_of_ne_nil hw))] at h'
    push_cast at h'
    linarith
  simp only [gmean, chiPart]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum,
    Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast (2 : ℝ),
    ← Real.rpow_natCast (3 : ℝ), ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
  congr 2
  · push_cast; field_simp
  · rw [Nat.cast_sum, hsum]; field_simp

/-- `G_* = ∏_k χ_k^{1/n}`. -/
lemma gmean_eq_prod {w : Word} :
    gmean w = ∏ k ∈ Finset.range w.length, chiPart w k ^ ((1 : ℝ) / w.length) :=
  (Real.finsetProd_rpow _ _ (fun k _ => (chiPart_pos w k).le) _).symm

/-- `G_* > 0`. -/
lemma gmean_pos (w : Word) : 0 < gmean w := by
  rw [gmean_eq_prod]
  exact Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (chiPart_pos w k) _

/-- **AM–GM, lower half** (`PROGRAM.md` §7): `G_*(w) ≤ A(w)`. -/
theorem gmean_le_amean {w : Word} (hw : w ≠ []) : gmean w ≤ amean w := by
  have hn : (0 : ℝ) < w.length := by exact_mod_cast List.length_pos_of_ne_nil hw
  have := Real.geom_mean_le_arith_mean_weighted (Finset.range w.length)
    (fun _ => (1 : ℝ) / w.length) (chiPart w) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp)
    (fun k _ => (chiPart_pos w k).le)
  rw [gmean_eq_prod, amean_eq hw, Finset.sum_div]
  refine this.trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  ring

/-- **AM–GM, upper half with explicit bounds.** If `m ≤ χ_k ≤ M` for all `k` (`m > 0`), then
`A(w) ≤ (M/m) G_*(w)`. -/
theorem amean_le_of_bounds {w : Word} (hw : w ≠ []) {m M : ℝ} (hm : 0 < m)
    (hlo : ∀ k < w.length, m ≤ chiPart w k) (hhi : ∀ k < w.length, chiPart w k ≤ M) :
    amean w ≤ M / m * gmean w := by
  have hn0 : w.length ≠ 0 := (List.length_pos_of_ne_nil hw).ne'
  have hn : (0 : ℝ) < w.length := by exact_mod_cast List.length_pos_of_ne_nil hw
  have hA : amean w ≤ M := by
    rw [amean_eq hw, div_le_iff₀ hn]
    calc ∑ k ∈ Finset.range w.length, chiPart w k ≤ ∑ _k ∈ Finset.range w.length, M :=
          Finset.sum_le_sum fun k hk => hhi k (Finset.mem_range.1 hk)
      _ = M * w.length := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have hG : m ≤ gmean w := by
    have hprod : m ^ w.length ≤ ∏ k ∈ Finset.range w.length, chiPart w k := by
      rw [show m ^ w.length = ∏ _k ∈ Finset.range w.length, m by simp]
      exact Finset.prod_le_prod₀ (fun _ _ => hm.le) fun k hk => hlo k (Finset.mem_range.1 hk)
    calc m = (m ^ w.length) ^ ((1 : ℝ) / w.length) := by
          rw [one_div, Real.pow_rpow_inv_natCast hm.le hn0]
      _ ≤ gmean w := Real.rpow_le_rpow (by positivity) hprod (by positivity)
  have hM : 0 ≤ M / m := div_nonneg (hm.le.trans ((hlo 0 (by omega)).trans (hhi 0 (by omega))))
    hm.le
  calc amean w ≤ M := hA
    _ = M / m * m := by field_simp
    _ ≤ M / m * gmean w := mul_le_mul_of_nonneg_left hG hM

/-- The index range of a nonempty word is nonempty. -/
lemma range_length_nonempty {w : Word} (hw : w ≠ []) : (Finset.range w.length).Nonempty :=
  Finset.nonempty_range_iff.2 (List.length_pos_of_ne_nil hw).ne'

/-- The **stark ratio** `C(w) = max_k χ_k / min_k χ_k`. -/
noncomputable def stark (w : Word) (hw : w ≠ []) : ℝ :=
  (Finset.range w.length).sup' (range_length_nonempty hw) (chiPart w) /
    (Finset.range w.length).inf' (range_length_nonempty hw) (chiPart w)

/-- **AM–GM sandwich** (`PROGRAM.md` §7): `G_*(w) ≤ A(w) ≤ C(w) G_*(w)`. -/
theorem amgm_sandwich {w : Word} (hw : w ≠ []) :
    gmean w ≤ amean w ∧ amean w ≤ stark w hw * gmean w :=
  ⟨gmean_le_amean hw, amean_le_of_bounds hw
    ((Finset.lt_inf'_iff _).2 fun k _ => chiPart_pos w k)
    (fun _ hk => Finset.inf'_le _ (Finset.mem_range.2 hk))
    (fun _ hk => Finset.le_sup' (chiPart w) (Finset.mem_range.2 hk))⟩

/-- The **AM/GM gap** `log(A/G_*) ≥ 0`. -/
theorem amgm_gap_nonneg {w : Word} (hw : w ≠ []) : 0 ≤ Real.log (amean w / gmean w) :=
  Real.log_nonneg ((one_le_div (gmean_pos w)).2 (gmean_le_amean hw))

end Syracuse.Program
