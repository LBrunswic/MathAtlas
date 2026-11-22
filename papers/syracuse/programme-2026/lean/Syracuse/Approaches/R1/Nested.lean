import Syracuse.Approaches.R1.WPow

/-!
# Nested families `(w^a w')^b w''`

A two-parameter family whose outer exponent `b` multiplies the whole inner word `v_a = w^a w'`.
Its exponents are bilinear in `(a, b)`, so it lies outside the run-torus picture. Yet it is
classified **elementarily and uniformly in `(w, w', w'')`**, with no Baker input:

* **Plücker step** (`nested_identity`):
  `D(w) · C(v_a, w'') = D(v_a) · C(w, w'') - 2^{a|w|} D(w'') · C(w, w')`.
  So `D(w) C(v_a, w'') = α 2^{a|w|} - β 3^{a len w}` with constants `α, β` (`nested_linear`).
* **Zero set** (`nested_zero_subsingleton`, `nested_zero_all`): `C(v_a, w'') = 0` holds for at most
  one `a`, unless `α = β = 0`, in which case it holds for every `a`.
* **Joint bound** (`nested_exceptional_finite`): only finitely many `a` admit a cycle with `b ≥ 2`
  and `C(v_a, w'') ≠ 0`. The reason: `|D(w) C| ≤ K (Z + T)` grows linearly in `Z + T`, while
  `|D(v_a^b w'')| ≥ (Z + T)^2 / 8` grows quadratically, where `Z = 2^{a|w|}`, `T = 3^{a len w}`.
* **Classification** (`nested_classification`). The cycle members are:
  - `b = 0`: the word `w''`;
  - `b = 1`: the family `w^a (w' w'')` (classified by `WPow`);
  - `b ≥ 2`: a finite set of pairs, together with the pairs where `C(v_a, w'') = 0` and `v_a` is a
    cycle word, in which case `v_a^b w''` is a cycle word for every `b`.
-/

namespace Syracuse.R1

open Syracuse Syracuse.CocycleCombine Filter

/-- **The Plücker step**, in any commutative ring. -/
theorem nested_identity {R : Type*} [CommRing R] (X Y : R) (w w' w'' : Word) (a : ℕ) :
    D X Y w * wedge X Y (wpow w a ++ w') w'' =
      D X Y (wpow w a ++ w') * wedge X Y w w'' - X ^ (a * w.sum) * D X Y w'' * wedge X Y w w' := by
  have h := wpow_append_identity X Y w w' a
  unfold wedge at h ⊢
  linear_combination (-D X Y w'') * h

/-- The two constants of the linear form. -/
def nα (w w' w'' : Word) : ℤ := 2 ^ w'.sum * Cw w w'' - Dz w'' * Cw w w'
def nβ (w w' w'' : Word) : ℤ := 3 ^ w'.length * Cw w w''

/-- `D(w) · C(v_a, w'') = α · 2^{a|w|} - β · 3^{a len w}`. -/
theorem nested_linear (w w' w'' : Word) (a : ℕ) :
    Dz w * Cw (wpow w a ++ w') w'' =
      nα w w' w'' * 2 ^ (a * w.sum) - nβ w w' w'' * 3 ^ (a * w.length) := by
  have h := nested_identity (2 : ℤ) 3 w w' w'' a
  simp only [Cw, nα, nβ, Dz] at h ⊢
  rw [h]
  simp only [D, List.sum_append, List.length_append, wpow_sum, wpow_length, pow_add]
  ring

lemma two_pow_ne_three_pow_int {m n : ℕ} (hm : 1 ≤ m) : (2 : ℤ) ^ m ≠ 3 ^ n := by
  intro h
  have h2 : (2 : ℤ) ∣ 3 ^ n := h ▸ dvd_pow_self 2 (by omega)
  have := Int.Prime.dvd_pow' (p := 2) (by norm_num) h2
  omega

/-- **Zero set, generic case.** Unless `α = β = 0`, at most one `a` has `C(v_a, w'') = 0`. -/
theorem nested_zero_subsingleton {w w' w'' : Word} (hw : w.Pos) (hw0 : w ≠ [])
    (hαβ : nα w w' w'' ≠ 0 ∨ nβ w w' w'' ≠ 0) :
    {a | Cw (wpow w a ++ w') w'' = 0}.Subsingleton := by
  have hs : 1 ≤ w.sum := by have := sum_ne_zero hw hw0; omega
  have key : ∀ a, Cw (wpow w a ++ w') w'' = 0 →
      nα w w' w'' * 2 ^ (a * w.sum) = nβ w w' w'' * 3 ^ (a * w.length) := by
    intro a h0
    have := nested_linear w w' w'' a
    rw [h0, mul_zero] at this
    linarith
  intro a ha b hb
  have e1 := key a ha
  have e2 := key b hb
  have hα : nα w w' w'' ≠ 0 := by
    rcases hαβ with h | h
    · exact h
    · intro h0; rw [h0, zero_mul] at e1
      exact h (by
        rcases mul_eq_zero.mp e1.symm with h' | h'
        · exact h'
        · exact absurd h' (by positivity))
  by_contra hne
  -- WLOG a < b
  have main : ∀ x y : ℕ, x < y → nα w w' w'' * 2 ^ (x * w.sum) = nβ w w' w'' * 3 ^ (x * w.length) →
      nα w w' w'' * 2 ^ (y * w.sum) = nβ w w' w'' * 3 ^ (y * w.length) → False := by
    intro x y hxy ex ey
    obtain ⟨k, rfl⟩ : ∃ k, y = x + (k + 1) := ⟨y - x - 1, by omega⟩
    have : nα w w' w'' * 2 ^ (x * w.sum) * 2 ^ ((k + 1) * w.sum) =
        nα w w' w'' * 2 ^ (x * w.sum) * 3 ^ ((k + 1) * w.length) := by
      have ey' : nα w w' w'' * (2 ^ (x * w.sum) * 2 ^ ((k + 1) * w.sum)) =
          nβ w w' w'' * (3 ^ (x * w.length) * 3 ^ ((k + 1) * w.length)) := by
        rw [← pow_add, ← pow_add, ← add_mul, ← add_mul]; exact ey
      linear_combination ey' - 3 ^ ((k + 1) * w.length) * ex
    have hnz : nα w w' w'' * 2 ^ (x * w.sum) ≠ 0 := mul_ne_zero hα (by positivity)
    exact two_pow_ne_three_pow_int (m := (k + 1) * w.sum) (n := (k + 1) * w.length)
      (Nat.one_le_iff_ne_zero.mpr (by positivity)) (mul_left_cancel₀ hnz this)
  rcases lt_or_gt_of_ne hne with h | h
  · exact main a b h e1 e2
  · exact main b a h e2 e1

/-- **Zero set, degenerate case.** If `α = β = 0`, then `C(v_a, w'') = 0` for every `a`. -/
theorem nested_zero_all {w w' w'' : Word} (hw : w.Pos) (hw0 : w ≠ [])
    (hα : nα w w' w'' = 0) (hβ : nβ w w' w'' = 0) (a : ℕ) : Cw (wpow w a ++ w') w'' = 0 := by
  have h := nested_linear w w' w'' a
  rw [hα, hβ, zero_mul, zero_mul, sub_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (Dz_ne_zero hw hw0)

/-! ## The joint bound -/

/-- A dominant term beats a subdominant one: `P^2/2 ≤ A P^b - c Q^b` when `λ Q ≤ P`. -/
lemma dom_sq {A c P Q l : ℝ} {b : ℕ} (hb : 2 ≤ b) (hA : 1 ≤ A) (hc : 0 ≤ c) (hQ : 0 ≤ Q)
    (hP : 1 ≤ P) (hl : 1 ≤ l) (hlc : 2 * c ≤ l ^ 2) (hPQ : l * Q ≤ P) :
    P ^ 2 / 2 ≤ A * P ^ b - c * Q ^ b := by
  have hl0 : 0 < l := by linarith
  have hQP : Q ≤ P / l := by rw [le_div_iff₀ hl0]; linarith
  have hQb : Q ^ b ≤ P ^ b / l ^ b := by
    rw [← div_pow]; exact pow_le_pow_left₀ hQ hQP b
  have hlb : l ^ 2 ≤ l ^ b := pow_le_pow_right₀ hl hb
  have hPb : P ^ 2 ≤ P ^ b := pow_le_pow_right₀ hP hb
  have hPb0 : 0 ≤ P ^ b := by positivity
  have h1 : c * Q ^ b ≤ c * (P ^ b / l ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hc
    exact hQb.trans (div_le_div_of_nonneg_left hPb0 (by positivity) hlb)
  have h2 : c * (P ^ b / l ^ 2) ≤ P ^ b / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  nlinarith

/-- **Joint bound.** Only finitely many `a` carry a cycle `(w^a w')^b w''` with `b ≥ 2` and
`C(w^a w', w'') ≠ 0`. -/
theorem nested_exceptional_finite {w w' w'' : Word} (hw : w.Pos) (hw0 : w ≠ []) (hw1 : w'.Pos)
    (hw2 : w''.Pos) :
    {a | ∃ b, 2 ≤ b ∧ IsCycleWord (wpow (wpow w a ++ w') b ++ w'') ∧
      Cw (wpow w a ++ w') w'' ≠ 0}.Finite := by
  set K : ℝ := |(nα w w' w'' : ℝ)| + |(nβ w w' w'' : ℝ)|
  have hs : 1 ≤ w.sum := by have := sum_ne_zero hw hw0; omega
  have hDw : (1 : ℝ) ≤ |(Dz w : ℝ)| := by
    have := Dz_ne_zero hw hw0
    exact_mod_cast Int.one_le_abs this
  -- the base ratio is not 1
  have hne : (2 : ℝ) ^ w.sum ≠ 3 ^ w.length := by
    exact_mod_cast two_pow_ne_three_pow_int (n := w.length) hs
  set A₂ : ℝ := 2 ^ w''.sum
  set c₃ : ℝ := 3 ^ w''.length
  set P₀ : ℝ := 2 ^ w'.sum
  set Q₀ : ℝ := 3 ^ w'.length
  have hA₂ : 1 ≤ A₂ := one_le_pow₀ (by norm_num)
  have hc₃ : 1 ≤ c₃ := one_le_pow₀ (by norm_num)
  have hP₀ : 1 ≤ P₀ := one_le_pow₀ (by norm_num)
  have hQ₀ : 1 ≤ Q₀ := one_le_pow₀ (by norm_num)
  -- Z + T → ∞
  have hZT : Tendsto (fun a : ℕ => ((2 : ℝ) ^ w.sum) ^ a + ((3 : ℝ) ^ w.length) ^ a) atTop atTop := by
    have h2 : (1 : ℝ) < 2 ^ w.sum := one_lt_pow₀ (by norm_num) (by omega)
    exact tendsto_atTop_mono (fun a => le_add_of_nonneg_right (by positivity))
      (tendsto_pow_atTop_atTop_of_one_lt h2)
  -- the dominance condition holds eventually
  have hdom : ∀ᶠ a : ℕ in atTop,
      (2 * c₃ * Q₀ * ((3 : ℝ) ^ w.length) ^ a ≤ P₀ * ((2 : ℝ) ^ w.sum) ^ a ∧
          ((3 : ℝ) ^ w.length) ^ a ≤ ((2 : ℝ) ^ w.sum) ^ a) ∨
        (2 * A₂ * P₀ * ((2 : ℝ) ^ w.sum) ^ a ≤ Q₀ * ((3 : ℝ) ^ w.length) ^ a ∧
          ((2 : ℝ) ^ w.sum) ^ a ≤ ((3 : ℝ) ^ w.length) ^ a) := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- 2^{|w|} < 3^{len w}: the 3-side dominates
      have hr : (1 : ℝ) < 3 ^ w.length / 2 ^ w.sum := by rw [one_lt_div (by positivity)]; exact hlt
      have ht := tendsto_pow_atTop_atTop_of_one_lt hr
      filter_upwards [ht.eventually_ge_atTop (2 * A₂ * P₀ / Q₀), ht.eventually_ge_atTop 1] with a h1 h2
      right
      have hZ : (0 : ℝ) < ((2 : ℝ) ^ w.sum) ^ a := by positivity
      rw [div_pow, le_div_iff₀ hZ] at h1 h2
      constructor
      · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h1; linarith
      · linarith
    · have hr : (1 : ℝ) < 2 ^ w.sum / 3 ^ w.length := by rw [one_lt_div (by positivity)]; exact hgt
      have ht := tendsto_pow_atTop_atTop_of_one_lt hr
      filter_upwards [ht.eventually_ge_atTop (2 * c₃ * Q₀ / P₀), ht.eventually_ge_atTop 1] with a h1 h2
      left
      have hT : (0 : ℝ) < ((3 : ℝ) ^ w.length) ^ a := by positivity
      rw [div_pow, le_div_iff₀ hT] at h1 h2
      constructor
      · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h1; linarith
      · linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hdom.and (hZT.eventually_gt_atTop (8 * K)))
  refine (Set.finite_Iio N).subset fun a ⟨b, hb, hcyc, hC⟩ => ?_
  by_contra hlt
  simp only [Set.mem_Iio, not_lt] at hlt
  obtain ⟨hd, hbig⟩ := hN a hlt
  set Z : ℝ := ((2 : ℝ) ^ w.sum) ^ a
  set T : ℝ := ((3 : ℝ) ^ w.length) ^ a
  have hZ1 : 1 ≤ Z := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hT1 : 1 ≤ T := one_le_pow₀ (one_le_pow₀ (by norm_num))
  -- upper bound: |D(w)| |C| ≤ K (Z + T)
  have hlin := nested_linear w w' w'' a
  have hup : |(Dz w : ℝ)| * |(Cw (wpow w a ++ w') w'' : ℝ)| ≤ K * (Z + T) := by
    rw [← abs_mul]
    have : ((Dz w : ℝ) * (Cw (wpow w a ++ w') w'' : ℝ)) =
        (nα w w' w'' : ℝ) * Z - (nβ w w' w'' : ℝ) * T := by
      have := congrArg (fun x : ℤ => (x : ℝ)) hlin
      push_cast at this
      rw [this, pow_mul', pow_mul']
    rw [this]
    calc |(nα w w' w'' : ℝ) * Z - (nβ w w' w'' : ℝ) * T|
        ≤ |(nα w w' w'' : ℝ)| * Z + |(nβ w w' w'' : ℝ)| * T := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < Z), abs_of_pos (by linarith : (0:ℝ) < T)]
      _ ≤ K * (Z + T) := by
          have := abs_nonneg (nα w w' w'' : ℝ); have := abs_nonneg (nβ w w' w'' : ℝ)
          nlinarith
  -- the inner word
  set v := wpow w a ++ w'
  have hv : v.Pos := wpow_append_pos hw hw1 a
  have hvne : v ≠ [] := by
    intro h0; apply hC; simp [Cw, wedge, h0, D]
  -- ceiling for the outer family: |D(v^b w'')| ≤ |C(v, w'')|
  have hceil := wpow_append_ceiling hv hw2 hC hcyc
  have hceilR : |((Dz (wpow v b ++ w'') : ℤ) : ℝ)| ≤ |((Cw v w'' : ℤ) : ℝ)| := by
    exact_mod_cast hceil
  -- closed form of D(v^b w'')
  have hDW : ((Dz (wpow v b ++ w'') : ℤ) : ℝ) = A₂ * (P₀ * Z) ^ b - c₃ * (Q₀ * T) ^ b := by
    simp only [v, Dz, D, List.sum_append, List.length_append, wpow_sum, wpow_length]
    push_cast
    simp only [A₂, c₃, P₀, Q₀, Z, T]
    ring
  -- lower bound: (Z+T)^2/8 ≤ |D(v^b w'')|
  have hlow : (Z + T) ^ 2 / 8 ≤ |((Dz (wpow v b ++ w'') : ℤ) : ℝ)| := by
    rw [hDW]
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := dom_sq (A := A₂) (c := c₃) (P := P₀ * Z) (Q := Q₀ * T) (l := 2 * c₃) hb hA₂
        (by linarith) (by positivity) (by nlinarith) (by linarith) (by nlinarith) (by nlinarith)
      have hPZ : Z ≤ P₀ * Z := by nlinarith
      refine le_trans ?_ (this.trans (le_abs_self _))
      nlinarith
    · have := dom_sq (A := c₃) (c := A₂) (P := Q₀ * T) (Q := P₀ * Z) (l := 2 * A₂) hb hc₃
        (by linarith) (by positivity) (by nlinarith) (by linarith) (by nlinarith) (by nlinarith)
      have hQT : T ≤ Q₀ * T := by nlinarith
      refine le_trans ?_ (this.trans ?_)
      · nlinarith
      · rw [abs_sub_comm]; exact le_abs_self _
  -- combine
  have hfinal : |(Dz w : ℝ)| * ((Z + T) ^ 2 / 8) ≤ K * (Z + T) := by
    calc |(Dz w : ℝ)| * ((Z + T) ^ 2 / 8) ≤ |(Dz w : ℝ)| * |((Cw v w'' : ℤ) : ℝ)| :=
          mul_le_mul_of_nonneg_left (hlow.trans hceilR) (abs_nonneg _)
      _ ≤ K * (Z + T) := hup
  have hpos : 0 < Z + T := by linarith
  have : (Z + T) ^ 2 / 8 ≤ K * (Z + T) := le_trans (by nlinarith [abs_nonneg (Dz w : ℝ)]) hfinal
  nlinarith

/-! ## The classification -/

lemma wpow_one' (v : Word) : wpow v 1 = v := by simp [wpow]

/-- **Classification of `(w^a w')^b w''`, uniform in `(w, w', w'')`.** For positive words with
`w ≠ []`, every cycle member falls in one of four cases:
1. `b = 0`: the word is `w''`;
2. `b = 1`: the word is `w^a (w' w'')`, classified by `wpow_append_classification`;
3. `b ≥ 2` with `C(w^a w', w'') ≠ 0`: a **finite** set of pairs `(a, b)`;
4. `b ≥ 2` with `C(w^a w', w'') = 0`: a cycle word iff `w^a w'` is. The set of such `a` is
   empty, a single point, or (when `α = β = 0`) everything. -/
theorem nested_classification {w w' w'' : Word} (hw : w.Pos) (hw0 : w ≠ []) (hw1 : w'.Pos)
    (hw2 : w''.Pos) :
    (∀ a, wpow (wpow w a ++ w') 0 ++ w'' = w'') ∧
    (∀ a, wpow (wpow w a ++ w') 1 ++ w'' = wpow w a ++ (w' ++ w'')) ∧
    {p : ℕ × ℕ | 2 ≤ p.2 ∧ IsCycleWord (wpow (wpow w p.1 ++ w') p.2 ++ w'') ∧
      Cw (wpow w p.1 ++ w') w'' ≠ 0}.Finite ∧
    (∀ a b, 1 ≤ b → wpow w a ++ w' ≠ [] → Cw (wpow w a ++ w') w'' = 0 →
      (IsCycleWord (wpow (wpow w a ++ w') b ++ w'') ↔ IsCycleWord (wpow w a ++ w'))) ∧
    ((nα w w' w'' ≠ 0 ∨ nβ w w' w'' ≠ 0) → {a | Cw (wpow w a ++ w') w'' = 0}.Subsingleton) ∧
    (nα w w' w'' = 0 → nβ w w' w'' = 0 → ∀ a, Cw (wpow w a ++ w') w'' = 0) := by
  refine ⟨fun a => by simp [wpow], fun a => by rw [wpow_one', List.append_assoc], ?_, ?_,
    nested_zero_subsingleton hw hw0, nested_zero_all hw hw0⟩
  · -- finitely many a, and for each such a finitely many b
    set Aset := {a | ∃ b, 2 ≤ b ∧ IsCycleWord (wpow (wpow w a ++ w') b ++ w'') ∧
      Cw (wpow w a ++ w') w'' ≠ 0}
    have hA : Aset.Finite := nested_exceptional_finite hw hw0 hw1 hw2
    have hB : ∀ a ∈ Aset, {b | IsCycleWord (wpow (wpow w a ++ w') b ++ w'')}.Finite := by
      rintro a ⟨b, -, -, hC⟩
      have hvne : wpow w a ++ w' ≠ [] := by
        intro h0; apply hC; simp [Cw, wedge, h0, D]
      exact wpow_append_finite (wpow_append_pos hw hw1 a) hvne hw2 hC
    refine (hA.biUnion fun a ha => (hB a ha).image fun b => (a, b)).subset ?_
    rintro ⟨a, b⟩ ⟨hb, hcyc, hC⟩
    simp only [Set.mem_iUnion, Set.mem_image]
    exact ⟨a, ⟨b, hb, hcyc, hC⟩, b, hcyc, rfl⟩
  · intro a b hb hvne hC
    have hWne : wpow (wpow w a ++ w') b ++ w'' ≠ [] := by
      obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      rw [wpow_succ]; intro h
      simp only [List.append_eq_nil_iff] at h
      exact hvne (List.append_eq_nil_iff.mpr h.1.1)
    rw [wpow_append_const (wpow_append_pos hw hw1 a) hvne hw2 hC hWne]
    constructor
    · intro h; exact ⟨hvne, h⟩
    · intro h; exact h.2

end Syracuse.R1
