import Syracuse.Approaches.R1.Nested
import Syracuse.Approaches.R1.Skeleton
import Syracuse.Approaches.CycleLiterature

/-!
# Two independent exponents on the same side: `u^a x v^b y`

The class D of the pattern chart, with two blocks growing independently, is r = 2, and no
polynomial core exists. When both blocks lie on the **same side** of `log₂ 3` (both
`2^{|·|} > 3^{len ·}`, or both `<`), the family is nevertheless classified **elementarily and
unconditionally**:

* the `w^a w'` ceiling applied to `u` gives `D(W) ∣ C(u, x v^b y)`. Moreover
  `D(v) · C(u, x v^b y)` is a linear form `α 2^{b|v|} - β 3^{b len v}` (`twoExp_linear`), while on
  the same side `|D(W)| ≳ 2^{a|u|} · 2^{b|v|}` (resp. `3^{…}`). That bounds `a`
  independently of `b` (`twoExp_a_bounded`);
* for each of the finitely many `a`, the rotation `v^b (y u^a x)` is a `w^a w'` family in `b`
  (`isCycleWord_rotate`, `wpow_append_finite`).

**Classification (`twoExp_classification`).** For positive words with `u, v ≠ []` on the same side, the
cycle members are a **finite** set of pairs `(a, b)`, together with:
- pairs with `C(u, x v^b y) = 0`, a cycle iff `u` is (`twoExp_degenerate_u`);
- pairs with `C(v, y u^a x) = 0`, a cycle iff `v` is (`twoExp_degenerate_v`).

The straddling case (one block on each side, e.g. `1^a 2^b`) can reach the critical band, and needs
a linear-forms lower bound: `Straddle.lean` classifies every side configuration conditional on
Matveev.
-/

namespace Syracuse.R1

open Syracuse Syracuse.CocycleCombine Filter

/-! ## Cycle words are invariant under rotation -/

lemma isCycleWord_iff_follows {w : Word} (hw : w.Pos) :
    IsCycleWord w ↔ w ≠ [] ∧ ∃ x : ℤ, Follows (2 : ℤ) 3 w x x := by
  constructor
  · rintro ⟨hne, hdvd⟩
    obtain ⟨hcyc, hgap⟩ := CycleLiterature.isSyrCycle_of_dvd hw hne hdvd
    refine ⟨hne, Sz w / Dz w, ?_⟩
    have hf := follows_gapWord (Sz w / Dz w) w.length
    rw [hgap, hcyc.2.2] at hf
    exact hf
  · rintro ⟨hne, x, hx⟩
    exact ⟨hne, ⟨x, by have := hx.cycle_equation; simp only [Sz, Dz]; rw [← this]⟩⟩

theorem isCycleWord_rotate {u v : Word} (hu : u.Pos) (hv : v.Pos) :
    IsCycleWord (u ++ v) ↔ IsCycleWord (v ++ u) := by
  have hp : ∀ {p q : Word}, p.Pos → q.Pos → (p ++ q).Pos := fun hp hq d hd => by
    rcases List.mem_append.mp hd with h | h
    · exact hp d h
    · exact hq d h
  have key : ∀ {p q : Word}, p.Pos → q.Pos → IsCycleWord (p ++ q) → IsCycleWord (q ++ p) := by
    intro p q hp' hq' h
    rw [isCycleWord_iff_follows (hp hp' hq')] at h
    rw [isCycleWord_iff_follows (hp hq' hp')]
    obtain ⟨hne, x, hx⟩ := h
    obtain ⟨y, h1, h2⟩ := hx.of_append
    refine ⟨fun h0 => hne ?_, y, h2.append h1⟩
    simp only [List.append_eq_nil_iff] at h0 ⊢
    exact ⟨h0.2, h0.1⟩
  exact ⟨key hu hv, key hv hu⟩

/-! ## The linear form -/

/-- The family member. -/
def twoExpWord (u x v y : Word) (a b : ℕ) : Word := wpow u a ++ x ++ wpow v b ++ y

/-- Coefficients of the linear form. -/
def tα (u x v y : Word) : ℤ :=
  Dz u * 2 ^ x.sum * (3 ^ y.length * Sz v + Sz y * Dz v) - Dz v * Sz u * 2 ^ (x.sum + y.sum)
def tβ (u x v y : Word) : ℤ :=
  Dz u * 2 ^ x.sum * 3 ^ y.length * Sz v - Dz u * 3 ^ y.length * Sz x * Dz v -
    Dz v * Sz u * 3 ^ (x.length + y.length)

/-- `D(v) · C(u, x v^b y) = α 2^{b|v|} - β 3^{b len v}`. -/
theorem twoExp_linear (u x v y : Word) (b : ℕ) :
    Dz v * Cw u (x ++ wpow v b ++ y) = tα u x v y * 2 ^ (b * v.sum) - tβ u x v y * 3 ^ (b * v.length) := by
  have hr := wpow_rel (2 : ℤ) 3 v b
  simp only [Cw, wedge, tα, tβ, Dz, Sz, D] at hr ⊢
  simp only [S_append, List.sum_append, List.length_append, wpow_sum, wpow_length, pow_add] at hr ⊢
  linear_combination ((2 ^ u.sum - 3 ^ u.length) * 2 ^ x.sum * 3 ^ y.length) * hr

/-! ## Bounding `a` -/

lemma two_pow_ne_three_pow_real {m n : ℕ} (hm : 1 ≤ m) : (2 : ℝ) ^ m ≠ 3 ^ n := by
  exact_mod_cast two_pow_ne_three_pow_int (n := n) hm

/-- Same side of `log₂ 3`. -/
def SameSide (u v : Word) : Prop :=
  ((3 : ℤ) ^ u.length < 2 ^ u.sum ∧ (3 : ℤ) ^ v.length < 2 ^ v.sum) ∨
    ((2 : ℤ) ^ u.sum < 3 ^ u.length ∧ (2 : ℤ) ^ v.sum < 3 ^ v.length)

/-- Domination by a factor 3: `2 A Z ≤ 3 |A Z - B T|` when `3B ≤ A` and `T ≤ Z`. -/
lemma dom3 {A B Z T : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hZ : 0 ≤ Z) (_hT : 0 ≤ T) (hAB : 3 * B ≤ A)
    (hTZ : T ≤ Z) : 2 * (A * Z) ≤ 3 * |A * Z - B * T| := by
  have h1 : B * T ≤ B * Z := mul_le_mul_of_nonneg_left hTZ hB
  have h2 : 3 * (B * Z) ≤ A * Z := by nlinarith
  have h3 : 0 ≤ A * Z - B * T := by nlinarith
  rw [abs_of_nonneg h3]; nlinarith

/-- **`a` is bounded**: only finitely many `a` carry a cycle with `C(u, x v^b y) ≠ 0`. -/
theorem twoExp_a_bounded {u x v y : Word} (hu : u.Pos) (hune : u ≠ []) (hx : x.Pos) (hv : v.Pos)
    (hvne : v ≠ []) (hy : y.Pos) (hside : SameSide u v) :
    {a | ∃ b, IsCycleWord (twoExpWord u x v y a b) ∧ Cw u (x ++ wpow v b ++ y) ≠ 0}.Finite := by
  have hus : 1 ≤ u.sum := by have := sum_ne_zero hu hune; omega
  have hDv : (1 : ℝ) ≤ |(Dz v : ℝ)| := by exact_mod_cast Int.one_le_abs (Dz_ne_zero hv hvne)
  -- abbreviations as plain numbers
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = |(tα u x v y : ℝ)| + |(tβ u x v y : ℝ)| := ⟨_, rfl⟩
  obtain ⟨Pu, hPu⟩ : ∃ P : ℝ, P = 2 ^ u.sum := ⟨_, rfl⟩
  obtain ⟨Qu, hQu⟩ : ∃ Q : ℝ, Q = 3 ^ u.length := ⟨_, rfl⟩
  obtain ⟨cx, hcx⟩ : ∃ c : ℝ, c = 2 ^ x.sum * 2 ^ y.sum := ⟨_, rfl⟩
  obtain ⟨dx, hdx⟩ : ∃ d : ℝ, d = 3 ^ x.length * 3 ^ y.length := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hcx1 : 1 ≤ cx := by rw [hcx]; exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hdx1 : 1 ≤ dx := by rw [hdx]; exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hPu2 : 2 ≤ Pu := by
    rw [hPu]; calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ u.sum := pow_le_pow_right₀ (by norm_num) hus
  have hQu1 : 1 ≤ Qu := by rw [hQu]; exact one_le_pow₀ (by norm_num)
  have hev : ∀ᶠ a : ℕ in atTop,
      ((3 : ℤ) ^ v.length < 2 ^ v.sum ∧ 3 * (dx * Qu ^ a) ≤ cx * Pu ^ a ∧ 3 * K < Pu ^ a) ∨
        ((2 : ℤ) ^ v.sum < 3 ^ v.length ∧ 3 * (cx * Pu ^ a) ≤ dx * Qu ^ a ∧ 3 * K < Qu ^ a) := by
    rcases hside with ⟨h1, hv1⟩ | ⟨h1, hv1⟩
    · have h1' : Qu < Pu := by rw [hPu, hQu]; exact_mod_cast h1
      have hr : (1 : ℝ) < Pu / Qu := by rw [one_lt_div (by linarith)]; exact h1'
      have ht := tendsto_pow_atTop_atTop_of_one_lt hr
      have ht2 := tendsto_pow_atTop_atTop_of_one_lt (by linarith : (1 : ℝ) < Pu)
      filter_upwards [ht.eventually_ge_atTop (3 * dx / cx), ht2.eventually_gt_atTop (3 * K)] with a ha hb
      left; refine ⟨hv1, ?_, hb⟩
      have hQa : 0 < Qu ^ a := by positivity
      rw [div_pow, le_div_iff₀ hQa, div_mul_eq_mul_div, div_le_iff₀ (by linarith)] at ha
      linarith
    · have h1' : Pu < Qu := by rw [hPu, hQu]; exact_mod_cast h1
      have hr : (1 : ℝ) < Qu / Pu := by rw [one_lt_div (by linarith)]; exact h1'
      have ht := tendsto_pow_atTop_atTop_of_one_lt hr
      have ht2 := tendsto_pow_atTop_atTop_of_one_lt (by linarith : (1 : ℝ) < Qu)
      filter_upwards [ht.eventually_ge_atTop (3 * cx / dx), ht2.eventually_gt_atTop (3 * K)] with a ha hb
      right; refine ⟨hv1, ?_, hb⟩
      have hPa : 0 < Pu ^ a := by positivity
      rw [div_pow, le_div_iff₀ hPa, div_mul_eq_mul_div, div_le_iff₀ (by linarith)] at ha
      linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine (Set.finite_Iio N).subset fun a ⟨b, hcyc, hC⟩ => ?_
  by_contra hlt
  simp only [Set.mem_Iio, not_lt] at hlt
  have hd := hN a hlt
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ((2 : ℝ) ^ v.sum) ^ b := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ((3 : ℝ) ^ v.length) ^ b := ⟨_, rfl⟩
  have hZ1 : 1 ≤ Z := by rw [hZ]; exact one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hT1 : 1 ≤ T := by rw [hT]; exact one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hw' : (x ++ wpow v b ++ y).Pos := by
    intro d hd'; simp only [List.mem_append] at hd'
    rcases hd' with (h | h) | h
    · exact hx d h
    · exact wpow_pos hv b d h
    · exact hy d h
  have hW : twoExpWord u x v y a b = wpow u a ++ (x ++ wpow v b ++ y) := by
    simp [twoExpWord, List.append_assoc]
  rw [hW] at hcyc
  set C : ℝ := ((Cw u (x ++ wpow v b ++ y) : ℤ) : ℝ) with hCdef
  have hceil : |((Dz (wpow u a ++ (x ++ wpow v b ++ y)) : ℤ) : ℝ)| ≤ |C| := by
    rw [hCdef]; exact_mod_cast wpow_append_ceiling hu hw' hC hcyc
  have hup : |(Dz v : ℝ)| * |C| ≤ K * (Z + T) := by
    rw [← abs_mul]
    have hlin := twoExp_linear u x v y b
    have e : ((Dz v : ℝ) * C) = (tα u x v y : ℝ) * Z - (tβ u x v y : ℝ) * T := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hlin
      push_cast at this
      rw [hCdef, this, hZ, hT, pow_mul', pow_mul']
    rw [e]
    calc |(tα u x v y : ℝ) * Z - (tβ u x v y : ℝ) * T|
        ≤ |(tα u x v y : ℝ)| * Z + |(tβ u x v y : ℝ)| * T := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Z), abs_of_pos (by linarith : (0 : ℝ) < T)]
      _ ≤ K * (Z + T) := by
          rw [hK]; have := abs_nonneg (tα u x v y : ℝ); have := abs_nonneg (tβ u x v y : ℝ); nlinarith
  have hDW : ((Dz (wpow u a ++ (x ++ wpow v b ++ y)) : ℤ) : ℝ) = (cx * Pu ^ a) * Z - (dx * Qu ^ a) * T := by
    simp only [Dz, D, List.sum_append, List.length_append, wpow_sum, wpow_length]
    push_cast
    rw [hcx, hdx, hPu, hQu, hZ, hT]
    ring
  rw [hDW] at hceil
  have hDv0 : (0 : ℝ) < |(Dz v : ℝ)| := by linarith
  rcases hd with ⟨hv', h1, h2⟩ | ⟨hv', h1, h2⟩
  · have hTZ : T ≤ Z := by
      rw [hZ, hT]; exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hv'.le) b
    have hA : 0 ≤ cx * Pu ^ a := by positivity
    have hB : 0 ≤ dx * Qu ^ a := by positivity
    have hZ0 : 0 < Z := by linarith
    have hlow := dom3 hA hB (by linarith) (by linarith) h1 hTZ
    have hC1 : |(Dz v : ℝ)| * (2 * ((cx * Pu ^ a) * Z)) ≤ |(Dz v : ℝ)| * (3 * |C|) :=
      mul_le_mul_of_nonneg_left (hlow.trans (by linarith)) hDv0.le
    have hKZ : K * (Z + T) ≤ 2 * K * Z := by
      have := mul_le_mul_of_nonneg_left hTZ hK0; linarith
    have h4 : 2 * ((cx * Pu ^ a) * Z) ≤ |(Dz v : ℝ)| * (2 * ((cx * Pu ^ a) * Z)) :=
      le_mul_of_one_le_left (by positivity) hDv
    have h5 : 2 * ((cx * Pu ^ a) * Z) ≤ 6 * K * Z := by linarith
    have h6 : cx * Pu ^ a ≤ 3 * K := by
      have : (cx * Pu ^ a) * Z ≤ (3 * K) * Z := by linarith
      exact le_of_mul_le_mul_right this hZ0
    have h7 : Pu ^ a ≤ cx * Pu ^ a := le_mul_of_one_le_left (by positivity) hcx1
    linarith
  · have hZT : Z ≤ T := by
      rw [hZ, hT]; exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hv'.le) b
    have hA : 0 ≤ cx * Pu ^ a := by positivity
    have hB : 0 ≤ dx * Qu ^ a := by positivity
    have hT0 : 0 < T := by linarith
    have hlow := dom3 hB hA (by linarith) (by linarith) h1 hZT
    rw [abs_sub_comm] at hlow
    have hC1 : |(Dz v : ℝ)| * (2 * ((dx * Qu ^ a) * T)) ≤ |(Dz v : ℝ)| * (3 * |C|) :=
      mul_le_mul_of_nonneg_left (hlow.trans (by linarith)) hDv0.le
    have hKT : K * (Z + T) ≤ 2 * K * T := by
      have := mul_le_mul_of_nonneg_left hZT hK0; linarith
    have h4 : 2 * ((dx * Qu ^ a) * T) ≤ |(Dz v : ℝ)| * (2 * ((dx * Qu ^ a) * T)) :=
      le_mul_of_one_le_left (by positivity) hDv
    have h5 : 2 * ((dx * Qu ^ a) * T) ≤ 6 * K * T := by linarith
    have h6 : dx * Qu ^ a ≤ 3 * K := by
      have : (dx * Qu ^ a) * T ≤ (3 * K) * T := by linarith
      exact le_of_mul_le_mul_right this hT0
    have h7 : Qu ^ a ≤ dx * Qu ^ a := le_mul_of_one_le_left (by positivity) hdx1
    linarith

/-! ## Degenerate loci and the classification -/

lemma pos_append {p q : Word} (hp : p.Pos) (hq : q.Pos) : (p ++ q).Pos := fun d hd => by
  rcases List.mem_append.mp hd with h | h
  · exact hp d h
  · exact hq d h

/-- If `C(u, x v^b y) = 0`, then `W` is a cycle word iff `u` is. -/
theorem twoExp_degenerate_u {u x v y : Word} (hu : u.Pos) (hune : u ≠ []) (hx : x.Pos) (hv : v.Pos)
    (hy : y.Pos) {a b : ℕ} (hC : Cw u (x ++ wpow v b ++ y) = 0) (hne : twoExpWord u x v y a b ≠ []) :
    IsCycleWord (twoExpWord u x v y a b) ↔ Dz u ∣ Sz u := by
  have hW : twoExpWord u x v y a b = wpow u a ++ (x ++ wpow v b ++ y) := by
    simp [twoExpWord, List.append_assoc]
  rw [hW] at hne ⊢
  exact wpow_append_const hu hune (pos_append (pos_append hx (wpow_pos hv b)) hy) hC hne

/-- If `C(v, y u^a x) = 0`, then `W` is a cycle word iff `v` is. -/
theorem twoExp_degenerate_v {u x v y : Word} (hu : u.Pos) (hx : x.Pos) (hv : v.Pos) (hvne : v ≠ [])
    (hy : y.Pos) {a b : ℕ} (hC : Cw v (y ++ wpow u a ++ x) = 0) (hne : twoExpWord u x v y a b ≠ []) :
    IsCycleWord (twoExpWord u x v y a b) ↔ Dz v ∣ Sz v := by
  have hrot : IsCycleWord (twoExpWord u x v y a b) ↔ IsCycleWord (wpow v b ++ (y ++ wpow u a ++ x)) := by
    have e1 : twoExpWord u x v y a b = (wpow u a ++ x) ++ (wpow v b ++ y) := by
      simp [twoExpWord, List.append_assoc]
    have e2 : wpow v b ++ (y ++ wpow u a ++ x) = (wpow v b ++ y) ++ (wpow u a ++ x) := by
      simp [List.append_assoc]
    rw [e1, e2]
    exact isCycleWord_rotate (pos_append (wpow_pos hu a) hx) (pos_append (wpow_pos hv b) hy)
  have hne' : wpow v b ++ (y ++ wpow u a ++ x) ≠ [] := by
    intro h; apply hne
    simp only [twoExpWord, List.append_eq_nil_iff] at h ⊢
    exact ⟨⟨⟨h.2.1.2, h.2.2⟩, h.1⟩, h.2.1.1⟩
  rw [hrot]
  exact wpow_append_const hv hvne (pos_append (pos_append hy (wpow_pos hu a)) hx) hC hne'

/-- **Classification of `u^a x v^b y` on the same side.** The cycle pairs with both cores nonzero
form a finite set. The remaining pairs are the two degenerate loci, where `W` is a cycle iff `u`
(resp. `v`) is. -/
theorem twoExp_classification {u x v y : Word} (hu : u.Pos) (hune : u ≠ []) (hx : x.Pos) (hv : v.Pos)
    (hvne : v ≠ []) (hy : y.Pos) (hside : SameSide u v) :
    {p : ℕ × ℕ | IsCycleWord (twoExpWord u x v y p.1 p.2) ∧ Cw u (x ++ wpow v p.2 ++ y) ≠ 0 ∧
      Cw v (y ++ wpow u p.1 ++ x) ≠ 0}.Finite := by
  have hA := twoExp_a_bounded hu hune hx hv hvne hy hside
  have hB : ∀ a ∈ {a | ∃ b, IsCycleWord (twoExpWord u x v y a b) ∧ Cw u (x ++ wpow v b ++ y) ≠ 0},
      {b | IsCycleWord (twoExpWord u x v y a b) ∧ Cw v (y ++ wpow u a ++ x) ≠ 0}.Finite := by
    intro a _
    by_cases hC : Cw v (y ++ wpow u a ++ x) = 0
    · exact Set.finite_empty.subset fun b hb => absurd hC hb.2
    refine (wpow_append_finite hv hvne (pos_append (pos_append hy (wpow_pos hu a)) hx) hC).subset ?_
    rintro b ⟨hcyc, -⟩
    have e1 : twoExpWord u x v y a b = (wpow u a ++ x) ++ (wpow v b ++ y) := by
      simp [twoExpWord, List.append_assoc]
    have e2 : wpow v b ++ (y ++ wpow u a ++ x) = (wpow v b ++ y) ++ (wpow u a ++ x) := by
      simp [List.append_assoc]
    show IsCycleWord (wpow v b ++ (y ++ wpow u a ++ x))
    rw [e2, ← isCycleWord_rotate (pos_append (wpow_pos hu a) hx) (pos_append (wpow_pos hv b) hy), ← e1]
    exact hcyc
  refine (hA.biUnion fun a ha => (hB a ha).image fun b => (a, b)).subset ?_
  rintro ⟨a, b⟩ ⟨hcyc, hC1, hC2⟩
  simp only [Set.mem_iUnion, Set.mem_image]
  exact ⟨a, ⟨b, hcyc, hC1⟩, b, ⟨hcyc, hC2⟩, rfl⟩

end Syracuse.R1
