import Syracuse.Approaches.R1.TwoExp

/-!
# Two independent exponents on any sides: `u^a x v^b y`, conditional on Matveev

`TwoExp.lean` classifies `u^a x v^b y` unconditionally when `u` and `v` lie on the **same side**
of `log₂ 3`. The **straddling** case (class X of the pattern chart: one block above, one below)
can reach the critical band, so it needs the place at infinity. This file supplies it, and the
argument is in fact **side-free**.

* **Two ceilings, one per block.** Rotating `W` so that `u`, resp. `v`, comes first, the `w^a w'`
  ceiling and the linear form `twoExp_linear` give
  `|D(W)| ≤ 2 K_u G_v^b` and `|D(W)| ≤ 2 K_v G_u^a`, with `G = max(2^{|·|}, 3^{len ·})`
  (`twoExp_ceiling_real`). Each ceiling is exponential in **one** exponent only.
* **Matveev.** A lower bound `max(2^E, 3^O) ≤ A (B+1)^κ |2^E - 3^O|` (`PolyLB`) follows from
  Matveev's two-logarithm theorem (`polyLB_of_matveev`, from `CycleGcd.MatveevTwoThree`).
* **The product beats it.** `max(2^E,3^O)² ≥ 2^E 3^O ≥ 2^{a+b} G_u^a G_v^b`, because the smaller of
  `2^{|u|}` and `3^{len u}` is at least 2. Multiplying the two ceilings therefore leaves
  `2^{a+b} ≤ const · (a+b+1)^{2κ}`, so `a + b` is bounded (`twoExp_finite_of_polyLB`).

**Classification (`twoExp_classification_of_matveev`).** Assuming `MatveevTwoThree c` (the
published theorem for `c = c₀`), for all positive `u, v ≠ []`, `x`, `y`, the cycle pairs `(a, b)`
off the two degenerate loci form a finite set. On the loci, `W` is a cycle iff `u` (resp. `v`) is
(`twoExp_degenerate_u`, `twoExp_degenerate_v`).

*Beyond two blocks.* With `k` independent blocks, the `k` rotation ceilings still suffice when
`min(A, B) < 1`, where `A = Σ_{above} (1 - len·log 3 / (|u| log 2))` and
`B = Σ_{below} (1 - |u| log 2 / (len·log 3))`. This is the tropical budget of
`approaches/places-elimination/SCHEME.md` §2.4: derived there, not formalized. For `k = 2`
straddling it always holds. (An earlier version of this note said two blocks is the limit; it
compared equal weights only, and that was wrong.)
-/

namespace Syracuse.R1

open Syracuse Syracuse.CocycleCombine Filter

/-! ## A polynomial lower bound for `|2^E - 3^O|`, from Matveev -/

/-- A polynomial lower bound for `|2^E - 3^O|` relative to `max(2^E, 3^O)`. -/
def PolyLB (A : ℝ) (κ : ℕ) : Prop :=
  ∀ E O : ℕ, (2 : ℝ) ^ E ≠ 3 ^ O →
    max ((2 : ℝ) ^ E) (3 ^ O) ≤ A * (((max E O : ℕ) : ℝ) + 1) ^ κ * |(2 : ℝ) ^ E - 3 ^ O|

/-- `e^t (s - t) ≤ e^s - e^t`. -/
lemma exp_gap (s t : ℝ) : Real.exp t * (s - t) ≤ Real.exp s - Real.exp t := by
  have h1 := Real.add_one_le_exp (s - t)
  have he : Real.exp s = Real.exp t * Real.exp (s - t) := by rw [← Real.exp_add]; congr 1; ring
  have ht := Real.exp_pos t
  rw [he]; nlinarith

/-- The one-sided core of `polyLB_of_matveev`. -/
lemma max_exp_le {s t P q : ℝ} (hst : t ≤ s) (hP : 1 ≤ P) (hq : 1 ≤ P * q) (hqΛ : q < s - t) :
    Real.exp s ≤ 2 * P * (Real.exp s - Real.exp t) := by
  have hg := exp_gap s t
  have ht := Real.exp_pos t
  have hD : 0 ≤ Real.exp s - Real.exp t := sub_nonneg.2 (Real.exp_le_exp.2 hst)
  have h1 : 1 ≤ P * (s - t) := le_trans hq (mul_le_mul_of_nonneg_left hqΛ.le (by linarith))
  have h2 : Real.exp t ≤ P * (Real.exp s - Real.exp t) := by
    calc Real.exp t ≤ Real.exp t * (P * (s - t)) := le_mul_of_one_le_right ht.le h1
      _ = P * (Real.exp t * (s - t)) := by ring
      _ ≤ P * (Real.exp s - Real.exp t) := mul_le_mul_of_nonneg_left hg (by linarith)
  have h3 : Real.exp s - Real.exp t ≤ P * (Real.exp s - Real.exp t) := le_mul_of_one_le_left hD hP
  linarith

/-- **Matveev gives a polynomial lower bound**: `MatveevTwoThree c` with `c ≥ 0` implies
`PolyLB (2 e^c) ⌈c⌉`. -/
theorem polyLB_of_matveev {c : ℝ} (hc : 0 ≤ c) (hM : CycleGcd.MatveevTwoThree c) :
    PolyLB (2 * Real.exp c) ⌈c⌉₊ := by
  intro E O hne
  set B : ℕ := max E O with hBdef
  have h2 : (2 : ℝ) ^ E = Real.exp (E * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have h3 : (3 : ℝ) ^ O = Real.exp (O * Real.log 3) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hΛ : (E : ℝ) * Real.log 2 - O * Real.log 3 ≠ 0 := by
    intro h; apply hne; rw [h2, h3]; congr 1; linarith
  have hlt := hM E O hΛ
  rw [← hBdef] at hlt
  have hB1 : (1 : ℝ) ≤ B := by
    have : 1 ≤ B := by
      have hEB : E ≤ B := le_max_left E O
      have hOB : O ≤ B := le_max_right E O
      by_contra h0
      have hE : E = 0 := by omega
      have hO : O = 0 := by omega
      exact hne (by simp [hE, hO])
    exact_mod_cast this
  set q := Real.exp (-c * (1 + Real.log B)) with hq
  set P := Real.exp c * ((B : ℝ) + 1) ^ ⌈c⌉₊ with hP
  have hq' : q < |(E : ℝ) * Real.log 2 - O * Real.log 3| :=
    (Real.lt_log_iff_exp_lt (abs_pos.2 hΛ)).1 hlt
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hpow1 : (1 : ℝ) ≤ ((B : ℝ) + 1) ^ ⌈c⌉₊ := one_le_pow₀ (by linarith)
  have hP1 : 1 ≤ P := by
    rw [hP]; exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp hc) hpow1
  have hPq : 1 ≤ P * q := by
    have hk : c * Real.log B ≤ (⌈c⌉₊ : ℝ) * Real.log ((B : ℝ) + 1) := by
      have hc' : c ≤ (⌈c⌉₊ : ℝ) := Nat.le_ceil c
      have hl : Real.log B ≤ Real.log ((B : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
      calc c * Real.log B ≤ (⌈c⌉₊ : ℝ) * Real.log B := mul_le_mul_of_nonneg_right hc' hlogB
        _ ≤ (⌈c⌉₊ : ℝ) * Real.log ((B : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _)
    have hexp : Real.exp (c * Real.log B) ≤ ((B : ℝ) + 1) ^ ⌈c⌉₊ := by
      have : ((B : ℝ) + 1) ^ ⌈c⌉₊ = Real.exp ((⌈c⌉₊ : ℝ) * Real.log ((B : ℝ) + 1)) := by
        rw [← Real.log_pow, Real.exp_log (by positivity)]
      rw [this]; exact Real.exp_le_exp.2 hk
    have e : P * q = ((B : ℝ) + 1) ^ ⌈c⌉₊ * Real.exp (-(c * Real.log B)) := by
      rw [hP, hq]
      have : Real.exp c * Real.exp (-c * (1 + Real.log B)) = Real.exp (-(c * Real.log B)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc Real.exp c * ((B : ℝ) + 1) ^ ⌈c⌉₊ * Real.exp (-c * (1 + Real.log B))
          = ((B : ℝ) + 1) ^ ⌈c⌉₊ * (Real.exp c * Real.exp (-c * (1 + Real.log B))) := by ring
        _ = _ := by rw [this]
    rw [e]
    calc (1 : ℝ) = Real.exp (c * Real.log B) * Real.exp (-(c * Real.log B)) := by
          rw [← Real.exp_add]; simp
      _ ≤ ((B : ℝ) + 1) ^ ⌈c⌉₊ * Real.exp (-(c * Real.log B)) :=
          mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
  have goal_form : 2 * Real.exp c * ((B : ℝ) + 1) ^ ⌈c⌉₊ = 2 * P := by rw [hP]; ring
  rw [goal_form, h2, h3]
  rcases le_total (O * Real.log 3) (E * Real.log 2) with hle | hle
  · rw [max_eq_left (Real.exp_le_exp.2 hle),
      abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 hle))]
    rw [abs_of_nonneg (sub_nonneg.2 hle)] at hq'
    exact max_exp_le hle hP1 hPq hq'
  · rw [max_eq_right (Real.exp_le_exp.2 hle), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 hle))]
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)] at hq'
    exact max_exp_le hle hP1 hPq hq'

/-! ## The two ceilings -/

/-- `K(u,x,v,y) = |α| + |β|`, the size of the linear form of `twoExp_linear`. -/
noncomputable def tK (u x v y : Word) : ℝ := |(tα u x v y : ℝ)| + |(tβ u x v y : ℝ)|

/-- `G(v) = max(2^{|v|}, 3^{len v})`. -/
noncomputable def tG (v : Word) : ℝ := max ((2 : ℝ) ^ v.sum) (3 ^ v.length)

lemma Dz_real (w : Word) : ((Dz w : ℤ) : ℝ) = 2 ^ w.sum - 3 ^ w.length := by
  simp [Dz, D]

/-- **The `u`-ceiling, uniform in `a`:** on a cycle with `C(u, x v^b y) ≠ 0`,
`|D(W)| ≤ 2 K G(v)^b`. -/
theorem twoExp_ceiling_real {u x v y : Word} (hu : u.Pos) (hx : x.Pos) (hv : v.Pos)
    (hvne : v ≠ []) (hy : y.Pos) {a b : ℕ} (hcyc : IsCycleWord (twoExpWord u x v y a b))
    (hC : Cw u (x ++ wpow v b ++ y) ≠ 0) :
    |((Dz (twoExpWord u x v y a b) : ℤ) : ℝ)| ≤ 2 * tK u x v y * tG v ^ b := by
  have hDv : (1 : ℝ) ≤ |(Dz v : ℝ)| := by exact_mod_cast Int.one_le_abs (Dz_ne_zero hv hvne)
  have hw' : (x ++ wpow v b ++ y).Pos := pos_append (pos_append hx (wpow_pos hv b)) hy
  have hW : twoExpWord u x v y a b = wpow u a ++ (x ++ wpow v b ++ y) := by
    simp [twoExpWord, List.append_assoc]
  rw [hW] at hcyc ⊢
  set C : ℝ := ((Cw u (x ++ wpow v b ++ y) : ℤ) : ℝ) with hCdef
  have hceil : |((Dz (wpow u a ++ (x ++ wpow v b ++ y)) : ℤ) : ℝ)| ≤ |C| := by
    rw [hCdef]; exact_mod_cast wpow_append_ceiling hu hw' hC hcyc
  set Z : ℝ := ((2 : ℝ) ^ v.sum) ^ b with hZ
  set T : ℝ := ((3 : ℝ) ^ v.length) ^ b with hT
  have hZG : Z ≤ tG v ^ b := pow_le_pow_left₀ (by positivity) (le_max_left _ _) b
  have hTG : T ≤ tG v ^ b := pow_le_pow_left₀ (by positivity) (le_max_right _ _) b
  have hK0 : 0 ≤ tK u x v y := by unfold tK; positivity
  have hup : |(Dz v : ℝ)| * |C| ≤ tK u x v y * (Z + T) := by
    rw [← abs_mul]
    have hlin := twoExp_linear u x v y b
    have e : ((Dz v : ℝ) * C) = (tα u x v y : ℝ) * Z - (tβ u x v y : ℝ) * T := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hlin
      push_cast at this
      rw [hCdef, this, hZ, hT, pow_mul', pow_mul']
    rw [e]
    have hZ0 : 0 ≤ Z := by positivity
    have hT0 : 0 ≤ T := by positivity
    calc |(tα u x v y : ℝ) * Z - (tβ u x v y : ℝ) * T|
        ≤ |(tα u x v y : ℝ)| * Z + |(tβ u x v y : ℝ)| * T := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hZ0, abs_of_nonneg hT0]
      _ ≤ tK u x v y * (Z + T) := by
          unfold tK
          have := abs_nonneg (tα u x v y : ℝ); have := abs_nonneg (tβ u x v y : ℝ); nlinarith
  have hC1 : |C| ≤ |(Dz v : ℝ)| * |C| := le_mul_of_one_le_left (abs_nonneg _) hDv
  have hZT : tK u x v y * (Z + T) ≤ 2 * tK u x v y * tG v ^ b := by
    have := mul_le_mul_of_nonneg_left (add_le_add hZG hTG) hK0; linarith
  linarith

/-- The rotation `v^b y u^a x` of `W` is the same family with the roles exchanged. -/
lemma twoExp_swap_cycle {u x v y : Word} (hu : u.Pos) (hx : x.Pos) (hv : v.Pos) (hy : y.Pos)
    (a b : ℕ) :
    IsCycleWord (twoExpWord u x v y a b) ↔ IsCycleWord (twoExpWord v y u x b a) := by
  have e1 : twoExpWord u x v y a b = (wpow u a ++ x) ++ (wpow v b ++ y) := by
    simp [twoExpWord, List.append_assoc]
  have e2 : twoExpWord v y u x b a = (wpow v b ++ y) ++ (wpow u a ++ x) := by
    simp [twoExpWord, List.append_assoc]
  rw [e1, e2]
  exact isCycleWord_rotate (pos_append (wpow_pos hu a) hx) (pos_append (wpow_pos hv b) hy)

lemma twoExp_swap_Dz (u x v y : Word) (a b : ℕ) :
    Dz (twoExpWord v y u x b a) = Dz (twoExpWord u x v y a b) := by
  simp only [Dz, D, twoExpWord, List.sum_append, List.length_append]
  ring

/-! ## Exponential beats polynomial -/

lemma eventually_poly_lt_two_pow (K : ℝ) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, K * ((n : ℝ) + 1) ^ k < 2 ^ n := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).const_mul
    (|K| * 2 ^ k)
  rw [mul_zero] at ht
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 1] with n hn hn1
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hle : ((n : ℝ) + 1) ^ k ≤ 2 ^ k * (n : ℝ) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) k
  have h1 : K * ((n : ℝ) + 1) ^ k ≤ |K| * (2 ^ k * (n : ℝ) ^ k) :=
    (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hle (abs_nonneg K))
  have h2 : |K| * (2 ^ k * (n : ℝ) ^ k) < 2 ^ n := by
    have : |K| * 2 ^ k * ((n : ℝ) ^ k / 2 ^ n) < 1 := hn
    rw [mul_div_assoc', div_lt_one h2n] at this
    linarith
  linarith

/-! ## Finiteness and the classification -/

/-- `2^{|u|} 3^{len u} ≥ 2 G(u)` for a nonempty positive word. -/
lemma two_mul_tG_le {u : Word} (hu : u.Pos) (hune : u ≠ []) :
    2 * tG u ≤ (2 : ℝ) ^ u.sum * 3 ^ u.length := by
  have hs : 1 ≤ u.sum := by have := sum_ne_zero hu hune; omega
  have hl : 1 ≤ u.length := List.length_pos_iff.2 hune
  have hP : (2 : ℝ) ≤ 2 ^ u.sum := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ u.sum := pow_le_pow_right₀ (by norm_num) hs
  have hQ : (2 : ℝ) ≤ 3 ^ u.length := by
    calc (2 : ℝ) ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ u.length := pow_le_pow_right₀ (by norm_num) hl
  unfold tG
  rcases le_total ((2 : ℝ) ^ u.sum) (3 ^ u.length) with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

lemma exp_count_le (a b p q r s : ℕ) :
    a * p + q + b * r + s + 1 ≤ (p + r + q + s + 1) * (a + b + 1) := by
  nlinarith [Nat.zero_le (a * r), Nat.zero_le (a * q), Nat.zero_le (a * s),
    Nat.zero_le (b * p), Nat.zero_le (b * q), Nat.zero_le (b * s)]

/-- The constant of the explicit bound: `4 A² K_u K_v (L+1)^{2κ}`, `L = |u|+|v|+|x|+|y|`. -/
noncomputable def tKc (A : ℝ) (κ : ℕ) (u x v y : Word) : ℝ :=
  4 * A ^ 2 * tK u x v y * tK v y u x * (((u.sum + v.sum + x.sum + y.sum : ℕ) : ℝ) + 1) ^ (2 * κ)

/-- **The explicit bound, on any sides.** Under `PolyLB A κ`, every cycle pair `(a, b)` of
`u^a x v^b y` with both cores nonzero satisfies `2^{a+b} ≤ tKc · (a+b+1)^{2κ}`. -/
theorem twoExp_pow_le_of_polyLB {A : ℝ} {κ : ℕ} (hLB : PolyLB A κ) {u x v y : Word}
    (hu : u.Pos) (hune : u ≠ []) (hx : x.Pos) (hv : v.Pos) (hvne : v ≠ []) (hy : y.Pos) {a b : ℕ}
    (hcyc : IsCycleWord (twoExpWord u x v y a b)) (hCu : Cw u (x ++ wpow v b ++ y) ≠ 0)
    (hCv : Cw v (y ++ wpow u a ++ x) ≠ 0) :
    (2 : ℝ) ^ (a + b) ≤ tKc A κ u x v y * (((a + b : ℕ) : ℝ) + 1) ^ (2 * κ) := by
  set L : ℕ := u.sum + v.sum + x.sum + y.sum with hL
  set Kc : ℝ := 4 * A ^ 2 * tK u x v y * tK v y u x * ((L : ℝ) + 1) ^ (2 * κ) with hKc
  have hKcdef : tKc A κ u x v y = Kc := by rw [hKc, hL]; rfl
  rw [hKcdef]
  -- the word and its exponents
  set W := twoExpWord u x v y a b with hWdef
  have hWpos : W.Pos := pos_append (pos_append (pos_append (wpow_pos hu a) hx) (wpow_pos hv b)) hy
  have hE : W.sum = a * u.sum + x.sum + b * v.sum + y.sum := by
    simp only [hWdef, twoExpWord, List.sum_append, wpow_sum]
  have hO : W.length = a * u.length + x.length + b * v.length + y.length := by
    simp only [hWdef, twoExpWord, List.length_append, wpow_length]
  have hOE : W.length ≤ W.sum := CycleLiterature.length_le_sum hWpos
  have hE1 : 1 ≤ W.sum := by
    have := sum_ne_zero hWpos hcyc.1; omega
  -- the two ceilings
  have hcu := twoExp_ceiling_real hu hx hv hvne hy hcyc hCu
  have hcyc' := (twoExp_swap_cycle hu hx hv hy a b).1 hcyc
  have hcv := twoExp_ceiling_real hv hy hu hune hx hcyc' hCv
  rw [twoExp_swap_Dz] at hcv
  rw [← hWdef] at hcu hcv
  -- the lower bound
  have hne : (2 : ℝ) ^ W.sum ≠ 3 ^ W.length := two_pow_ne_three_pow_real hE1
  have hlb := hLB W.sum W.length hne
  rw [max_eq_left hOE, ← Dz_real] at hlb
  set M : ℝ := max ((2 : ℝ) ^ W.sum) (3 ^ W.length) with hM
  set d : ℝ := |((Dz W : ℤ) : ℝ)| with hd
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hd0 : 0 ≤ d := abs_nonneg _
  have hGu : 0 < tG u := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hGv : 0 < tG v := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hKu : 0 ≤ tK u x v y := by unfold tK; positivity
  have hKv : 0 ≤ tK v y u x := by unfold tK; positivity
  -- `M² ≥ 2^E 3^O ≥ 2^{a+b} G_u^a G_v^b`
  have hMsq : (2 : ℝ) ^ W.sum * 3 ^ W.length ≤ M ^ 2 := by
    rw [sq]; exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (by positivity) hM0.le
  have hprod : (2 : ℝ) ^ (a + b) * (tG u ^ a * tG v ^ b) ≤ (2 : ℝ) ^ W.sum * 3 ^ W.length := by
    have hx1 : (1 : ℝ) ≤ 2 ^ x.sum * 3 ^ x.length :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
    have hy1 : (1 : ℝ) ≤ 2 ^ y.sum * 3 ^ y.length :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
    have hua := pow_le_pow_left₀ (by positivity) (two_mul_tG_le hu hune) a
    have hvb := pow_le_pow_left₀ (by positivity) (two_mul_tG_le hv hvne) b
    have e : (2 : ℝ) ^ W.sum * 3 ^ W.length =
        ((2 : ℝ) ^ u.sum * 3 ^ u.length) ^ a * ((2 : ℝ) ^ v.sum * 3 ^ v.length) ^ b *
          ((2 ^ x.sum * 3 ^ x.length) * (2 ^ y.sum * 3 ^ y.length)) := by
      rw [hE, hO]; ring
    rw [e]
    calc (2 : ℝ) ^ (a + b) * (tG u ^ a * tG v ^ b) = (2 * tG u) ^ a * (2 * tG v) ^ b := by ring
      _ ≤ ((2 : ℝ) ^ u.sum * 3 ^ u.length) ^ a * ((2 : ℝ) ^ v.sum * 3 ^ v.length) ^ b :=
          mul_le_mul hua hvb (by positivity) (by positivity)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hx1 hy1)
  -- the ceilings multiplied
  have hdsq : d ^ 2 ≤ (2 * tK u x v y * tG v ^ b) * (2 * tK v y u x * tG u ^ a) := by
    rw [sq]; exact mul_le_mul hcu hcv hd0 (by positivity)
  -- `M² ≤ A² (B+1)^{2κ} d²`
  have hMA : M ^ 2 ≤ (A * ((W.sum : ℝ) + 1) ^ κ * d) ^ 2 := pow_le_pow_left₀ hM0.le hlb 2
  -- `B + 1 ≤ (L + 1)(a + b + 1)`
  have hBn : ((W.sum : ℝ) + 1) ≤ ((L : ℝ) + 1) * (((a + b : ℕ) : ℝ) + 1) := by
    have : W.sum + 1 ≤ (L + 1) * (a + b + 1) := by
      rw [hE, hL]; exact exp_count_le a b _ _ _ _
    exact_mod_cast this
  have hBpow : ((W.sum : ℝ) + 1) ^ (2 * κ) ≤
      ((L : ℝ) + 1) ^ (2 * κ) * (((a + b : ℕ) : ℝ) + 1) ^ (2 * κ) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hBn _
  -- assemble: `2^{a+b} G ≤ Kc (a+b+1)^{2κ} G` with `G = G_u^a G_v^b > 0`
  set G : ℝ := tG u ^ a * tG v ^ b with hG
  have hG0 : 0 < G := by positivity
  have hchain : (2 : ℝ) ^ (a + b) * G ≤ (Kc * (((a + b : ℕ) : ℝ) + 1) ^ (2 * κ)) * G := by
    have e1 : (A * ((W.sum : ℝ) + 1) ^ κ * d) ^ 2 = A ^ 2 * ((W.sum : ℝ) + 1) ^ (2 * κ) * d ^ 2 := by
      ring
    have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
    have step1 : (2 : ℝ) ^ (a + b) * G ≤ A ^ 2 * ((W.sum : ℝ) + 1) ^ (2 * κ) * d ^ 2 := by
      rw [← e1]; exact hprod.trans (hMsq.trans hMA)
    have step2 : A ^ 2 * ((W.sum : ℝ) + 1) ^ (2 * κ) * d ^ 2 ≤
        A ^ 2 * (((L : ℝ) + 1) ^ (2 * κ) * (((a + b : ℕ) : ℝ) + 1) ^ (2 * κ)) *
          ((2 * tK u x v y * tG v ^ b) * (2 * tK v y u x * tG u ^ a)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hBpow hA2) hdsq (sq_nonneg _) (by positivity)
    have e2 : A ^ 2 * (((L : ℝ) + 1) ^ (2 * κ) * (((a + b : ℕ) : ℝ) + 1) ^ (2 * κ)) *
          ((2 * tK u x v y * tG v ^ b) * (2 * tK v y u x * tG u ^ a)) =
        (Kc * (((a + b : ℕ) : ℝ) + 1) ^ (2 * κ)) * G := by
      rw [hKc, hG]; ring
    linarith
  exact le_of_mul_le_mul_right hchain hG0

/-- **Finiteness from a polynomial lower bound, on any sides.** -/
theorem twoExp_finite_of_polyLB {A : ℝ} {κ : ℕ} (hLB : PolyLB A κ) {u x v y : Word}
    (hu : u.Pos) (hune : u ≠ []) (hx : x.Pos) (hv : v.Pos) (hvne : v ≠ []) (hy : y.Pos) :
    {p : ℕ × ℕ | IsCycleWord (twoExpWord u x v y p.1 p.2) ∧ Cw u (x ++ wpow v p.2 ++ y) ≠ 0 ∧
      Cw v (y ++ wpow u p.1 ++ x) ≠ 0}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_poly_lt_two_pow (tKc A κ u x v y) (2 * κ))
  refine ((Set.finite_Iio N).prod (Set.finite_Iio N)).subset ?_
  rintro ⟨a, b⟩ ⟨hcyc, hCu, hCv⟩
  suffices hab : a + b < N by
    simp only [Set.mem_prod, Set.mem_Iio]; omega
  by_contra hge
  rw [not_lt] at hge
  have := twoExp_pow_le_of_polyLB hLB hu hune hx hv hvne hy hcyc hCu hCv
  linarith [hN (a + b) hge]

/-- **Classification of every two-exponent family, conditional on Matveev.** Under
`MatveevTwoThree c` with `c ≥ 0` (the published theorem for `c = c₀`), the cycle pairs of
`u^a x v^b y` with both cores nonzero form a finite set, on **either** side of `log₂ 3`. -/
theorem twoExp_classification_of_matveev {c : ℝ} (hc : 0 ≤ c) (hM : CycleGcd.MatveevTwoThree c)
    {u x v y : Word} (hu : u.Pos) (hune : u ≠ []) (hx : x.Pos) (hv : v.Pos) (hvne : v ≠ [])
    (hy : y.Pos) :
    {p : ℕ × ℕ | IsCycleWord (twoExpWord u x v y p.1 p.2) ∧ Cw u (x ++ wpow v p.2 ++ y) ≠ 0 ∧
      Cw v (y ++ wpow u p.1 ++ x) ≠ 0}.Finite :=
  twoExp_finite_of_polyLB (polyLB_of_matveev hc hM) hu hune hx hv hvne hy

/-- The published constant: `twoExp_classification_of_matveev` at `c = c₀`. -/
theorem twoExp_classification_of_matveev₀ (hM : CycleGcd.MatveevTwoThree CycleGcd.c₀)
    {u x v y : Word} (hu : u.Pos) (hune : u ≠ []) (hx : x.Pos) (hv : v.Pos) (hvne : v ≠ [])
    (hy : y.Pos) :
    {p : ℕ × ℕ | IsCycleWord (twoExpWord u x v y p.1 p.2) ∧ Cw u (x ++ wpow v p.2 ++ y) ≠ 0 ∧
      Cw v (y ++ wpow u p.1 ++ x) ≠ 0}.Finite :=
  twoExp_classification_of_matveev CycleGcd.c₀_pos.le hM hu hune hx hv hvne hy

/-! ## The degenerate loci, and the complete statement -/

/-- `α 2^{b|w|} = β 3^{b len w}` has at most one solution `b` unless `α = β = 0`. -/
lemma exp_eq_subsingleton {α β : ℤ} {w : Word} (hw : w.Pos) (hw0 : w ≠ [])
    (hαβ : α ≠ 0 ∨ β ≠ 0) : {b : ℕ | α * 2 ^ (b * w.sum) = β * 3 ^ (b * w.length)}.Subsingleton := by
  have hs : 1 ≤ w.sum := by have := sum_ne_zero hw hw0; omega
  intro a e1 b e2
  simp only [Set.mem_ofPred_eq] at e1 e2
  have hα : α ≠ 0 := by
    rcases hαβ with h | h
    · exact h
    · intro h0; rw [h0, zero_mul] at e1
      exact h (by
        rcases mul_eq_zero.mp e1.symm with h' | h'
        · exact h'
        · exact absurd h' (by positivity))
  by_contra hne
  have main : ∀ x y : ℕ, x < y → α * 2 ^ (x * w.sum) = β * 3 ^ (x * w.length) →
      α * 2 ^ (y * w.sum) = β * 3 ^ (y * w.length) → False := by
    intro x y hxy ex ey
    obtain ⟨k, rfl⟩ : ∃ k, y = x + (k + 1) := ⟨y - x - 1, by omega⟩
    have : α * 2 ^ (x * w.sum) * 2 ^ ((k + 1) * w.sum) =
        α * 2 ^ (x * w.sum) * 3 ^ ((k + 1) * w.length) := by
      have ey' : α * (2 ^ (x * w.sum) * 2 ^ ((k + 1) * w.sum)) =
          β * (3 ^ (x * w.length) * 3 ^ ((k + 1) * w.length)) := by
        rw [← pow_add, ← pow_add, ← add_mul, ← add_mul]; exact ey
      linear_combination ey' - 3 ^ ((k + 1) * w.length) * ex
    have hnz : α * 2 ^ (x * w.sum) ≠ 0 := mul_ne_zero hα (by positivity)
    exact two_pow_ne_three_pow_int (m := (k + 1) * w.sum) (n := (k + 1) * w.length)
      (Nat.one_le_iff_ne_zero.mpr (by positivity)) (mul_left_cancel₀ hnz this)
  rcases lt_or_gt_of_ne hne with h | h
  · exact main a b h e1 e2
  · exact main b a h e2 e1

/-- **The `u`-locus** `{b | C(u, x v^b y) = 0}` is at most one point, or everything. -/
theorem twoExp_zero_u (u x : Word) {v : Word} (y : Word) (hv : v.Pos) (hvne : v ≠ []) :
    {b | Cw u (x ++ wpow v b ++ y) = 0}.Subsingleton ∨ ∀ b, Cw u (x ++ wpow v b ++ y) = 0 := by
  by_cases h : tα u x v y = 0 ∧ tβ u x v y = 0
  · right; intro b
    have hl := twoExp_linear u x v y b
    rw [h.1, h.2, zero_mul, zero_mul, sub_zero] at hl
    exact (mul_eq_zero.mp hl).resolve_left (Dz_ne_zero hv hvne)
  · left
    refine (exp_eq_subsingleton hv hvne (not_and_or.1 h)).anti fun b hb => ?_
    simp only [Set.mem_ofPred_eq] at hb ⊢
    have hl := twoExp_linear u x v y b
    rw [hb, mul_zero] at hl
    linarith

/-- **The complete statement, conditional on Matveev.** For positive `u, v ≠ []`, `x`, `y`, there
is a finite set `F` of exponent pairs such that a nonempty `W = u^a x v^b y` is a cycle word iff
`(a, b) ∈ F`, or `C(u, x v^b y) = 0` and `u` is a cycle word, or `C(v, y u^a x) = 0` and `v` is. Each
locus is a single value of one exponent, or everything (`twoExp_zero_u`). -/
theorem twoExp_cycles_of_matveev {c : ℝ} (hc : 0 ≤ c) (hM : CycleGcd.MatveevTwoThree c)
    {u x v y : Word} (hu : u.Pos) (hune : u ≠ []) (hx : x.Pos) (hv : v.Pos) (hvne : v ≠ [])
    (hy : y.Pos) :
    ∃ F : Set (ℕ × ℕ), F.Finite ∧ ∀ a b, twoExpWord u x v y a b ≠ [] →
      (IsCycleWord (twoExpWord u x v y a b) ↔ (a, b) ∈ F ∨
        (Cw u (x ++ wpow v b ++ y) = 0 ∧ Dz u ∣ Sz u) ∨
        (Cw v (y ++ wpow u a ++ x) = 0 ∧ Dz v ∣ Sz v)) := by
  refine ⟨_, twoExp_classification_of_matveev hc hM hu hune hx hv hvne hy, fun a b hne => ?_⟩
  constructor
  · intro hcyc
    by_cases hCu : Cw u (x ++ wpow v b ++ y) = 0
    · exact Or.inr (Or.inl ⟨hCu, (twoExp_degenerate_u hu hune hx hv hy hCu hne).1 hcyc⟩)
    by_cases hCv : Cw v (y ++ wpow u a ++ x) = 0
    · exact Or.inr (Or.inr ⟨hCv, (twoExp_degenerate_v hu hx hv hvne hy hCv hne).1 hcyc⟩)
    exact Or.inl ⟨hcyc, hCu, hCv⟩
  · rintro (h | ⟨hCu, hd⟩ | ⟨hCv, hd⟩)
    · exact h.1
    · exact (twoExp_degenerate_u hu hune hx hv hy hCu hne).2 hd
    · exact (twoExp_degenerate_v hu hx hv hvne hy hCv hne).2 hd

end Syracuse.R1
