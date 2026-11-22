import Syracuse.Approaches.R1.WPow

/-!
# Towers: `((u₀^{a₁} u₁)^{a₂} u₂)^{a₃} ⋯`

A **tower** has a base word `u₀` and suffixes `u₁, …, u_k`. Its members are built by
`v ↦ v^b u_{j}` with exponents `b ≥ 1` (`towerSet`). The main theorem
(`tower_cycleStarts_finite`) is that **the cycle words of a tower start at only finitely many
integers**. A tower therefore contains cycle words of finitely many cycles, each possibly repeated
as powers. The proof is elementary: no linear forms in logarithms.

The invariant is **tameness** (`Tame`). A set of words is tame when it has
* bounded fixed points: `S(v) ≤ c · |D(v)|`;
* only finitely many members in each band `2^{|v|} ≍ 3^{len v}`.

The step `V ↦ {v^b u}` preserves tameness (`tame_step`). On a tame set, the w^a w′ ceiling
`D(v^b u) ∣ C(v, u)`, together with `|D(v^b u)| ≳ max(2^{|v|}, 3^{len v})^2` for `b ≥ 2`, leaves
only finitely many `v` with `C(v, u) ≠ 0` (`tame_cycles`). When `C(v, u) = 0`, the start point of
`v^b u` is that of `v` (`start_const`), so it is already counted one level down.
-/

namespace Syracuse.R1

open Syracuse Syracuse.CocycleCombine Filter

/-- `max(2^{|w|}, 3^{len w})`. -/
def Mx (w : Word) : ℤ := max (2 ^ w.sum) (3 ^ w.length)

/-- The ratio band `2^{|w|} ≤ R 3^{len w}` and `3^{len w} ≤ R 2^{|w|}`. -/
def InBand (R : ℤ) (w : Word) : Prop := (2 : ℤ) ^ w.sum ≤ R * 3 ^ w.length ∧ (3 : ℤ) ^ w.length ≤ R * 2 ^ w.sum

/-- Tame sets of words. -/
structure Tame (V : Set Word) : Prop where
  pos : ∀ v ∈ V, v.Pos ∧ v ≠ []
  fix : ∃ c : ℤ, ∀ v ∈ V, Sz v ≤ c * |Dz v|
  band : ∀ R : ℤ, {v | v ∈ V ∧ InBand R v}.Finite

/-- One tower step: `{v^b u : v ∈ V, b ≥ 1}`. -/
def step (V : Set Word) (u : Word) : Set Word := {w | ∃ v ∈ V, ∃ b, 1 ≤ b ∧ w = wpow v b ++ u}

/-- Appending a fixed word. -/
def appendSet (V : Set Word) (u : Word) : Set Word := {w | ∃ v ∈ V, w = v ++ u}

/-- The integers that start a cycle whose gap word lies in `V`. -/
def cycleStarts (V : Set Word) : Set ℤ := {x | ∃ w ∈ V, w ≠ [] ∧ Sz w = x * Dz w}

/-- The tower with base `u₀` and suffixes `us`. -/
def towerSet (u₀ : Word) (us : List Word) : Set Word := us.foldl step {u₀}

/-! ## Elementary size facts -/

lemma Sz_nonneg : ∀ w : Word, 0 ≤ Sz w
  | [] => by simp [Sz]
  | d :: w => by
    have := Sz_nonneg w
    simp only [Sz, S_cons] at this ⊢
    positivity

lemma Mx_pos (w : Word) : 1 ≤ Mx w := le_max_of_le_left (one_le_pow₀ (by norm_num))

lemma abs_Dz_le_Mx (w : Word) : |Dz w| ≤ Mx w := by
  unfold Mx; simp only [Dz, D]
  have h2 : (0 : ℤ) ≤ 2 ^ w.sum := by positivity
  have h3 : (0 : ℤ) ≤ 3 ^ w.length := by positivity
  rw [abs_le]; constructor
  · have := le_max_right ((2 : ℤ) ^ w.sum) (3 ^ w.length); linarith
  · have := le_max_left ((2 : ℤ) ^ w.sum) (3 ^ w.length); linarith

lemma out_band {w : Word} (h : ¬ InBand 3 w) : 2 * Mx w ≤ 3 * |Dz w| := by
  unfold InBand at h; unfold Mx; simp only [Dz, D]
  have p2 : (0 : ℤ) ≤ 2 ^ w.sum := by positivity
  have p3 : (0 : ℤ) ≤ 3 ^ w.length := by positivity
  rw [not_and_or, not_le, not_le] at h
  rcases h with h | h
  · have hm : max ((2 : ℤ) ^ w.sum) (3 ^ w.length) = 2 ^ w.sum := max_eq_left (by linarith)
    rw [hm, abs_of_pos (by linarith)]; linarith
  · have hm : max ((2 : ℤ) ^ w.sum) (3 ^ w.length) = 3 ^ w.length := max_eq_right (by linarith)
    rw [hm, abs_of_neg (by linarith)]; linarith

lemma Mx_wpow_append (v u : Word) (b : ℕ) : Mx v ^ b ≤ Mx (wpow v b ++ u) := by
  unfold Mx
  simp only [List.sum_append, List.length_append, wpow_sum, wpow_length]
  have key : ∀ x y : ℤ, 0 ≤ x → 0 ≤ y → max x y ^ b ≤ max (x ^ b) (y ^ b) := by
    intro x y hx hy
    rcases le_total x y with h | h
    · rw [max_eq_right h]; exact le_max_right _ _
    · rw [max_eq_left h]; exact le_max_left _ _
  refine (key _ _ (by positivity) (by positivity)).trans (max_le_max ?_ ?_)
  · rw [pow_add, ← pow_mul, mul_comm]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
  · rw [pow_add, ← pow_mul, mul_comm]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))

lemma inBand_of_Mx_le {w : Word} {L : ℤ} (h : Mx w ≤ L) : InBand L w := by
  unfold InBand
  have h2 : (2 : ℤ) ^ w.sum ≤ L := (le_max_left _ _).trans h
  have h3 : (3 : ℤ) ^ w.length ≤ L := (le_max_right _ _).trans h
  have hL : 0 ≤ L := le_trans (by positivity) h2
  exact ⟨h2.trans (le_mul_of_one_le_right hL (one_le_pow₀ (by norm_num))),
    h3.trans (le_mul_of_one_le_right hL (one_le_pow₀ (by norm_num)))⟩

/-- `D(v) · S(v^b) = S(v) · D(v^b)`. -/
lemma Dz_Sz_wpow (v : Word) (b : ℕ) : Dz v * Sz (wpow v b) = Sz v * Dz (wpow v b) := by
  simp only [Sz, Dz]; rw [S_wpow, D_wpow]; ring

/-- Bounded exponents near a noncritical ratio. -/
lemma finite_exponents {v : Word} (hv : v.Pos) (hne : v ≠ []) (K : ℤ) :
    {b : ℕ | (2 : ℤ) ^ (b * v.sum) ≤ K * 3 ^ (b * v.length) ∧
      (3 : ℤ) ^ (b * v.length) ≤ K * 2 ^ (b * v.sum)}.Finite := by
  have hs : 1 ≤ v.sum := by have := sum_ne_zero hv hne; omega
  have hne' : (2 : ℤ) ^ v.sum ≠ 3 ^ v.length := by
    intro h
    have h2 : (2 : ℤ) ∣ 3 ^ v.length := h ▸ dvd_pow_self 2 (by omega)
    have := Int.Prime.dvd_pow' (p := 2) (by norm_num) h2
    omega
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have hr : (1 : ℝ) < (3 : ℝ) ^ v.length / 2 ^ v.sum := by
      rw [one_lt_div (by positivity)]; exact_mod_cast hlt
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop (K : ℝ))
    refine (Set.finite_Iio N).subset fun b hb' => ?_
    obtain ⟨-, h2⟩ := hb'
    by_contra hb; simp only [Set.mem_Iio, not_lt] at hb
    have := hN b hb
    rw [div_pow, lt_div_iff₀ (by positivity)] at this
    have h2' : ((3 : ℝ) ^ v.length) ^ b ≤ K * ((2 : ℝ) ^ v.sum) ^ b := by
      rw [← pow_mul, ← pow_mul, mul_comm v.length, mul_comm v.sum]; exact_mod_cast h2
    linarith
  · have hr : (1 : ℝ) < (2 : ℝ) ^ v.sum / 3 ^ v.length := by
      rw [one_lt_div (by positivity)]; exact_mod_cast hgt
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop (K : ℝ))
    refine (Set.finite_Iio N).subset fun b hb' => ?_
    obtain ⟨h1, -⟩ := hb'
    by_contra hb; simp only [Set.mem_Iio, not_lt] at hb
    have := hN b hb
    rw [div_pow, lt_div_iff₀ (by positivity)] at this
    have h1' : ((2 : ℝ) ^ v.sum) ^ b ≤ K * ((3 : ℝ) ^ v.length) ^ b := by
      rw [← pow_mul, ← pow_mul, mul_comm v.length, mul_comm v.sum]; exact_mod_cast h1
    linarith

/-! ## Tameness -/

/-- A finite set of nonempty positive words is tame. -/
theorem tame_finite {V : Set Word} (hV : V.Finite) (hpos : ∀ v ∈ V, v.Pos ∧ v ≠ []) : Tame V := by
  refine ⟨hpos, ⟨∑ v ∈ hV.toFinset, Sz v, fun v hv => ?_⟩, fun R => hV.subset fun v h => h.1⟩
  have hD : 1 ≤ |Dz v| := Int.one_le_abs (Dz_ne_zero (hpos v hv).1 (hpos v hv).2)
  have hle : Sz v ≤ ∑ v ∈ hV.toFinset, Sz v :=
    Finset.single_le_sum (fun w _ => Sz_nonneg w) (hV.mem_toFinset.mpr hv)
  have h0 : 0 ≤ ∑ v ∈ hV.toFinset, Sz v := Finset.sum_nonneg fun w _ => Sz_nonneg w
  nlinarith

lemma step_band {V : Set Word} (hV : Tame V) {u : Word} (R : ℤ) :
    {w | w ∈ step V u ∧ InBand R w}.Finite := by
  set R₁ := |R| * 3 ^ u.length * 2 ^ u.sum + 1
  have hR₁ : 1 ≤ R₁ := by
    have : 0 ≤ |R| * 3 ^ u.length * 2 ^ u.sum := by positivity
    omega
  set Vb := {v | v ∈ V ∧ InBand R₁ v}
  have hVb : Vb.Finite := hV.band R₁
  have hB : ∀ v ∈ Vb, {b : ℕ | (2 : ℤ) ^ (b * v.sum) ≤ R₁ * 3 ^ (b * v.length) ∧
      (3 : ℤ) ^ (b * v.length) ≤ R₁ * 2 ^ (b * v.sum)}.Finite := fun v hv =>
    finite_exponents (hV.pos v hv.1).1 (hV.pos v hv.1).2 R₁
  refine (hVb.biUnion fun v hv => (hB v hv).image fun b => wpow v b ++ u).subset ?_
  rintro w ⟨⟨v, hv, b, hb, rfl⟩, h1, h2⟩
  simp only [List.sum_append, List.length_append, wpow_sum, wpow_length, pow_add] at h1 h2
  have hRabs : R ≤ |R| := le_abs_self R
  have hu2 : (1 : ℤ) ≤ 2 ^ u.sum := one_le_pow₀ (by norm_num)
  have hu3 : (1 : ℤ) ≤ 3 ^ u.length := one_le_pow₀ (by norm_num)
  have hx : (0 : ℤ) < 2 ^ (b * v.sum) := by positivity
  have hy : (0 : ℤ) < 3 ^ (b * v.length) := by positivity
  -- exponent-level band for v^b
  have hRu : |R| * 3 ^ u.length ≤ R₁ := by
    have : |R| * 3 ^ u.length ≤ |R| * 3 ^ u.length * 2 ^ u.sum :=
      le_mul_of_one_le_right (by positivity) hu2
    omega
  have hRu' : |R| * 2 ^ u.sum ≤ R₁ := by
    have : |R| * 2 ^ u.sum ≤ |R| * 3 ^ u.length * 2 ^ u.sum := by
      rw [mul_assoc, mul_comm (3 ^ u.length : ℤ), ← mul_assoc]
      exact le_mul_of_one_le_right (by positivity) hu3
    omega
  have e1 : (2 : ℤ) ^ (b * v.sum) ≤ R₁ * 3 ^ (b * v.length) := by
    calc (2 : ℤ) ^ (b * v.sum) ≤ 2 ^ (b * v.sum) * 2 ^ u.sum := le_mul_of_one_le_right hx.le hu2
      _ ≤ R * (3 ^ (b * v.length) * 3 ^ u.length) := h1
      _ ≤ |R| * (3 ^ (b * v.length) * 3 ^ u.length) :=
          mul_le_mul_of_nonneg_right (le_abs_self R) (by positivity)
      _ = (|R| * 3 ^ u.length) * 3 ^ (b * v.length) := by ring
      _ ≤ R₁ * 3 ^ (b * v.length) := mul_le_mul_of_nonneg_right hRu hy.le
  have e2 : (3 : ℤ) ^ (b * v.length) ≤ R₁ * 2 ^ (b * v.sum) := by
    calc (3 : ℤ) ^ (b * v.length) ≤ 3 ^ (b * v.length) * 3 ^ u.length := le_mul_of_one_le_right hy.le hu3
      _ ≤ R * (2 ^ (b * v.sum) * 2 ^ u.sum) := h2
      _ ≤ |R| * (2 ^ (b * v.sum) * 2 ^ u.sum) :=
          mul_le_mul_of_nonneg_right (le_abs_self R) (by positivity)
      _ = (|R| * 2 ^ u.sum) * 2 ^ (b * v.sum) := by ring
      _ ≤ R₁ * 2 ^ (b * v.sum) := mul_le_mul_of_nonneg_right hRu' hx.le
  -- v itself lies in the band R₁
  have hvb : InBand R₁ v := by
    unfold InBand
    constructor
    · by_contra hc; push Not at hc
      have : (R₁ * 3 ^ v.length) ^ b < (2 ^ v.sum) ^ b :=
        pow_lt_pow_left₀ hc (by positivity) (by omega)
      have hRb : R₁ ≤ R₁ ^ b := le_self_pow₀ hR₁ (by omega)
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm v.length, mul_comm v.sum] at this
      nlinarith
    · by_contra hc; push Not at hc
      have : (R₁ * 2 ^ v.sum) ^ b < (3 ^ v.length) ^ b :=
        pow_lt_pow_left₀ hc (by positivity) (by omega)
      have hRb : R₁ ≤ R₁ ^ b := le_self_pow₀ hR₁ (by omega)
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm v.length, mul_comm v.sum] at this
      nlinarith
  simp only [Set.mem_iUnion, Set.mem_image]
  exact ⟨v, ⟨hv, hvb⟩, b, ⟨e1, e2⟩, rfl⟩

/-- **The step preserves tameness.** -/
theorem tame_step {V : Set Word} (hV : Tame V) {u : Word} (hu : u.Pos) : Tame (step V u) := by
  obtain ⟨c, hc⟩ := hV.fix
  have hpos : ∀ w ∈ step V u, w.Pos ∧ w ≠ [] := by
    rintro w ⟨v, hv, b, hb, rfl⟩
    refine ⟨wpow_append_pos (hV.pos v hv).1 hu b, ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
    rw [wpow_succ]; intro h
    simp only [List.append_eq_nil_iff] at h
    exact (hV.pos v hv).2 h.1.1
  refine ⟨hpos, ?_, step_band hV⟩
  -- fixed points
  set E := {w | w ∈ step V u ∧ InBand 3 w}
  have hE : E.Finite := step_band hV 3
  set c₀ := ∑ w ∈ hE.toFinset, Sz w
  set K := 3 ^ u.length * |c| + Sz u
  refine ⟨c₀ + 3 * K, fun w hw => ?_⟩
  have hD1 : 1 ≤ |Dz w| := Int.one_le_abs (Dz_ne_zero (hpos w hw).1 (hpos w hw).2)
  have hc₀ : 0 ≤ c₀ := Finset.sum_nonneg fun w _ => Sz_nonneg w
  have hK : 0 ≤ K := by have := Sz_nonneg u; positivity
  by_cases hb3 : InBand 3 w
  · have hle : Sz w ≤ c₀ := Finset.single_le_sum (fun w _ => Sz_nonneg w) (hE.mem_toFinset.mpr ⟨hw, hb3⟩)
    nlinarith
  · obtain ⟨v, hv, b, hb, rfl⟩ := hw
    have hob := out_band hb3
    have hvne := (hV.pos v hv).2
    have hDv : Dz v ≠ 0 := Dz_ne_zero (hV.pos v hv).1 hvne
    -- S(v^b) ≤ |c| |D(v^b)|
    have hSb : Sz (wpow v b) ≤ |c| * |Dz (wpow v b)| := by
      have hrel := Dz_Sz_wpow v b
      have hcv := hc v hv
      have h1 : |Dz v| * Sz (wpow v b) = Sz v * |Dz (wpow v b)| := by
        have := congrArg abs hrel
        rwa [abs_mul, abs_mul, abs_of_nonneg (Sz_nonneg _), abs_of_nonneg (Sz_nonneg _)] at this
      have hDv1 : 0 < |Dz v| := abs_pos.mpr hDv
      have : |Dz v| * Sz (wpow v b) ≤ |Dz v| * (|c| * |Dz (wpow v b)|) := by
        rw [h1]
        have : Sz v ≤ |c| * |Dz v| := hcv.trans (by nlinarith [le_abs_self c, abs_nonneg (Dz v)])
        nlinarith [abs_nonneg (Dz (wpow v b))]
      exact le_of_mul_le_mul_left this hDv1
    have hMb : |Dz (wpow v b)| ≤ Mx (wpow v b ++ u) := by
      refine (abs_Dz_le_Mx _).trans ?_
      unfold Mx
      simp only [List.sum_append, List.length_append, pow_add]
      exact max_le_max (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num)))
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num)))
    have h2b : (2 : ℤ) ^ (wpow v b).sum ≤ Mx (wpow v b ++ u) := by
      unfold Mx; simp only [List.sum_append, pow_add]
      exact le_max_of_le_left (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num)))
    have hSw : Sz (wpow v b ++ u) ≤ K * Mx (wpow v b ++ u) := by
      have hSu := Sz_nonneg u
      have t1 : 3 ^ u.length * Sz (wpow v b) ≤ 3 ^ u.length * (|c| * Mx (wpow v b ++ u)) :=
        mul_le_mul_of_nonneg_left (hSb.trans (mul_le_mul_of_nonneg_left hMb (abs_nonneg c)))
          (by positivity)
      have t2 : 2 ^ (wpow v b).sum * Sz u ≤ Mx (wpow v b ++ u) * Sz u :=
        mul_le_mul_of_nonneg_right h2b hSu
      have hexp : Sz (wpow v b ++ u) = 3 ^ u.length * Sz (wpow v b) + 2 ^ (wpow v b).sum * Sz u := by
        simp only [Sz]; rw [S_append]
      rw [hexp]
      calc 3 ^ u.length * Sz (wpow v b) + 2 ^ (wpow v b).sum * Sz u
          ≤ 3 ^ u.length * (|c| * Mx (wpow v b ++ u)) + Mx (wpow v b ++ u) * Sz u := add_le_add t1 t2
        _ = K * Mx (wpow v b ++ u) := by simp only [K]; ring
    have h3 : K * (2 * Mx (wpow v b ++ u)) ≤ K * (3 * |Dz (wpow v b ++ u)|) :=
      mul_le_mul_of_nonneg_left hob hK
    have h4 : 0 ≤ K * |Dz (wpow v b ++ u)| := mul_nonneg hK (abs_nonneg _)
    have h5 : 0 ≤ c₀ * |Dz (wpow v b ++ u)| := mul_nonneg hc₀ (abs_nonneg _)
    nlinarith

/-- **Cycles at one step.** On a tame set, only finitely many `v` carry a cycle word `v^b u` with
`b ≥ 2` and `C(v, u) ≠ 0`. -/
theorem tame_cycles {V : Set Word} (hV : Tame V) {u : Word} (hu : u.Pos) :
    {v | v ∈ V ∧ ∃ b, 2 ≤ b ∧ IsCycleWord (wpow v b ++ u) ∧ Cw v u ≠ 0}.Finite := by
  obtain ⟨c, hc⟩ := hV.fix
  set E := {w | w ∈ step V u ∧ InBand 3 w}
  have hE : E.Finite := step_band hV 3
  set LE := ∑ w ∈ hE.toFinset, Mx w
  set K := Sz u + |Dz u| * |c|
  refine (hV.band (LE + 3 * K)).subset fun v ⟨hv, b, hb, hcyc, hC⟩ => ⟨hv, inBand_of_Mx_le ?_⟩
  have hK : 0 ≤ K := by have := Sz_nonneg u; positivity
  have hLE : 0 ≤ LE := Finset.sum_nonneg fun w _ => le_trans zero_le_one (Mx_pos w)
  have hMv := Mx_pos v
  have hpow := Mx_wpow_append v u b
  have hMvb : Mx v ≤ Mx v ^ b := le_self_pow₀ hMv (by omega)
  by_cases hb3 : InBand 3 (wpow v b ++ u)
  · have hmem : wpow v b ++ u ∈ E := ⟨⟨v, hv, b, by omega, rfl⟩, hb3⟩
    have : Mx (wpow v b ++ u) ≤ LE := Finset.single_le_sum (fun w _ => le_trans zero_le_one (Mx_pos w))
      (hE.mem_toFinset.mpr hmem)
    nlinarith
  · have hob := out_band hb3
    have hvp := (hV.pos v hv).1
    have hceil := wpow_append_ceiling hvp hu hC hcyc
    have hCle : |Cw v u| ≤ K * Mx v := by
      have h1 : |Cw v u| ≤ |Dz v| * Sz u + |Dz u| * Sz v := by
        simp only [Cw, wedge]
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (Sz_nonneg u), abs_of_nonneg (Sz_nonneg v)]
      have h2 : Sz v ≤ |c| * |Dz v| := (hc v hv).trans (by nlinarith [le_abs_self c, abs_nonneg (Dz v)])
      have h3 := abs_Dz_le_Mx v
      have := Sz_nonneg u
      nlinarith [abs_nonneg (Dz u), abs_nonneg c, abs_nonneg (Dz v)]
    have hsq : Mx v ^ 2 ≤ Mx v ^ b := pow_le_pow_right₀ hMv hb
    nlinarith

/-! ## Start points -/

/-- **Degenerate step.** If `C(v, u) = 0` and `v^b u` is a cycle word starting at `x`, then `v`
starts at `x` too. -/
theorem start_const {v u : Word} (hv : v.Pos) (hvne : v ≠ []) (hu : u.Pos) {b : ℕ} (hb : 1 ≤ b)
    (hC : Cw v u = 0) {x : ℤ} (hx : Sz (wpow v b ++ u) = x * Dz (wpow v b ++ u)) :
    Sz v = x * Dz v := by
  have hid := wpow_append_identity (2 : ℤ) 3 v u b
  rw [show wedge (2 : ℤ) 3 v u = 0 from hC, mul_zero, sub_eq_zero] at hid
  have hWne : wpow v b ++ u ≠ [] := by
    obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
    rw [wpow_succ]; intro h
    simp only [List.append_eq_nil_iff] at h
    exact hvne h.1.1
  have hDW := Dz_ne_zero (wpow_append_pos hv hu b) hWne
  have h' : Dz v * Sz (wpow v b ++ u) = Sz v * Dz (wpow v b ++ u) := hid
  rw [hx] at h'
  have : Dz (wpow v b ++ u) * (Sz v) = Dz (wpow v b ++ u) * (x * Dz v) := by linear_combination -h'
  exact mul_left_cancel₀ hDW this

/-- Start points of a step decompose: the `b = 1` part, a finite part, and the previous level. -/
theorem cycleStarts_step {V : Set Word} (hV : Tame V) {u : Word} (hu : u.Pos) :
    ∃ F : Set ℤ, F.Finite ∧
      cycleStarts (step V u) ⊆ cycleStarts (appendSet V u) ∪ F ∪ cycleStarts V := by
  set Vc := {v | v ∈ V ∧ ∃ b, 2 ≤ b ∧ IsCycleWord (wpow v b ++ u) ∧ Cw v u ≠ 0}
  have hVc : Vc.Finite := tame_cycles hV hu
  have hB : ∀ v ∈ Vc, {b | IsCycleWord (wpow v b ++ u)}.Finite := by
    rintro v ⟨hv, b, -, -, hC⟩
    exact wpow_append_finite (hV.pos v hv).1 (hV.pos v hv).2 hu hC
  set F := ⋃ v ∈ Vc, (fun b => Sz (wpow v b ++ u) / Dz (wpow v b ++ u)) '' {b | IsCycleWord (wpow v b ++ u)}
  refine ⟨F, hVc.biUnion fun v hv => (hB v hv).image _, ?_⟩
  rintro x ⟨w, ⟨v, hv, b, hb, rfl⟩, hne, hx⟩
  have hvp := (hV.pos v hv).1
  have hvne := (hV.pos v hv).2
  by_cases hb1 : b = 1
  · subst hb1
    left; left
    exact ⟨v ++ u, ⟨v, hv, rfl⟩, by simpa [wpow] using hne, by simpa [wpow] using hx⟩
  by_cases hC : Cw v u = 0
  · right
    exact ⟨v, hv, hvne, start_const hvp hvne hu hb hC hx⟩
  · left; right
    have hcyc : IsCycleWord (wpow v b ++ u) := ⟨hne, x, by rw [hx]; ring⟩
    simp only [F, Set.mem_iUnion, Set.mem_image]
    refine ⟨v, ⟨hv, b, by omega, hcyc, hC⟩, b, hcyc, ?_⟩
    rw [hx, Int.mul_ediv_cancel _ (Dz_ne_zero (wpow_append_pos hvp hu b) hne)]

/-! ## Towers -/

lemma towerSet_snoc (u₀ : Word) (us : List Word) (u : Word) :
    towerSet u₀ (us ++ [u]) = step (towerSet u₀ us) u := by
  simp [towerSet, List.foldl_append]

lemma appendSet_step (V : Set Word) (u' u : Word) : appendSet (step V u') u = step V (u' ++ u) := by
  ext w; constructor
  · rintro ⟨_, ⟨v, hv, b, hb, rfl⟩, rfl⟩; exact ⟨v, hv, b, hb, by simp⟩
  · rintro ⟨v, hv, b, hb, rfl⟩; exact ⟨wpow v b ++ u', ⟨v, hv, b, hb, rfl⟩, by simp⟩

/-- The tower statement, by induction on the depth. -/
theorem tower_main : ∀ (n : ℕ) (us : List Word), us.length = n → ∀ u₀ : Word, u₀.Pos → u₀ ≠ [] →
    (∀ u ∈ us, u.Pos) → Tame (towerSet u₀ us) ∧ (cycleStarts (towerSet u₀ us)).Finite := by
  intro n
  induction n with
  | zero =>
    intro us hl u₀ hu₀ hne _
    rw [List.length_eq_zero_iff.mp hl]
    refine ⟨tame_finite (by simp [towerSet]) (by simp [towerSet, hu₀, hne]), ?_⟩
    refine ((Set.finite_singleton (Sz u₀ / Dz u₀))).subset ?_
    rintro x ⟨w, hw, hwne, hx⟩
    simp only [towerSet, List.foldl_nil, Set.mem_singleton_iff] at hw
    subst hw
    simp only [Set.mem_singleton_iff]
    rw [hx, Int.mul_ediv_cancel _ (Dz_ne_zero hu₀ hwne)]
  | succ n ih =>
    intro us hl u₀ hu₀ hne hus
    obtain ⟨us', u, rfl⟩ : ∃ us' u, us = us' ++ [u] := by
      rcases List.eq_nil_or_concat us with h | ⟨L, b, h⟩
      · rw [h] at hl; simp at hl
      · exact ⟨L, b, by rw [h, List.concat_eq_append]⟩
    have hl' : us'.length = n := by simpa using hl
    have hus' : ∀ u ∈ us', u.Pos := fun x hx => hus x (by simp [hx])
    have hu : u.Pos := hus u (by simp)
    obtain ⟨hT, hfin⟩ := ih us' hl' u₀ hu₀ hne hus'
    rw [towerSet_snoc]
    refine ⟨tame_step hT hu, ?_⟩
    obtain ⟨F, hF, hsub⟩ := cycleStarts_step hT hu
    refine (((?_ : (cycleStarts (appendSet (towerSet u₀ us') u)).Finite).union hF).union hfin).subset hsub
    -- the b = 1 part is a tower of depth n with a merged last suffix
    rcases List.eq_nil_or_concat us' with h0 | ⟨L, u', h⟩
    · subst h0
      refine (Set.finite_singleton (Sz (u₀ ++ u) / Dz (u₀ ++ u))).subset ?_
      rintro x ⟨w, ⟨v, hv, rfl⟩, hwne, hx⟩
      simp only [towerSet, List.foldl_nil, Set.mem_singleton_iff] at hv
      rw [hv] at hwne hx
      simp only [Set.mem_singleton_iff]
      have hp : (u₀ ++ u).Pos := fun d hd => by
        rcases List.mem_append.mp hd with h | h
        · exact hu₀ d h
        · exact hu d h
      rw [hx, Int.mul_ediv_cancel _ (Dz_ne_zero hp hwne)]
    · rw [List.concat_eq_append] at h
      subst h
      rw [towerSet_snoc, appendSet_step, ← towerSet_snoc]
      have hu' : u'.Pos := hus' u' (by simp)
      refine (ih (L ++ [u' ++ u]) (by simpa using hl') u₀ hu₀ hne ?_).2
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hus' x (by simp [h])
      · simp only [List.mem_singleton] at h
        subst h
        intro d hd
        rcases List.mem_append.mp hd with h | h
        · exact hu' d h
        · exact hu d h

/-- **Tower theorem.** Every tower contains cycle words starting at only finitely many integers.
Equivalently, a tower meets only finitely many cycles. -/
theorem tower_cycleStarts_finite {u₀ : Word} (hu₀ : u₀.Pos) (hne : u₀ ≠ []) {us : List Word}
    (hus : ∀ u ∈ us, u.Pos) : (cycleStarts (towerSet u₀ us)).Finite :=
  (tower_main us.length us rfl u₀ hu₀ hne hus).2

end Syracuse.R1
