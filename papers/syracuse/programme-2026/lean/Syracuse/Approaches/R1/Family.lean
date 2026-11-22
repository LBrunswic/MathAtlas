import Syracuse.Approaches.CocycleCombine
import Syracuse.Approaches.R1.LPoly

/-!
# r = 1 families and their closed form

An r = 1 family is a list of segments: fixed words, and growing blocks `β^{m a + c}` whose
slopes `|β| / len β` all equal `p / q`. Writing `|β| = k p`, `len β = k q`, put `s = (3^q)^a` and
`t = (2^p / 3^q)^a`. For every member `W(a)` this file proves the closed form (`Family.closed`):

* `μ · S(W(a)) = s^N · γ(t)`, where `γ` has degree `≤ N` (`Family.natDegree_G`);
* `D(W(a)) = s^N · δ(t)`, where `δ = xc · t^N - yc` (`Family.D_closed`).

Here `N = Σ k m`, `μ = ∏ (2^{|β|} - 3^{len β}) ≠ 0`, and `xc` and `yc` are positive. The data are
computed by `Seg.data` and `Data.comb` over `ℚ`-coefficient lists, so `decide` can evaluate them.
-/

namespace Syracuse.R1

open Syracuse Syracuse.CocycleCombine Polynomial

/-- A segment of a family word. -/
inductive Seg
  | fixed (w : Word)
  | grow (β : Word) (k m c : ℕ)
  deriving DecidableEq, Repr

/-- A one-parameter family: the common slope `p / q` and the segments. -/
structure Family where
  p : ℕ
  q : ℕ
  segs : List Seg
  deriving DecidableEq, Repr

/-- The word a segment contributes at parameter `a`. -/
def Seg.word : Seg → ℕ → Word
  | .fixed w, _ => w
  | .grow β _ m c, a => wpow β (m * a + c)

/-- The word of a segment list. -/
def segsWord : List Seg → ℕ → Word
  | [], _ => []
  | s :: l, a => s.word a ++ segsWord l a

/-- The family member `W(a)`. -/
def Family.word (F : Family) (a : ℕ) : Word := segsWord F.segs a

/-- Positivity of a word, as a `Bool`. -/
def posB (w : Word) : Bool := w.all fun d => decide (1 ≤ d)

lemma posB_iff (w : Word) : posB w = true ↔ w.Pos := by
  simp [posB, Word.Pos]

/-- Validity of a segment for slope `p / q`. -/
def Seg.okB (p q : ℕ) : Seg → Bool
  | .fixed w => posB w
  | .grow β k _ _ => posB β && β.sum == k * p && β.length == k * q && decide (1 ≤ k)

/-- Validity of a family: `p, q ≥ 1` and every segment valid. -/
def Family.okB (F : Family) : Bool :=
  decide (1 ≤ F.p) && decide (1 ≤ F.q) && F.segs.all (Seg.okB F.p F.q)

/-! ## Data and closed form -/

/-- Closed-form data of a segment list: the degree `d`, `G` (with `μ S = s^d G(t)`), the
coefficients `xc`, `yc` (with `2^{sum} = xc (s t)^d` and `3^{len} = yc s^d`), and the
denominator `μ`. -/
structure Data where
  d : ℕ
  G : List ℚ
  xc : ℚ
  yc : ℚ
  μ : ℚ

/-- The data of one segment. -/
def Seg.data : Seg → Data
  | .fixed w => ⟨0, [(Sz w : ℚ)], (2 : ℚ) ^ w.sum, (3 : ℚ) ^ w.length, 1⟩
  | .grow β k m c =>
    ⟨k * m, lsmul (Sz β : ℚ) (lsub (lmono (k * m) ((2 : ℚ) ^ (β.sum * c))) [(3 : ℚ) ^ (β.length * c)]),
      (2 : ℚ) ^ (β.sum * c), (3 : ℚ) ^ (β.length * c), (2 : ℚ) ^ β.sum - 3 ^ β.length⟩

/-- Data of a concatenation (`S(uv) = 3^{len v} S(u) + 2^{sum u} S(v)`). -/
def Data.comb (u v : Data) : Data :=
  ⟨u.d + v.d, ladd (lsmul (v.μ * v.yc) u.G) (lsmul u.μ (lmul (lmono u.d u.xc) v.G)),
    u.xc * v.xc, u.yc * v.yc, u.μ * v.μ⟩

/-- Data of the empty word. -/
def Data.unit : Data := ⟨0, [], 1, 1, 1⟩

/-- Data of a segment list. -/
def segsData : List Seg → Data
  | [] => Data.unit
  | s :: l => (s.data).comb (segsData l)

/-- Data of a family. -/
def Family.data (F : Family) : Data := segsData F.segs

/-- The binomial `δ = xc t^N - yc`. -/
def Data.delta (D : Data) : List ℚ := lsub (lmono D.d D.xc) [D.yc]

/-- The two run coordinates. -/
noncomputable def sv (q a : ℕ) : ℚ := ((3 : ℚ) ^ q) ^ a
noncomputable def tv (p q a : ℕ) : ℚ := ((2 : ℚ) ^ p / 3 ^ q) ^ a

lemma sv_mul_tv (p q a : ℕ) : sv q a * tv p q a = ((2 : ℚ) ^ p) ^ a := by
  rw [sv, tv, ← mul_pow]; congr 1; field_simp

/-- The closed form of `D`, `S` for data `D` and word `w` at parameter `a`. -/
def Holds (p q a : ℕ) (D : Data) (w : Word) : Prop :=
  D.μ * (Sz w : ℚ) = sv q a ^ D.d * (toPoly D.G).eval (tv p q a) ∧
    (2 : ℚ) ^ w.sum = sv q a ^ D.d * (D.xc * tv p q a ^ D.d) ∧
    (3 : ℚ) ^ w.length = sv q a ^ D.d * D.yc

lemma holds_unit (p q a : ℕ) : Holds p q a Data.unit [] := by
  simp [Holds, Data.unit]

lemma holds_comb {p q a : ℕ} {u v : Data} {w₁ w₂ : Word} (h₁ : Holds p q a u w₁)
    (h₂ : Holds p q a v w₂) : Holds p q a (u.comb v) (w₁ ++ w₂) := by
  obtain ⟨hS₁, hX₁, hY₁⟩ := h₁
  obtain ⟨hS₂, hX₂, hY₂⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · have hS := S_append (2 : ℤ) 3 w₁ w₂
    simp only [Data.comb, toPoly_ladd, toPoly_lsmul, toPoly_lmul, toPoly_lmono, eval_add,
      eval_mul, eval_C, eval_pow, eval_X]
    rw [Sz, hS]; push_cast
    rw [show u.μ * v.μ * ((3 : ℚ) ^ w₂.length * (S 2 3 w₁ : ℤ) + (2 : ℚ) ^ w₁.sum * (S 2 3 w₂ : ℤ)) =
      v.μ * (3 : ℚ) ^ w₂.length * (u.μ * (Sz w₁ : ℚ)) + u.μ * (2 : ℚ) ^ w₁.sum * (v.μ * (Sz w₂ : ℚ))
      by simp only [Sz]; ring, hS₁, hS₂, hX₁, hY₂]
    ring
  · simp only [Data.comb, List.sum_append, pow_add, hX₁, hX₂]; ring
  · simp only [Data.comb, List.length_append, pow_add, hY₁, hY₂]; ring

/-- Validity as a `Prop` for one segment. -/
lemma Seg.okB_grow {p q : ℕ} {β : Word} {k m c : ℕ} (h : (Seg.grow β k m c).okB p q = true) :
    β.Pos ∧ β.sum = k * p ∧ β.length = k * q ∧ 1 ≤ k := by
  simp only [Seg.okB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨(posB_iff β).mp h.1.1.1, h.1.1.2, h.1.2, h.2⟩

lemma holds_seg {p q a : ℕ} (s : Seg) (hs : s.okB p q = true) :
    Holds p q a s.data (s.word a) := by
  cases s with
  | fixed w => simp [Holds, Seg.data, Seg.word]
  | grow β k m c =>
    obtain ⟨-, hsum, hlen, -⟩ := Seg.okB_grow hs
    have hst := sv_mul_tv p q a
    have hX : (2 : ℚ) ^ (wpow β (m * a + c)).sum =
        sv q a ^ (k * m) * ((2 : ℚ) ^ (β.sum * c) * tv p q a ^ (k * m)) := by
      rw [wpow_sum, show sv q a ^ (k * m) * ((2 : ℚ) ^ (β.sum * c) * tv p q a ^ (k * m)) =
        (2 : ℚ) ^ (β.sum * c) * (sv q a * tv p q a) ^ (k * m) by ring, hst, ← pow_mul, ← pow_mul,
        ← pow_add, hsum]
      congr 1; ring
    have hY : (3 : ℚ) ^ (wpow β (m * a + c)).length =
        sv q a ^ (k * m) * (3 : ℚ) ^ (β.length * c) := by
      rw [wpow_length, sv, ← pow_mul, ← pow_mul, mul_comm, ← pow_add, hlen]
      congr 1; ring
    refine ⟨?_, hX, hY⟩
    have hSD : Dz β * Sz (wpow β (m * a + c)) = Sz β * Dz (wpow β (m * a + c)) := by
      simp only [Sz, Dz]
      rw [S_wpow, D_wpow]; ring
    have hSDq : ((2 : ℚ) ^ β.sum - 3 ^ β.length) * (Sz (wpow β (m * a + c)) : ℚ) =
        (Sz β : ℚ) * ((2 : ℚ) ^ (wpow β (m * a + c)).sum - 3 ^ (wpow β (m * a + c)).length) := by
      have := congrArg (fun z : ℤ => (z : ℚ)) hSD
      simp only [Dz, D, Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_ofNat] at this
      exact this
    simp only [Seg.data, Seg.word]
    rw [hSDq, hX, hY]
    simp only [toPoly_lsmul, toPoly_lsub, toPoly_lmono, toPoly_cons, toPoly_nil, eval_mul, eval_C,
      eval_sub, eval_pow, eval_X, mul_zero, add_zero]
    ring

lemma holds_segs {p q a : ℕ} : ∀ l : List Seg, (l.all (Seg.okB p q)) = true →
    Holds p q a (segsData l) (segsWord l a)
  | [], _ => holds_unit p q a
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact holds_comb (holds_seg s h.1) (holds_segs l h.2)

/-- **Closed form of a valid family.** -/
theorem Family.closed {F : Family} (hF : F.okB = true) (a : ℕ) :
    Holds F.p F.q a F.data (F.word a) := by
  simp only [Family.okB, Bool.and_eq_true] at hF
  exact holds_segs F.segs hF.2

/-- `D(W(a)) = s^N δ(t)`. -/
theorem Family.D_closed {F : Family} (hF : F.okB = true) (a : ℕ) :
    (Dz (F.word a) : ℚ) = sv F.q a ^ F.data.d * (toPoly F.data.delta).eval (tv F.p F.q a) := by
  obtain ⟨-, hX, hY⟩ := F.closed hF a
  simp only [Dz, D, Int.cast_sub, Int.cast_pow, Int.cast_ofNat, Data.delta, toPoly_lsub,
    toPoly_lmono, toPoly_cons, toPoly_nil, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
    mul_zero, add_zero]
  rw [hX, hY]; ring

/-! ## Degree and positivity invariants -/

lemma natDegree_seg (s : Seg) : (toPoly s.data.G).natDegree ≤ s.data.d := by
  cases s with
  | fixed w => simp [Seg.data]
  | grow β k m c =>
    simp only [Seg.data, toPoly_lsmul, toPoly_lsub, toPoly_lmono, toPoly_cons, toPoly_nil, mul_zero,
      add_zero]
    refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_sub_le _ _).trans (max_le (natDegree_C_mul_X_pow_le _ _) ?_)
    simp

lemma natDegree_segs : ∀ l : List Seg, (toPoly (segsData l).G).natDegree ≤ (segsData l).d
  | [] => by simp [segsData, Data.unit]
  | s :: l => by
    have h₁ := natDegree_seg s
    have h₂ := natDegree_segs l
    simp only [segsData, Data.comb, toPoly_ladd, toPoly_lsmul, toPoly_lmul, toPoly_lmono]
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le _ _).trans (h₁.trans (Nat.le_add_right _ _))
    · refine (natDegree_C_mul_le _ _).trans ((natDegree_mul_le).trans ?_)
      exact add_le_add ((natDegree_C_mul_X_pow_le _ _)) h₂

/-- `deg γ ≤ N`. -/
theorem Family.natDegree_G (F : Family) : (toPoly F.data.G).natDegree ≤ F.data.d :=
  natDegree_segs F.segs

lemma pos_seg (s : Seg) : 1 ≤ s.data.xc ∧ 1 ≤ s.data.yc := by
  cases s <;> simp only [Seg.data] <;> exact ⟨one_le_pow₀ (by norm_num), one_le_pow₀ (by norm_num)⟩

lemma pos_segs : ∀ l : List Seg, 1 ≤ (segsData l).xc ∧ 1 ≤ (segsData l).yc
  | [] => by simp [segsData, Data.unit]
  | s :: l => by
    obtain ⟨a, b⟩ := pos_seg s
    obtain ⟨c, d⟩ := pos_segs l
    exact ⟨one_le_mul_of_one_le_of_one_le a c, one_le_mul_of_one_le_of_one_le b d⟩

/-- `2^m ≠ 3^n` unless both exponents vanish. -/
lemma two_pow_ne_three_pow {m n : ℕ} (hm : 1 ≤ m) : (2 : ℚ) ^ m - 3 ^ n ≠ 0 := by
  intro h
  have h' : (2 : ℤ) ^ m = 3 ^ n := by exact_mod_cast (sub_eq_zero.mp h)
  have h2 : (2 : ℤ) ∣ 3 ^ n := h' ▸ dvd_pow_self 2 (by omega)
  have := Int.Prime.dvd_pow' (p := 2) (by norm_num) h2
  omega

lemma mu_seg {p q : ℕ} (s : Seg) (hs : s.okB p q = true) (hp : 1 ≤ p) : s.data.μ ≠ 0 := by
  cases s with
  | fixed w => simp [Seg.data]
  | grow β k m c =>
    obtain ⟨-, hsum, -, hk⟩ := Seg.okB_grow hs
    simp only [Seg.data]
    exact two_pow_ne_three_pow (by rw [hsum]; nlinarith)

lemma mu_segs {p q : ℕ} (hp : 1 ≤ p) : ∀ l : List Seg, (l.all (Seg.okB p q)) = true →
    (segsData l).μ ≠ 0
  | [], _ => by simp [segsData, Data.unit]
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    exact mul_ne_zero (mu_seg s h.1 hp) (mu_segs hp l h.2)

theorem Family.mu_ne_zero {F : Family} (hF : F.okB = true) : F.data.μ ≠ 0 := by
  simp only [Family.okB, Bool.and_eq_true, decide_eq_true_eq] at hF
  exact mu_segs hF.1.1 F.segs hF.2

theorem Family.xc_ge (F : Family) : 1 ≤ F.data.xc := (pos_segs F.segs).1
theorem Family.yc_ge (F : Family) : 1 ≤ F.data.yc := (pos_segs F.segs).2

lemma mu_int_seg (s : Seg) : ∃ z : ℤ, (z : ℚ) = s.data.μ := by
  cases s with
  | fixed w => exact ⟨1, by simp [Seg.data]⟩
  | grow β k m c => exact ⟨2 ^ β.sum - 3 ^ β.length, by simp [Seg.data]⟩

lemma mu_int_segs : ∀ l : List Seg, ∃ z : ℤ, (z : ℚ) = (segsData l).μ
  | [] => ⟨1, by simp [segsData, Data.unit]⟩
  | s :: l => by
    obtain ⟨a, ha⟩ := mu_int_seg s
    obtain ⟨b, hb⟩ := mu_int_segs l
    exact ⟨a * b, by simp [segsData, Data.comb, ha, hb]⟩

/-- `μ` is an integer. -/
theorem Family.mu_int (F : Family) : ∃ z : ℤ, (z : ℚ) = F.data.μ := mu_int_segs F.segs

lemma wpow_pos {β : Word} (hβ : β.Pos) (n : ℕ) : (wpow β n).Pos := by
  intro d hd
  simp only [wpow, List.mem_flatten, List.mem_replicate] at hd
  obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hd
  exact hβ d hl

lemma segsWord_pos {p q : ℕ} : ∀ l : List Seg, (l.all (Seg.okB p q)) = true →
    ∀ a, (segsWord l a).Pos
  | [], _, _ => fun d hd => by simp [segsWord] at hd
  | s :: l, h, a => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    intro d hd
    simp only [segsWord, List.mem_append] at hd
    rcases hd with hd | hd
    · cases s with
      | fixed w => exact (posB_iff w).mp (by simpa [Seg.okB] using h.1) d hd
      | grow β k m c => exact wpow_pos (Seg.okB_grow h.1).1 _ d hd
    · exact segsWord_pos l h.2 a d hd

/-- Every member of a valid family is a positive word. -/
theorem Family.word_pos {F : Family} (hF : F.okB = true) (a : ℕ) : (F.word a).Pos := by
  simp only [Family.okB, Bool.and_eq_true] at hF
  exact segsWord_pos F.segs hF.2 a

lemma segsWord_ne_nil {p q : ℕ} (hq : 1 ≤ q) : ∀ l : List Seg, (l.all (Seg.okB p q)) = true →
    1 ≤ (segsData l).d → ∀ a, 1 ≤ a → segsWord l a ≠ []
  | [], _, h, _, _ => by simp [segsData, Data.unit] at h
  | s :: l, h, hd, a, ha => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [segsData, Data.comb] at hd
    simp only [segsWord, ne_eq, List.append_eq_nil_iff, not_and]
    intro hs
    by_cases hl : 1 ≤ (segsData l).d
    · exact segsWord_ne_nil hq l h.2 hl a ha
    · exfalso
      cases s with
      | fixed w => simp [Seg.data] at hd; omega
      | grow β k m c =>
        obtain ⟨-, -, hlen, hk⟩ := Seg.okB_grow h.1
        simp only [Seg.data] at hd
        have hm : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with h0 | h0
          · rw [h0] at hd; omega
          · exact h0
        have := congrArg List.length hs
        simp only [Seg.word, wpow_length, hlen, List.length_nil] at this
        have : 1 ≤ (m * a + c) * (k * q) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        omega

/-- For `N ≥ 1`, every member with `a ≥ 1` is nonempty. -/
theorem Family.word_ne_nil {F : Family} (hF : F.okB = true) (hN : 1 ≤ F.data.d) {a : ℕ}
    (ha : 1 ≤ a) : F.word a ≠ [] := by
  simp only [Family.okB, Bool.and_eq_true, decide_eq_true_eq] at hF
  exact segsWord_ne_nil hF.1.2 F.segs hF.2 hN a ha

/-- `toPoly δ = C xc · X^N - C yc`. -/
lemma Data.toPoly_delta (D : Data) : toPoly D.delta = C D.xc * X ^ D.d - C D.yc := by
  simp [Data.delta]

/-- `N = 0` makes the family constant. -/
lemma segsWord_const {p q : ℕ} : ∀ l : List Seg, (l.all (Seg.okB p q)) = true →
    (segsData l).d = 0 → ∀ a, segsWord l a = segsWord l 0
  | [], _, _, _ => rfl
  | s :: l, h, hd, a => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [segsData, Data.comb, Nat.add_eq_zero_iff] at hd
    simp only [segsWord, segsWord_const l h.2 hd.2 a]
    congr 1
    cases s with
    | fixed w => rfl
    | grow β k m c =>
      obtain ⟨-, -, -, hk⟩ := Seg.okB_grow h.1
      simp only [Seg.data] at hd
      have hm : m = 0 := by
        rcases Nat.mul_eq_zero.mp hd.1 with h0 | h0
        · omega
        · exact h0
      simp [Seg.word, hm]

theorem Family.word_const {F : Family} (hF : F.okB = true) (h0 : F.data.d = 0) (a : ℕ) :
    F.word a = F.word 0 := by
  simp only [Family.okB, Bool.and_eq_true] at hF
  exact segsWord_const F.segs hF.2 h0 a

end Syracuse.R1
