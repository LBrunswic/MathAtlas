import GXScaffold.Branched.GaloisExamples

open Set Function Topology unitInterval

namespace GX

/-- The tube bounding boxes of `j` against the link boxes of `i` are separated. -/
def AntoineTubeSep (i j : Fin 64) : Prop :=
  antoineEx (antoineT i) + antoineEx (antoineT j) + 7 ≤ |(antoineZ i).1 - (antoineZ j).1| ∨
  antoineEy (antoineT i) + antoineEy (antoineT j) + 7 ≤ |(antoineZ i).2 - (antoineZ j).2|

instance antoineTubeSep_decidable (i j : Fin 64) : Decidable (AntoineTubeSep i j) := by
  unfold AntoineTubeSep; infer_instance

set_option maxRecDepth 100000 in
theorem antoine_tubeSep_or_adj : ∀ i j : Fin 64, i ≠ j → AntoineTubeSep i j ∨ AntoineAdj i j := by
  decide

theorem antoineNbhd_bounds {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineNbhd) :
    |p.1| < 9 / 8 ∧ |p.2.1| < 9 / 8 ∧ |p.2.2| < 1 / 4 := by
  have hp' : (max |p.1| |p.2.1| - 7 / 8) ^ 2 + p.2.2 ^ 2 < 1 / 16 := hp
  have h1 : (max |p.1| |p.2.1| - 7 / 8) ^ 2 < 1 / 16 := by nlinarith [sq_nonneg p.2.2]
  have h2 : p.2.2 ^ 2 < 1 / 16 := by nlinarith [sq_nonneg (max |p.1| |p.2.1| - 7 / 8)]
  have h1' : max |p.1| |p.2.1| < 9 / 8 := by nlinarith
  refine ⟨(le_max_left _ _).trans_lt h1', (le_max_right _ _).trans_lt h1', ?_⟩
  exact abs_lt_of_sq_lt_sq (by linarith) (by norm_num)

theorem antoineMap_bounds_nbhd (i : Fin 64) {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineNbhd) :
    |(antoineMap i p).1 - (antoineZ i).1 / 640| < (antoineEx (antoineT i) + 7) / 640 ∧
      |(antoineMap i p).2.1 - (antoineZ i).2 / 640| < (antoineEy (antoineT i) + 7) / 640 := by
  obtain ⟨hx, hy, hz⟩ := antoineNbhd_bounds hp
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMap, h, antoinePerm, antoineEx, antoineEy, add_sub_cancel_left, abs_mul,
      abs_of_pos (show (0 : ℝ) < 7 / 80 by norm_num)] <;>
    push_cast <;> refine ⟨?_, ?_⟩ <;> linarith

/-- A tube point `(a, b, c)` and a link point `(a', b', c')` of two interlocking links, with
`a = a' + s`, `b = c'`, `c = b'`, `s = ±5/4`, cannot coincide. -/
theorem antoine_tube_aux {a b c a' b' c' s : ℝ} (hs : s = 5 / 4 ∨ s = -(5 / 4))
    (h1 : a = a' + s) (h2 : b = c') (h3 : c = b')
    (hp : (max |a| |b| - 7 / 8) ^ 2 + c ^ 2 < 1 / 16)
    (hp' : |c'| ≤ 1 / 8 ∧ max |a'| |b'| ≤ 1 ∧ 3 / 4 ≤ max |a'| |b'|) : False := by
  obtain ⟨hc', ha1', ha2'⟩ := hp'
  rw [← h2] at hc'
  rw [← h3] at ha1' ha2'
  have hc : c ^ 2 < 1 / 16 := by nlinarith [sq_nonneg (max |a| |b| - 7 / 8)]
  have hc4 : |c| < 1 / 4 := abs_lt_of_sq_lt_sq (by linarith) (by norm_num)
  have hA' : 3 / 4 ≤ |a'| := by
    rcases le_max_iff.1 ha2' with h | h
    · exact h
    · linarith
  have hx' : |a'| ≤ 1 := (le_max_left _ _).trans ha1'
  have hρ : max |a| |b| ≤ 1 / 2 ∨ 2 ≤ max |a| |b| := by
    have hb : |b| ≤ 1 / 2 := by linarith
    rw [abs_le] at hx'
    rcases le_abs'.1 hA' with h | h <;> rcases hs with rfl | rfl <;>
      first
      | (left; refine max_le ?_ hb; rw [abs_le]; constructor <;> linarith)
      | (right; refine le_max_of_le_left ?_; rw [abs_of_neg (by linarith)]; linarith)
      | (right; refine le_max_of_le_left ?_; rw [abs_of_pos (by linarith)]; linarith)
  rcases hρ with h | h <;> nlinarith [sq_nonneg c]

theorem antoineTube_disjoint (i j : Fin 64) (hij : i ≠ j) :
    Disjoint (antoineMap j '' antoineNbhd) (antoineMap i '' antoineLink) := by
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ ⟨p', hp', heq⟩
  rcases antoine_tubeSep_or_adj i j hij with hsep | hadj
  · obtain ⟨b1, b2, -⟩ := antoineMap_bounds i hp'
    obtain ⟨b1', b2'⟩ := antoineMap_bounds_nbhd j hp
    rw [← heq] at b1' b2'
    rw [abs_le] at b1 b2
    rw [abs_lt] at b1' b2'
    rcases hsep with h | h
    · have h' : ((antoineEx (antoineT i) + antoineEx (antoineT j) + 7 : ℤ) : ℝ) ≤
          |((antoineZ i).1 : ℝ) - (antoineZ j).1| := by exact_mod_cast h
      push_cast at h'
      rcases le_abs'.1 h' with h'' | h'' <;> linarith
    · have h' : ((antoineEy (antoineT i) + antoineEy (antoineT j) + 7 : ℤ) : ℝ) ≤
          |((antoineZ i).2 : ℝ) - (antoineZ j).2| := by exact_mod_cast h
      push_cast at h'
      rcases le_abs'.1 h' with h'' | h'' <;> linarith
  · have hp1 : (max |p.1| |p.2.1| - 7 / 8) ^ 2 + p.2.2 ^ 2 < 1 / 16 := hp
    rcases hadj with ⟨hy, hx, ht⟩ | ⟨hx, hy, ht⟩
    · have hy' : ((antoineZ i).2 : ℝ) = (antoineZ j).2 := by exact_mod_cast hy
      have hx' : ((antoineZ i).1 : ℝ) - (antoineZ j).1 = 70 ∨
          ((antoineZ i).1 : ℝ) - (antoineZ j).1 = -70 := by
        rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 70)).1 hx with h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr (by exact_mod_cast h)
      rcases ht with ⟨ti, tj⟩ | ⟨ti, tj⟩
      · -- link `i` horizontal, tube `j` vertical (`y`-plane)
        simp only [antoineMap, ti, tj, antoinePerm, Prod.mk.injEq] at heq
        obtain ⟨e1, e2, e3⟩ := heq
        refine antoine_tube_aux (a := p.1) (b := p.2.1) (c := p.2.2) (a' := p'.1)
          (b' := p'.2.1) (c' := p'.2.2)
          (s := if ((antoineZ i).1 : ℝ) - (antoineZ j).1 = 70 then 5/4 else -(5/4))
          ?_ ?_ (by linarith) (by linarith) hp1 hp'
        · split_ifs <;> simp
        · rcases hx' with h | h
          · rw [if_pos h]; linarith
          · rw [if_neg (by rw [h]; norm_num)]; linarith
      · simp only [antoineMap, ti, tj, antoinePerm, Prod.mk.injEq] at heq
        obtain ⟨e1, e2, e3⟩ := heq
        refine antoine_tube_aux (a := p.1) (b := p.2.1) (c := p.2.2) (a' := p'.1)
          (b' := p'.2.1) (c' := p'.2.2)
          (s := if ((antoineZ i).1 : ℝ) - (antoineZ j).1 = 70 then 5/4 else -(5/4))
          ?_ ?_ (by linarith) (by linarith) hp1 hp'
        · split_ifs <;> simp
        · rcases hx' with h | h
          · rw [if_pos h]; linarith
          · rw [if_neg (by rw [h]; norm_num)]; linarith
    · have hx' : ((antoineZ i).1 : ℝ) = (antoineZ j).1 := by exact_mod_cast hx
      have hy' : ((antoineZ i).2 : ℝ) - (antoineZ j).2 = 70 ∨
          ((antoineZ i).2 : ℝ) - (antoineZ j).2 = -70 := by
        rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 70)).1 hy with h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr (by exact_mod_cast h)
      rcases ht with ⟨ti, tj⟩ | ⟨ti, tj⟩
      · simp only [antoineMap, ti, tj, antoinePerm, Prod.mk.injEq] at heq
        obtain ⟨e1, e2, e3⟩ := heq
        refine antoine_tube_aux (a := p.2.1) (b := p.1) (c := p.2.2) (a' := p'.2.1)
          (b' := p'.1) (c' := p'.2.2)
          (s := if ((antoineZ i).2 : ℝ) - (antoineZ j).2 = 70 then 5/4 else -(5/4))
          ?_ ?_ (by linarith) (by linarith) (by rw [max_comm]; exact hp1)
            ⟨hp'.1, by rw [max_comm]; exact hp'.2.1, by rw [max_comm]; exact hp'.2.2⟩
        · split_ifs <;> simp
        · rcases hy' with h | h
          · rw [if_pos h]; linarith
          · rw [if_neg (by rw [h]; norm_num)]; linarith
      · simp only [antoineMap, ti, tj, antoinePerm, Prod.mk.injEq] at heq
        obtain ⟨e1, e2, e3⟩ := heq
        refine antoine_tube_aux (a := p.2.1) (b := p.1) (c := p.2.2) (a' := p'.2.1)
          (b' := p'.1) (c' := p'.2.2)
          (s := if ((antoineZ i).2 : ℝ) - (antoineZ j).2 = 70 then 5/4 else -(5/4))
          ?_ ?_ (by linarith) (by linarith) (by rw [max_comm]; exact hp1)
            ⟨hp'.1, by rw [max_comm]; exact hp'.2.1, by rw [max_comm]; exact hp'.2.2⟩
        · split_ifs <;> simp
        · rcases hy' with h | h
          · rw [if_pos h]; linarith
          · rw [if_neg (by rw [h]; norm_num)]; linarith

end GX
