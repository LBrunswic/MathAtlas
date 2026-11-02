import GXScaffold.Branched.GaloisExamples

open Set Filter Topology Function

noncomputable section
namespace GX

def antoineEz : Fin 3 → ℤ
  | 0 => 7
  | 1 => 56
  | 2 => 56

theorem antoineMap_bounds_z (i : Fin 64) {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineLink) :
    |(antoineMap i p).2.2| ≤ antoineEz (antoineT i) / 640 := by
  obtain ⟨hz, hm, -⟩ := hp
  have hx : |p.1| ≤ 1 := (le_max_left _ _).trans hm
  have hy : |p.2.1| ≤ 1 := (le_max_right _ _).trans hm
  rcases antoineT_cases i with h | h | h <;>
    simp only [antoineMap, h, antoinePerm, antoineEz, abs_mul,
      abs_of_pos (show (0 : ℝ) < 7 / 80 by norm_num)] <;> push_cast <;> linarith

theorem antoineComp_succ' (w : ℕ → Fin 64) (n : ℕ) :
    antoineComp w (n + 1) = antoineMap (w 0) ∘ antoineComp (fun k => w (k + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show antoineComp w (n + 1) ∘ antoineMap (w (n + 1)) = _
    rw [ih]; rfl

theorem antoineComp_mem_link (w : ℕ → Fin 64) (n : ℕ) {p : ℝ × ℝ × ℝ} (hp : p ∈ antoineLink) :
    antoineComp w n p ∈ antoineLink := by
  have := antoineComp_antitone w (Nat.zero_le n) ⟨p, hp, rfl⟩
  simpa [antoineComp] using this

theorem antoine_mem_stage_of_map {i : Fin 64} {q : ℝ × ℝ × ℝ} (hq : q ∈ antoineLink) {j : ℕ}
    (h : antoineMap i q ∈ antoineStage (j + 1)) : q ∈ antoineStage j := by
  obtain ⟨w, hw⟩ := mem_iUnion.1 h
  obtain ⟨r, hr, hrq⟩ := hw
  rw [antoineComp_succ'] at hrq
  have hr' := antoineComp_mem_link (fun k => w (k + 1)) j hr
  by_cases hi : w 0 = i
  · subst hi
    exact mem_iUnion.2 ⟨_, r, hr, antoineMap_injective _ hrq⟩
  · exact absurd (Set.disjoint_left.1 (antoineMap_disjoint hi) ⟨_, hr', hrq⟩ ⟨q, hq, rfl⟩) id

theorem antoine_mem_stage_of_comp (u : ℕ → Fin 64) (k : ℕ) {q : ℝ × ℝ × ℝ}
    (hq : q ∈ antoineLink) {j : ℕ} (h : antoineComp u k q ∈ antoineStage (j + k)) :
    q ∈ antoineStage j := by
  induction k generalizing q j with
  | zero => simpa [antoineComp] using h
  | succ k ih =>
    have h' : antoineComp u k (antoineMap (u k) q) ∈ antoineStage ((j + 1) + k) := by
      rw [show j + 1 + k = j + (k + 1) by omega]; exact h
    exact antoine_mem_stage_of_map hq (ih (antoineMap_mem _ hq) h')

theorem antoine_mem_necklace_of_comp (u : ℕ → Fin 64) (k : ℕ) {q : ℝ × ℝ × ℝ}
    (hq : q ∈ antoineLink) (h : antoineComp u k q ∈ antoineNecklaceR3) : q ∈ antoineNecklaceR3 :=
  mem_iInter.2 fun j => antoine_mem_stage_of_comp u k hq (mem_iInter.1 h (j + k))

theorem antoineNecklaceR3_subset_stage (n : ℕ) : antoineNecklaceR3 ⊆ antoineStage n :=
  iInter_subset _ n

theorem antoine_mem_stage_one {p : ℝ × ℝ × ℝ} (h : p ∈ antoineStage 1) :
    ∃ i : Fin 64, ∃ q ∈ antoineLink, antoineMap i q = p := by
  obtain ⟨w, q, hq, e⟩ := mem_iUnion.1 h
  exact ⟨w 0, q, hq, e⟩

theorem antoineZ_zero : antoineZ 0 = (-560, -560) := by decide
theorem antoineT_zero : antoineT 0 = 0 := by decide
theorem antoineZ_one : antoineZ 1 = (-490, -560) := by decide
theorem antoineT_one : antoineT 1 = 1 := by decide

/-- The fixed point of `g₀`, a point of the necklace. -/
def antoineP0 : ℝ × ℝ × ℝ := (-(70 / 73), -(70 / 73), 0)

theorem antoineMap_zero_p0 : antoineMap 0 antoineP0 = antoineP0 := by
  simp only [antoineMap, antoineZ_zero, antoineT_zero, antoinePerm, antoineP0]
  ext <;> push_cast <;> ring

theorem antoineP0_mem : antoineP0 ∈ antoineLink := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [antoineP0] <;> norm_num

theorem antoineComp_zero_p0 (k : ℕ) : antoineComp (fun _ => 0) k antoineP0 = antoineP0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show antoineComp _ k (antoineMap 0 antoineP0) = _
    rw [antoineMap_zero_p0, ih]

theorem antoineP0_mem_comp (k : ℕ) : antoineP0 ∈ antoineComp (fun _ => 0) k '' antoineLink :=
  ⟨_, antoineP0_mem, antoineComp_zero_p0 k⟩

theorem antoineP0_mem_necklace : antoineP0 ∈ antoineNecklaceR3 :=
  mem_iInter.2 fun k => mem_iUnion.2 ⟨_, antoineP0_mem_comp k⟩

end GX
-- integer separation facts
theorem antoine_sep_p0 : ∀ i : Fin 64, i ≠ 0 →
    73 * antoineEx (antoineT i) < |-44800 - 73 * (antoineZ i).1| ∨
      73 * antoineEy (antoineT i) < |-44800 - 73 * (antoineZ i).2| := by decide

theorem antoine_sep_mer : ∀ i : Fin 64, i ≠ 1 →
    antoineEx (antoineT i) < |-490 - (antoineZ i).1| ∨
      antoineEy (antoineT i) + 12 < |-560 - (antoineZ i).2| := by decide

end GX
end
