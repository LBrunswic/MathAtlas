import Syracuse.Approaches.R1.Decide

/-!
# Decided r = 1 families

Each theorem evaluates the verified procedure `decideR1` in the kernel (`decide +kernel`, which is
not `native_decide`) and reads off the exact cycle set via `decideR1_iff`. The literals are
emitted by `approaches/places-elimination/r1_lean.py lit SPEC`. A 70-family randomized suite
(`r1_lean.py suite`) agrees with brute force on `a ≤ 30` with no mismatches.
-/

namespace Syracuse.R1.Examples

open Syracuse.R1

/-- `1^a 2 1^a 3 1^a` (the `twoRunWord 1 2 3` family): no cycles. -/
def tr123 : Family := ⟨1, 1, [.grow [1] 1 1 0, .fixed [2], .grow [1] 1 1 0, .fixed [3], .grow [1] 1 1 0]⟩
theorem tr123_cycles : ∀ a, IsCycleWord (tr123.word a) ↔ a ∈ ([] : List ℕ) :=
  decideR1_iff (F := tr123) (v := .finite []) (by decide) (by decide +kernel)

/-- `3^a 1 3^a 2 3^a`: only `a = 0`, the word `[1, 2]` of the `-5` cycle. -/
def tr312 : Family := ⟨3, 1, [.grow [3] 1 1 0, .fixed [1], .grow [3] 1 1 0, .fixed [2], .grow [3] 1 1 0]⟩
theorem tr312_cycles : ∀ a, IsCycleWord (tr312.word a) ↔ a ∈ [0] :=
  decideR1_iff (F := tr312) (v := .finite [0]) (by decide) (by decide +kernel)

/-- `(1,2)^a 1 (1,2)^{2a} 4` (block slope `3/2`): no cycles. -/
def blk : Family := ⟨3, 2, [.grow [1, 2] 1 1 0, .fixed [1], .grow [1, 2] 1 2 0, .fixed [4]]⟩
theorem blk_cycles : ∀ a, IsCycleWord (blk.word a) ↔ a ∈ ([] : List ℕ) :=
  decideR1_iff (F := blk) (v := .finite []) (by decide) (by decide +kernel)

/-- `2^a 1 2^{a+1} 3`: no cycles. -/
def off : Family := ⟨2, 1, [.grow [2] 1 1 0, .fixed [1], .grow [2] 1 1 1, .fixed [3]]⟩
theorem off_cycles : ∀ a, IsCycleWord (off.word a) ↔ a ∈ ([] : List ℕ) :=
  decideR1_iff (F := off) (v := .finite []) (by decide) (by decide +kernel)

/-- `(1,3)^a 2^a`: degenerate (`D` and `S` share the factor `z - s`), still no cycles. -/
def degen : Family := ⟨2, 1, [.grow [1, 3] 2 1 0, .grow [2] 1 1 0]⟩
theorem degen_cycles : ∀ a, IsCycleWord (degen.word a) ↔ a ∈ ([] : List ℕ) :=
  decideR1_iff (F := degen) (v := .finite []) (by decide) (by decide +kernel)

/-- `(1,2)^a`: constant fixed point `-5`; a cycle for every `a ≥ 1`. -/
def pow12 : Family := ⟨3, 2, [.grow [1, 2] 1 1 0]⟩
theorem pow12_cycles : ∀ a, IsCycleWord (pow12.word a) ↔ (1 ≤ a ∨ a ∈ ([] : List ℕ)) :=
  decideR1_iff (F := pow12) (v := .allFrom 1 []) (by decide) (by decide +kernel)

/-- `2^a` (the trivial cycle) and `1^a` (the `-1` cycle). -/
def pow2 : Family := ⟨2, 1, [.grow [2] 1 1 0]⟩
def pow1 : Family := ⟨1, 1, [.grow [1] 1 1 0]⟩
theorem pow2_cycles : ∀ a, IsCycleWord (pow2.word a) ↔ (1 ≤ a ∨ a ∈ ([] : List ℕ)) :=
  decideR1_iff (F := pow2) (v := .allFrom 1 []) (by decide) (by decide +kernel)
theorem pow1_cycles : ∀ a, IsCycleWord (pow1.word a) ↔ (1 ≤ a ∨ a ∈ ([] : List ℕ)) :=
  decideR1_iff (F := pow1) (v := .allFrom 1 []) (by decide) (by decide +kernel)

/-- `1^a 2 1 1 4`: exactly `a = 3`, the `-17` cycle `(1,1,1,2,1,1,4)`. -/
def m17 : Family := ⟨1, 1, [.grow [1] 1 1 0, .fixed [2, 1, 1, 4]]⟩
theorem m17_cycles : ∀ a, IsCycleWord (m17.word a) ↔ a ∈ [3] :=
  decideR1_iff (F := m17) (v := .finite [3]) (by decide) (by decide +kernel)

end Syracuse.R1.Examples
