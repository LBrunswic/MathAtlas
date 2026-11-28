import GFNBounds.Paper.Attribute

/-!
# Export fixture D, compiled as the module `GFNBounds.Paper.AppendixFixD`

A placed assembly theorem with glue around a conjunct (`Nat.le_of_lt`), which
`GFNBounds.Paper.conjunctsOf` refuses: the exporter must throw before writing. Compiled in a
temporary directory by `run.sh`.
-/

namespace GFNBounds.Paper.FixD

theorem lt1 (n : Nat) : n < n + 1 := Nat.lt_succ_self n
theorem c : (1 : Nat) = 1 := rfl
theorem glued (n : Nat) : n ≤ n + 1 ∧ (1 : Nat) = 1 := ⟨Nat.le_of_lt (lt1 n), c⟩

end GFNBounds.Paper.FixD

attribute [paper "lem:paperattr_test_export_glue"] GFNBounds.Paper.FixD.glued
