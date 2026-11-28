import GFNBounds.Paper.Attribute

/-!
# Export fixture A, compiled as the module `GFNBounds.Paper.AppendixFixA`

Never part of the library: `run.sh` copies it to a temporary directory and compiles it there
with `lean -o`, so it reaches no `.olean` of the package and no committed `docs/lean-facts.json`.
An assembly module by name (`GFNBounds.Paper.Appendix*`), so its placed theorem gets `conjuncts`.
-/

namespace GFNBounds.Paper.FixA

theorem zero_eq : (0 : Nat) = 0 := rfl
theorem one_eq : (1 : Nat) = 1 := rfl
/-- An assembly theorem: a tuple of two project theorems. -/
theorem asm (n : Nat) (_h : 0 < n) : (0 : Nat) = 0 ∧ (1 : Nat) = 1 := ⟨zero_eq, one_eq⟩
/-- A placed `def` in an assembly module: gets `paper`, never `conjuncts`. -/
def d : Nat := 0

end GFNBounds.Paper.FixA

attribute [paper "lem:paperattr_test_export_asm"] GFNBounds.Paper.FixA.asm
attribute [paper "lem:paperattr_test_export_def"] GFNBounds.Paper.FixA.d
attribute [paper "lem:paperattr_test_export_same"] GFNBounds.Paper.validLabel
attribute [paper "lem:paperattr_test_export_dup"] GFNBounds.Paper.labels
