import GFNBounds.Paper.Attribute

/-!
# Export fixture C, compiled as the module `GFNBounds.Paper.FixC`

Does not import fixture A. It repeats A's placement of `lem:paperattr_test_export_same` on
`validLabel` (an identical pair from two modules: one link, deduplicated by the exporter), adds a
second label to `validLabel`, and places a theorem outside the assembly modules (gets `paper`,
no `conjuncts`). Compiled in a temporary directory by `run.sh`, never in the package.
-/

namespace GFNBounds.Paper.FixC

theorem single : (2 : Nat) = 2 := rfl

end GFNBounds.Paper.FixC

attribute [paper "lem:paperattr_test_export_same"] GFNBounds.Paper.validLabel
attribute [paper "lem:paperattr_test_export_c"] GFNBounds.Paper.validLabel
attribute [paper "lem:paperattr_test_export_single"] GFNBounds.Paper.FixC.single
