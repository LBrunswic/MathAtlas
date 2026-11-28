import GFNBounds.Paper.Attribute

/-!
# Export fixture B, compiled as the module `GFNBounds.Paper.FixB`

Does not import fixture A, so the attribute's `add` cannot see that A already placed
`lem:paperattr_test_export_dup`, on `GFNBounds.Paper.labels`. B places it on `validLabel`: the
cross-module duplicate only the exporter catches. Compiled in a temporary directory by `run.sh`.
-/

attribute [paper "lem:paperattr_test_export_dup"] GFNBounds.Paper.validLabel
