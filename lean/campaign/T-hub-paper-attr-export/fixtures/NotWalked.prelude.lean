-- Prelude spliced by run.sh after the import lines of a temporary copy of the exporter: a
-- project declaration of the main module, which the walk (imported GFNBounds.* modules only)
-- never emits, carrying a placement. The attribute accepts it; the exporter must throw.
theorem GFNBounds.Paper.FixNotWalked.t : True := trivial
attribute [paper "lem:paperattr_test_export_unwalked"] GFNBounds.Paper.FixNotWalked.t
