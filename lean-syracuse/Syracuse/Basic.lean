import Mathlib.Data.Nat.Basic

/-!
# Syracuse — package root (wave 0 placeholder)

The library of `papers/syracuse`: the author's paper on non-trivial cycles of the 3x+1 (Syracuse) problem, formalized in a package of its own at the
hub's pin (DEC-138). Scope first: the whole paper. Wave 0 only checks that the package builds
against the hub's Mathlib; the statements arrive in `Syracuse/` module by module.
-/

namespace Syracuse

/-- Package marker (wave 0). -/
def packageName : String := "Syracuse"

end Syracuse
