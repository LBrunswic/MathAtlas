import Benzecri.Chapter3.FacettesSphere

/-!
# The closed positive simplex of `S(m)`

One definition of the closed positive orthant of `ℝᵐ⁺¹` and of the closed simplex
`s(orthant − {O})` of `S(m)` (for `m = 2`, the closed triangle), the instance of several Chapter 3
files. `FacetteDualeInstance` re-exports both names (`Chapter3/FacetteDuale.lean`), which until
T-bz-c3-dedupe-simplexe carried a second, identical copy.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`; imports
`Benzecri.Chapter3.FacettesSphere`. No `sorry`; standard axioms only.
-/

namespace Benzecri

open Sphere

namespace TriangleInstance

/-- The closed positive orthant of `ℝᵐ⁺¹`. -/
def orthant (m : ℕ) : Set (Fin (m + 1) → ℝ) := {v | ∀ i, 0 ≤ v i}

/-- The closed simplex of `S(m)`: the rays of the positive orthant (for `m = 2`, a closed
triangle). -/
def simplexS (m : ℕ) : Set (S m) := ofCone (orthant m)

end TriangleInstance

end Benzecri
