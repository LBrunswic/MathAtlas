# 0109 — Chapter3/HyperplanSeparant: Hahn–Banach on a finite-dimensional slice P = affine

*Found 2026-11-28 by T-bz-c3-hyperplan-separant; recorded by the master session.*

Chapter3/HyperplanSeparant: Hahn–Banach on a finite-dimensional slice P = affineSpan T of a bare vector space: carry P to Fin n → ℝ by y ↦ (D.subtype ∘ (finBasis D).equivFun.symm) y + O (an AffineMap built with ⟨toFun, linear, map_vadd'⟩), separate there with geometric_hahn_banach_of_nonempty_interior (interior from Convex.interior_nonempty_iff_affineSpan_eq_top), pull the form back with LinearMap.exists_extend (exists_separe_finset).
