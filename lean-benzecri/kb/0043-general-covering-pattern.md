# 0043 — Universal-cover statements: prove them for any simply connected covering

*Found 2026-11-21 by T-bz-result-b-proj; recorded by the master session.*

Statements about « le revêtement universel »: prove them for any simply connected covering π : N → V, with [ChartedSpace X N] [HasGroupoid N _] and IsGXMorphism π. Divisibility comes from isDivisible_of_isCoveringMap and Hausdorffness from resultB_t2Space_of_isCoveringMap. Then specialise to UniversalCover V v₀ through the components of revetement_universel_divisible_proj/_aff (covering, simply connected, morphism). A non-vacuity witness then needs no computation inside UniversalCover: give N concretely and take V := N/Γ (Structure/Quotient: hasGroupoid_quotient, isGXMorphism_quotientMk, and isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap).
