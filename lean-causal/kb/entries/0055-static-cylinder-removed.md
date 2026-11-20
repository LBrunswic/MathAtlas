---
id: 0055
title: Slices of static spacetimes are Cauchy; removing a reachable cylinder kills every Cauchy surface
kind: pattern
created: 2026-11-20
---
Every slice {t = t₀} of a static spacetime over a complete geodesic space is a Cauchy surface
(`staticCausality.isCauchySurface_slice`, Geroch (ii)⇒(iii) with t − t₀). Removing the cylinder
ℝ × A over a closed A reached by a 1-Lipschitz ray (`staticCausality.IsRayTo`) leaves an open set
with no Cauchy surface in the library's sense and not globally hyperbolic
(`IsRayTo.not_exists_isCauchySurfaceOn`, `.not_globallyHyperbolicOn`): cheap non-GH open subsets of
GH models, e.g. the regular part of E_α. (The library's Cauchy surfaces test causal curves, so
"no Cauchy surface" here is weaker than the classical, timelike-tested statement.) The pattern
"a curve runs into the boundary" is `Causality.inextensible_Iio_of_tendsto_not_mem` (model-free,
in a model-importing module: a hoist candidate, kb/0047) (`Causal.Model.EAlphaCauchy`,
T-loc-ealpha-cauchy).
