---
id: 0277
title: Static ℝ × X side conditions live in Causal.Model.StaticCauchy
kind: pattern
created: 2026-11-23
---
For the ladder side conditions of any static ℝ × X (`staticCausality.noCausalEndpoint`, `chronalNeighbours`, `causallyOpen`, `stronglyCausalOpen`, `hasTimeFunction`, `isCauchySurface_slice`, `IsRayTo`) import `Causal.Model.StaticCauchy`, not `Causal.Model.EAlphaCauchy`: it does not pull in `Causal.Model.Massive` (T-loc-ealpha-tidy). One witness for the half-plane `staticCausality (Ioi 0)`'s ladder properties beside ¬ CausallyCompact is `Causal.halfPlane_separates` (`Causal.Model.HalfPlaneLadder`), the same object as `Causal.halfPlane_hypotheses`.
