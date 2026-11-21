# 0045 — Pitfall: two ChartedSpace instances on a quotient under projOfAff

*Found 2026-11-21 by T-bz-result-b-proj; recorded by the master session.*

Pitfall: under `attribute [local instance] projOfAff`, a quotient N/Γ of an affine N has two ChartedSpace (S n) instances. projOfAff applies to the quotient's affine charts, and MulAction.instChartedSpaceQuotient comes from N's projective charts. hasGroupoid_quotient and isGXMorphism_quotientMk use the latter, so `letI` it before calling them (« synthesized type class instance is not definitionally equal »).
