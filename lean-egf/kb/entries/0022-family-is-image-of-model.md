---
id: 0022
title: A paper's parameterized family is the image of a model, never a membership predicate
kind: pattern
created: 2026-11-22
---
Found by AUDIT-1 of T-egf-families. A "family parameterized by a model" (affine toroidal,
isometry spherical) is `Set.range (M.flow ·)` over a structure whose parameter type is non-empty
(`EGF.AffineToroidalModel`, `EGF.affineToroidalFamily`; `EGF.IsometrySphericalModel`,
`EGF.isometrySphericalFamily`). A predicate on members ("every member has these moves") is
satisfied by the empty family, so a Prop "every such family is universal" is refuted for nothing
and a universality theorem over it proves nothing. Richness the theorem needs is then a named
hypothesis on the family (`EGF.IsRichToroidalModel`, `EGF.IsRichSphericalModel`, correction C-31).
