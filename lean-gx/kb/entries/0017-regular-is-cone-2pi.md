---
id: 0017
title: A regular point is a cone point of angle 2π: rotate a chart onto the apex of C_{2π}
kind: pattern
created: 2026-11-20
---
Found by T-gx-troyanov-two-pi. `GX.IsConePoint.of_mem_reg` (`GX.Spherical.TroyanovTwoPi`): take a chart e at x, a chart a of C_{2π} at its apex (regular, `SphCone.sing_eq_empty`), and a rotation g with g • e x = a apex; then a⁻¹ ∘ g ∘ e, restricted to the preimage of the apex's connected component, is the X_{2π}-chart. Its a.e.-morphism property is `GX.isAEMorphism_of_chart_eq`: a map out of an open U ⊆ e.source with a ∘ f = g • e is a.e. (through `IsAEMorphismOf.regLocusOf_eq` and `IsRegularOn.of_exists`).
