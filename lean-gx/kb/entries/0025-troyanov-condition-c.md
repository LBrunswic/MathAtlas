---
id: 0025
title: Troyanov's condition of record is Theorem C's (GX.TroyanovAngleConditionC); the printed one is C plus χ' ≤ θ_j
kind: pattern
created: 2026-11-22
---
Found by T-gx-troyanov-theorem-c (DEC-174). The condition of record is `GX.TroyanovAngleConditionC` (`GX/Spherical/TroyanovTheoremC.lean`): 0 < χ' < 4π and χ' < 2θ_j for every j, where χ' = Σ(θ_i − 2π) + 4π. DEC-69's `GX.TroyanovAngleCondition` is the paper's narrower citation. It is exactly C plus χ' ≤ θ_j for every j (`troyanovAngleCondition_iff_troyanovAngleConditionC`), so state new Troyanov work against C and derive the printed form. C alone forces s ≥ 3 and positive angles (`.three_le`, `.pos`). It is invariant under adding or removing angles 2π (`troyanovAngleConditionC_removeNth_iff`), so the two-pi reduction ports verbatim.
