---
id: 0026
title: The strict Troyanov constructions already work under Theorem C's condition; only s ≥ 5 with an angle above 2π is open
kind: pattern
created: 2026-11-22
---
Found by T-gx-troyanov-theorem-c. The hypotheses of `GX.exists_isConeSphere_of_subcritical` are Theorem C's. At s = 4 every hypothesis of `GX.exists_isConeSphere_dart` follows from C once the angle above 2π is put at index 0; `h23` comes from χ' < 2θ_1 together with θ_0 > 2π. So the C-form of Troyanov is proved for s ≤ 4 and for all angles ≤ 2π (`troyanovTheoremC_four`, `troyanovTheoremC_of_le_two_pi`). The open case, the obligation `GX.troyanovTheoremC` in the scaffold `TroyanovAngles`, is again s ≥ 5 with an angle above 2π, now over a wider set of tuples (`troyanovAngleConditionC_five_not_printed`).
