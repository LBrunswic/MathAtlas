---
id: 0094
title: Never use the Hausdorff measure as a surface area
kind: pitfall
created: 2026-11-27
---
Found by T-yamabe-brown-york. Do not use μH[d] as a surface measure (Mathlib's Hausdorff measure is unnormalised); an area of ∂C can be read as the Minkowski content lim_{t→0+}(|cthickening t C| − |C|)/t, computed for a ball by cthickening_closedBall, Measure.addHaar_closedBall and HasDerivAt.tendsto_slope_zero_right (Ref.hasBdryArea_closedBall).
