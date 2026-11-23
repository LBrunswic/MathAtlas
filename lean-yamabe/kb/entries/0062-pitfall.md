---
id: 0062
title: pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-yamabe-trace-compact. pitfall: the library never proves |∇u|_g = Mfd.gradNorm measurable, so a W^{1,2} bound of u − w cannot be derived from w12 u and w12 w: eLpNorm_add_le needs AEStronglyMeasurable, and the lower lintegral of a non-measurable function is not subadditive. Split the derivative term in the chart, where fderivWithin of chartFun (ρu) is continuous on ℍ̄ (fderivWithin_sub, then eLpNorm_sub_le), and state the estimate for differences (Yamabe.Mfd.local_trace_interp, trace_interp_sub).
