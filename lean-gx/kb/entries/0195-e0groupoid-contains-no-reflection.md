---
id: 0195
title: e0Groupoid contains no reflection
kind: pattern
created: 2026-11-28
---
Found by T-btz-isom-e0. e0Groupoid contains no reflection: GX.BTZIsom.not_conj_localForm. An element of G that reads near an axis point as (tau, z) -> (tau + a, w conj z) is impossible, by the determinant of Isom(M3) = SO_0(1,2) x| R^3. So the R of GX.E0AbsMax.e0Loop_localForm is always a rotation (use linear_isometry_complex, then not_conj_localForm). Rigid.lean:73's 'k = -1 not excluded' concerns the winding in that proof, not G.
