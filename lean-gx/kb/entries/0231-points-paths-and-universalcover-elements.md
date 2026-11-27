---
id: 0231
title: Points, paths and UniversalCover elements of Reg M must be typed e0RegMFlat M, not the sub
kind: pattern
created: 2026-11-28
---
Found by T-btz-admissible. Points, paths and UniversalCover elements of Reg M must be typed e0RegMFlat M, not the subtype E0LM.e0RegM M: the two are defeq but not at instances transparency, so rw/simp fail on mixed terms (BTZCircle.ptF; regCoverBase unfolds by show (show E0LM.e0RegM M from proj w).1 = _).
