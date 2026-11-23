---
id: 0052
title: pattern:
kind: pattern
created: 2026-11-23
---
Found by T-perf-main. pattern: an explicit O(delta^2) for 1/Lambda(delta) without calculus. Lambda solves Lambda^2 - T Lambda + delta = 0, so h = 1/Lambda solves P(h) = delta h^2 - T h + 1 = 0, and (h - g)(Lambda - delta g) = P(g) for any g. Take g the linearisation and bound Lambda - delta g below. HasDerivAt then follows from hasDerivAt_iff_isLittleO and IsBigO.trans_isLittleO (isLittleO_pow_id one_lt_two) (Yamabe.inv_lamMax_sub_le, hasDerivAt_inv_lamMax). (The C¹ instance is argued, not formalized.)
