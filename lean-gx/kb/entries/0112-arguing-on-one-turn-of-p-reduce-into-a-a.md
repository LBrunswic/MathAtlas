---
id: 0112
title: Arguing on one turn of ℓ(p): reduce into [a, a + 2) and split at a, b, a+1, b+1
kind: pattern
created: 2026-11-23
---
Found by T-bbs-hs-link-types. To argue on one turn of l(p) (delta^2, period 2), reduce t into [a, a + 2) with GX.exists_linkCover_eq_Ico theta a t. Then split by GX.mem_Ico_two_cases into the four points a, b, a+1, b+1 and the four open intervals between them; linkCover (y + 1) = -linkCover y moves between the halves.
