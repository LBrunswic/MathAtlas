---
id: 0096
title: fin_two_induction instead of the set workaround of kb/0071
kind: pattern
created: 2026-11-23
---
Found by T-bbs-psl2-normal-forms. Matrix.SpecialLinearGroup.fin_two_induction turns A : SL(2,R) into <!![a, b; c, d], hdet>, so simp evaluates the entries and the determinant is hdet. It avoids the `set b := A 0 1` mismatches of kb/0071.
