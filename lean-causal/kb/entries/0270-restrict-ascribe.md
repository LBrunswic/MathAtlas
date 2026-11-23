---
id: 0270
title: Ascribe a restricted curve before using it as a chronal curve
kind: pitfall
created: 2026-11-23
---
`CurveOn.restrict (…) |>.causalCurveOn` fails: the restricted term's type is `CurveOn r W c a b`, not `ChronalCurveOn`; ascribe it first (`have hc : C.ChronalCurveOn W c a b := CurveOn.restrict …`), the cousin of kb/0010. Also at this pin: `Icc \ {b} = Ico` is `Set.Icc_sdiff_right` (not `Icc_diff_right`), and a def on ℝ by `if t < 1` must be `noncomputable` (kb/0004).
