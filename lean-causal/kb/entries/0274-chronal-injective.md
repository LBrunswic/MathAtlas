---
id: 0274
title: A chronal curve of a chronological open set is injective; homotopies must not pause
kind: pitfall
created: 2026-11-23
---
A chronal curve of an open set with no `x ≪ x` is injective (`Causality.ChronalCurveOn.injOn`, Causal/TimelikeHomotopy.lean), so a reparametrisation with a pause is never chronal there. A homotopy built by concatenating at a fixed split point degenerates when one piece is constant: Sbierski's Step 2.1 (1507.00601 :572–579) prints one whose end slices are constant on half of `[0, 1]` (`timelikeLine_not_chronalCurveOn_pause`); split at `s = t` instead. On the timelike line the chronal curves of `U` over `[a, b]` are exactly the continuous strictly increasing maps into `U` (`timelikeLine_chronalCurveOn_iff`), the quick way to build curves and homotopies of ℝ.
