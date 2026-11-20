---
id: 0039
title: The causal IsRigid is satisfiable on a connected, non-trivial base
kind: pitfall
created: 2026-11-20
---
`DensWitness.bigCausality` on ℝ (U fills half of ]x,y] in measure, or y − x ≥ 1) is rigid, because
its morphisms preserve midpoints locally (`Causal.CBG.SubExtensionAbstract`). Test any claim that
assumes `IsRigid` against it before trying to prove the claim (T-ett-subextension, DEC-60).
