---
id: 0062
title: The model-free corresponding-point toolkit is in the ETT layer
kind: pattern
created: 2026-11-21
---
`Causal.CorrespondingPoints`: K⁻ and causal convexity, Def 3.5 in (U, ψ) form (`CBG.Corresponds`),
`CBG.IsCorrPair`/`KSide`, `lem:corresponding_K`, Prop 3.7 (iii) ⇒ (i), and witnesses on the timelike
and lightlike lines. `Causal.CorrespondingSpacelike`: (3.10) ⟺ the ETT form (`spacelike_iff`),
Sbierski Lemma 3.11 (`exists_lt_Jminus_compl_subset`), Lemma 3.9's core
(`IsCorrPair.exists_corresponds_of_le`), the set of corresponding points closed. Same full names as
before (T-abs-hoist-cbg-cores). Still behind a model import: `correspondingSet`, `correspondingExt`
(model-free, unlisted), and the CBG interface itself (Geometry, Dev, cbg; T-abs-hoist-cbg-geometry).
