---
id: 0181
title: E_κ is connected: SFAManifolds.massive_connectedSpace (a theorem, not an instance)
kind: pattern
created: 2026-11-21
---
`haveI := SFAManifolds.massive_connectedSpace Real.pi`, via `preconnectedSpace_of_geodesicSpace` (the metric-space copy is `Causal.staticCausality.preconnectedSpace_of_geodesic`, LemmaKBare.lean; hoist one into `Causal.Static` later). `ConnectedSpace E0` is `inferInstance`. Note: `Causal.Remarks.EModelsBPrime` is a leaf, not in the closure of SFABTZ/SFALine/SFAMassiveLine/MeasuresManifolds; import it explicitly for the existence forms (T-ett-singular-sfa).
