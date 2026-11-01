---
id: 0025
title: A scaffold module not imported by the scaffold root is invisible to the axiom sweep
kind: pitfall
created: 2026-11-01
---
`make check`'s axiom sweep (`scripts/AxiomSweep.lean`) and `lake build CausalScaffold` see only what
`scaffold/CausalScaffold.lean` (and `Causal.lean`) import. Until 2026-11-01 the scaffold root imported
the 5 ETT modules only, so no Barbot module (`CausalScaffold.Flat.*`, `Port.*`, `Splitting`,
`CurvesExtend`, `CompactCauchy`) had ever been swept: every "axiom-clean" claim rested on an agent's
own `#print axioms`. Rule: a new scaffold module is added to the scaffold root in the commit that
creates it (the master does it — authors may not edit the root), and graduation adds it to
`Causal.lean`. `lake env lean` on a single file proves nothing about the sweep.
