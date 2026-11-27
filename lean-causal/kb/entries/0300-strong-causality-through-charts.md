---
id: 0300
title: Strong causality through charts: ChartIso carries StronglyCausalOn
kind: pattern
created: 2026-11-27
---
`Causal.ChartIso.stronglyCausalOn_iff` (`Causal.StronglyCausalTransport`, ETT layer) says that `W ≤ chartSource e` is strongly causal as a spacetime iff `chartImage e W` is. `Causality.locallyStronglyCausal_of_chartIso`: chart-isomorphic near each point to locally strongly causal models gives `LocallyStronglyCausal`; for a model chart use `…_of_forall_chartIso_of_stronglyCausal` with the model's `StronglyCausal`. Every flat spacetime is locally strongly causal (`Causal.Flat.flatCausality_locallyStronglyCausal`, `Causal.Model.TimeCylinderLSC`), so the flat time cylinder is locally strongly causal and not strongly causal. The node is invariant under causal isomorphisms (`IsCausalIso.locallyStronglyCausal_iff`).
