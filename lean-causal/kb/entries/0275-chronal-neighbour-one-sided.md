---
id: 0275
title: has_chronal_neighbour from one-sided neighbours, and from Z⁺ at E₀
kind: pattern
created: 2026-11-23
---
`Causality.ChronalPastNeighbours.hasChronalNeighbourEverywhere` and `ChronalFutureNeighbours.hasChronalNeighbourEverywhere` (point forms `.hasChronalNeighbour`; Causal/ChronalNeighbourConjoined.lean) give the node from the one-sided notions, which are no nodes: `causal_ladder` does not derive it from them, but carries it across `C.dual`. On singular flat spacetimes the node is the future disjunct, from the field `mem_Zplus` with `U = M` through `Causality.hasChronalNeighbourEverywhere_of_forall_mem_Zplus` (Causal/ChronalNeighbourBridge.lean) (`SingularFlatAxioms.hasChronalNeighbourEverywhere`, `E0.hasChronalNeighbourEverywhere`, `SFALocal.hasChronalNeighbourEverywhere` under `IsoChartsCoverDEC25` alone; Causal/Model/E0ChronalNeighbour.lean); the past disjunct holds iff `p ∉ sing₀`, which at a manifold needs absolute minimality (kb/0135). `LocZplus D ⇒ D.ChronalFutureNeighbours` is `E0LM.LocZplus.chronalFutureNeighbours` (Causal/CausallyPlainLocZ.lean; `h.chronalFutureNeighbours`), the one line `fun V v hv => h V v hv V (V.isOpen.mem_nhds hv)`; the E₀ module cites both lemmas (T-abs-hoist-stranded-homes).
