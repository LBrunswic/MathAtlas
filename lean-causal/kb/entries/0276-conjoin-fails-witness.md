---
id: 0276
title: Conjoin a node into a recorded separation, and simulate the re-pointing first
kind: pattern
created: 2026-11-23
---
To make one declaration the witness of a ladder [[fails]] entry whose node was split off, destructure the old separation and rebuild it with the node's lemma inserted: `let ⟨h₁, …, hₙ⟩ := old_separates; ⟨h₁, …, hₙ, node⟩` (Causal/ChronalNeighbourConjoined.lean: `notchedCausality_separates_hasChronalNeighbour`, `globalLine_separates_hasChronalNeighbour`). Before proposing new `from` ids, simulate in memory: `copy.deepcopy(ladder.load())`, edit the entries, then compare `ladder.matrix` and `ladder._contradictions` before and after. The ladder resolves witness names in `Causal/` only, so the re-pointing waits for graduation.
