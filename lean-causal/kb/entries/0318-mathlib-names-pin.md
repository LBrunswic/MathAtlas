---
id: 0318
title: Names at this pin: second countability from a countable cover, closed in a subtype, connected sets in clopen opens
kind: pitfall
created: 2026-11-28
---
At this Mathlib pin: `secondCountableTopology_of_countable_cover` is `TopologicalSpace.secondCountableTopology_of_countable_cover` (not exported by `open Topology`); `isClosed_preimage_val : IsClosed (s ↓∩ t) ↔ s ∩ closure (s ∩ t) ⊆ t` is the one-line route from "closed in `s`" to a closure inclusion; `IsPreconnected.subset_of_closure_inter_subset` puts a connected set in a relatively clopen open set (`Causal.ErsEtaleGluing`).
