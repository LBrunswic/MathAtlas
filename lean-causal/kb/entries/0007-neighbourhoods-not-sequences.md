---
id: 0007
title: Second countability is almost never needed: argue on neighbourhoods and directed families
kind: pattern
created: 2026-09-27
---
## When
The paper says "since `M` is second countable it suffices to show sequential closedness", or
takes a decreasing sequence of compact sets.

## Do
* Closedness: `isClosed_of_closure_subset`, then `mem_closure_iff_nhds`.
* A decreasing sequence of compact sets: a directed family and
  `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`.
* A compact set covered by an increasing family of open sets: `IsCompact.elim_directed_cover`.
* Sequences are needed where the definition has them (`K^±`): ask `FirstCountableTopology M`.

## Why
`prop:relation_fermee`, `prop:GH_Jferme`, `prop:GH_fortement_causal` hold without any
countability. Record the dropped hypothesis as `⚠ weakened`.
