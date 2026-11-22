---
id: 0230
title: Gluing has two Lean forms; which constructions keep which
kind: pattern
created: 2026-11-22
---
Gluing (DEC-167) has two Lean forms: the hereditary `∀ W, P.AbsolutelyMinimalOn W` and the M-only `P.AbsolutelyMinimal` (which the field takes is OQ-95). `Causal.GluingGeneric.*` says for each generic construction which it preserves: dual, transport, `relativeTo`, the two-space, family and agree-locally gluings and the (G,X) causality keep both; the M-only form fails exactly where an open piece becomes a space of its own (`(C.restrict W).toSubtype`, pullback along open embeddings, `chartTransport`, `ofOpens` pieces), the witness always the transparent-point line on ℝ ∖ {0}. M-only plus hereditary on the members of an open cover gives hereditary (`Causal.absolutelyMinimalOn_of_locally`, `Causal.GXStructure`), so for locally causally arc-connected causalities the two forms agree. `Causal.GluingModels.*` (T-abs-gluing-models) inventories 75 concrete causalities in both forms (campaign/T-abs-gluing-models/REPORT.json `inventory`).
