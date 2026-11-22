---
id: 0231
title: Proving a concrete causality glues hereditarily: three routes
kind: pattern
created: 2026-11-22
---
(1) causal arc-connectedness (`Causal.GluingModels.forall_of_causallyArcConnected`); (2) a chain of an absolutely minimal neighbour avoiding the bad points (the cut line: a timelike chain whose right ends avoid `a`, the step across `a` taken in one member of the cover); (3) subdividing a segment by `exists_subdivision_Icc` (spokes, `galileo 0`). The restriction to an open `W` as a spacetime is `(C.restrict W).toSubtype`, whose absolute minimality on `V'` is `C.AbsolutelyMinimalOn (imageOpens V')` (`LocalCausality.toSubtype_absolutelyMinimalOn_iff`); `C.relativeTo W` is another object (diagonal outside `W`).
