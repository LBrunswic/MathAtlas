---
id: 0212
title: CurvesExtend gives only image containment, never an extension of the parametrised curve
kind: pitfall
created: 2026-11-22
---
`CurvesExtend` (and `exists_inextensible_of_t1_secondCountable`) give c(I) ⊆ γ(J), not an extension over J ⊇ I with γ = c on I. A strict extension of a curve with constant pieces needs the time-graph curve (`exists_inextensible_of_timeFunction`, T ∘ γ = id) and `Causality.extensible_of_timeGraph_future` / `_past` (ported from lean-gx). Past-set lemma: `Causality.isCauchySurfaceOn_of_isPast` (T-ett-cauchy-ext-e0).
