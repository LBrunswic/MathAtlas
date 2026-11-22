---
id: 0233
title: Pullback preserves gluing along open maps only
kind: pattern
created: 2026-11-22
---
`Causality.pullback` preserves gluing along open maps (`pullback_absolutelyMinimalOn_all`, step `pullLink_refine`); along the continuous non-open bijection `Bool → Prop` it does not (`sierpinski_pullback_not_absolutelyMinimal`). Every precausality on Sierpiński space is hereditarily minimal (`Precausality.absolutelyMinimalOn_prop`). Lowering a chain through a map: `GluingGeneric.transGen_of_image` (injectivity only in the step).
