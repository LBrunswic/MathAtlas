# 0003 — The universal cover is here: grep `Benzecri.UniversalCover` before porting it again

*Found 2026-11-20 by T-bz-universal-cover; recorded by the master session.*

`Benzecri.Port.UniversalCover` is a mechanical, Mathlib-only port of lean-causal's
`Causal/Port/UniversalCover.lean` (82ee40f, itself gx's at e5a1d46): construction, covering map,
simple connectedness, universal property, uniqueness, `deckEquiv`. Deck groups as automorphism
groups: `deckAut G X π` (a `Subgroup` of `GXAut`) with `properlyDiscontinuousSMul`, `isCancelSMul`,
`compactSpace_quotient`; `isDivisible_of_isCoveringMap` turns any simply connected covering of a
compact Hausdorff (G,X)-manifold into a divisible one (`Benzecri/UniversalCoverRow.lean`).
