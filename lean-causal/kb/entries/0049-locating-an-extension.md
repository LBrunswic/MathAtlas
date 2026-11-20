---
id: 0049
title: Locating an extension is a characterisation, and needs a chronal neighbour
kind: pattern
created: 2026-11-20
---
Under causal arc-connectedness a chronal curve leaves an open `O` iff some boundary point of `O`
has a chronal neighbour (`Causality.futureBoundary_union_pastBoundary_nonempty_iff`), and a future
one iff `I⁺(O) ⊄ O` (`futureBoundary_nonempty_iff`); the first exit is
`ChronalCurveOn.exists_firstExit`. Without the localisation hypothesis `HasChronalNeighbour` the
Lorentzian lemma (Sbierski 1507.00601 Lemma 2.17) fails in ETT (`not_exists_leaving_bare`). Also:
under causal arc-connectedness, `p ∈ Z⁺` iff `I⁺(p)` is non-empty with no separation axiom
(`CausallyArcConnected.mem_Zplus_iff`; `AbsolutelyMinimal.mem_Zplus_iff` asks T1)
(`Causal.LocateExtension`, T-abs-locate-extension).
