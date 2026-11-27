---
id: 0248
title: Two ETT-layer re-proofs can now cite their originals
kind: pattern
created: 2026-11-23
---
`Causal.Ladder.Dual`'s `curvesExtend_dual_iff` duplicates `Causality.CurvesExtend.dual` (`Causal.CauchyExtension`), and `Causal.LadderLocal`'s `PushUp.causallyOpen_of_chronalNeighbours` duplicates `Causality.causallyOpen_of_pushUp` (`Causal.LemmaK`): both were re-proved because the originals were model-stranded, which they no longer are (T-abs-hoist-lemma-k). Merge at the next tidy. Since T-abs-hoist-dual-cover, `Causal.Ladder.Dual`'s `hasTimeFunction_dual_iff` cites `Causality.dual_hasTimeFunction`; Since T-tac-dual-has-chronal-neighbour `curvesExtend_dual_iff` cites `Causality.CurvesExtend.dual` too: Dual repeats no proof; LadderLocal's `PushUp.causallyOpen_of_chronalNeighbours` remains (T-abs-merge-stranded-duplicates).

**Update 2026-11-27 (T-abs-merge-stranded-duplicates): merged.** `Causal.LemmaK` (a leaf) imports `Causal.LadderLocal` (which does not reach it, so no cycle; LemmaK is outside `Causal.Ladder.Rules`' closure, which is unchanged) and its `Causality.causallyOpen_of_pushUp` and `causallyOpenFuture_of_pushUp` now cite `PushUp.causallyOpen_of_chronalNeighbours` and `PushUp.causallyOpenFuture_of_chronalPastNeighbours`, whose hypotheses are theirs definitionally. Both names of each pair stay, with the same types; LadderLocal gained no import. No ETT-layer proof of `push_up ⇒ causally_open` is repeated.
