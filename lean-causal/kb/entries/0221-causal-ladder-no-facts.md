---
id: 0221
title: causal_ladder's fact rules, and why CurvesExtend is not one yet
kind: pitfall
created: 2026-11-22
---
`causal_ladder` makes rules of the ladder's checked implications and, since T-tac-ladder-integration, of its checked causality-sort `[[fact]]`s: a safe apply rule under the fact's standing (it closes `P t` for any causality term once the standing instances synthesise), plus a safe forward rule with the causality's rule pattern when an emitted edge reads the property. But `curves_extend`'s rule is NOT in `Causal.Ladder.Rules`: its module `Causal.CurvesExtendSecondCountable` imports Rules through `Causal.MaximalZorn` → `Causal.ErsMughd`, and emit-lean skips it with a `-- skipped fact … cycle` line (`Causal.Ladder.Test` registers it locally to test it). Until that cycle is broken (split `Causal.AbstractDev` out of `MaximalZorn.lean`), discharge `C.CurvesExtend` by the term `Causality.curvesExtend_of_t1_secondCountable C`.
