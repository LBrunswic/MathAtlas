---
id: 0223
title: causal_ladder across time reversal (Rules imports Dual)
kind: pattern
created: 2026-11-22
---
`Causal.Ladder.Rules` imports `Causal.Ladder.Dual` (T-tac-ladder-integration), so for every user `causal_ladder` closes a goal about `C.dual` from facts about `C` and conversely: the two-sided nodes are transported both ways, and the past forms of the one-sided nodes come from the generated rules firing on `C.dual`. Transport fires only where a `C.dual` occurs in the goal or a hypothesis (aesop rule pattern `Causality.dual C`); one-sided facts are never transported (DEC-163). This makes kb/0091's `dual_*` transport `have`s unnecessary (T-tac-ladder-dual).
