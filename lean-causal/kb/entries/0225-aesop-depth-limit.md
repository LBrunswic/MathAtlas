---
id: 0225
title: aesop's depth limit counts forward steps: long conjunctions and nested reversals
kind: pitfall
created: 2026-11-22
---
Every forward step counts towards aesop's `maxRuleApplicationDepth`. `causal_ladder` runs at 60 since T-tac-ladder-integration (it was 30; `maxSafePrefixRuleApplications` 200 only bounds the expansion behind the error message after a failure, Aesop/Search/Main.lean:229, and changes no verdict). From 16 facts of `C`, goals about `C.dual.dual.dual` close; a provable `C.dual⁵` goal still stops at the depth (3.4 s) and `C.dual⁷` exceeds the heartbeats. Close long conjunctions one conjunct at a time (`⟨by causal_ladder, …⟩`); a `fail_if_success` test must fail by exhaustion, not at a limit (T-tac-ladder-dual's and T-tac-ladder-integration's audits).
