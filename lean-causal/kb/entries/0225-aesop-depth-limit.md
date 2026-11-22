---
id: 0225
title: aesop's depth limit counts forward steps: long conjunctions and nested reversals
kind: pitfall
created: 2026-11-22
---
`causal_ladder` leaves aesop's `maxRuleApplicationDepth` at 30, and every forward step counts. A long conjunction closed by one call can stop at the depth once time reversal doubles the saturation (seven facts: eleven conjuncts close, twelve do not), and with nested reversals in a large context even a single provable goal can (`C.dual.dual.CausallyOpen` from 16 facts of `C`), and a refuted one can end at the depth instead of by exhaustion. Close conjuncts one at a time (`⟨by causal_ladder, …⟩`); a `fail_if_success` test must fail by exhaustion, not at a limit (T-tac-ladder-dual's audit).
