---
id: 0224
title: A forward rule that grows its term needs an aesop rule pattern
kind: pattern
created: 2026-11-22
---
A forward rule that grows its term (`C.P → C.dual.P`) loops in aesop, whose deduplication compares types up to reducible transparency (`Causality.dual` is not reducible, so `C.dual.dual.P` is not `C.P`): guard it with a rule pattern on the grown subterm, so it fires only where that subterm already occurs. A guard class with an `outParam` also terminates but makes every call pay (40% slower on `Test.lean`) (T-tac-ladder-dual).
