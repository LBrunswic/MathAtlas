---
id: 0251
title: Checking a definition-body refactor that keeps every statement
kind: pattern
created: 2026-11-23
---
Unlike a verbatim hoist (kb/0063), a refactor of a definition's body that keeps every statement is checked by `#check @n` byte-identity on every declaration that mentions the notions (before: from HEAD's oleans, written to the campaign dir before the first edit). Expect value-hash changes in proofs whose source is unchanged (the elaborated terms embed the unfolded types) and type changes only in the definition's `eq_1` and in term-mode matchers (kb/0066); prove each redefined notion equal by `rfl` to a verbatim copy of its HEAD body (T-abs-one-sided-future-base).
