---
id: 0003
title: `induction h` on `TransGen` rewrites every hypothesis mentioning the endpoint
kind: pitfall
created: 2026-09-27
---
## When
`induction h with` on `h : Relation.TransGen r a b`, with another hypothesis about `a` or `b` in
context (typically the one `h` was derived from).

## Symptom
The induction hypothesis comes out as an implication (`C.le V z b → …`) and the step fails with
an application type mismatch.

## Do
`clear` the hypothesis before `induction` (or `revert` it on purpose). For induction from the
head use `induction h using Relation.TransGen.head_induction_on with | single hl => … |
@head a' c' hl _ ih => …`: name the implicit points, a bare `_` for them cannot be synthesized.
