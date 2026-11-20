---
id: 0045
title: Inextensibility is not monotone under nesting
kind: pitfall
created: 2026-11-20
---
`LeNested C C'` (every ≤_U of C is one of C') does not make C-inextensible curves C'-inextensible:
ETT's inextensibility is by extension, and a point with no C-past ends a C-inextensible curve
that C' extends. Ask `InextensibleNestedOn`, or derive it on M with
`Causality.inextensibleNestedOn_top` (C arc-connected, causal, strongly causal, closed J^±, no
endpoints) (`Causal.NestedCausalities`, T-abs-nested-causalities; OQ-41 (b)).
