---
id: 0079
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-3p1-theorem-m-theta. Pitfall: with `have h1 : T := congrArg Prod.fst (h.comm z)`, the expected type T makes Lean unify f a1 = f a2 against T and fail when the right side is defeq but not syntactic, e.g. (iotaTilde w).1 against w.1. Write `have h1 := congrArg Prod.fst (h.comm z)` without a type and `exact` it.
