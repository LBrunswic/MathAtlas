---
id: 0099
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-quotient-circle. Pitfall: mem_connectedComponentIn hx0 with hx0 : x0 < f x0 elaborates with F := Real.lt x0 (a set as a predicate) and x := f x0; ascribe (show x0 in {x | x < f x} from hx0) and pass the set explicitly (J := connectedComponentIn {x | x < f x} x0).
