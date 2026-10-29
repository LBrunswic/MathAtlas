---
id: 0010
title: `h.foo` fails when the type of `h` unfolds to a `∀`
kind: pitfall
created: 2026-09-27
---
## Symptom
`Invalid field … The environment does not contain Function.foo` on `h : C.AbsolutelyMinimal`.

## Do
Call the theorem by name: `AbsolutelyMinimal.mem_Zplus_iff h`. Likewise an implicit cover
hypothesis of `generated` cannot be inferred from the goal: pass `(hU := hcover)`.
