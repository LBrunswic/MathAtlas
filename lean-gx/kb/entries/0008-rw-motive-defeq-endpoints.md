---
id: 0008
title: rw fails on paths whose endpoints are defeq but not syntactic
kind: pitfall
created: 2026-11-20
---
`rw` fails ("motive is not type correct", at instances transparency) when path endpoints are
definitionally but not syntactically equal (`D.x₀` vs a named point, `↑⟨q, h⟩` vs `q`). State
restrictions with syntactic endpoints (a dedicated restriction def, cf. `GX.grifSub`), chain
equalities with `Eq.trans` / `refine` instead of `rw`, and push `Subtype.val` through
`Path.trans_apply` with `apply_dite Subtype.val` before `split_ifs` (T-gx-slsc-compact).
