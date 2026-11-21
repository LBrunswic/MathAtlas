---
id: 0095
title: Universe order, and tools/ladder.py's parser
kind: pitfall
created: 2026-11-21
---
a def's universe parameters come in the order of the `universe` command, so declare first the universe a statement must name (`universe v u w`, then `ChainsInherit.{v} mor`); do not write `def foo.{v, u, w}`: tools/ladder.py's DECL_FQ reads its name as `foo.` and the declaration never resolves for binders (T-abs-maximal-zorn).
