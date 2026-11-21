---
id: 0083
title: Narrowing a moved declaration's imports can change its proof term
kind: pitfall
created: 2026-11-21
---
A verbatim move into a module with a smaller import closure can elaborate to a different proof
term of the same type, because instance search takes another path (T-abs-hoist-levin:
`exists_timeFunction_of_secondCountable` differed until `Mathlib.Topology.Compactness.Paracompact`
was imported). A hoist's check compares proof terms as well as types (kb/0063); when one differs,
re-elaborate the old text in the old closure to attribute it, and add the import that restores the
old instance path.
