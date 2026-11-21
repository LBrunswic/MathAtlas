---
id: 0004
title: Deprecated and renamed lemmas at mathlib `fabf563a`; a deprecation is a build failure
kind: pitfall
created: 2026-09-27
---
## When
Always: the strict library compiles with `warningAsError`.

## Known at this pin
| do not write | write |
|---|---|
| `Set.diff_eq_empty` | `Set.sdiff_eq_empty` |
| `Set.diff_subset_diff_left` | `Set.sdiff_subset_sdiff_left` |
| `Set.union_diff_cancel` | `Set.union_sdiff_cancel` |
| `measure_diff_null` | `measure_sdiff_null` |
| `div_lt_iff` / `lt_div_iff` | `div_lt_iff₀` / `lt_div_iff₀` |
| `push_neg` (a deprecation warning, so a strict build failure) | `push Not` |

`nhdsWithin_inter_of_mem : s ∈ 𝓝[t] a → 𝓝[s ∩ t] a = 𝓝[t] a`; the primed version keeps `s`.
A definition whose type is a class (`TopologicalSpace M`) must be `@[reducible]`.

## Do
Search the pinned sources, never memory:
`grep -rn "theorem name" .lake/packages/mathlib/Mathlib/`.
