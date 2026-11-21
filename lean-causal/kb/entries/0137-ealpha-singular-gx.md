---
id: 0137
title: E_κ as a singular (G,X)-manifold: Causal.EAlphaGX.singularGX κ
kind: pattern
created: 2026-11-21
---
`Causal.EAlphaGX.singularGX κ` (a noncomputable abbrev; make it a local instance) is the maximal a.e. atlas of the disc charts, for every `κ > 0`. `Reg = regPart` and `Sing = singLine` for `κ ≠ 2π` (`reg_eq`, `sing_eq`); `Reg = univ` and `Sing = ∅` at `2π` (`reg_eq_univ_two_pi`). DEC-25's `hreg` at every `κ` is `EAlphaGX.chartIso_of_mem_aeAtlas`, and for the family `{κ // 0 < κ}` it is `hreg_family` over the local instance `singularGXFamily`. To package with E₀ into `MassAModel`, case on `o` in a module importing both (T-ett-ealpha-gx-structure).
