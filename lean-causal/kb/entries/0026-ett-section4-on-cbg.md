---
id: 0026
title: ETT §4 is stated through the CBG library, via CommonSubDev
kind: pattern
created: 2026-11-20
---
ETT §4's setting (a common sub-extension N with j₁, j₂, f = j₂∘j₁⁻¹, and the literal set C of
non-separated pairs) maps onto Sbierski's CGHD setting of `Causal.CBG` by
`CommonSubDev.cghdData`, and the literal C is the library's `Corresponds` relation
(`CommonSubDev.mem_C_iff`). State any further §4 bridge through these two, not from scratch
(`Causal/CBG/ETTSection4.lean`, T-ett-cbg-anchor).

Every morphism of CBG developments is injective (`Dev.IsMorphism.injective`, from
`Geometry.timeFunction`), so the readings of ETT's undefined "maximal Cauchy extension"
(every Cauchy embedding out is bijective / every morphism out is bijective / universal) coincide.
Rows proved this way stay partial until the E₀ instance exists (DEC-134, T-ett-port-e0).
