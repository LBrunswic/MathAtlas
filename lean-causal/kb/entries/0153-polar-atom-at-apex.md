---
id: 0153
title: Pushing a measure by Cone.polar puts an atom at the apex
kind: pitfall
created: 2026-11-21
---
`Cone.polar` sends `r ≤ 0` to the apex, so the image of a measure on `ℝ × ℝ/κℤ` positive on open sets has an atom there (`Causal.MeasuresEAlpha.map_polar_apex_pos`), its product with `dt` charges the singular line, and it leaves the class of `λ₃` (`not_absolutelyContinuous_map_polar`). Restrict `r` to `]0, ∞[` and prove positivity on open sets by hand: a ball about `mk ⟨r, θ⟩` contains `polar(r + ε/2, θ)` (`coneMeasure_pos`) (T-ett-measures-ealpha).
