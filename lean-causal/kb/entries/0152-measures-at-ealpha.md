---
id: 0152
title: Measures at E_κ: the Borel σ-algebra of Cone κ is declared once, in Causal.MeasuresEAlpha
kind: pattern
created: 2026-11-21
---
`instMeasurableSpaceCone`, `instBorelSpaceCone` (`Causal.MeasuresEAlpha`): do not declare another. `λ₃` is `MeasuresEAlpha.lam3 κ = dt ⊗ coneMeasure κ`, with `coneMeasure κ = polar_*(dr on ]0, ∞[ ⊗ Haar on ℝ/κℤ)`. `ModelMeasures` at `E_κ` is `MeasuresEAlpha.modelMeasures` (`U = E_κ`, one measure `muE κ` on both sides); the paper's `U_p` form is `paper_measures_local` (T-ett-measures-ealpha).
