---
id: 0203
title: E₀'s τ-translation as a mathlib Flow, causal and null
kind: pattern
created: 2026-11-22
---
`Causal.SingularRowsSplitting.tauFlow` (`tauFlow t x = (x.1 + t, x.2)` by rfl) is a causal flow (`isCausalFlow_tauFlow`): orbits are curves through `E0.curveOn_of_continuousOn` and `E0.causalCurveOn_of_curveOn`, Le from `E0.le_iff_closed` at equal angles, inextensibility from `IsCausalFlow.of_causalCurveIn` (`inextensible_of_flow`). It is null (`not_lt_tauFlow`); `vecteurFlow_e0` is a VecteurFlow at E₀ and `tauFlow_split` splits E₀ along every Cauchy surface (T-ett-geroch-split-flow).
