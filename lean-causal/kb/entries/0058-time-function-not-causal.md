---
id: 0058
title: An ETT time function does not make a causality causal; strict increase does
kind: pitfall
created: 2026-11-20
---
ETT's `IsTimeFunction` (`defi:fonction_temps`) is only non-decreasing along ≤, and does not imply
`IsCausal`: the doubled line ℝ × Bool with `Prod.fst` (`doubledLine`,
`exists_isTimeFunction_not_isCausal`). A function strictly increasing along ≤ does, with no
continuity and any preorder codomain (`Causality.isCausal_of_timeFunction`). So "a global time
function ⇒ stably causal" (ERS 3.29) binds to the ladder node `time_function` (strict), not to
ETT's time function (`Causal.CausalIsoInvariance`, T-abs-causal-iso-invariance).
