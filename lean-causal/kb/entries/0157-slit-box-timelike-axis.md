---
id: 0157
title: The slit box at a timelike axis: work in parameter space, recover the angle mod κ′
kind: pattern
created: 2026-11-21
---
Work with `b = (t, r, θ)` and `pt b = (t, polar(r, θ))` rather than an angle function on `E_κ`; a sector chart normalized by a real representative `φ` of its centre (`rotIsom φ * chart k`, `φ = k.θ`) is the development (`Causal.BPrimeEAlpha.chart_dev`, `eventually_chart_ringIndex_pt`). A development into `E^{1,2}` fixes the target angle only mod `2π`; recover it mod `κ′` from the target sector charts (`chartAngle`) with `exists_forall_of_isPreconnected` (a locally determined, pointwise unique choice is global on a preconnected set). The stabiliser of the time axis: `isom_of_timeAxis` (`LinearMap.det_prodMap`; `linear_isometry_complex`, `Complex.det_conjAe` exclude the reflection) (T-ett-bprime-ealpha).
