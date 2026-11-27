---
id: 0303
title: Galileo's spacetime in its curve form: everything but local strong causality
kind: pattern
created: 2026-11-27
---
`Causal.galileoCurve n` (`Causal.GalileoCurveForm`) is an ETT-layer causality on `ℝ × (Fin n → ℝ)`: `≪_U` runs along continuous curves of `U` with strictly increasing time. It is causally arc-connected, absolutely minimal on every open set, push-up, causally open, tarentin, plain, with chronal neighbours, a time function and future one-connected; for `n ≥ 1` no non-empty open set is strongly causal (`galileoCurve_not_stronglyCausalOn`). `galileoCurve_separates` decides all 21 causality nodes, and is the witness of sixteen pairs `X ⇏ locally_strongly_causal` in either reading of DEC-167. It is the printed `galileo n` on convex opens (`galileoCurve_lt_iff_galileo_of_convex`) and differs from it elsewhere (`galileoCurve_ne_galileo`); what "generate" means in ETT.tex's item 4 is OQ-108's.
