---
id: 0020
title: Model spaces are static spacetimes over a geodesic space
kind: pattern
created: 2026-10-30
---
`staticCausality X` (`Causal/Static.lean`) on ℝ × X, for `X` a `GeodesicSpace`, is the paper's
curve-defined causality (`defi:causal_Ealpha`): `≤_U` by graphs of 1-Lipschitz maps inside `U`,
`≪_U` by `c`-Lipschitz ones, `c < 1`. It carries every library property (absolutely minimal,
push-up in every open set, tarentin, strongly causal, globally hyperbolic when `X` is proper,
`J = cl I`). Minkowski is `staticCausality (EuclideanSpace ℝ (Fin n))` (`Causal/Minkowski.lean`);
`E_α`, `α > 0`, is `staticCausality (Cone α)` (`Causal/Model/`). Cheap LOCAL counterexamples are
static spacetimes over a non-complete or non-proper `X`: the half-plane ℝ × ]0,∞[
(`geodesicSpace_Ioi_zero`), and ℝ × C([0,1], ℝ) when second countability is required — not
ℝ × (ℕ →ᵇ ℝ), which is not second countable (the paper's spacetimes are, l.255).
Techniques: past from future by the time flip (`flipT`); push-up by re-timing inside a thickening
(`IsCompact.exists_thickening_subset_open`).
