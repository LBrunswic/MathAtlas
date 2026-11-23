# Sbierski, *C⁰-inextendibility of Schwarzschild and the spacelike diameter* (arXiv 1507.00601) — a reading map, not a story

*An external paper (arXiv 1507.00601 v2, J. Differential Geom. 108, 2018), ledgered for the ETT
programme as Barbot's was by DEC-34 and Sbierski's dezornification as `papers/sbierski-mghd`. There
is nothing to retell: this file names what reading and formalizing it is for, so the gates can
count it. Its Lean home is `lean-causal`; its binder (`certificate/binder.toml`, target
T-bind-sbierski-schwarzschild) will split every row into the three layers of
`programme/README.md`.*

## Objective

Show that Minkowski space and the maximal analytic Schwarzschild spacetime admit no extension
with a merely continuous metric, and isolate which steps of that argument are causal topology
(layer 1 of the programme) and which need the metric (layer 3).

## S-sbierski-schwarzschild-1 Causality for continuous metrics

Timelike curves, their directions and extendibility, Cauchy hypersurfaces, timelike homotopy and
timelike separation are set up for continuous metrics (`schwdef:timelike_curve`,
`schwdef:future_past_extendible`, `schwdef:cauchy_hypersurface`,
`schwdef:timelike_homotopic_fixed_endpoints`, `schwdef:timelike_separated_set`), with the one
causal input the argument needs: chronological futures are open (`schwprop:FutureOpen`,
`schwprop:UnionPasts`), and near-Minkowskian charts (`schwlem:NormalForm`, `schwprop:FlowChart`).

## S-sbierski-schwarzschild-2 Locating an extension

A continuous extension is found along a timelike curve that leaves the original manifold
(`schwlem:ExtensionLemma`, Lemma 2.17). In the programme this is the layer-1 step whose
localisation property is a chronal neighbour at frontier points (DEC-159), and Minkowski's
inextendibility (`schwthm:MinkInex`) is its first use.

## S-sbierski-schwarzschild-3 Schwarzschild and the spacelike diameter

The exterior is handled by future one-connectedness and the divergence of the timelike diameter
(`schwthm:Exterior`, `schwprop:ExtFutCon`, `schwprop:LengthToInfty`), the interior by a new
invariant, the spacelike diameter, finite under regular flow charts (`schwdef:spacelike_diameter`,
`schwdef:DefRegFlowChart`, `schwthm:DiamFinite`) and infinite near the singularity
(`schwthm:Inex`, `schwprop:IntFutCon`, `schwlem:BoundsOnReach`); together they give the main
theorem (`schwthm:MainThm`). These steps are metric and belong to layer 3.
