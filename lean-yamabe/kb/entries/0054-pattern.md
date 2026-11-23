---
id: 0054
title: pattern:
kind: pattern
created: 2026-11-23
---
Found by T-perf-main. pattern: on the model, the step u -> |u| of perforated l.458-460 is the Prop MeasuredModel.AbsLatticeApprox (scaffold Perforated/Main): nonnegative w_k with no larger energy and trace norms and ||w_k||_{p*} -> ||u||_{p*}. le_Fq_of_lattice passes to the limit with ge_of_tendsto. The exact AbsLattice implies it (constant sequence), and the C^1 reading satisfies it through w_e = sqrt(u^2+e^2) - e although |u| is not C^1. The toy model satisfies the exact form (toy_absLattice). (The C¹ instance is argued, not formalized.)
