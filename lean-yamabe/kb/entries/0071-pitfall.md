---
id: 0071
title: pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-perf-poincare. pitfall: in rw [measure_singleton] the first singleton matched may be the μ one, which then asks for NoAtoms μ. Give measure_singleton (μ := (volume : Measure (EuclideanSpace ℝ (Fin N)))).
