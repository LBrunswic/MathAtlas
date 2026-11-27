---
id: 0301
title: Re-conjoining a separation: obtain, not a term-mode let-destructure
kind: pitfall
created: 2026-11-27
---
Destructuring a long conjunction in term mode (`let ⟨h₀, …, h₁₀⟩ := thm; ⟨…⟩`, kb/0276's pattern) compiles to an auxiliary `match_1_1` whose kernel check took 6.2 s at `timeCylinder 0`; `by obtain ⟨…⟩ := thm; exact ⟨…⟩` took 1.2 s for the whole module (`Causal.Model.TimeCylinderLSC`). To find the slow declaration and its phase, run `lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=300 <file>`; plain `-Dprofiler=true` gives only the cumulative times.
