---
id: 0266
title: ERS Thm 4.75 on second countable backgrounds
kind: pattern
created: 2026-11-23
---
`Causal.Ers475CauchyForm`: `IsCauchyLocalDevelopment` is `IsLocalDevelopment` less its `acausal` and `split` fields; `ers_theorem_4_75(_eqOn)_secondCountable` with it are at least as strong as the originals on second countable spaces (the original follows by `fun i => (hdev i).isCauchyLocalDevelopment`), not siblings. `maxDevelopmentIn_eq`, `ers_theorem_4_64_in`, `isDevelopmentIn_maxDevelopmentIn`, `isDevelopmentIn_localDevelopmentUnion` and `ers_prop_4_63` get `…_of_isCauchySurfaceOn_secondCountable` siblings (kb/0226). `IsCauchySurfaceOn.of_inter_eq`: `S'` Cauchy in `W` and `S ∩ W = S' ∩ W` give `S` Cauchy in `W`; its twin `Causal.CBG.isCauchySurfaceOn_congr'` is model-stranded in `Causal.Flat.CBGSlice` (kb/0061).
