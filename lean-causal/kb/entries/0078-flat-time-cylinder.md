---
id: 0078
title: The flat time cylinder: an absolutely minimal ETT spacetime with every local ladder property and ≪ total
kind: pattern
created: 2026-11-21
---
`Causal.Flat.TimeCylinder d` (ℤe₀\𝐌ⁿ, causality `timeCylinder d`, `Causal.Model.FlatTimeCylinder`) is
T2, second countable, connected, with curves_extend, absolutely_minimal, causally_arc_connected,
push_up, tarentin, chronal_neighbours, causally_open and causally_plain, each stated as the ladder's
own definition, and `≪_M` total (`timeCylinder_lt_top`): not causal, not strongly causal, no time
function, not GH. Every diamond is the whole cylinder, so causal compactness is compactness:
false for d ≥ 1, true for d = 0, the timelike circle (`timeCylinder_causallyCompact_iff`). Being
absolutely minimal (on every open set), its separations into is_causal and below hold in either
reading of `defi:causalite` (OQ-18) (`timeCylinder_separates`, `timeCylinder_zero_separates`).
Every flat-model module reaches `Causal.Port.GXBasic`, `.UniversalCover`, `.Developing` through
`Causal.Flat.Developing`; a "no Port" rule for a model module can only mean direct imports, or no
`Causal.Port.E0*` (T-loc-flat-time-cylinder).
