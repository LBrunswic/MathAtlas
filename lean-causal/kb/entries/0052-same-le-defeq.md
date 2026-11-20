---
id: 0052
title: Two causalities with the same ≤ share J, diamonds, causal openness and GH by defeq
kind: pattern
created: 2026-11-20
---
The lightlike and timelike lines have the same causal relation, so every property that reads only
≤ transfers by definitional equality: `lightlikeLine_globallyHyperbolic := timelikeLine_globallyHyperbolic`,
`lightlikeLine_causallyOpen`, and `(timelikeLine_tarentin : lightlikeLine.Tarentin)` — but
`lightlikeLine_tarentin` already exists in the model-importing `Causal.Remarks.Tarentin`: use the
ascription in a layer-1 module, do not redeclare it (a duplicate name was caught at graduation).
A cheap way to get separating examples for properties that read ≪ (T-abs-ladder-local-defs,
T-abs-locate-extension).
