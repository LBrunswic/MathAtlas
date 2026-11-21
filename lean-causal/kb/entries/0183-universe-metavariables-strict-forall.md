---
id: 0183
title: A strict theorem quantifying ∀ {M : Type u}, used as a term, needs its universe explicit
kind: pitfall
created: 2026-11-21
---
`Causal.tarentin_exemples`, `Causal.lorentz_tarentin` used inside another theorem fail with « contains universe level metavariables »: write `tarentin_exemples.{u}` explicitly (T-ett-singular-rows-local).
