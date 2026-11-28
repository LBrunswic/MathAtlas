---
id: 0331
title: A combining macron is not an identifier character
kind: pitfall
created: 2026-11-28
---
A combining macron is not an identifier character: `obtain ⟨t̄, …⟩` fails with a bare "expected token" at the binder. Write `tb` (`Causal.FlrwTypeClosedAmbient`).
