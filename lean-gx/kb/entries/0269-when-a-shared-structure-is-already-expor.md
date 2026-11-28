---
id: 0269
title: When a shared structure is already exported (here E0Surgery.LFSpears), add a missing prope
kind: pattern
created: 2026-11-28
---
Found by T-btz-g3-dedupe. When a shared structure is already exported (here E0Surgery.LFSpears), add a missing property as a hypothesis of the few lemmas that use it (hcovers) rather than as a field: a field retypes the structure and its constructor, a hypothesis retypes nothing, and each family passes its own field (`Dat.covers`).
