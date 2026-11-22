---
id: 0027
title: Typechecking new modules through /tmp oleans: symlink the existing scaffold oleans into /tmp (refines 0019)
kind: pattern
created: 2026-11-22
---
Found by T-yamabe-analysis (round 2). Refines kb 0019: once /tmp/X/YamabeScaffold exists on LEAN_PATH, Lean looks for every YamabeScaffold module there; symlink the round-1 .lake oleans (Basic, Sobolev, Trace, Rellich, External) into /tmp/X/YamabeScaffold first.
