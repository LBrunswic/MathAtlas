---
id: 0240
title: lean-gx's pinned Causal did not have ACDProof / MaxUnipProof / BieberbachProof built; `lak
kind: pattern
created: 2026-11-28
---
Found by T-btz-linear-part-faithful. lean-gx's pinned Causal did not have ACDProof / MaxUnipProof / BieberbachProof built; `lake build Causal.Flat.ACDProof Causal.Flat.MaxUnipProof Causal.Flat.BieberbachProof` from lean-gx builds them (a few minutes) before any module importing them typechecks.
