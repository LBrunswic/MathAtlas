---
id: 0228
title: lake build --no-build is a dry run
kind: pattern
created: 2026-11-22
---
`lake build <Module> --no-build` exits 3 and lists the out-of-date jobs without building anything: run it before the real `lake build <Module>` to see whether upstream (Causal.*, mathlib) would be rebuilt, which CAMPAIGN.md says to stop and report.
