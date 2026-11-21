---
id: 0171
title: AddCircle at this pin: explicit periods, and CompactSpace needs AddCircle.Real
kind: pitfall
created: 2026-11-21
---
The period is an explicit argument of `AddCircle.coe_zero P`, `coe_eq_zero_iff P`, `coe_add_period P t`, `coe_period` (not of `coe_add` / `coe_sub` in `rw`). `CompactSpace (AddCircle P)` needs `import Mathlib.Topology.Instances.AddCircle.Real`, not `.Defs`. A def gluing two maps with `if t ∈ D` needs `classical` (kb 0145) (T-ett-line-development).
