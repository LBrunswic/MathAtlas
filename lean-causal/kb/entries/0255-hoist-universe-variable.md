---
id: 0255
title: A hoisted declaration under variable {M : Type*} must keep its universe parameter
kind: pitfall
created: 2026-11-23
---
Moving a declaration stated under `variable {M : Type*}` into a scope with `universe u` / `variable {M : Type u}` changes its universe parameter from `u_1` to `u`: the constant's `levelParams` and type hash change, though `#check @` (which prints fresh universe names) does not show it. Reopen a scope carrying the original variable line, e.g. a block after the module's `end Causal` (T-abs-hoist-dual-cover's `dual_hasTimeFunction`; its audit corrected the `#check` claim).
