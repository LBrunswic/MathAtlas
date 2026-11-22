---
id: 0236
title: ConstantInfo.value? misses theorem bodies without allowOpaque
kind: pitfall
created: 2026-11-22
---
In meta-scripts at this pin, `ConstantInfo.value?` returns `none` for theorems unless called with `(allowOpaque := true)`; a dependency scan that forgets it silently misses every theorem body (T-abs-gluing-models).
