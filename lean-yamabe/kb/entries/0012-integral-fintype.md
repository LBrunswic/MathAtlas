---
id: 0012
title: Pitfall: integral_fintype's only explicit argument at this pin is the integrability
kind: pitfall
created: 2026-11-21
---
Found by T-yamabe-negative. After `rw [integral_fintype]`, close the side goal with `.of_finite`.
