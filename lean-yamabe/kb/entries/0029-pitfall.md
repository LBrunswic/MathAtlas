---
id: 0029
title: Pitfall:
kind: pitfall
created: 2026-11-22
---
Found by T-yamabe-rellich-criterion. Pitfall: at this pin LinearMap.range does not elaborate on a ContinuousLinearMap (it expects a →ₛₗ): write LinearMap.range T.toLinearMap; the FiniteDimensional instance on the range of a map out of a finite-dimensional space is then found (LinearMap.finiteDimensional_range).
