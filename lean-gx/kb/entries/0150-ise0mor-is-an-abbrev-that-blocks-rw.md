---
id: 0150
title: IsE0Mor is an abbrev that blocks rw
kind: pitfall
created: 2026-11-27
---
Found by T-btz-embeddings. IsE0Mor is an abbrev that blocks rw: to use StructureGroupoid.liftPropOn_univ, first `show ChartedSpace.LiftPropOn e0Groupoid.IsLocalStructomorphWithinAt f univ`; the inclusion of an Opens is (StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp e0Groupoid).liftProp_subtype_val.
