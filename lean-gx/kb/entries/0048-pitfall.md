---
id: 0048
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-rp1-circles. Pitfall: Circle's topology instance is not syntactically the subtype topology, so Topology.IsInducing.subtypeVal does not rewrite against it. Use GX.RP1.isInducing_coe, which is stated with @ and instTopologicalSpaceCircle.
