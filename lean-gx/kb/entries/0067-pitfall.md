---
id: 0067
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-photon-circles. Pitfall: inside namespace GX.IsPhotonCircle (any structure namespace reusing a GX name), exists_hasLiftedHolonomy resolves to the theorem being declared and fails as non-terminating recursion. Write GX.exists_hasLiftedHolonomy (compare kb/0046).
