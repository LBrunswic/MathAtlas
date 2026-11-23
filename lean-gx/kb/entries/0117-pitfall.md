---
id: 0117
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-hs-link-types. Pitfall: `(hS hx : 0 < _).ne' h0` leaves `?m = 0` unsolved. Write `(show 0 < Q (dsProj p σ) from hS hx).ne' h0`. Likewise, membership in {σ | 0 ≤ nullPairing p σ} needs a `show` before `not_le.2`.
