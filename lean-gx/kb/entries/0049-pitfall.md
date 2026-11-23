---
id: 0049
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-rp1-circles. Pitfall: `first | ring | linear_combination h` never reaches linear_combination, because ring falls back to ring_nf and succeeds. Use ring1.
