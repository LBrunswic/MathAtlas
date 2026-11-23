---
id: 0095
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-psl2-normal-forms. Pitfall: `first | ring | linear_combination ...` never reaches the second branch, because `ring` that fails falls back to ring_nf with a 'Try this' and does not fail. Use `ring1`.
