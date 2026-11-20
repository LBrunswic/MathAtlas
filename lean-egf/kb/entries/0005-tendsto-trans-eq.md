---
id: 0005
title: `h.trans_eq` on a Tendsto resolves to LE.le.trans_eq
kind: pitfall
created: 2026-11-20
---
Found by T-egf-headline. `Tendsto f l l'` unfolds to a map-le, so `h.trans_eq e` elaborates as `LE.le.trans_eq` and fails or proves the wrong thing. Rewrite the limit with `simpa using` instead.
