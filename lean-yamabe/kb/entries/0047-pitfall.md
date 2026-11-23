---
id: 0047
title: pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-perf-upper. pitfall: at this pin ENNReal.toReal_rpow reads x.toReal ^ z = (x ^ z).toReal. To turn (x ^ z).toReal into x.toReal ^ z, rewrite with ← ENNReal.toReal_rpow.
