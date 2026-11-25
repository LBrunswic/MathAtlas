---
id: 0136
title: Pitfall:
kind: pitfall
created: 2026-11-25
---
Found by T-bbs-p-p. Pitfall: with A : GammaP C.antipode.pt expected, `gammaNeg C.pt X • linkMove B hB σ` fails instance search (HSMul (GammaP (−C.pt)) (Link C.antipode.pt)); bind `let A : GammaP C.antipode.pt := gammaNeg C.pt X` and close the rewrite chain with rfl.
