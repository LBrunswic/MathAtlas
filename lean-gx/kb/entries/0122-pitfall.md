---
id: 0122
title: Pitfall:
kind: pitfall
created: 2026-11-25
---
Found by T-bbs-positive-hs-surface. Pitfall: `h₀.relate hθ hθ' h₀'` where hθ : IsOrientedTangent p θ and the circle's pt is p only up to delta (regular p, or a `mk p …` built in the proof) can hit a whnf/isDefEq timeout, because the implicit C is unified from hθ first. Pass (C := …) explicitly and restate hθ as IsOrientedTangent C.pt θ.
