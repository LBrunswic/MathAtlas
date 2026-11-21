---
id: 0148
title: Property 3 of an admissible measure does not restrict to a causally convex open set by itself
kind: pitfall
created: 2026-11-21
---
`lem:restriction_convexe` carries property 4 to a causally convex open `V`, not bare property 3: the mass of `J⁻(q) ∖ J⁻(p)` must lie inside `V`. Prove the local form first, `0 < μ ((J⁻(q) ∖ J⁻(p)) ∩ W)` for every open `W ∋ q` (`Causal.E0.pos_past_inter`, `pos_future_inter`), then restrict with `Causal.E0.admissiblePastOn_restrict_of` / `admissibleFutureOn_restrict_of` (T-ett-measures-e0).
