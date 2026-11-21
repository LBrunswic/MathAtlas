---
id: 0113
title: A causality carried by a family of arcs (arcCausality)
kind: pattern
created: 2026-11-21
---
A causality carried by a family of arcs (Causal.arcCausality γ, Causal.GHWithoutTarentin): x ≤_U y iff x = y ∈ U or a TransGen chain of steps along one arc inside U, ≪ empty; for any continuous arcs it is causally arc-connected and absolutely minimal on every open set for every cover (a step is its arc by CurveOn.comp_affine, a chain by CurveOn.exists_concat). Under ArcCoherent γ (two arcs through a point reach it at the same parameter and agree before it) a chain is one step (ArcCoherent.le_iff), and it is causal, causally compact and GH, its diamonds the arc pieces (ArcCoherent.diamond_eq_image); a set convex along every arc is causally convex (ArcCoherent.causallyConvexIn); a continuous T strictly increasing along every arc is a time function (ArcCoherent.hasTimeFunction). Combs of polygonal arcs in a subspace of ℝ × ℝ (T2, second countable, a metric for free) are cheap absolutely minimal witnesses for questions on strong causality and time functions (T-abs-gh-without-tarentin).
