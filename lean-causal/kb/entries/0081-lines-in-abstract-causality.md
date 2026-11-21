---
id: 0081
title: Straight lines in an abstract causality, and the slope-δ cone on ℝ × E
kind: pattern
created: 2026-11-21
---
A continuous ℓ : ℝ → M whose parameter is read by a continuous T, causal in W on every segment
inside W, is an inextensible causal curve of W over `connectedComponentIn (ℓ ⁻¹' W) t`
(`Causal.Causality.inextensible_connectedComponentIn`, [T2Space M]; no CurvesExtend, no antisymmetry,
nothing of C outside W); with a Cauchy surface S of W, every such line through a point of W meets S
on that piece (`IsCauchySurfaceOn.exists_mem_connectedComponentIn`). Use it when a model cone is
curve-nested in an abstract C and a line is only known C-causal inside W. It is in the ETT-layer module
`Causal.InextensiblePiece` (T-abs-hoist-inextensible-piece), with the one-sided criteria
`futureInextensible_of_isLUB_notMem` and `pastInextensible_of_isGLB_notMem`; a layer-1 module may
import it. The cone: `Causal.slopeCone E δ hδ`, the static
causality transported along (t, x) ↦ (t, δ • x); ≤ at M is ‖q.2 − p.2‖ ≤ δ(q.1 − p.1)
(`slopeCone_le_top_iff`), δ-Lipschitz graphs are its causal curves
(`slopeCone_causalCurveOn_graph`), δ ≤ 1 is ≤-nested in the static cone
(`slopeCone_leNested_staticCausality`); ERS's ℓ¹ cone is E = WithLp 1 (Fin d → ℝ). A cheap GH open set
with Cauchy surface and non-empty boundary: the Minkowski slab (`minkowski_isCauchySurfaceOn_slab`)
(T-loc-quasilinear-one-sided).
