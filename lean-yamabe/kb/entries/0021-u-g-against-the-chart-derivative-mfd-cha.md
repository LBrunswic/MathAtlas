---
id: 0021
title: |∇u|_g against the chart derivative (Mfd.chart_comparison): give IsContinuousRiemannianBundle explicitly
kind: pattern
created: 2026-11-22
---
Found by T-yamabe-analysis (round 2). Pattern: |∇u|_g against the chart derivative (Mfd.chart_comparison): give IsContinuousRiemannianBundle explicitly as ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩ (it is not inferred under the letI RiemannianBundle), then eventually_norm_trivializationAt_lt / eventually_norm_symmL_trivializationAt_lt and TangentBundle.symmL_trivializationAt.
