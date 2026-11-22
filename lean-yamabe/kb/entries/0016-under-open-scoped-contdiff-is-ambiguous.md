---
id: 0016
title: Under open scoped ContDiff, ∞ is ambiguous; defs not mentioning N need `variable (N) in`
kind: pitfall
created: 2026-11-22
---
Found by T-yamabe-analysis. Pitfall: under open scoped ContDiff, ∞ is ambiguous between ℕ∞ω and ℝ≥0∞ (write ⊤ for eLpNorm bounds); defs over ChartedSpace (EuclideanHalfSpace N) M whose type does not mention N need `variable (N) in` (IsC1 N u, IsLocallyLebesgue N μ).
