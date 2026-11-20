---
id: 0009
title: At this pin: lintegral_finsetSum, zero_le, and the ∞ of open scoped ContDiff
kind: pitfall
created: 2026-11-20
---
Found by T-egf-backward-policy. `zero_le` takes no explicit argument; `lintegral_finset_sum` is deprecated for `lintegral_finsetSum`, and rewriting with `lintegral_finsetSum _ h` fails unless `h` is a `have` with the exact summand. `open scoped ContDiff` makes `∞` ambiguous with `ℝ≥0∞`: write a Diffeomorph's smoothness index as `WithTop ℕ∞` and open only `Manifold`.
