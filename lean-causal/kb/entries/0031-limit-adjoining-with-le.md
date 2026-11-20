---
id: 0031
title: Adjoining a curve's limit point needs only p ≤ c t, not closed pasts
kind: pattern
created: 2026-11-20
---
The library's limit-adjoining lemmas (`causalCurveIn_insert`, `extensible_of_tendsto`,
`Inextensible.not_tendsto_at*`) use the closedness of J⁻(x) only to get p ≤ c t. The `*_of_le`
versions in `Causal.LimitCurves` take that fact as the hypothesis; use them when pasts are not
closed (T-ett-geroch-iii-i).
