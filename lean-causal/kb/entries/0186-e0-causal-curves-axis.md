---
id: 0186
title: A causal curve of E₀ into a BTZ point stays on the axis and cannot jump over an axis point
kind: pattern
created: 2026-11-21
---
Its τ is continuous (`CurveOn.continuousOn`), so by `intermediate_value_Icc` it hits the axis point at any intermediate τ: this is how to show `¬ E0.causality.le W x p` when `W` omits an axis point between them (`CupCapBTZCounterexample.not_le_pE_of_fst_nonpos`). The printed strongly causal `lem:cup_cap_BTZ` is refuted at E₀ ∖ {w} (`not_cupCapBTZAsPrinted`) (T-ett-cupcap-btz-cex).
