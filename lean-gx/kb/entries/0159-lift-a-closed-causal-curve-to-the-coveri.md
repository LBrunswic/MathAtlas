---
id: 0159
title: Lift a closed causal curve to the covering when no invariant time function exists
kind: pattern
created: 2026-11-27
---
Found by T-bbs-hcausal-tachyons. To exclude CCCs where no Gamma_p-invariant time function exists, lift the curve to the covering. GX.GammaLinkCircle.DevData.exists_lift_curve_periodic gives (s, t) with s(r+1) = s(r) + n, and eventually_chart_lift reads every cone chart along it as g . arcPt p (vlift s) t. Then use GX.GammaLinkCircle.DevData.not_hasCCC_of_future_past, which needs only a future and a past time-like direction in the developed image.
