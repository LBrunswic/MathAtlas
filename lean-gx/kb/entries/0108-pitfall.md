---
id: 0108
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-hs-suspension. Pitfall: (GammaLinkCircle.regular p).pt is p only up to delta. Instance search then fails, e.g. HSMul (GammaP p) (Link (regular p).pt). Restate the facts with explicit types first (obtain ⟨d', hd'⟩ : ∃ d' : ℝ → Link p, d' = Δ.d) and pass p explicitly to lemmas (dirOf_gammaP p, smul_arcPt p).
