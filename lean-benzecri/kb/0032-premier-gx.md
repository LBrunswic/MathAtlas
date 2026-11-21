# 0032 — Chapter 2 § 3's 1°a and 1°b for any (G, X): Benzecri.PremierGX

*Found 2026-11-21 by T-bz-c2-premier-affine; recorded by the master session.*

In `Chapter2/PremierAffine.lean`. They need only a compatible chart φ with connected source P and hmove : ∀ E, IsCompact E → ∃ g : GXAut G X M, g • E ⊆ P, plus [PreconnectedSpace M] [LocPathConnectedSpace M] [IsAnalyticAction G X]. They give the developing map equal to φ on P (`PremierGX.exists_isDeveloping_eqOn`), the injectivity of every developing map (`PremierGX.injective_of_isDeveloping`), the chart (`PremierGX.exists_chart_eqOn`) and its uniqueness (`PremierGX.eq_of_eqOn`). Feed hmove from Prop. 7 or 7′ with G := ⊤. The projective `Developpement.lean` could be rederived from them.
