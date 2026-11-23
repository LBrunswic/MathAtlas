---
id: 0090
title: The toPSL bridge for a lift of ρ ∈ Γ_p: toPSL f = pslMk (gammaToSL θ ρ)
kind: pattern
created: 2026-11-23
---
Found by T-bbs-gammap-elements. From a lift f with linkCover (f t) = ρ • linkCover t to toPSL f = pslMk (gammaToSL θ ρ): GTilde.toPSL_eq_iff.2 fun t => by rw [← linkToRP1_linkCover, hρf, linkToRP1_smul, linkToRP1_linkCover]. pslMk (gammaToSL θ ρ) = 1 iff the tangent action is ±id (GX.GammaP.pslMk_gammaToSL_eq_one_iff). A fixed point on RP1 is an eigen-ray (GX.GammaP.exists_tangent_eq_smul_of_fixed).
