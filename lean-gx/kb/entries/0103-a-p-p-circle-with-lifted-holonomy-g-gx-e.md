---
id: 0103
title: A (Γ_p, ℓ(p))-circle with lifted holonomy δ²g: GX.exists_isLiftedDev_delta_sq_mul
kind: pattern
created: 2026-11-23
---
Found by T-bbs-hs-remark-existence. A (Gamma_p, l(p))-circle with lifted holonomy delta^2 g (g a lift of A with a fixed point) is GX.exists_isLiftedDev_delta_sq_mul. It returns the fields (cs, hcs, hL) and (GammaLinkCircle.mk p cs hcs hL).IsLiftedDev theta E D (delta^(2:Z) * g), so C.pt = p by rfl. It uses exists_gammaLinkCircle_quotient_of_forall_lt with D = linkCover, hlt from sub_one_lt_apply_of_fixed, and hDf from linkCover_add_two_mul.
