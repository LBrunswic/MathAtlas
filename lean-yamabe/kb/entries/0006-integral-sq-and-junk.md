---
id: 0006
title: ∫ f² as a squared L² norm; absorbing a junk Bochner integral
kind: pattern
created: 2026-11-21
---
Found by T-yamabe-kobayashi. ∫ f² = (eLpNorm f 2 ν).toReal² for f ∈ L² (`Yamabe.integral_sq_eq_normSq`, from `MemLp.eLpNorm_eq_integral_rpow_norm`); an L^{p*} function is in L² on a finite measure (`Yamabe.memLp_two_of_pStar`, `MemLp.mono_exponent`). A junk Bochner integral (non-integrable integrand = 0) is absorbed by a `by_cases` on integrability; state `integrable_…` lemmas so that the integrals in a law are genuine.
