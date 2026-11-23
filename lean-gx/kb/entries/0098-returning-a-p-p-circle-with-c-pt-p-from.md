---
id: 0098
title: Returning a (Γ_p, ℓ(p))-circle with C.pt = p from an existential
kind: pattern
created: 2026-11-23
---
Found by T-bbs-quotient-circle. To return a (Gamma_p, l(p))-circle with C.pt = p from an existential, return its fields (cs, hcs, hL) and state (GammaLinkCircle.mk p cs hcs hL).IsDevAlong E d: D : R -> Link p then typechecks, and the consumer builds C := <p, cs, hcs, hL> with C.pt = p by rfl (GX.exists_gammaLinkCircle_quotient_of_forall_lt).
