---
id: 0097
title: A quotient circle J/⟨f⟩ is GX.exists_gxQuotientCircle
kind: pattern
created: 2026-11-23
---
Found by T-bbs-quotient-circle. A quotient circle J/<f> (J an interval, f an increasing homeomorphism of J, x < f x) is GX.exists_gxQuotientCircle: it conjugates f to s -> s + 1 by a fundamental domain psi : R -> J (GX.exists_reparam_conj_add_one: f as an Equiv.Perm J via BijOn.equiv, psi s = (F ^ floor s) (x0 + fract s * (f x0 - x0))), then builds R/Z with the structure of D o psi (GX.exists_gxQuotient_add_one: Multiplicative Z acting by GX.addIntAction through letI, GX.gxQuotient, Orbits ~ Circle by Quotient.lift RP1.proj and Equiv.toHomeomorphOfContinuousOpen).
