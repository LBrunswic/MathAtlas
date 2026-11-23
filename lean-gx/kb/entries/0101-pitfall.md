---
id: 0101
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-quotient-circle. Pitfall: Quotient.lift on Orbits G M (= Quotient (MulAction.orbitRel G M), an explicit setoid) needs `letI : Setoid M := MulAction.orbitRel G M` for `a ≈ b` to elaborate; inside, Quotient.sound h : orbitMk G a = orbitMk G b feeds GX.exists_smul_eq_of_orbitMk_eq.
