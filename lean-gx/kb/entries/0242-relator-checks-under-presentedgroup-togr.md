---
id: 0242
title: Relator checks under PresentedGroup.toGroup
kind: pattern
created: 2026-11-28
---
Found by T-btz-surface-group-nonmetabelian. Relator checks under PresentedGroup.toGroup: rewrite FreeGroup.lift of the relator into List.ofFn products, simp [List.ofFn_succ, the generator map, Fin.succ_ne_zero, i.succ.succ != 1 lemmas], then simp only [commutatorElement_def]; group. Avoid Fin.ext_iff in that simp (it loops on the if-chain definitions).
