---
id: 0023
title: Maximal chains of the causal order, and abstract Section 4
kind: pattern
created: 2026-10-30
---
Causal completeness (DEC-21) is about `IsMaxChain (C.le ⊤) S`; `isMaxChain_iff_comparableClosed`
says it is "every point comparable to all of S lies in S", and in a causal spacetime the author's
literal cut wording gives the same completeness (`Causal/ChainsOrder.lean`). Least upper bounds
of chains in a causally compact T2 spacetime come from a nested family of compact diamonds.
Section 4 abstractly: `IsEMorphism` = strong morphism ∧ local isomorphism (DEC-17); rigidity
(`rem:CBG_analytique`) does not follow from it (`timelikeLine_not_isRigid`) and is a named
hypothesis; the component of an inextensible curve in an open set is inextensible there
(`inextensible_ordConnectedComponent`, needs M causal).
