# 0057 — Closing an editorial enonce by a term-mode assembly of strict lemmas

*Found 2026-11-22 by T-bz-c2-proprietes; recorded by the master session.*

An editorial enonce whose parts are already strict lemmas closes by a term-mode assembly: one theorem whose type is the conjunction, in printed order, and a refine with one anonymous-constructor component per property. Put the instance-bound data inside the conjunct (∀ (l) [Fact (l ≠ 0)] …), as SeptiemeProprietePrinted does. Then a 'Printed' def with the same shape is refuted by projecting one conjunct (.2.2.2.2.2.2) and reusing the existing per-property refutation.
