# 0053 — Corrected Déf. 1/1′: IsPocheAffNC / IsPocheProjNC, and how to use them

*Found 2026-11-22 by T-bz-poche-nonconstant; recorded by the master session.*

Corrected Déf. 1/1′ (DEC-178): IsPocheAffNC / IsPocheProjNC (PocheNonConstante.lean) extend the printed IsPocheAff / IsPocheProj with nonConstant : ∃ x y, z x ≠ z y. hP.exists_ne_zero feeds the strict _of_ne_zero lemmas (ligne_brisee_poche_of_ne_zero, septieme_propriete_of_ne_zero), and hP.toIsPocheAff / hP.toIsPocheProj reach every printed-pocket lemma. nonConstant_tfae gives the five equivalent readings. Witnesses: exists_isPocheAffNC_demiEspace and exists_isPocheProjNC_demiEspace (n + 1 ≥ 1). There is none in dimension 0.
