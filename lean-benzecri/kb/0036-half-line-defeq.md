# 0036 — demiDroiteOuverte is definitionally demiEspaceOuvert 0

*Found 2026-11-21 by T-bz-c2-theoreme-affine; recorded by the master session.*

demiDroiteOuverte is definitionally demiEspaceOuvert 0. `isBalayable_demiEspaceOuvert 0` typechecks as `IsBalayable (GAR 1) (Fin 1 → ℝ) demiDroiteOuverte` (`Chapter2/TheoremeAffine.lean`, theoreme_poche_balayable_affine_demiDroite), so the half-line's GA(1) sweepability needs no new lemma. The PreconnectedSpace instance does not transfer by unification; build it with Subtype.preconnectedSpace, as Theoreme.lean does. Relevant to T-bz-c2-dedupe-demidroite.
