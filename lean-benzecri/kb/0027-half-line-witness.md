# 0027 — A sweepable witness with a non-constant cote and P ≠ V: the half-line

*Found 2026-11-21 by T-bz-c2-developpement; recorded by the master session.*

`theoreme_premier_demiDroite` (`Chapter2/Developpement.lean`): `]0, ∞[ ⊂ ℝ¹` with the canonical
projective structure, swept by its homotheties, with the pocket `P = ]0, 1[ ≠ V`. The homotheties
are `GXAut` through `Sphere.hemiChart_apply_eq_smul` with
`(LinearEquiv.smulOfNeZero ℝ _ c hc).toAffineEquiv` and `GXAut.ofBijective`. The `z ≡ 0` model of
`ℝⁿ` is `isBalayable_model` / `theoreme_premier_model`, where `P = V`.
