# 0021 — Affine automorphisms are projective ones: GXAut.affToProj and its general transport

*Found 2026-11-21 by T-bz-c2-cas-affin; recorded by the master session.*

`Benzecri.GXAut.affToProj : GXAut (GAR n) (Fin n → ℝ) V →* GXAut (GSR n) (S n) V`, for the
canonical projective structure `projOfAff`, sends each affine automorphism to itself
(`GXAut.affToProj_smul` is `rfl`; `GXAut.affToProj_injective`), and `IsBalayableFor.affToProj`
keeps the same compact. The general forms are `IsGXMorphism.transport` and `GXAut.transport`,
for any open embedding of models equivariant through a group morphism `G' →* G`. Use them
wherever an affine statement is derived from its projective twin (`Chapter2/CasAffin.lean`; next
user: T-bz-c2-theoreme-affine).
