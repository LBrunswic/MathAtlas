---
id: 0031
title: def:egf of record is EGF.IsEGFErgodic; invariance under quasi-measure-preserving generators
kind: convention
created: 2026-11-22
---
Found by T-egf-def-egf (`EGF/DefEGF.lean`, DEC-146). An EGF is `EGF.IsEGFErgodic lam F Φ α` with
`Φ : Fin p → S ≃ᵐ S` and fields `policy` (`IsEGFPolicy`, C-27), `nonsingular`
(`lam.map (Φ i) ≪ lam ∧ lam.map (Φ i).symm ≪ lam`), `ergodic` (`IsGroupErgodic lam (egfGroup Φ)`).
Use `h.ergodic_moves` for the generator form, `h.isKernelErgodic hpos` for the kernel (positive
weights), `h.isUniversalPolicy` / `h.isUniversalFamilyEps` for universality, `h.inflowAC` for
`F_in ≪ λ`. Torus and sphere moves as measurable equivalences: `EGF.torusAffineME`, `EGF.rotME`
(their `egfGroup` is `torusAffineGroup` / `sphereRotGroup` by `rfl`). A set a.e.-invariant under
quasi-measure-preserving generators and their inverses is a.e.-invariant under the generated subgroup
(`EGF.ae_invariant_of_mem_closure_of_quasi`, by `Subgroup.closure_induction`); without
nonsingularity the generator and group forms differ (`EGF.FourCycle.isGroupErgodic_not_forall`).
