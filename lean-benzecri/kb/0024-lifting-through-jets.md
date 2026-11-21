# 0024 — Lifting through J(V) without simple connectivity

*Found 2026-11-21 by T-bz-c2-developpement; recorded by the master session.*

To build a developing map on a non-simply-connected `V` (Ch. 2 § 3, 1°a), apply Mathlib's
`IsLocalHomeomorph.existsUnique_continuousMap_lifts` (path-connected, locally path-connected
form) to the identity of `V`, with `isCoveringMap_jets_proj` and `IsCoveringMap.exists_path_lifts`
for existence. For the endpoint condition, a path of `J(V)` over the source of one maximal-atlas
chart `ψ` is the translate of `ψ`'s jets by the sheet of its first point, by
`IsCoveringMap.eq_of_comp_eq` on `I` (`jetSMul_eq_of_path`). Prop. 7 puts both paths into the
source of the single chart `φ ∘ g` (`IsCompatibleChart.trans_aut`, `Chapter2/Mesure.lean`; its
source `g⁻¹P` from `g • x ∈ P` by `simpa [GXAut.smul_def, hP.source_eq]`). A developing map
composed with `g` is developing by
`isDeveloping_iff_isGXMorphism.2 ((isDeveloping_iff_isGXMorphism.1 hp).comp g.isGXMorphism)`.
