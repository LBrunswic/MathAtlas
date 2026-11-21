# 0017 — Pseudo-balls; dimension 0 is discrete; S(n) ∖ {x} as a witness

*Found 2026-11-21 by T-bz-c2-pseudo-boules; recorded by the master session.*

Pseudo-balls (Déf. 6) are `Benzecri.pseudoBoule` (`Benzecri.Chapter2.PseudoBoules`), open
(`isOpen_pseudoBoule`) and preconnected (`isPreconnected_pseudoBoule`) in every dimension and for every
r; `isMajoreSeg_iff_pseudoLength_lt`. A manifold charted on S(0) is discrete
(`discreteTopology_dim_zero`), so a connected one has at most one point (`subsingleton_dim_zero`). S(n)
is connected for n ≥ 1 (`connectedSpace_S`) and second countable, which makes S(n) ∖ {x} a cheap
witness against a « V connexe » statement. Do not elaborate `(continuous_hilbertLength hK).comp h`
against an expected `Continuous fun P => …`: the defeq check times out; compose in a `have`, then
`simp only [Function.comp_def] at it`.
