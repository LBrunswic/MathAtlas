---
id: 0054
title: ERS Thm 4.64's causal skeleton, and the half of Step 2 that is not layer 1
kind: pattern
created: 2026-11-20
---
`Causal.Causality.ers_theorem_4_64` (`Causal.ErsUniqueness`): solutions are an agreement predicate
with `AgreementGlues`; a common development is `IsCommonDevelopment` (S Cauchy; GH not asked: that
would be Geroch (iii)⇒(i)); the restart (ERS Steps 3–5 + Prop 4.63) is `SliceRestart`, which is
`ers_theorem_4_82`'s `hstep` definitionally (`ers_theorem_4_82_of_sliceRestart`).
`exists_spacelike_boundary_point` run in one development gives a point of that development only:
placing it in the other (ERS's "γ ⊆ U₂") is the named hypothesis `FrontierStaysIn`, and a restart
located in U₁ alone is unsuppliable. Relative GH plus `TarentinOn W` give J± closed in W
(`GloballyHyperbolicOn.closure_Jminus_inter_subset`), so 4.82's `hJm`, `hJp` are consequences
(`ers_theorem_4_82_of_globallyHyperbolicOn`) (T-abs-ers-thm-4-64).
