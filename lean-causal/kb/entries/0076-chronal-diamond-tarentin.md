---
id: 0076
title: Two-sided chronology near a point gives tarentin there: chronal_neighbours ⇒ tarentin
kind: pattern
created: 2026-11-21
---
The chronological diamond I⁺_U(p) ∩ I⁻_U(q) lies in the open diamond Int J_M(p, q)
(`Causality.Iplus_inter_Iminus_subset_openDiamond`, from the openness axioms and `le_of_lt`), so
Z⁺ = Z⁻ = M ⇒ tarentin (`tarentin_of_Zplus_Zminus`) and chronal_neighbours ⇒ tarentin
(`ChronalNeighbours.tarentin`), with no separation axiom (`Causal.ChronalTarentin`). The chain
chronal neighbours ⇒ Z⁺ = Z⁻ = M ⇒ tarentin is strict at both arrows: `globalLine_separates_Z` at
the first (they agree under absolute minimality on T1, `AbsolutelyMinimal.chronalNeighbours_iff_Z`),
`lightlikeLine_separates_Z` at the second (the lightlike line is tarentin with Z± = ∅). To prove a
model tarentin when it has chronology, show Z⁺ = Z⁻ = M instead of computing diamonds
(`globalLine_tarentin`, four lines) (T-abs-chronal-neighbours-tarentin).
