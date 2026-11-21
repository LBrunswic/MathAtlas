---
id: 0077
title: push_up ∧ chronal_neighbours ⇒ causally_plain; the plainness criterion is in the ETT layer
kind: pattern
created: 2026-11-21
---
`Causality.PushUp.causallyPlain_of_chronalNeighbours` (`Causal.CausallyPlainLocZ`, no standing
axiom): chronal neighbours give `E0LM.LocZplus C` and `E0LM.LocZminus C ∅` (chronology in
W ⊓ interior N, carried to W by `lt_mono`; interior ∅ = ∅), and `causallyPlain_of_locZ` concludes.
Chronal neighbours cannot be dropped (`deux_pushup`: the lightlike line). With
`pushUp_of_causallyPlain_of_absolutelyMinimal`, push-up and plainness coincide for absolutely
minimal T1 causalities with chronal neighbours. The criterion (`E0LM.Loc*`, `rel_of_causallyConvex`,
`locZplus_of`, `locZminus_of`, `locTarentin_of`, `causallyPlain_of_locZ`) now sits in the ETT layer;
`SingularFlatAxioms.causallyPlain` and the `BTZAxioms` lemmas sit in `Causal.SingularFlatPlain`,
beside `Causal.SingularFlat`, out of the Port (T-abs-hoist-plain-locz; corrects kb 0061, 0064).
