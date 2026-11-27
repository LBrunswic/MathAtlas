---
id: 0294
title: ERS witnesses on the line: 4.68's Lean forms allow a disconnected U₂; 4.82's hstep is never exercised
kind: pattern
created: 2026-11-27
---
`Causal.ErsWitnesses` and `Causal.ErsSCWitnesses` give every ERS §4 form a timelike-line witness. Cor 4.68's Lean forms ask of `U₂` only `hlocal`, `hstay`, `hstep` and the disagreement, not that `u₂` is a development (the weakening `Causal/ErsUniqueness.lean:64` discloses), so `U₂ = ]-1,1[ ∪ ]2,3[` witnesses them; in the paper's reading 4.68 has no instance on ℝ (`real_ers_corollary_4_68_agree`), nor with one flat causality on 1+1 Minkowski (argued): a witness needs a non-flat causality or two causalities. 4.82's `hstep` holds vacuously whenever every development lies in `dom i₁` (`ers_theorem_4_82_hstep_of_le`) and, given the rest, is equivalent to the conclusion (`_iff`). For the union lemmas use a two-point `S` in a disconnected `B` with an infinite family of pieces: with `S` one point `eq_of_mem` and `of_subset` are trivial. The problem with solutions `id` on every open set (`ErsSCWitness.idSol`) has more than one development domain, and makes 4.73's named inputs theorems.
