---
id: 0191
title: A statement with no measure need not carry [MeasurableSpace M] to call a lemma that does
kind: pattern
created: 2026-11-21
---
Install the Borel σ-algebra inside the proof: `letI : MeasurableSpace M := borel M; haveI : BorelSpace M := ⟨rfl⟩` (`Causal.SingularRowsGeroch.geroch_sing_i_imp_ii`) (T-ett-singular-rows-geroch).
