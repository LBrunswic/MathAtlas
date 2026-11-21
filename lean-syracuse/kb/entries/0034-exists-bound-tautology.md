---
id: 0034
title: Pitfall: an existential bound in front of an implication is a tautology
kind: pitfall
created: 2026-11-21
---
Found by T-syr-no-circuit's AUDIT-1. ∃ B, (∀ x, P x → f x ≤ B → Q x) → ∀ x, P x → Q x holds for every P, Q and f: take B = f of a counterexample, which makes the hypothesis false. State the bound as a conjunct, ∃ B, (∀ x, P x → f x ≤ B) ∧ …, with B chosen before the reading (`noCircuit_of_cited`). An auditor's probe that proves a conditional theorem without its cited hypothesis is the test.
