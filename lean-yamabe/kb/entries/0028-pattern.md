---
id: 0028
title: Pattern:
kind: pattern
created: 2026-11-22
---
Found by T-yamabe-rellich-criterion. Pattern: the functional-analytic half of Rellich–Kondrachov is YamabeScaffold.RellichCriterion (Mathlib only): exists_subseq_tendsto_eLpNorm_of_approx needs only AEStronglyMeasurable u_k, an L^p bound ∃ K : ℝ≥0, ∀ k, eLpNorm (u k) p μ ≤ K, and for every ε > 0 a Finset s of an arbitrary index type with MemLp g_i and eLpNorm (u k − ∑ i ∈ s, c i • g i) p μ ≤ ofReal ε — no bound on the coefficients (the cell averages); exists_subseq_tendsto_eLpNorm_two is its p = 2 form, with Mfd.rellich_kondrachov's conclusion.
