---
id: 0036
title: Finitely many cycles: a computable candidate Finset, one decide per membership
kind: pattern
created: 2026-11-21
---
Found by T-syr-cited-steps. Every cycle (x, n) of ℤ with p_n ≤ B lies in the computable `citedStepsCandidates B`, because lem:base fixes x from a (`mem_citedStepsCandidates`); `Set.Finite.subset` of its coercion gives finiteness. Close small memberships one `decide` at a time (a conjunction of three hit maxRecDepth), and at literal (x, n, B) pass `(x := …) (n := …) (B := …)` explicitly.
