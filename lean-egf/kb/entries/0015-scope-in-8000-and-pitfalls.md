---
id: 0015
title: The ledger reads SCOPE from the first 8000 characters; two measure pitfalls
kind: pitfall
created: 2026-11-21
---
Found by T-egf-sampling-corollaries. `tools/ledger.py` reads the SCOPE block from `text[:8000]` and its regex needs the Provenance line (or `-/`) inside them: a long module docstring fails silently. A rewrite lemma whose function argument is inferred from `hf.add hg` gets a beta-unreduced pattern `fun a => f a + g a` that does not match `f + g`. `IsFiniteMeasure (c • μ)` is an instance for `c : ℝ≥0`, not `ℝ≥0∞`: build finite examples with `(2⁻¹ : ℝ≥0) • dirac false`.
