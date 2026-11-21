---
id: 0082
title: A theorem declared in two modules with the same type builds silently
kind: pitfall
created: 2026-11-21
---
Lean v4.31.0 merges a constant declared in two imported modules when the types agree
(`subsumesInfo`, `Lean/Environment.lean:2183–2203` of the toolchain), so a duplicate full name
builds, even with both modules in one import set: `Causal.lean` imported both copies of
`Causality.locallyCompactSpace_of_globallyHyperbolic` (LemmaKSC, LemmaKObstruction; equal types,
different proofs) until T-abs-hoist-levin merged them. A build cannot find a duplicate: grep the
sources or compare environment dumps.
