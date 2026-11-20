---
id: 0047
title: Model-free lemmas once stranded in model-importing modules: now in the ETT layer
kind: pitfall
created: 2026-11-20
---
A layer-1 module may not import a model (`programme/README.md`). These model-free results sat in
modules that do, and were hoisted by T-abs-hoist-model-free (same full names, same statements):
`Causality.exists_minimal_of_isCompact` (Sbierski Lemma 3.9) and its relative form
`exists_minimal_of_isCompact_on` are in `Causal.CompactMinimal`; `curveOn_of_rel_imp`,
`inextensible_ordConnectedComponent_of_le` and the section `Relative` are in `Causal.CurveComponents`;
`Causal.Flat.dependenceDomain` (namespace `Flat` kept for the name) is in `Causal.DependenceDomain`.
`Causal.NestedCausalities`' duplicates are gone except `dependenceDomainOn`, now an `abbrev` of
`Flat.dependenceDomain` (reducible: `simp`/`rw` see through it). Before writing a layer-1 lemma,
grep the model-importing modules too: a model-free result may still sit behind a model import.
