---
id: 0278
title: A rename: deprecated wrappers, not `alias`, and a dump with the old names substituted back
kind: pattern
created: 2026-11-23
---
Write a renamed declaration's old name as a `@[deprecated New (since := "…")]` `theorem`/`abbrev` wrapper (as `Causal/Port/E0GXStructure.lean` does), not Batteries' `alias`: `tools/ledger.py` and `tools/ladder.py` find declarations by scanning for `theorem`/`def`/`abbrev`, so an `alias`ed name would stop resolving there (T-abs-dependence-domain-home, DEC-198). With `-DwarningAsError=true` a use of the old name is an error; inside the old namespace an unqualified name now resolves to the deprecated wrapper, so qualify it. Check a rename by a before/after constant dump with the old names substituted back into every type and value (lean-causal/campaign/T-abs-dependence-domain-home/scratch/dump_subst_cmp.py): every pair must match. Lean 4.31's deprecation message adds a "different namespace" note that a `#guard_msgs` must include.
