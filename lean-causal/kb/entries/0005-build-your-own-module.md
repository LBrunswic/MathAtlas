---
id: 0005
title: Iterate with `lake env lean`, build only your own module
kind: house-rule
created: 2026-09-27
---
## When
Several sessions work in this tree at once.

## Do
* Typecheck: `lake env lean scaffold/CausalScaffold/Foo.lean` (writes nothing).
* Build, at the end: `lake build CausalScaffold.Foo`.
* Never `lake build Causal`, `lake build CausalScaffold`, `lake build` or `make check`: the
  lakefile globs every file of a library, another session's unfinished file included.
* Never touch `.lake/`, `lakefile.toml`, `lake-manifest.json`.

## Why
Lake at v4.31.0 has no build lock. Two builds are safe only on disjoint leaf modules whose
imports are already built; the master session builds everything between waves.
