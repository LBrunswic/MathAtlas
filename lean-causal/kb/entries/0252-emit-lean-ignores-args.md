---
id: 0252
title: tools/ladder.py emit-lean --help runs emit-lean
kind: pitfall
created: 2026-11-23
---
`python3 tools/ladder.py emit-lean --help` RUNS emit-lean: the tool ignores extra arguments and rewrites `Causal/Ladder/Rules.lean` and `Test.lean` in place. For a dry run call `ladder.emit_lean` / `ladder.emit_test` in memory (`campaign/T-abs-one-sided-future-base/emit_probe.py`); DualTest's generator takes an output path (`dual_closure.py shipped /tmp/x.lean`).
