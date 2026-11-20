---
id: 0048
title: The `causal_ladder` tactic, and regenerating its rules
kind: pattern
created: 2026-11-20
---
`causal_ladder` (`import Causal.Ladder.Rules`) closes a ladder property of a term from the ladder
properties in the context, by aesop safe forward rules: conjunctive premises are matched as they
stand, cycles stop by deduplication, a conditional edge never fires without its side hypothesis.
It uses no hypothesis under a binder and does not reason across `C.dual`; `simp` is off, but the
builtin `assumption` matches up to definitional equality. `Causal/Ladder/Rules.lean` and `Test.lean`
are generated: after any change to `programme/ladder.toml`, or to the imports of a witness's module,
run `python3 tools/ladder.py emit-lean` and rebuild them; `tests/test_programme.py` fails on a stale
or hand-edited copy. An edge becomes a rule only with an empty `under`, both ends of sort causality,
and a witness in an ETT-layer module (T-tac-ladder-core).
