---
id: 0337
title: Lean does not catch a reversed dual iff: the shape check does
kind: pitfall
created: 2026-11-28
---
A generated dual rule from an implication `K : C.P → C.dual.P` states `p_of_dual` as `(K h :)`: the empty ascription elaborates `K h` before unifying with `P C`, and `C.dual.dual` is `C` by `rfl`. The same `rfl` lets `K.2 h` prove `P C` from `P C.dual` whichever way an iff key is oriented, so compiling the emitted module does not detect a key whose iff is reversed. `tools/ladder.py`'s textual shape check refuses it instead (fixture `dual-shape`, T-tac-ladder-dual-key); keep it when the emitter changes. Related: kb/0264 (positives that close by `rfl` without the rule).
