---
id: 0058
title: Pattern:
kind: pattern
created: 2026-11-23
---
Found by T-yamabe-analysis (round 3). Pattern: check a primed copy syntactically inside the file with a run_cmd: find? both constants, compare levelParams.length, then `a.type == b.type.instantiateLevelParams b.levelParams (a.levelParams.map Level.param)` and throwError otherwise (Expr.eqv ignores binder names and info). Unlike `type_of% … = type_of% … := rfl` it rejects a copy that differs by unfolding a definition (tested: w12 unfolded).
