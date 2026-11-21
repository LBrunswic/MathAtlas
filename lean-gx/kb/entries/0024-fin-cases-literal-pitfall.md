---
id: 0024
title: `fin_cases i` yields ⟨k, _⟩ indices that literal-index lemmas do not match
kind: pitfall
created: 2026-11-21
---
Found by T-gx-troyanov-four. After `fin_cases i`, lemmas stated at literal indices are not matched by `rw` or `linarith` (timeouts at whnf). In tactic mode use `match i with | 0 => … | 3 => …`, which keeps the literals, or `show` the literal form first.
