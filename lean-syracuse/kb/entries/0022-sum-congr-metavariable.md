---
id: 0022
title: Pitfall: Finset.sum_congr with no target leaves a metavariable that rw closes by rfl
kind: pitfall
created: 2026-11-21
---
Found by T-syr-steiner. In `Finset.sum_congr rfl (fun t ht => by rw [h]; exact …)` with no target given, the target function is a metavariable; `rw` closes the goal by `rfl` and assigns it, so nothing is rewritten ('no goals' on the `exact`). State the target sum first, or pass `(g := …)`.
