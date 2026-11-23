---
id: 0066
title: Hoisting renames private declarations; term-mode matches add auxiliary constants
kind: pitfall
created: 2026-11-21
---
A private declaration's internal name records its module (`_private.<Module>.0.<name>`): after a
hoist a dump shows it as removed plus added, and every user's value hash changes. Check those by
substituting the old name back into the term (kb/0063). A term-mode `let ⟨…⟩ := h` in a theorem
creates an auxiliary matcher constant (`<thm>.match_1_1`); `obtain` in tactic mode does not — prefer
tactic mode where a dispatch counts new declarations (T-abs-hoist-time-function). In a hoist, a
theorem's `_simp_1_n`, a def's `_proof_1`, `.eq_1` and `.congr_simp`, and a structure's
`mk._flat_ctor`, `casesOn`, `rec`, `recOn` and field projections move with their parent under the
same names: count them in the dump (68 constants for 25 declarations in T-loc-ealpha-tidy).
