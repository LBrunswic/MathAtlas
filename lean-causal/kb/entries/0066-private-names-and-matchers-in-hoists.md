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
tactic mode where a dispatch counts new declarations (T-abs-hoist-time-function).
