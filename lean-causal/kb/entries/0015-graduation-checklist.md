---
id: 0015
title: Graduating a scaffold file — what the gates do not catch by themselves
kind: house-rule
created: 2026-10-29
---
The master session's checklist, each item paid for once:
1. `lake env lean -DwarningAsError=true <file>` before moving: the strict lib is warningAsError.
2. Move, rewrite `import CausalScaffold.X` → `Causal.X` everywhere (scaffold files that import a
   graduated one too), add the import to `Causal.lean`, delete the stale
   `.lake/build/lib/lean/CausalScaffold/X.*`.
3. Every scaffold module is imported by `scaffold/CausalScaffold.lean`, or
   `scripts/AxiomSweep.lean` does not see it.
4. The ledger reads a mark only for the prefixes in `ledger.toml`'s `label_prefixes`
   (`cexemple` was missing until 2026-10-29); after a rebuild, check the marked label has
   `lean_files`.
5. Curated `decls` must be textual declarations: an anonymous `instance` has no name in the
   source, and `ledger.py check` fails on it.
6. A partial row needs `extra_lean_files` and `lean_proved_override = "partial"`; a closed one
   counts toward closure only in bucket `A`.
In zsh `for f in $G` does not split words: run multi-file shell steps under `bash -c`.
