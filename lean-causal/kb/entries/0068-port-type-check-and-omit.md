---
id: 0068
title: Checking a gx → Causal port by elaborated types; omit changes types
kind: pattern
created: 2026-11-21
---
Found by T-ett-gxsingular-dec25. Run the toolchain's `lean` on a probe with `LEAN_PATH` = lean-gx's package and build lib directories (read-only, no lake in lean-gx); in both environments rename `GX.x` → `Causal.x` in `.const` and projection nodes, then compare kind, universes, type and value hashes. In a port, `omit [inst] in` changes the elaborated type when gx kept the unused instance argument: use `set_option linter.unusedSectionVars false in` instead. A local `have key : ∀ {Z : Type*} …` cannot be used at two universes: state it as a top-level lemma.
