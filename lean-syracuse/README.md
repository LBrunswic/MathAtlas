# lean-syracuse — the Lean library of On non-trivial cycles of the 3x+1 problem

The formalization of `papers/syracuse`: the author's paper on non-trivial cycles of the 3x+1 (Syracuse) problem, in a package of its own at the hub's pin
(DEC-138). A strict library `Syracuse` and a scaffold library `SyracuseScaffold`, Lean `v4.31.0`, mathlib
`fabf563a` (the hub's pin, `hub.toml`). Scope first: the whole paper.

    python3 ../tools/dropbox_ignore.py                   # once, BEFORE any build: .lake must never sync
    taskset -c 0-11 lake build SyracuseScaffold.<Module>  # one module — the iteration loop
    make check                                           # strict build, scaffold build, sorry count, axiom sweep

## Conventions

- **Strict and scaffold.** `Syracuse/` is `warningAsError`: no `sorry`, no warning. `scaffold/SyracuseScaffold/`
  allows tagged `sorry -- SORRY(<label>): <obstruction>`; graduation into `Syracuse/` is a file move, by the
  master session only. `Syracuse` never imports `SyracuseScaffold`.
- **Marks.** ``**`label`**`` in a strict module docstring certifies the paper's statement in full; the
  ledger (`papers/syracuse/ledger/`) reads the marks. Anything less is written without the mark.
- **Layering (wave 0).** Mathlib only.
- **Protocol.** Every agent follows `docs/CAMPAIGN.md`; the knowledge base is `kb/INDEX.md`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml` and `lake-manifest.json`.
