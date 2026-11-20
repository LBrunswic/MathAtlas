# lean-yamabe — the Lean library of the Yamabe gap

The formalization of `papers/yamabe`: the author's paper on the Yamabe gap, in a package of its own at the hub's pin
(DEC-139). A strict library `Yamabe` and a scaffold library `YamabeScaffold`, Lean `v4.31.0`, mathlib
`fabf563a` (the hub's pin, `hub.toml`). Scope first: §6 first: the punctured-flat-torus bounds and their proofs (DEC-139).

    python3 ../tools/dropbox_ignore.py                   # once, BEFORE any build: .lake must never sync
    taskset -c 0-11 lake build YamabeScaffold.<Module>  # one module — the iteration loop
    make check                                           # strict build, scaffold build, sorry count, axiom sweep

## Conventions

- **Strict and scaffold.** `Yamabe/` is `warningAsError`: no `sorry`, no warning. `scaffold/YamabeScaffold/`
  allows tagged `sorry -- SORRY(<label>): <obstruction>`; graduation into `Yamabe/` is a file move, by the
  master session only. `Yamabe` never imports `YamabeScaffold`.
- **Marks.** ``**`label`**`` in a strict module docstring certifies the paper's statement in full; the
  ledger (`papers/yamabe/ledger/`) reads the marks. Anything less is written without the mark.
- **Layering (wave 0).** Mathlib only.
- **Protocol.** Every agent follows `docs/CAMPAIGN.md`; the knowledge base is `kb/INDEX.md`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml` and `lake-manifest.json`.
