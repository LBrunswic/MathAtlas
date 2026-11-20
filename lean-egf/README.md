# lean-egf — the Lean library of *Ergodic Generative Flows*

The formalization of `papers/egf`: *Ergodic Generative Flows* (Brunswic et al., ICML 2025), in a
package of its own at the hub's pin (DEC-133, as DEC-112 did for Benzécri), without waiting for
OQ-1 (whether GFNBoundsLean is absorbed in-tree). A strict library `EGF` and a scaffold library
`EGFScaffold`, Lean `v4.31.0`, mathlib `fabf563a` (the hub's pin, `hub.toml`). The headline anchor
is `EGF.main_universality` (DEC-133).

    python3 ../tools/dropbox_ignore.py               # once, BEFORE any build: .lake must never sync
    taskset -c 0-11 lake build EGFScaffold.<Module>  # one module — the iteration loop
    make check                                       # strict build, scaffold build, sorry count, axiom sweep

EGF is the author's own paper: its story is rewritten in `papers/egf/STORY.md` and rebuilt from
this library; the camera-ready draft in `papers/egf/legacy/` is a story source only (DEC-4).

## Conventions

- **Strict and scaffold.** `EGF/` is `warningAsError`: no `sorry`, no warning. `scaffold/EGFScaffold/`
  allows tagged `sorry -- SORRY(<label>): <obstruction>`; graduation into `EGF/` is a file move, by
  the master session only. `EGF` never imports `EGFScaffold`.
- **Marks.** ``**`label`**`` in a strict module docstring certifies the paper's statement in full;
  the ledger (`papers/egf/ledger/`) reads the marks. Anything less is written without the mark.
- **Layering (wave 0).** Mathlib only. Reusing GFNBoundsLean (`lean/`, `GFNBounds.Core`) would add a
  `[[require]]` on the read-only submodule: the first EGF target decides, then OQ-1.
- **Protocol.** Every agent follows `docs/CAMPAIGN.md`; the knowledge base is `kb/INDEX.md`.

Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml` and `lake-manifest.json`.
