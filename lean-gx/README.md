# lean-gx — the Lean library of *On branched coverings of singular (G,X)-manifolds*

The formalization of `papers/gx` (L. Brunswic; arXiv 2010.10610; Geom. Dedicata 2024; the story
source is the accepted version, DEC-24), **together with the classical developing theorem** for
(G,X)-manifolds (DEC-23). A strict library `GX` and a scaffold library `GXScaffold`, Lean
`v4.31.0`, mathlib `fabf563a` (the hub's pin, `hub.toml`).

    python3 ../tools/dropbox_ignore.py   # once, BEFORE any build: .lake must never sync
    lake build GXScaffold.Topology.Portly  # one module — the iteration loop
    make check                           # strict build, scaffold build, sorry count, axiom sweep

A package of its own (DEC-23): `lean/` is the read-only GFNBoundsLean submodule (OQ-1), and gx
does not depend on `lean-causal` — the (G,X)-groupoid of `lean-causal/Causal/GXStructure.lean`
is ported, with its origin cited. Graduation into `lean/` is two `git mv`s.

## The two libraries

| library | where | rule |
|---|---|---|
| `GX` | `GX/` | strict: `warningAsError`, so a `sorry`, an unused variable or a deprecation fails the build |
| `GXScaffold` | `scaffold/GXScaffold/` | `sorry` permitted and tagged `SORRY(<label>): <obstruction>`; never imported by `GX`. The campaign writes here (`docs/CAMPAIGN.md`); a file graduates by `git mv` |

## Conventions

- Namespace `GX`. Hypotheses are the weakest the proof uses; a hypothesis the paper omits but
  the proof needs is added and recorded as a finding (DEC-27).
- A (G,X)-manifold is `[ChartedSpace X M] [HasGroupoid M (gxGroupoid G X)]` over the maximal atlas
  (DEC-16); the rigidity ("analyticity") of the action is a separate class, `IsRigidAction`.
- A singular (G,X)-manifold carries a maximal almost-everywhere atlas (DEC-25).
- The knowledge base of `lean-causal/kb/` applies where it is not about causality (the docstring
  contract 0006, never outrun the paper 0011, names at this pin 0004, charts 0018); gx-specific
  entries are in `kb/INDEX.md`.
