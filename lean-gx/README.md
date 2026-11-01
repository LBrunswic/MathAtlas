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

## Modules

| module | certifies | note |
|---|---|---|
| `GX.Topology.Portly` | `def:portly_skeletal_subset`, `lem:path_covering`, `lem:portly_first_countable` | the closure properties of l.383–390; infinite concatenation of paths |
| `GX.Topology.UniversalCover` | — (infrastructure, cited at l.1156) | `SemilocallySimplyConnected`; the universal cover constructed, simply connected, `IsCoveringMap`, universal property; `Deck ≃* π₁`; composition of coverings; π₁ countable |
| `GX.Structure.Basic` | — (l.293, l.341–343) | `ClosedUnderRestriction (gxGroupoid G X)` and open subsets as (G,X)-manifolds (WP-26d); analytic actions, the paper's (G,X)-atlases ⇔ `HasGroupoid (gxGroupoid G X)` (ported from `lean-causal/Causal/GXStructure.lean`), (G,X)-morphisms, pullback along local homeomorphisms |
| `GX.Structure.Developing` | — (the classical developing theorem, l.293/344; DEC-23) | `GX.developing_theorem`, `GX.developing_unique`, `GX.developing_descends`, `GX.developing_theorem_of_simplyConnected`; the literal l.344 statement refuted for bare maps |
| `GX.Spread.Basic` | `def:category_spreads`, `rem:spread_open_respectively_co`, `def:continuous_map_ordinary_locus`, `rem:ordinary_locii_open_but`, `rem:singular_on_singular`, `lem:spread_partial_covering`, `cex:openess`, `cex:portlyness`, `lem:ord_iso` | the ordinary locus as ruled by DEC-40; `cex:portlyness` on the paper's own space (its coarsest spread topology exists) |
| `GX.Singular.Atlas` | `def:almost_everywhere_atlas_topological`, `cor:maximal_atlas`, the category of singular (G,X)-manifolds, `lem:regf1`, `lem:GX_sing_homeo_reg`, … | `lem:GX_atlas_union`, `rem:morphisms_analytical_two_equal`, `lem:aepullback` and three more partial (corrected or read; findings in the ledger) |
| `GX.Spread.Completion` | `def:complete_spread_spread_completion`, `cor:totdiscont` | Fox's completion built from ends; `theo:Fox_completion_functor` and `prop:spread_fiber` partial (domain of the functor; "injective open") |
| `GX.Branched.Basic` | `def:branched_covering` … `lem:subcovering_general` (9 rows) | `lem:complete_path_carac` with Fox's extension property |
| `GX.Branched.Universality` | `prop:universality`, `rem:completion_covering`, `rem:considering_maximal_covering_possibly` | the maximal covering branched over a skeletal S; `prop:branched_covering_composition` corrected (finite fibres or slsc), its counterexample on `D_∞` |
| `GX.Singular.Quotient` | `prop:aeGXquotient` | quotients; conical models `E^n_α` by a cone distance; five example rows partial (readings) |
| `GX.Singular.Suspension` | `def:topological_suspension` … `rem:proof_above_works_quotient` (8 rows) | suspensions; `prop:susp_portly`, `lem:connected_union` |
| `GX.Topology.PortlyExamples` | — | `ex:following_example_skeletal_itemize` partial: item 3 false as written (bow-tie), its corrected form proved; dimension theory for closed totally disconnected sets and the local structure of simplicial complexes built (WP-26g, 0 `sorry`) |
| `GX.Branched.Paths` | §3.3 (8 of 12 rows closed) | almost trivial loops in the literal compact-open reading (DEC-55), almost homotopy, `theo:ramified_covering_path`, the fibres ℤ^ℕ |
| `GX.Branched.Galois` | §3.4 (11 of 13 rows closed) | Galoisian and quasi-Galoisian coverings, `prop:Galoisian_semilocal`, `theo:Galois_cor` |
| `GX.SingularII.Unloopable` | §2.5 opening | locally unloopable models, branched coverings of singular manifolds |
| `GX.SingularII.Developing` | §2.5.1 | **the singular developing theorem** `GX.singular_developing_theorem` (`prop:branched_devmap`), holonomy, descent |
| `GX.SingularII.Tame` | §2.5.2 | tame singularities, `theo:local_tame` |
| `GXScaffold.SingularII.Models` | §2.5.3–4 | analytic families, X_A-atlases, virtually tame models; `theo:local_virt_tame` (2 tagged `sorry`s) |
| `GXScaffold.SingularII.SpreadTop` | §2.5 close | `lem:spread_top`, the spread topology (scaffold because it imports Models) |
| `GXScaffold.Branched.GaloisExamples` | — | the closing examples; Antoine's necklace explicit (DEC-58/68), Antoine's theorem a tagged `sorry` |
