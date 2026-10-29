# lean-causal — the Lean library of *Topological spacetimes (I)*

The formalization of `papers/ett`: a strict library `Causal` and a scaffold library
`CausalScaffold`, Lean `v4.31.0`, mathlib `fabf563a` (the hub's pin, `hub.toml`).

    python3 ../tools/dropbox_ignore.py   # once, BEFORE any build: .lake must never sync
    lake exe cache get                   # mathlib from ~/.cache/mathlib, no download
    lake build Causal.Generated          # one module — the iteration loop
    make check                           # strict build, scaffold build, sorry count, axiom sweep

**This directory is a provisional home.** The hub's plan puts every project in the one package
under `lean/`. Until GFNBoundsLean is absorbed in-tree (WP-8, OQ-1) `lean/` is a read-only
submodule, so the library is grown here in the layout it will have there: graduation is
`git mv lean-causal/Causal lean/Causal` and
`git mv lean-causal/scaffold/CausalScaffold lean/scaffold/CausalScaffold`, and
`papers/ett/ledger/ledger.toml`'s `[lean] root` goes back to `../../../lean` (OQ-11).

## The two libraries

| library | where | rule |
|---|---|---|
| `Causal` | `Causal/` | strict: `warningAsError`, so a `sorry`, an unused variable or a deprecation fails the build |
| `CausalScaffold` | `scaffold/CausalScaffold/` | `sorry` permitted and tagged; never imported by `Causal`. A module is here either because a proof is missing or because it rests on a **reading of the paper awaiting the author's ruling** — each module says which. The layer of the curves graduated on 2026-09-27 (DEC-6); the scaffold holds the campaign's files (`docs/CAMPAIGN.md`) until they graduate |

## Modules

| module | certifies | note |
|---|---|---|
| `Causal.Causality` | `defi:causalite`, `def:precausality` | the structures; `J^±`, `I^±`; time reversal `dual` |
| `Causal.Properties` | `defi:causalement_plat`, `defi:pushup`, `def:diamonds`, `def:causally_compact`, `def:alexandrov_topology`, `def:causal_spacetime`, `def:tarentin_spacetime`, `def:strongly_tarentin_point`, `def:globally_hyperbolic` | strong causality in two forms, causal openness one- and two-sided (OQ-8, OQ-9) |
| `Causal.StrongCausality` | `rem:topological_spacetime_strongly_causal`, `prop:FZenon_injectif` | `prop:tarentin_topological_spacetime_causality` under two-sided causal openness |
| `Causal.GlobalHyperbolicity` | `prop:relation_fermee`, `prop:GH_Jferme` | `prop:GH_fortement_causal` with the full diamond, or under causal openness |
| `Causal.Reachable` | `defi:futur_continue`, `rem:suite_croissante`, `lem:K_facile`, `lem:passe_coherent`, `prop:tarentin_fort_K`, `prop:K_plongement_ordre` and the two "obviously holds" remarks | `K^±`, the relative interior |
| `Causal.Generated` | `lem:union_causalite`, `def:precausality_generated_notation_lemma`, `def:topological_space_causality_absolutely`, `lem:precausalite_engendre_minimale`, `theo:causalite_engendre` | the Baire hypothesis is not used (OQ-10) |
| `Causal.Local` | — | a causality given on an open subset extends to the space |
| `Causal.Minimal` | `prop:topological_spacetime_absolutely_minimal`, `rem:absolutely_minimal_topological_spacetime`, `lem:cup_cap`, `rem:same_notation_one_proves` | |
| `Causal.Subdivision` | — | the Lebesgue-number step |
| `Causal.Lines` | `rem:droites_pas_plates` | the three lines of `ex:causalities_lines`; the timelike line satisfies the hypotheses of the library |
| `Causal.Measure` | `defi:mesure_dieckmann`, `rem:mesure_bord`, `prop:cont_ext_cont` | |
| `Causal.Curves` | `def:causal_chronological_curve` | causal and chronal curves, as ruled by DEC-6 (OQ-7) |
| `Causal.ArcConnected` | `def:causal_arc_connectedness`, `def:local_causal_arc_connectedness`, `rem:cac_local`, `prop:cac_engendre`, `cor:causalement_connexe_minimal`, `lem:precausalite_restriction_minimale`, `lem:pushup_local`, `lem:restriction_convexe` | causal arc-connectedness |
| `Causal.LinesCurves` | — | the timelike line is causally arc-connected |

What each label's status is, which declarations carry it and what formalizing found in the paper
is in `papers/ett/ledger/LEDGER.md`, generated from the sources and from
`papers/ett/certificate/curation.toml`.

## Conventions

* **The module docstring is a contract** (the GFN library's `kb/entries/0004`): title; the labels
  certified, in the form ``**`label`**`` the ledger reads, with their line in
  `papers/ett/legacy/labeled/ETT.tex`; the paper's own sentences in a block quote; a hypothesis
  checklist (`✓ carried`, `⚠ weakened`, `⚠ strengthened`); `## SCOPE (disclosed)`; `Provenance:`.
  A label proved under a reading or a hypothesis the paper does not have is written **without**
  the mark, and is `partial` in the ledger.
* **Everything is indexed by an open set.** `C.le U x y`, `C.Jplus U A`, `C.Kplus U A`: the
  spacetime `M` is `U = ⊤`. A property of the open subset `W` seen as a spacetime is `…On W`.
  No subtype of `M` appears in a statement.
* **Past from future.** A statement about the past is the statement about the future of
  `C.dual`; every property has its `dual_…` lemma.
* **Weakest sufficient hypotheses.** A theorem asks for the separation and countability it uses,
  not for "second countable Hausdorff"; the checklist says what was dropped.
