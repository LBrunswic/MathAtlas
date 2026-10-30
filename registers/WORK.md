# Work register

The state of every work package. Kept by the project-manager agent; `tools/registers.py check`
fails on a malformed row. Status: `PROPOSED · APPROVED · IN-PROGRESS · BLOCKED (reason) · IN-REVIEW · DONE · DROPPED · SUPERSEDED`.

| WP | Phase | Item | Status | Updated | Note |
|---|---|---|---|---|---|
| WP-1 | 0 | Hub skeleton: repository, symlink, `hub.toml`, `CLAUDE.md`, registers | DONE | 2026-09-19 | DEC-1 |
| WP-2 | 0 | Submodules `lean` (GFNBoundsLean@main, read-only) and `tools/leanlink` (LeanLink, new private remote) | DONE | 2026-09-19 | DEC-2; LeanLink's wiring committed at `935c114` and pushed |
| WP-3 | 0 | `tools/ledger.py` + `tools/texgraph.py` generalised from the GFN Bounds ledger; regression byte-identical modulo commit ids | DONE | 2026-09-19 | `tools/regression_ledger.sh` |
| WP-4 | 0 | Legacy snapshots with manifests for egf, ett, gx, yamabe, syracuse, dyniso; nonacyclic PDF only | DONE | 2026-09-19 | DEC-4; `tools/legacy_check.py` |
| WP-5 | 0 | EGF: labels, ledger, `STORY.md` skeleton, gates green | DONE | 2026-09-19 | DEC-3; 16 statements, 6 labels added; the story's words remain the author's |
| WP-6 | 0 | Labels and ledgers for ett, gx, yamabe, syracuse, dyniso | DONE | 2026-09-19 | label-audit drives it |
| WP-7 | 0 | Gates: dropbox-ignore, host, registers, deps, legacy-frozen, ledger, story, no-legacy-prose; `make check` and `make selftest` | DONE | 2026-09-19 | every gate has a fixture |
| WP-8 | 1 | Absorb GFNBoundsLean in-tree (subtree), `projects.toml`, generalised audits | PROPOSED | 2026-09-19 | after 2026-09-25; OQ-1 |
| WP-9 | 1 | Absorb GFNCertified as `papers/gfnbounds`, `tools/paper.mk` | PROPOSED | 2026-09-19 | after WP-8 |
| WP-10 | 1 | EGF pilot end to end: `lean/EGF`, anchors, exposition, fresh body, PDF with computed badges | PROPOSED | 2026-09-19 | DEC-3 |
| WP-11 | 0 | The double DAG: `tools/doubledag.py` (principals, witnesses, twin edges, the flat baseline) | DONE | 2026-09-20 | DEC-5; measured on the GFN pair, `reports/doubledag/gfnbounds/` |
| WP-12 | 0 | The Opus backend: `tools/llm.py`, cassettes, refusal on an invented name, `verify` | DONE | 2026-09-20 | DEC-5; 9 cassettes, 6.40 USD recorded |
| WP-13 | 0 | `tools/dag_reconcile.py` and its proposals on the GFN pair | DONE | 2026-09-20 | DEC-5; 9 edges read, none applied — OQ-6 |
| WP-14 | 0 | The test suite: 50 tests, offline; `make test`, `gate-tests`, `gate-cassettes` | DONE | 2026-09-20 | DEC-5 |
| WP-15 | 2 | ETT: the strict library `Causal`, first layer — causalities, the causal vocabulary, strong causality, global hyperbolicity, `K^±`, the generated causality and absolute minimality, the three lines, admissible measures. 12 modules, no `sorry`, every declaration within the standard axioms (`make -C lean-causal check`) | IN-REVIEW | 2026-09-26 | awaits the author's reading of the statements; grown in `lean-causal/` while `lean/` is a read-only submodule (OQ-11, WP-8); 37 labels closed, 7 partial in `papers/ett/ledger/` |
| WP-16 | 2 | ETT: the scaffold library `CausalScaffold`, the layer of the curves — causal and chronal curves, causal arc-connectedness, `prop:cac_engendre`, `lem:pushup_local`, `lem:restriction_convexe`. No `sorry`; in the scaffold because the definition of a causal curve is a reading | DONE | 2026-10-29 | OQ-7 ruled by DEC-6: graduated into `lean-causal/Causal/`; nine rows in bucket A, closure 46 of 137 |
| WP-17 | 2 | `tools/ledger_curate.py`: the curated fields of a ledger written from an authored `certificate/curation.toml`, with its tests | DONE | 2026-09-26 | 9 tests; `papers/ett/certificate/curation.toml` is its first user |
| WP-18 | 2 | ETT: what formalizing found in the paper, recorded per label in the ledger (`paper_findings`) and triaged | IN-REVIEW | 2026-09-26 | five findings would change a sentence (OQ-7, OQ-8, OQ-9, OQ-10); the `.tex` is not touched; three of them ruled on 2026-09-27 (DEC-6, DEC-7, DEC-8) |
| WP-19 | 2 | ETT: the ledger brought to the GFN model — every row triaged (bucket, size, note), sections and statement numbers, milestones and roadmap, `trace_check` and `SORRY-STATUS` on the Lean side, `ledger_curate --check` in the gate | IN-PROGRESS | 2026-09-27 | DEC-9; plan Part A |
| WP-20 | 2 | ETT: the agent campaign, wave 1 — morphisms and time functions, three examples, push-up cores, gluing topology, local-to-global admissible measures | IN-REVIEW | 2026-10-29 | DEC-9; five packages, each audited read-only by a second agent; 8 modules graduated into `Causal/` (22 strict, 0 `sorry`), `Morphism` and `PushoutCausal` stay in the scaffold on OQ-12; 19 labels stated, 3 closed, closure 49 of 137; OQ-12…OQ-16 raised; reports in `lean-causal/campaign/` |
| WP-21 | 2 | ETT: the agent campaign, wave 2 — chains, Cauchy surfaces and Geroch, (G,X)-structures | IN-REVIEW | 2026-10-30 | DEC-9; three packages, each audited read-only and re-audited after the rulings DEC-12…DEC-16; 7 modules graduated (`Causal` 29 modules, 0 `sorry`); `GerochEquiv` (the cited (iii)⇒(i)) and `GXSingular` (OQ-19) stay in the scaffold; 5 labels closed (`def:cauchy_surface`, `def:cauchy_time_function`, and the three of WP-1 under DEC-12), closure 54 of 137; OQ-17…OQ-19 raised |
