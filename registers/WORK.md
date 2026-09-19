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
