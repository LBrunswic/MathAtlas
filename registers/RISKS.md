# Risk register

Probability and impact: `L · M · H`. Status: `OPEN · MITIGATED · OCCURRED · CLOSED`.

| R | Raised | Risk | Prob | Impact | Response | Owner | Status |
|---|---|---|---|---|---|---|---|
| R-1 | 2026-09-19 | Work here destabilises the ICLR submission (GFNCertified, due 2026-09-25) | M | H | Avoid: DEC-2 freeze; submodules read-only; `FREEZE=1` skips `lib-check` and expires | AUTHOR | OPEN |
| R-2 | 2026-09-19 | The 8 GB Lean build syncs into Dropbox | M | M | Avoid: `tools/dropbox_ignore.py` sets the xattr before any build; `make check` verifies it | BUILD | MITIGATED |
| R-3 | 2026-09-19 | Old prose leaks into the new papers and the "forget the first writing" rule erodes | M | H | Reduce: `tools/no_legacy_prose.py` on every check; legacy frozen by manifest | BUILD | OPEN |
| R-4 | 2026-09-19 | Drafts with no git and no remote (ETT, GX, GFN Bounds, Void Dynamics) are lost | L | H | Reduce: byte-identical snapshots with manifests in this repository, pushed to GitHub | BUILD | MITIGATED |
| R-5 | 2026-09-19 | The non-acyclic GFlowNet `.tex` is not found and the paper cannot get a ledger | M | M | Accept: `ledger.py` refuses `source = "pdf"` (exit 2) so the gap stays visible; OQ-3 | AUTHOR | OPEN |
