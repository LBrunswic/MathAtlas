# Decisions register

The author's rulings, and the questions awaiting one. Only the author decides. The project-manager
agent appends a ruling the author gave, quoted where the words matter, and never edits a row once
it is committed; `tools/registers.py check` fails if one is. A ruling that reverses an earlier one
is a new row that names it.

## Decisions

| DEC | Date | Decision | By | Context |
|---|---|---|---|---|
| DEC-1 | 2026-09-19 | The hub is `~/Dropbox/LeanArticles`, symlinked as `~/LeanArticles`: one repository for the common Lean library and the papers rebuilt from it; light governance (these registers, gated by `tools/registers.py`), not the PRINCE2 `.pm/` workspace | AUTHOR | Plan `~/.claude/plans/the-objective-of-this-woolly-koala.md`, approved 2026-09-19; answers "Dropbox + symlink", "Light: registers + DECISIONS.md" |
| DEC-2 | 2026-09-19 | The freeze: until 2026-09-25 (ICLR paper deadline; the submission is `~/Dropbox/GFNCertified`) nothing in the GFN line is written from this repository; GFNBoundsLean and LeanLink are pinned as read-only submodules; `lib-check` is skipped under `FREEZE=1`, and the gate fails if that variable is still set after 2026-09-26 | AUTHOR | answer "Pin as submodules now, absorb after 25 Sep" |
| DEC-3 | 2026-09-19 | The first project formalized is EGF (Ergodic Generative Flows), in the GFN line, reusing `GFNBounds.Core`; the non-acyclic GFlowNet paper follows once its `.tex` source is recovered (only the PDF is on node1) | AUTHOR | answer "EGF/NonAcyclic first" |
| DEC-4 | 2026-09-19 | Every legacy draft is snapshotted byte for byte into `papers/<slug>/legacy/orig/` with a sha256 manifest, and `legacy/labeled/` may differ from it by `\label{}` only; the new prose shares no twelve-word run with the legacy (`tools/no_legacy_prose.py`) | AUTHOR | the plan's "forget the first writing", made mechanical |

## Open questions

| OQ | Raised | Question | Blocks | Status |
|---|---|---|---|---|
| OQ-1 | 2026-09-19 | Absorb GFNBoundsLean and GFNCertified in-tree on 26 Sep, or after the ICLR decision so the GitHub URLs stay live for reviewers? | Phase 1 | OPEN |
| OQ-2 | 2026-09-19 | Adopt LeanLink's `@[paper "label"]` attribute as the label-to-declaration binding from the EGF pilot on, or keep `certificate/appendix.toml` only? | Phase 1 step 6 | OPEN |
| OQ-3 | 2026-09-19 | Where is the non-acyclic GFlowNet `.tex` (Overleaf? hyperlolipop?) | papers/nonacyclic | OPEN |
| OQ-4 | 2026-09-19 | Do post-2020 Syracuse notes on hyperlolipop replace the 2020 draft as the story source? | papers/syracuse | OPEN |
