# LeanArticles — standing instructions

One repository for formalizing the author's research in Lean: a **common Lean library** and the
**papers rebuilt from it**. Each paper project starts from an old draft that is a *story source*
only: its statements and their dependencies are extracted (`tools/ledger.py`), its story is
rewritten fresh in `papers/<slug>/STORY.md`, and its prose is never reused — `make check` fails
on any twelve-word run shared with `legacy/orig/`. The plan this follows is
`~/.claude/plans/the-objective-of-this-woolly-koala.md` (2026-09-19).

## Hosts

**Check `hostname`.** `node1` is canonical: it runs `lake`, every gate and every commit
(`tools/host_guard.py` refuses `make check` elsewhere). The laptop `hyperlolipop` edits
`papers/**/*.tex`, `STORY.md` and `certificate/exposition/*.md` through the Dropbox copy, in Kile.
The repository lives at `~/Dropbox/LeanArticles`, symlinked as `~/LeanArticles`.
`lean/.lake` carries the xattr `user.com.dropbox.ignored` so a Lean build never syncs; set it
again with `python3 tools/dropbox_ignore.py` if the directory is ever recreated.

**Never create a git worktree of this repository.** The Lean build is 8 GB and is not
worktree-portable; parallel work uses short-lived `lane/*` branches in the single checkout.

## The GFN line (freeze retired, DEC-131; absorbed in-tree, DEC-157)

The DEC-2 freeze ended with the ICLR deadline and was retired by DEC-131. DEC-157 (OQ-1) absorbed
GFNBoundsLean in-tree as the seed of `lean/` (T-gfn-absorb: a subtree merge of its `main` at
`2e9865c`, so its history is kept): `lean/` is no longer a submodule, and its gate runs as a hub
package. `tools/leanlink` stays a read-only submodule. `lib-check` runs `make -C lean check`,
which regenerates the tracked `lean/docs/` and `lean/paper-map.json`: restore them with
`git -C lean checkout -- .` after a gate, unless regenerating them is what the commit is for.
The other packages merge into `lean/` eventually (DEC-158), not yet.

## Layout

| path | what |
|---|---|
| `lean/` | the Lean library: one package, per project a strict lib (`warningAsError`, `sorry` is an error) and a scaffold lib; `projects.toml` lists them and every audit iterates it |
| `lean-causal/` | the ETT library (`Causal` strict, `CausalScaffold` scaffold), a package of its own at the hub's pin **until the packages merge into `lean/`** (DEC-158; OQ-11); laid out so that moving it into `lean/` is a file move. `make -C lean-causal check` is its gate; read `lean-causal/README.md` |
| `papers/<slug>/` | one per paper: `paper.toml`, `STORY.md`, `legacy/` (frozen snapshot + `MANIFEST.json`), `ledger/` (generated statement ledger + DAG), `certificate/` (anchors, exposition), `paper/body/**` (prose only) and `paper/generated/**` |
| `tools/` | the gates and generators (stdlib Python); `tools/leanlink` is the LeanLink submodule; `tools/cassettes/` holds every recorded model exchange |
| `tests/` | the tools' own tests, run by `make check`; they replay cassettes and never call a model |
| `reports/` | measured evidence: `doubledag/gfnbounds/` is the double DAG of the one pair where both halves exist |
| `registers/` | WORK, QA, DECISIONS, RISKS, DEPS — state, kept by the project-manager agent, gated by `tools/registers.py` |
| `bib/note.bib` | the master bibliography |

## The double DAG

Two graphs over one mathematics, and the reason this repository holds both halves.

- **The statement DAG** is read top-down off the draft: nodes are `\label`s, edges are the
  references a statement or its proof makes (`tools/ledger.py`).
- **The Lean DAG** is read bottom-up off the compiled environment: nodes are declarations, edges
  are `uses_type` (the statement's vocabulary) and `uses_value` (the proof term's).

`tools/doubledag.py` couples them through the map `label -> declarations` and compares them edge
by edge. The projection goes through **principals**: within a label, a declaration that another
declaration of the same label transitively uses is *subordinate*; the rest are principals, and a
walk stops only at another label's principal. That is what stops a helper listed under two labels
from fabricating an edge between them — measured on the GFN pair, it removes 55% of the Lean-only
edges while keeping 66% of the agreements (`reports/doubledag/gfnbounds/DOUBLEDAG.md`).

Every edge is `both`, `lean-only`, `tex-only`, `twin` (a body statement and its full form: a
restatement, not a dependency) or `tex-only-unformalized`. **A Lean edge carries a witness**: the
shortest chain of declarations from one principal to the other. An edge a reader cannot check is
an assertion, not evidence.

`tools/dag_reconcile.py` asks Claude Opus what a disagreement *means* — one edge per question,
with both statements, the witness chain and each declaration's elaborated type in front of it —
and writes proposals. It never edits the ledger, the draft or the map: **the model proposes and
the author disposes.** Every exchange is recorded in a cassette under `tools/cassettes/`, so the
tests replay them offline for nothing and a reviewer reads what was asked beside what came back.
**No gate calls a model** (`tests/test_no_model_in_gates.py`, which runs the whole gate with
every ask refused).

## Rules that are gates, not advice

- **Reports are generated, never written.** Everything under `papers/*/ledger/` and
  `papers/*/paper/generated/` is regenerated and diffed by `make check`; a hand edit fails `nohand`.
- **The badge is never authored.** A statement's certification status is computed from the Lean
  closure (`certified` / `certified*` / `stated, unproved` / `not yet formalised`).
- **`paper/body/**` contains no mathematics environment, no proof or sketch, and no number.**
  Statements arrive through `\input{generated/tip/…}`; numbers through `\num…`.
- **Lean ≥ paper, never Lean < paper.** A Lean declaration narrower than the paper statement is
  never its anchor. Iceberg: as few story-sized anchors as possible, assembly theorems preferred.
- **The Lean kernel is the proof checker.** Auditors check that the Lean *statement* is the paper's,
  not the proof. Scaffold placement is not a `sorry`: read the sorry count, not the directory.
- **A gate must be able to fail.** Every gate has a fixture under `tools/fixtures/<gate>/` and
  `make selftest` fails if the gate passes on it. Absence of the checked thing is a failure.
- **No LLM call and no Lean build inside the TeX compile.** Binders resolve biber-style
  (`.llk` → `.llr`) between passes.
- **Every legacy statement gets a `\label`** in `legacy/labeled/`; the ledger keys on labels and
  `ledger.py check` fails on an unlabeled statement environment.
- **A model proposes, it never decides.** No gate calls one; every exchange is recorded; an
  answer naming a label or a declaration that does not exist is refused, not returned.
- `pipefail` in every Makefile; never `cmd | tail` without it; assert every programmatic edit.

## The completion team (`/atlas-team`)

`roadmap/roadmap.toml` lists the targets beyond what the ledgers record as closed (schema in its
header; `python3 tools/roadmap.py check|status|next|set|gates`). The skill
`.claude/skills/atlas-team/SKILL.md` runs one iteration: pick one action, dispatch the agent
(`.claude/agents/`: `roadmap-planner`, `atlas-builder`, `target-closer`, then `target-auditor`),
graduate what the audit passes, curate, gate, commit and push, journal (`roadmap/JOURNAL.md`).
Run it once with `/atlas-team` or unattended with `/loop /atlas-team`. It never rules: a reading
becomes an OQ row and the target waits; a `needs-ruling` target moves only on a DEC row. The
atlas (`reports/atlas/`, `make -C reports/atlas`) draws the ledgers with the roadmap overlaid.

## The ETT programme (`/ett-programme`)

ETT is a reasoning system for causality (the author, 2026-11-20). Every result is factored into a
causal-topological argument, the localisation properties it needs, geometric lemmas per model
proving them, and classification criteria (`programme/README.md`). The programme's roadmap is
`programme/roadmap.toml`, its causality ladder `programme/ladder.toml` (`tools/ladder.py`; the
`causal_ladder` tactic is generated from it), and each ledgered Sbierski paper has a binder
`papers/<slug>/certificate/binder.toml` (`tools/binder.py`). The loop is
`.claude/skills/ett-programme/SKILL.md` with the agents programme-planner, ladder-keeper,
tactics-builder, publisher (and target-closer/target-auditor for layers 1 and 3). It shares this
checkout with `/atlas-team` through leases (`tools/lease.py`): each loop takes the paths it works on,
commits with `git commit --only` its own paths, and rebuilds only the ledgers whose Lean root it
committed into.

## The EGF programme (`/egf-programme`)

*Ergodic Generative Flows* is fully formalized **and corrected** by a loop of its own (DEC-141,
2026-11-21), modelled on the ETT programme: `.claude/skills/egf-programme/SKILL.md`, lease name `egf`,
charter `papers/egf/programme/README.md`, roadmap `papers/egf/programme/roadmap.toml`. Its agents are
egf-planner, paper-corrector, tex-lean-checker, egf-experimenter (and target-closer/target-auditor
for lean-egf). Its corrections register `papers/egf/programme/corrections.toml` (gate:
`tools/corrections.py check`) records every place the paper is wrong or short: refutation, corrected
form, Lean anchor, status `found → proved → adopted → applied → reviewed`. Under DEC-141's standing
ruling the loop adopts the smallest correction proved sufficient; genuine readings stay OQ rows.
Adopted corrections are applied to the arXiv v2 working copy `~/Dropbox/ErgodicGFN arXiv/source`
(outside the hub, its own git repository, no remote; the author reviews the diff and uploads). The
experiments are reproduced in the private `LBrunswic/egf-reproduction` (`node1:~/egf-reproduction`),
GPU work on node1 only. `/atlas-team` leaves `lean-egf` and `papers/egf` to this loop.

## Governance (light, DEC-1)

`registers/DECISIONS.md` is the authority for the author's rulings (append-only, `DEC-n`).
The project-manager agent organises, records and evaluates nothing; only the author decides.
Mathematics, priorities, what runs and what is committed remain the author's.
