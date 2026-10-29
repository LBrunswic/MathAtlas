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

## The freeze (until 2026-09-25)

The ICLR 2027 submission is `~/Dropbox/GFNCertified` (paper due 25 Sep 2026). Until then this
repository only *references* `~/GFNBoundsLean` (submodule `lean/`, read-only) and `~/Dropbox/LeanLink`
(submodule `tools/leanlink`): nothing in the GFN line is written from here, `lib-check` is skipped
under `FREEZE=1`, and that variable is a `registers/DECISIONS.md` row whose expiry the gate
enforces. After 25 Sep, GFNBoundsLean is imported in-tree as the seed of the library and GFNCertified
becomes `papers/gfnbounds/` (plan, Phase 1).

## Layout

| path | what |
|---|---|
| `lean/` | the Lean library: one package, per project a strict lib (`warningAsError`, `sorry` is an error) and a scaffold lib; `projects.toml` lists them and every audit iterates it |
| `lean-causal/` | the ETT library (`Causal` strict, `CausalScaffold` scaffold), a package of its own at the hub's pin **while `lean/` is a read-only submodule** (OQ-11); laid out so that moving it into `lean/` is a file move. `make -C lean-causal check` is its gate; read `lean-causal/README.md` |
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

## Governance (light, DEC-1)

`registers/DECISIONS.md` is the authority for the author's rulings (append-only, `DEC-n`).
The project-manager agent organises, records and evaluates nothing; only the author decides.
Mathematics, priorities, what runs and what is committed remain the author's.
