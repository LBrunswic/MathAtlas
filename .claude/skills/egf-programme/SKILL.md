---
name: egf-programme
description: One iteration (a wave) of the EGF programme team, which fully formalizes and corrects the paper Ergodic Generative Flows (DEC-141). It plans; closes Lean targets in lean-egf; adopts proved corrections under the standing ruling; applies adopted corrections to the arXiv v2 working copy and checks each edit against its Lean anchor; and runs the reproduction experiments on node1's GPU. Agents run in parallel; integration happens once per wave, then gates, commits and push. Run it once with /egf-programme, or unattended with /loop /egf-programme. Shares the checkout with /atlas-team and /ett-programme through leases.
argument-hint: "[once | status | <target-id>]"
allowed-tools: Read, Write, Edit, Bash, Glob, Grep, Agent, SendMessage
---

# /egf-programme: one iteration (a wave) of the EGF programme

The programme is defined in `papers/egf/programme/README.md`; read it first. Its rulings are
DEC-141 (the standing ruling, and OQ-49, 50, 55, 60, 66 and the families).

You are the **master**. The agents plan, prove, correct, check and experiment. You alone:
- graduate, curate, move statuses, adopt corrections, gate, commit and push;
- **adopt** a correction (`found/proved → adopted`), and only under a DEC row that rules it.
  DEC-141's standing ruling covers a correction whose printed form Lean refutes, or which repairs
  a proof, a missing hypothesis or a convention, when its corrected form is proved. It does not
  cover a genuine reading between two different statements: that is an OQ row, and the entry
  waits.

The author alone rules. `CLAUDE.md` binds you, and so do the rulings in `registers/DECISIONS.md`.

The files of this loop:
- `papers/egf/programme/roadmap.toml` (always passed to `tools/roadmap.py` as
  `--file papers/egf/programme/roadmap.toml`);
- `papers/egf/programme/corrections.toml` (`tools/corrections.py`);
- `papers/egf/programme/JOURNAL.md`;
- `lean-egf/` and `papers/egf/`.

Outside the hub:
- the v2 working copy `~/Dropbox/ErgodicGFN arXiv/source` (its own git repository, no remote);
- the reproduction repository `~/egf-reproduction` (private GitHub `LBrunswic/egf-reproduction`).

Its lease name is `egf`.

Arguments:
- `status`: print the roadmap status, `tools/corrections.py status`, `git -C <v2> log --oneline -5`
  and the last journal entry, then stop.
- `<target-id>`: work that target instead of choosing.
- `once`, or nothing: a normal iteration.

## 0. Preconditions: stop the iteration if one fails

1. `hostname` is `node1`. Then `cd /home/maxbrain/Dropbox/LeanArticles`.
2. **Your lease.** `python3 tools/lease.py show`. If an `egf` lease is held by a live pid other than
   this session's process, another iteration is running: stop. Otherwise take the base lease
   `python3 tools/lease.py take egf <pid of this session's process> papers/egf/programme`. Do not use
   `$$`, which is a short-lived shell.
3. `python3 tools/lease.py tree egf` passes. Every changed path is held by you or by another live
   loop. A change nobody holds means a human is working: stop and say so.
4. `git pull --ff-only origin main`. If it is not a fast-forward, stop.
5. All three must pass:
   - `python3 tools/roadmap.py --file papers/egf/programme/roadmap.toml check`;
   - `python3 tools/corrections.py check`;
   - `git -C "$HOME/Dropbox/ErgodicGFN arXiv/source" status --porcelain` is empty. If not, the
     author is editing the paper: leave every `correct` target out of this iteration.

## 1. Evaluate

- `python3 tools/roadmap.py --file papers/egf/programme/roadmap.toml status` and
  `python3 tools/corrections.py status`.
- **New DEC rows** since the last journal entry: move the `needs-ruling` and `blocked` targets they
  rule, with `--evidence "DEC-n: …"`. Set each OQ row they answer to `RULED (DEC-n)`; OQ rows are
  edited in place, DEC rows never are.
- **Adoption.** Every `proved` entry of `corrections.toml` whose basis DEC-141 (or a later DEC
  row) covers is adopted, as in § 3 "adopt". This is cheap master work: do it every iteration.
- Read the last three entries of `papers/egf/programme/JOURNAL.md` and the last entry of
  `roadmap/JOURNAL.md` and `programme/JOURNAL.md`: the other loops may hold lean-egf's neighbours or
  the registers.

## 2. Choose the wave

The caps are `MAX_PARALLEL` and `MAX_PER_PACKAGE` in `tools/roadmap.py`, shared with `/atlas-team`
and `/ett-programme`; the leases enforce them across the loops. Take the first rule that applies:

1. **Resume** `active` targets, at the step their campaign directory or their journal line shows.
   Then top up with rule 3.
2. **Plan**, alone, when either holds:
   - a planner target is `ready` (`python3 tools/roadmap.py --file papers/egf/programme/roadmap.toml next --owner planner`);
   - fewer than two `ready` targets remain for closer, corrector and experimenter together.

   Dispatch **egf-planner**. A planning run edits the roadmap, so it is never part of a wave.
3. **The wave:**
   `python3 tools/roadmap.py --file papers/egf/programme/roadmap.toml wave --owner closer,master,corrector,experimenter`.
   Correctors and experimenters come one at a time; `wave` already enforces that. For each target,
   take its lease **before** dispatching, at the finest grain:
   - a closer: its new files and `lean-egf/campaign/<id>/`;
   - a master target: the paths it edits (`papers/egf/certificate/curation.toml`,
     `papers/egf/ledger`, `registers/DECISIONS.md` only for the moment you edit them);
   - a corrector and an experimenter: nothing in the hub (they write outside it), but record the
     target `active` first.

   If `take` refuses because another loop holds an overlapping path, leave that target out.
4. Nothing is dispatchable: write "idle: waiting on rulings or on another loop", listing what
   blocks, and stop the loop.

## 3. Act

Set every target of the wave `active`, then dispatch every agent at once, in the background, in
one message.

| owner | agent | dispatch |
|---|---|---|
| closer | **target-closer** | as in `/atlas-team` (block, package `lean-egf`, labels, new files, report directory `lean-egf/campaign/<id>/`), with the roadmap file named: `papers/egf/programme/roadmap.toml`. Add **the corrected-form rule**: (a) state the strongest true form with the fewest added hypotheses, each named; (b) keep the printed form as a Prop beside its refutation; (c) port from GFNBounds (`lean/GFNBounds/**`, read-only) by copying with a provenance comment `-- ported from GFNBounds.<Name> (lean/<file>:<line>)`, never by importing it (lean-egf kb 0001, OQ-1); (d) report, for each proved correction, the corrections entry `C-n` it anchors and the declaration names. |
| corrector | **paper-corrector** | the target block; the list of `adopted` entries whose `batch` is this target (full TOML of each); the v2 path; the rule that it edits `source/main.tex` only, one marker comment `% EGF-C<n>` per edit, and `latexmk` must stay green on node1 |
| experimenter | **egf-experimenter** | the target block; the repository path `~/egf-reproduction`; the conda env; what the previous repro targets left (their result paths) |
| master | yourself | see "adopt" and "package" below |

**Checks, as each agent reports:**
- A closer's REPORT gets **target-auditor**, with the same dispatch.
- A corrector's batch gets **tex-lean-checker**, with the batch's entries and `git -C <v2> diff`. The
  corrector does not commit; you do, after the check.
- A `major` verdict gets one fix round, sent back to the same agent with SendMessage, then a second
  check. Still `major`: nothing integrates, and the target goes back to `ready` with the findings in
  `evidence`.
- An experimenter's run is checked by its own artefacts: the result files it names exist, the
  smoke test passes, and `scripts/guard.py` was used.

### adopt (master)

For each entry to adopt:
1. Check its `anchor` names the corrected form (read the declarations' statements, not only their
   names), and that `corrected`, `summary` and `added_hypotheses` describe that form faithfully.
2. Add the ruling DEC row to `basis`, then run `python3 tools/corrections.py set C-n adopted`, which
   refuses an entry that breaks a rule.
3. Curate `papers/egf/certificate/curation.toml` for its label: `decls`, `notes` (the entry, DEC-141),
   `lean_proved_override` / `blocked_on`. A row whose corrected form is now the form of record
   closes, as T-ett-ruled-rows did for DEC-7/DEC-8. The printed form stays a Prop with its
   refutation, and the finding stays in `paper_findings`.

### package (master, `T-egf-v2-package`)

In the v2 working copy:
1. Append a "Changes from v1" appendix from `python3 tools/corrections.py errata --format tex`.
2. Build with `latexmk -pdf` on node1.
3. Rebuild `../source.tar.gz` (only the files the build reads, `main.bbl` for the bibliography;
   check it in a clean temporary directory with `pdflatex` alone) and `../preview.pdf`.
4. Commit in v2. **Never upload, never add a remote.** The author reviews `git diff camera-ready..HEAD` (the tag of the first commit: the camera-ready plus the equal-contribution stars).

**Integrate once, at the end of the wave:**
- graduate clean Lean files (`git mv` scaffold → `lean-egf/EGF/`, module path and namespace,
  import added to `EGF.lean`; take a lease on `lean-egf/EGF.lean` only for the moment you edit it),
  then `make -C lean-egf check`;
- move corrections entries: `proved` for those a graduated declaration now anchors (add `anchor`),
  then adopt as above;
- for a checked corrector batch: commit in v2, one commit per batch, message
  `EGF-C<n>[,…]: <summary>`. Then `python3 tools/corrections.py set C-n applied --commit <v2 sha>`
  for each entry;
- write the OQ rows for genuine readings (never a DEC row);
- rebuild the egf ledger (see § 5).

A failed target leaves the wave as `ready` or `blocked`, with its reason recorded. Its files are
reverted or stay in the scaffold.

## 4. Gates: nothing may get redder

- `make -C lean-egf check` when lean-egf was touched (`PATH=$HOME/.elan/bin:$PATH`).
- `python3 tools/corrections.py check` and both of this loop's roadmap checks
  (`tools/roadmap.py --file papers/egf/programme/roadmap.toml check`, and the hub's `check`).
- `python3 -m unittest tests.test_corrections tests.test_roadmap`.
- `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex` in the v2 working copy, when it
  changed: no error, no undefined reference or citation.
- `make -k check 2>&1 | tee /tmp/egf-programme-gate.log`, then
  `python3 tools/roadmap.py --file papers/egf/programme/roadmap.toml gates /tmp/egf-programme-gate.log`.
  Then restore the read-only submodule with `git -C lean checkout -- .`.
  - If the hub gate fails **on a path another loop holds**, it is that loop's work in progress,
    not yours. Record it in the journal and do not revert.

## 5. Commit and push: only what you hold

**The ledger.** Do not run `make ledgers` (it rewrites every paper's ledger). Take
`tools/lease.py take egf <pid> papers/egf/ledger` for the moment, then rebuild with
`python3 tools/ledger.py -c papers/egf/ledger/ledger.toml build`, commit `--only` those files, and
drop that sub-lease. Lease `registers/DECISIONS.md` the same way while you append an OQ row or set
one `RULED`.

**Restatements.** A rebuilt ledger may carry a new strong candidate: a finding saying `FALSE` or "false as printed/written", or a `not_…`/`Cex` declaration. The `restate` gate of papers-check then fails until it is registered. Take the lease of `papers/egf/certificate/restatements.toml` and `RESTATED.md`, run `python3 tools/restate.py seed egf`, and commit them with the ledger. `/restate` rewrites them; never write a rewrite yourself.

In the hub, commit with `git commit --only $(python3 tools/lease.py mine egf) …`, never `-a`:
1. One commit per target: its Lean, curation, corrections entries, registers.
2. Then the ledger, and commit it.
3. Then the roadmap statuses:
   `python3 tools/roadmap.py --file papers/egf/programme/roadmap.toml set <id> done --commit <sha>`.
   For a `correct` target, `<sha>` is the hub commit that moved its entries to `applied`. For a
   `repro` target, it is the hub commit that recorded the reproduction repository's commit in the
   target's `evidence`. Then commit.

Messages follow the repository's style, with `Host: node1` and the Co-Authored-By trailer. Push a
fast-forward of `main`, retrying network errors up to four times. In the reproduction repository,
commit and push to its private remote. In v2, commit only, and never add a remote. Then drop every
lease except the base one.

## 6. Journal and hand-off

Append to `papers/egf/programme/JOURNAL.md`:

```
## <date> <time> · wave of K · <ids>
- per target: <id> (<kind>): result; audit/check verdict
- corrections: <tools/corrections.py status summary line>
- ledger: <closed>/<16> rows closed (bucket A)
- v2: <last commit, one line>; repro: <last result, one line>
- gates: lean-egf ✓, corrections ✓, roadmaps ✓, v2 build ✓, hub: no new red
- commits: <shas> (hub) · <shas> (v2) · <shas> (repro)
- asks: <OQ rows written or still open>
- next: <what `wave` would pick now>
```

Commit it, then drop the base lease (`tools/lease.py drop egf`). Give the user three lines:
1. what was done;
2. what the author is asked;
3. what comes next.

## Stop conditions for /loop

Stop when any of these holds:
- two consecutive iterations end without a commit;
- the push is rejected;
- a gate turns red because of your own work and cannot be reverted;
- only rulings, the author's review, or other loops' leases block the remaining targets.

## Never

- Write a DEC row or decide a reading. Adopt a correction without a DEC row that covers it, or
  apply one that is not `adopted`.
- Edit a path another loop holds, or commit one: `--only` with your own lease.
- Edit `legacy/`, the `lean/` submodule, `reports/atlas/`, `programme/`, or a generated file by
  hand (the ledgers, `paper/generated/`).
- Upload anything to arXiv, add a remote to the v2 repository, or make any repository public.
- Run a GPU job anywhere but node1, or train on hyperlolipop (`scripts/guard.py` must pass first).
- Run two `lake build`s of lean-egf at once, create a worktree, or push anything but a fast-forward.
