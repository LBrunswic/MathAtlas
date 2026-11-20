---
name: ett-programme
description: One iteration (a wave) of the ETT programme team. It builds the roadmap that splits causal-topological statements from geometric ones, ledgers Sbierski's papers and binds them to ETT, organises the causality ladder, closes abstract and localisation targets, builds ladder automation, and publishes the blueprint and progress reports. Agents run in parallel; integration happens once per wave, then gates, commit and push. Run it once with /ett-programme, or unattended with /loop /ett-programme. Shares the checkout with /atlas-team through leases.
argument-hint: "[once | status | <target-id>]"
allowed-tools: Read, Write, Edit, Bash, Glob, Grep, Agent, SendMessage
---

# /ett-programme: one iteration (a wave) of the ETT programme

The programme is defined in `programme/README.md`. ETT is a reasoning system for causality. Each
result is factored into four layers:
1. a causal-topological global argument;
2. the localisation properties it needs;
3. a geometric lemma, per model, proving them;
4. classification criteria.

You are the **master**. The agents plan, organise, prove, build tactics and publish. You alone
graduate, curate, set up papers, move statuses, gate, commit and push. The author alone rules.
`CLAUDE.md` binds you, and so do the rulings in `registers/DECISIONS.md`.

The files of this loop:
- `programme/roadmap.toml` (always passed to `tools/roadmap.py` as `--file programme/roadmap.toml`);
- `programme/ladder.toml`;
- `programme/JOURNAL.md`;
- the binders `papers/<slug>/certificate/binder.toml`.

Its lease name is `programme`.

Arguments:
- `status`: print the roadmap status, `tools/ladder.py check`, `tools/binder.py status` and the
  last journal entry, then stop.
- `<target-id>`: work that target instead of choosing.
- `once`, or nothing: a normal iteration.

## 0. Preconditions: stop the iteration if one fails

1. `hostname` is `node1`. Then `cd /home/maxbrain/Dropbox/LeanArticles`.
2. **Your lease.** `python3 tools/lease.py show`. If a `programme` lease is held by a live pid other
   than this session's process, another iteration is running: stop. Otherwise take the base lease
   `python3 tools/lease.py take programme <pid of this session's process> programme`. Do not use
   `$$`, which is a short-lived shell.
3. `python3 tools/lease.py tree programme` passes. Every changed path is held by you or by another
   live loop (`/atlas-team` holds its own). A change nobody holds means a human is working: stop
   and say so.
4. `git pull --ff-only origin main`. It works with the other loop's uncommitted changes as long as
   they do not conflict. If it is not a fast-forward, stop.
5. Both roadmaps pass `check`, and `python3 tools/ladder.py check` and `python3 tools/binder.py check`
   pass.

## 1. Evaluate

- Run `python3 tools/roadmap.py --file programme/roadmap.toml status` and `tools/ladder.py check`.
  The summary line says how many ladder pairs are classified.
- New DEC rows since the last journal entry move `needs-ruling` targets, as in `/atlas-team` step 1.
- Read the last three entries of `programme/JOURNAL.md`, and the last entry of
  `roadmap/JOURNAL.md`. The other loop may have closed something you depend on, such as the E₀ port.

## 2. Choose the wave

The caps are `MAX_PARALLEL` and `MAX_PER_PACKAGE` in `tools/roadmap.py`. They are shared with
`/atlas-team`, and the leases enforce them across the two loops. Take the first rule that applies:

1. **Resume** `active` targets, at the step their campaign directory shows. Then top up with rule 3.
2. **Plan**, alone, when either holds:
   - fewer than two `ready` abstract or localisation targets, or
   - a paper was set up since the planner last ran (its binder target becomes `ready`).

   Dispatch **programme-planner**. A planning run edits the roadmap, so it is never part of a
   wave.
3. **The wave:**
   `python3 tools/roadmap.py --file programme/roadmap.toml wave --owner closer,master,keeper,tactician,publisher`.
   For each target, take its lease **before** dispatching, at the finest grain:
   - a closer or tactician: its new files and `<package>/campaign/<id>/`;
   - the keeper: `programme/ladder.toml`;
   - the publisher: `reports/blueprint` or `reports/programme`;
   - the master: `papers/<slug>`.

   If `take` refuses because `/atlas-team` holds an overlapping path, leave that target out of the
   wave.
4. Nothing is dispatchable: write "idle: waiting on rulings or on /atlas-team", listing what
   blocks, and stop the loop.

## 3. Act

Set every target of the wave `active`, then dispatch every agent at once, in the background, in
one message.

| owner | agent | dispatch |
|---|---|---|
| keeper | **ladder-keeper** | the target block, and the `matrix` summary |
| tactician | **tactics-builder** | the target block, the package, the new files, the report directory |
| publisher | **publisher** | the target block |
| closer (`abstract`) | **target-closer** | as in `/atlas-team` (block, package, labels if any, new files, report directory), **plus the layer-1 rule:** the module imports only the ETT layer of lean-causal. It does not import `Causal.Minkowski`, `Causal.Static`, `Causal.Flat.*`, `Causal.Model.*`, `Causal.Port.*` or `Causal.SingularFlat`. Its hypotheses are ladder properties (the target's `uses`) or explicit localisation hypotheses, and its statement mentions no metric, curve length or geodesic. Try `causal_ladder` first when it exists. |
| closer (`localisation`) | **target-closer** | the same, **plus the layer-3 rule:** state, for the target's `model`, the ladder properties it `provides`, as instances of the ladder definitions, so the abstract theorems apply to the model without restatement |
| master | yourself | the set-up of `/atlas-team`'s skill (§ set up). For a Sbierski paper the Lean root is lean-causal, the source comes from arXiv into `papers/<slug>/sources/` (the archived text in `references/sbierski/text/` is the extraction, not the LaTeX), and labels are prefixed per paper (`mghd:`, `ers:`, …) |

As each closer or tactician reports, dispatch **target-auditor** with the same dispatch. For
`abstract` targets, tell it to check the layer-1 rule:
- grep the imports;
- read the statement for metric notions;
- check that each hypothesis is a ladder property or a declared localisation hypothesis.

A `major` verdict gets one fix round, as in `/atlas-team`. The keeper's and the publisher's work is
checked by its own tool and gate (`ladder.py check`, two identical builds, zero page errors), not
by the auditor.

**Integrate once, at the end of the wave:**
- graduate clean Lean files: take a lease on the package's root file `Causal.lean` only for the
  moment you edit it, then `make -C <package> check`;
- `python3 tools/ladder.py emit-lean` whenever ladder edges became `checked`, then rebuild
  `Causal.Ladder.Rules` in the same commit;
- curate the ledgers of the papers whose rows a target closed;
- write the OQ rows for readings, as in `/atlas-team` (never a DEC row);
- set up the papers;
- run `make ledgers`.

A failed target leaves the wave as `ready` or `blocked`, with its reason recorded. Its files are
reverted or stay in the scaffold.

## 4. Gates: nothing may get redder

- `make -C <package> check` for every package touched.
- `python3 tools/ladder.py check`, `python3 tools/binder.py check`, and both roadmaps' `check`.
- `python3 -m unittest tests.test_programme tests.test_roadmap`.
- `make -k check 2>&1 | tee /tmp/ett-programme-gate.log`, then
  `python3 tools/roadmap.py --file programme/roadmap.toml gates /tmp/ett-programme-gate.log`.
  Then restore the read-only submodule with `git -C lean checkout -- .`.
  - If the hub gate fails **on a path `/atlas-team` holds**, it is the other loop's work in
    progress, not yours. Record it in the journal and do not revert.

## 5. Commit and push: only what you hold

**Ledgers in a shared checkout.** `make ledgers` rewrites every paper's ledger, and a ledger moves
whenever its Lean root gets a commit, from either loop. So do not run `make ledgers`. For each
paper whose Lean root you committed into (lean-causal: ett, barbot and the Sbierski papers; lean-gx:
gx, bbs; lean-benzecri: benzecri), take `tools/lease.py take programme <pid> papers/<p>/ledger` for the
moment, rebuild with `python3 tools/ledger.py -c papers/<p>/ledger/ledger.toml build`, commit
`--only` those files, and drop that lease. Lease `registers/DECISIONS.md` the same way while you
append an OQ row.

Commit with `git commit --only $(python3 tools/lease.py mine programme) …`, never `-a`. This keeps
the other loop's staged work out of your commits.
1. One commit per target: its Lean, curation, registers, ladder, binder, report or site.
2. Then `make ledgers` and the blueprint rebuild, and commit those.
3. Then the roadmap statuses: `python3 tools/roadmap.py --file programme/roadmap.toml set <id> done --commit <sha>`
   for each target, and commit.

Messages follow the repository's style, with `Host: node1` and the Co-Authored-By trailer. Push a
fast-forward of `main`, retrying network errors up to four times. Then drop every lease except the
base one.

## 6. Journal and hand-off

Append to `programme/JOURNAL.md`:

```
## <date> <time> · wave of K · <ids>
- per target: <id> (<kind>, layer n): result; audit verdict
- ladder: <classified>/<pairs> pairs, <checked> checked edges, <consequences> consequences
- binders: <tools/binder.py status lines>
- gates: package ✓, ladder ✓, binder ✓, roadmaps ✓, hub: no new red
- commits: <shas>
- next: <what `wave` would pick now>
```

Commit it, then drop the base lease (`tools/lease.py drop programme`). Give the user three lines:
1. what was done;
2. what the author is asked;
3. what comes next.

## Stop conditions for /loop

Stop when any of these holds:
- two consecutive iterations end without a commit;
- the push is rejected;
- a gate turns red because of your own work and cannot be reverted;
- only rulings, or only `/atlas-team`'s leases, block the remaining targets.

## Never

- Write a DEC row or decide a reading. Mark a corrected form without a ruling.
- Edit a path another loop holds, or commit one: `--only` with your own lease.
- Edit `reports/atlas/` (it belongs to `/atlas-team`), `legacy/`, the `lean/` submodule, or a
  generated file by hand. Generated files include `Causal/Ladder/Rules.lean`, the ledgers, the site
  and the report numbers.
- Let a layer-1 (`abstract`) module import a model or a metric.
- Run two `lake build`s of one package at once, create a worktree, or push anything but a
  fast-forward.
