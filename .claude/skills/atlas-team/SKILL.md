---
name: atlas-team
description: One iteration (a wave) of the LeanArticles completion team. Reads the roadmap, picks a wave of up to MAX_PARALLEL independent targets (or one planning run), dispatches the matching agents in parallel (roadmap-planner, atlas-builder, target-closer, then target-auditor), integrates the result, runs the gates, commits, pushes, and writes the journal. Run it once with /atlas-team, or unattended with /loop /atlas-team. Triggers on '/atlas-team', 'run the team', 'next target', 'complete the atlas'.
argument-hint: "[once | status | <target-id>]"
allowed-tools: Read, Write, Edit, Bash, Glob, Grep, Agent, SendMessage
---

# /atlas-team: one iteration (a wave) of the completion team

You are the **master** of the iteration. The agents write, prove, plan and audit. You alone
graduate files, curate ledgers, move roadmap statuses, run gates, commit and push. The author
alone rules. This file is the whole protocol; `CLAUDE.md` at the hub root binds you too.

Arguments:
- `status`: print `python3 tools/roadmap.py status` and the last journal entry, then stop.
- `<target-id>`: work that target instead of choosing one.
- `once`, or nothing: a normal iteration.

## 0. Preconditions: stop the iteration if one fails

1. `hostname` is `node1`. Everything else (gates, lake, commits) is node1-only.
2. `cd /home/maxbrain/Dropbox/LeanArticles`.
3. **The lock.** If `.atlas-team.lock` exists and its pid is alive, another iteration is
   running: stop. Otherwise write the pid of this Claude session's own process (not `$$`, which
   is a short-lived shell), the date and the session id to it. Remove it at the end, on every
   path out.
4. `git status --short` is clean, or shows only the campaign and scaffold files of `active`
   targets from an interrupted wave, which you then resume. Anything else means a human or another session
   is working: stop and say so.
5. `git pull --ff-only origin main`. If it is not a fast-forward, stop.
6. `python3 tools/roadmap.py check` passes.

## 1. Evaluate

- `python3 tools/roadmap.py status`.
- Look for new rulings: `registers/DECISIONS.md` rows dated after the last journal entry. For
  each `needs-ruling` target whose `question` a DEC row now decides, run
  `python3 tools/roadmap.py set <id> ready --evidence "DEC-n: <one line>"`, or `dropped`, as
  ruled. For each `blocked` target whose `oq` is now RULED, move it to `ready`. Only a DEC row
  counts as a ruling.
- Read the last three entries of `roadmap/JOURNAL.md`.

## 2. Choose the wave

The concurrency caps live in `tools/roadmap.py`: `MAX_PARALLEL` targets per wave and
`MAX_PER_PACKAGE` per Lean package. Change them there and nowhere else. Take the first rule that
applies:

1. Some targets are `active`: **resume** them. Each one resumes at the step its campaign
   directory shows: no REPORT, then close; REPORT but no AUDIT, then audit; AUDIT, then
   integrate. Then top the wave up with rule 4.
2. Fewer than two `ready` closer targets, or the last planner run was five or more iterations
   ago: **plan**, alone. The planner edits `roadmap/roadmap.toml`, which the wave's
   bookkeeping also edits, so a planning run is never part of a wave.
3. **The wave:** `python3 tools/roadmap.py wave` lists up to `MAX_PARALLEL` ready targets
   (owners closer, master, builder), in priority order and pairwise independent:
   - no shared label;
   - no dependency between them;
   - at most `MAX_PER_PACKAGE` per package, and a target marked `exclusive = true` alone in
     its package;
   - at most one builder;
   - nothing in a package that an active target fills up.

   Leave the builder out of the wave unless the last builder run was three or more iterations
   ago, and run the tool again with `--owner closer,master` if so.
4. Topping up after a resume: the same `wave` command. It already counts the active targets.
5. The wave is empty and `python3 tools/roadmap.py next --owner planner` gives a target:
   **plan** (research).
6. Otherwise nothing is dispatchable: write the journal entry "idle: waiting on rulings" with
   the list of `needs-ruling` questions, then stop the loop.

## 3. Act

Set every target of the wave `active` first (`python3 tools/roadmap.py set <id> active`), then:

1. **Dispatch every agent at once.** Send one Agent call per closer and per builder, all in the
   same message and all in the background. Do the `master` set-ups yourself while they run.
2. **Audit as each REPORT arrives.** Dispatch its auditor in the background as soon as the
   closer's report comes in; do not wait for the whole wave. A `major` verdict gets one fix round
   from the same closer, as below.
3. **Integrate once, at the end of the wave.** When every agent of the wave has reported:
   - graduate everything clean, package by package;
   - run each package's `make -C <package> check` once;
   - then curate, write the OQ rows and the kb entries, and run `make ledgers` once.

   The strict libraries are frozen while a wave runs (each package's `docs/CAMPAIGN.md`).
   Graduating, or building a whole package, while closers in that package are still elaborating
   would rebuild under them.
4. **A target that fails** (an audit still `major`, an agent that stops without a REPORT, or a
   gate it alone turns red) leaves the wave as `ready` or `blocked`, with the reason in
   `evidence`. Its files stay in the scaffold or are reverted. The rest of the wave still
   integrates.

Dispatch prompts are built per target as described below. Within one package, give each closer
disjoint new files, and say in each prompt which other targets share the package and which
files they own. Closers in one package typecheck with `lake env lean <file>`, which writes
nothing. Each runs `lake build` of its own module only, at its very end. Two `lake build`s of
the same package must not overlap, so a closer's prompt tells it to retry after a minute if
another build of the package is in progress (`pgrep -f "lake build"` with that package's
directory as working directory).

### plan

Dispatch **roadmap-planner**. The prompt gives:
- why it was called (rule 2 or 5, and the target if one applies);
- the last journal entries.

Then run `python3 tools/roadmap.py check`. For a research target the planner completed, set it
`done` in step 6.

### build

Dispatch **atlas-builder** with the target block. Verify the result yourself:
- `make -C reports/atlas -B` twice; the second run must change nothing;
- the builder reports zero page errors.

### close

1. **Dispatch.** Choose the package from the paper: ett/barbot → `lean-causal`, gx and bbs
   research → `lean-gx`, benzecri → `lean-benzecri`. Choose new file names in that package's
   scaffold, following its existing layout. Dispatch **target-closer** with:
   - the target block, verbatim;
   - the package;
   - the labels;
   - the exact new files it may write;
   - its report directory `<package>/campaign/<target-id>/`.

2. **Audit.** Dispatch **target-auditor** with the same dispatch and the REPORT. On `major`:
   send the findings back to the same closer (SendMessage to its id) for one fix round, then
   audit again. If it is still `major` after that, nothing graduates:
   - leave the files in the scaffold;
   - set the target `ready`, appending the audit's findings to `evidence`;
   - or set it `blocked` if the problem is a reading (see 4).
3. **Graduate** what is clean, as the package's earlier graduations did
   (`lean-causal/docs/BARBOT-GRADUATION.md` is the model):
   - `git mv` the file from the scaffold to the strict tree;
   - rename the module path and namespace (`XScaffold.Foo` → `X.Foo`);
   - add the import to the strict root file;
   - remove it from the scaffold root.

   Files with a `sorry` stay in the scaffold. Then run `make -C <package> check`, which must be
   green.
4. **Readings.** For each `question` in the REPORT that the paper leaves open, append an OQ row
   to `registers/DECISIONS.md` in the table's format: next free `OQ-n`, today, the question
   with the reading taken, what it blocks, `OPEN`. If a label cannot close without it, set
   `blocked --oq OQ-n`. **Never write a DEC row.** Rulings are the author's.
5. **Curate.** Update `papers/<paper>/certificate/curation.toml` for each label:
   - the declarations (`decls`);
   - `notes` (target id, audit verdict);
   - `paper_findings`;
   - the hypothesis checklist.

   A corrected form is marked only if a DEC row already rules it. Then run `make ledgers`.
6. **The REPORT's `kb_proposals`** go into the package's `kb/` as new entries, following its
   `INDEX.md` format.

### set up (owner `master`: packages, ledgers, transcriptions)

You do this yourself; no agent writes a package or a ledger. Follow the precedent's wave-0
commit to the letter: Barbot's `papers/barbot/` (DEC-34) for an external paper, and Benzécri's
`4d24ddf` (DEC-112) for a new package together with its paper. The pieces:

- **paper:**
  - `papers/<slug>/paper.toml`;
  - `legacy/orig/` (snapshot), `legacy/labeled/` (labels added, `tools/autolabel.py`) and
    `MANIFEST.json`;
  - `ledger/ledger.toml`, then `python3 tools/ledger.py -c papers/<slug>/ledger/ledger.toml build`;
  - `certificate/curation.toml`;
  - a reading-map `STORY.md` for an external paper, or the skeleton for the author's own.
- **package:**
  - `lean-<slug>/` with `lakefile.toml` at the hub's pin, the strict and scaffold libraries, and
    `scripts/` (copy `sorry_count.py` and `AxiomSweep.lean`);
  - `Makefile` with `check`, `docs/CAMPAIGN.md` and `README.md`;
  - `python3 tools/dropbox_ignore.py` before the first build;
  - `lean-<slug>/.lake` added to `hub.toml`'s `dropbox_ignored`;
  - `lake exe cache get`;
  - `make -C lean-<slug> check` green on the empty library.

Then point the paper's `ledger.toml` `[lean] root` at the package. A transcription from a scan
records in `MANIFEST.json` that the author has to check it. Close with the gates, as for close. When it runs in a wave, you do the set-up yourself
while the agents work, and integrate it with the rest of the wave.

## 4. Gates: an iteration may not make anything redder

- `make -C <package> check` for every package touched.
- `python3 tools/roadmap.py check`.
- `make -C reports/atlas`, which rebuilds the atlas from the new ledgers and roadmap.
- `make -k check 2>&1 | tee /tmp/atlas-team-gate.log`, then
  `python3 tools/roadmap.py gates /tmp/atlas-team-gate.log`. This fails if any hub gate fails
  that `[gates] known_red` does not list. `lib-check` runs GFNBoundsLean's own gate, which
  regenerates `docs/` and `paper-map.json` inside the read-only `lean/` submodule. Restore it
  every time, with `git -C lean checkout -- .`. The submodule is never committed from here.

If a gate fails because of this iteration's work:
- revert this iteration's changes to tracked files (`git checkout -- <files>`; `git mv` back
  what you graduated);
- keep the campaign directory;
- set the target `ready` with the failure in `evidence`;
- commit only that.

## 5. Commit and push

**Ledgers come after the Lean commit.** A ledger records the last commit that touched its Lean
package (`tools/ledger.py`, `git_commit`), so the order is fixed:
1. commit the work, **one commit per target** (Lean, curation, registers and kb for that target),
   so that each target's `done --commit` names its own commit;
2. `make ledgers` and `make -C reports/atlas`, then commit the regenerated ledgers and atlas.
   That commit touches no Lean, so it leaves the ledgers current, and `papers-check` stays green.

Then one last commit for the wave's roadmap statuses:

```
python3 tools/roadmap.py set <id> done --commit <sha of that target's commit> --evidence "<what closed>"   # per target
make -C reports/atlas
git commit -am "roadmap: wave of <date>: <ids> done"
```

Messages follow the repository's style:
- the subject names the target;
- the body says what closed, what did not and why, the audit verdict, the gates run, and the
  new OQ rows;
- then `Host: node1` and the Co-Authored-By trailer.

Then `git push origin main`, retrying network errors up to four times. Never force-push. If the
push is rejected, stop the loop and say so.

## 6. Journal and hand-off

Append one entry to `roadmap/JOURNAL.md`:

```
## <date> <time> · wave of K · <target-ids, or "plan">
- per target: <id>: closed N/M labels | partial | blocked on OQ-n | failed (why); audit clean | minor | major (round r)
- gates: package ✓, roadmap ✓, atlas ✓, hub: no new red
- commits: <sha> [<sha>]
- wall time: <start–end>; agents in parallel: K
- next: <what `wave` would pick now>
```

Commit it with the work, or on its own if the work commit already went. Remove the lock. Give
the user a three-line summary:
1. what was done;
2. what the author is asked, if anything;
3. what comes next.

## Stop conditions for /loop

Stop scheduling further iterations, and say why, when any of these happens:
- two consecutive iterations end without a commit;
- the push is rejected;
- a gate turns red for a reason this iteration cannot revert;
- rule 6 applies (only rulings remain).

Otherwise ask for the next iteration soon: the work is CPU-bound on node1 and nothing external
is being waited on.

## Never

- Write a DEC row, or decide a reading.
- Mark a corrected form without a DEC row ruling it.
- Edit `legacy/`, the `lean/` submodule, a generated ledger by hand, or `hub.toml [freeze]`.
- Run two `lake build`s of the same package at once: not yourself, and not by dispatching two
  closers whose final builds you have not told to wait for each other.
- Exceed the caps of `tools/roadmap.py` (`MAX_PARALLEL`, `MAX_PER_PACKAGE`), or put a planner in a
  wave.
- Create a worktree (CLAUDE.md: the build is not worktree-portable).
- Push anything but a fast-forward of `main`.
