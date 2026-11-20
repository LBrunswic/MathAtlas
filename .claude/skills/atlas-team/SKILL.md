---
name: atlas-team
description: One iteration of the LeanArticles completion team. Reads the roadmap, picks exactly one action (plan, build the atlas, or close a target), dispatches the matching agent (roadmap-planner, atlas-builder, target-closer, then target-auditor), integrates the result, runs the gates, commits, pushes, and writes the journal. Run it once with /atlas-team, or unattended with /loop /atlas-team. Triggers on '/atlas-team', 'run the team', 'next target', 'complete the atlas'.
argument-hint: "[once | status | <target-id>]"
allowed-tools: Read, Write, Edit, Bash, Glob, Grep, Agent, SendMessage
---

# /atlas-team: one iteration of the completion team

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
   running: stop. Otherwise write `$$ <date>` to it. Remove it at the end, on every path out.
4. `git status --short` is clean, or shows only an `active` target's campaign files from an
   interrupted iteration, which you then resume. Anything else means a human or another session
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

## 2. Choose exactly one action

Take the first rule that applies:

1. A target is `active`: **resume** it at the step its campaign directory shows: no REPORT,
   then close; REPORT but no AUDIT, then audit; AUDIT, then integrate.
2. Fewer than two `ready` closer targets, or the last planner run was five or more iterations
   ago: **plan**.
3. `python3 tools/roadmap.py next --owner builder` gives a target, and the last builder run was
   three or more iterations ago: **build**.
4. `python3 tools/roadmap.py next --owner closer` gives a target: **close** it.
5. `python3 tools/roadmap.py next --owner planner` gives a target: **plan** (research).
6. Otherwise nothing is dispatchable: write the journal entry "idle: waiting on rulings" with
   the list of `needs-ruling` questions, then stop the loop.

## 3. Act

Set the target `active` first: `python3 tools/roadmap.py set <id> active`.

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

   Packages of different targets may run in parallel only if they do not share a package. By
   default, run one target at a time.
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

One commit for the work (files, curation, ledgers, registers, kb, atlas) and, if the target
closed, a second one:

```
python3 tools/roadmap.py set <id> done --commit <sha of the first commit> --evidence "<what closed>"
make -C reports/atlas
git commit -am "roadmap: <id> done"
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
## <date> <time> · <action> · <target-id or "—">
- result: closed N/M labels | partial | blocked on OQ-n | planned K targets | atlas: <change>
- audit: clean | minor | major (round r)
- gates: package ✓, roadmap ✓, atlas ✓, hub: no new red
- commits: <sha> [<sha>]
- next: <what rule 2 would pick now>
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
- Run two `lake` builds of the same package at once.
- Create a worktree (CLAUDE.md: the build is not worktree-portable).
- Push anything but a fast-forward of `main`.
