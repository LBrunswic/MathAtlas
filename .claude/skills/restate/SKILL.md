---
name: restate
description: One iteration of the restatement loop. It detects the paper statements found false or imprecise as written (tools/restate.py, from the curated ledgers), has statement-rewriter triage them and rewrite each in natural language from the rigorous Lean, has statement-checker verify every rewrite against its Lean anchor, then gates, commits and pushes. Run it once with /restate, or unattended with /loop /restate. Shares the checkout with the other loops through leases.
argument-hint: "[once | status | <slug>]"
allowed-tools: Read, Write, Edit, Bash, Glob, Grep, Agent, SendMessage
---

# /restate: one iteration of the restatement loop

The statements live in `papers/<slug>/certificate/restatements.toml`. Their schema, the status
ladder (`found → drafted → checked → reviewed`, or `dismissed` / `blocked`) and the gate are in the
docstring of `tools/restate.py`.

You are the **master**: you seed, dispatch, mark entries `checked`, render, gate, commit and push.
- **statement-rewriter** triages and rewrites.
- **statement-checker** checks.
- **The author** reviews (`reviewed`) and rules readings (DEC rows).

`CLAUDE.md` binds you. Your lease name is `restate`.

Arguments:
- `status`: print `python3 tools/restate.py status` and `python3 tools/restate.py detect`, then stop.
- `<slug>`: work only that paper.
- `once`, or nothing: a normal iteration.

## 0. Preconditions: stop the iteration if one fails

1. `hostname` is `node1`. Then `cd /home/maxbrain/Dropbox/LeanArticles`.
2. **The lease.** Run `python3 tools/lease.py show`.
   - If a `restate` lease is held by a live pid other than this session's process, another
     iteration runs: stop.
   - Otherwise run `python3 tools/lease.py take restate <pid of this session's process> reports/restate`.
     This is the base lease: the journal's directory.
3. `git pull --ff-only origin main`. If it is not a fast-forward, stop.

## 1. Detect

- `python3 tools/restate.py detect`. Any unregistered strong candidate is a ledger row that a loop
  curated since the last seed.
- For each paper with candidates, take `papers/<slug>/certificate/restatements.toml` and
  `papers/<slug>/certificate/RESTATED.md` under your lease. Then run
  `python3 tools/restate.py seed <slug>`.
- Seed weak candidates (`--all`) only when no strong `found` entry remains anywhere. They are the
  next tier.
- `python3 tools/restate.py check` must pass.
  - A **stale** entry means the printed statement changed. Reset it to `found` by editing its
    `printed` and `printed_sha256` to the ledger's, and note it in the journal.
  - A **checked** entry whose check went stale is an edited rewrite: move it back to `drafted` by
    hand (status edit only) and send it to the checker.

## 2. Choose the wave

Allow at most `MAX_PARALLEL` agents (tools/roadmap.py), counting rewriters and checkers together.
A paper takes one agent at a time, and gx and ett first.
1. **Check** every paper that has `drafted` entries: one statement-checker per paper, at most 10
   entries each.
2. **Rewrite**: one statement-rewriter per paper that has `found` entries, at most 8 entries each.
   Order them as follows:
   - `false` before the rest (they carry a `refutation`);
   - then entries whose anchor is certified (curated `decls` with a DEC basis);
   - then the rest, in ledger order.
3. Nothing is dispatchable: only `blocked` entries (waiting on OQs) or `checked` ones (waiting on
   the author) remain. Write "idle" in the journal with those lists, and stop the loop.

Before dispatching, take the lease of each paper's `restatements.toml` and `RESTATED.md` (for a
checker, also `papers/<slug>/certificate/restate`). If `take` refuses, leave that paper out.

## 3. Act

Dispatch every agent at once, in the background, in one message. Give each:
- the slug;
- the labels;
- "write only papers/<slug>/certificate/restatements.toml" (rewriter), or "write only your CHECK
  files" (checker).

When a **checker** reports, for each `faithful` CHECK file:

```
python3 tools/restate.py set <slug> <label> checked --check CHECK-<label>-<n>.json
```

`set` refuses if the CHECK does not match the entry. A `minor` or `major` verdict goes back to a
statement-rewriter with the findings, for one fix round, and then to the checker again. Still not
faithful after that: leave the entry `drafted` and journal the findings.

When a **rewriter** reports, run `python3 tools/restate.py check <slug>`. Its entries must hold
every rule. Entries it dismissed or blocked are final for this iteration.

## 4. Gates

- `python3 tools/restate.py render` for the papers touched, then `python3 tools/restate.py check`.
- `python3 -m unittest tests.test_restate -q`.
- `python3 tools/papers_check.py`. A failure on a path another loop holds is that loop's work in
  progress: journal it, do not revert it.

## 5. Commit and push: only what you hold

Run `git commit --only $(python3 tools/lease.py mine restate)` with one commit per paper. The
message says:
- how many entries were seeded, drafted, checked, dismissed (with the reasons in short) and
  blocked (with their OQs);
- then `Host: node1` and the Co-Authored-By trailer.

Push a fast-forward of `main`, retrying network errors up to four times. Then drop every lease
except the base one.

## 6. Journal and hand-off

Append to `reports/restate/JOURNAL.md`, creating it if needed:

```
## <date> <time> · <papers>
- seeded n; drafted n; checked n; dismissed n; blocked n (OQ-…)
- per paper: <restate.py status line>
- waiting on the author: <checked entries to review>
- commits: <shas>
```

Commit the journal, then drop the base lease (`tools/lease.py drop restate`). Give the user three
lines: what was done, what the author is asked (the checked entries to review, the OQs), and what
comes next.

## The author's review

The author reads `papers/<slug>/certificate/RESTATED.md`: printed beside rewritten, with the Lean.
On their word, record it with:

```
python3 tools/restate.py set <slug> <label> reviewed --review "<date>: <how>"
```

You never mark `reviewed` without their word. A rewrite the author changes goes back to `drafted`,
and from there to the checker.

## Stop conditions for /loop

Stop when any of these holds:
- two consecutive iterations end without a commit;
- the push is rejected;
- only `blocked` and `checked` entries remain.

## Never

- Edit Lean, ledgers, `curation.toml`, `legacy/` or `DECISIONS.md`, or write a DEC row.
- Mark `reviewed` without the author.
- Commit a path you do not hold, or run `git commit -a`.
