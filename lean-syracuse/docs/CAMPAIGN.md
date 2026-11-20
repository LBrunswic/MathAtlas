# The campaign — protocol for every agent

The author's decisions DEC-9 (campaigns of parallel agents) and DEC-38 (each wave a workflow:
authors on disjoint scaffold files, a read-only audit of every file, fixers, a re-audit), applied to
Syracuse by DEC-138 (a package of its own, as DEC-112 for Benzécri and DEC-133 for EGF). Syracuse is formalized by parallel
agents, each owning disjoint new files of the scaffold; the master session (`/atlas-team`) alone
graduates files, runs the gates, curates the ledger and commits. This file is the whole protocol.
Your dispatch names your target, your labels and your files; everything else is here.

## Where things are

| what | where |
|---|---|
| repository | `/home/maxbrain/Dropbox/LeanArticles` (host `node1`; check `hostname`) |
| the paper | `papers/syracuse/legacy/labeled/` — the author's draft, frozen, read-only |
| the story | `papers/syracuse/STORY.md` — the fragments `S-syracuse-N` and the anchors each one names |
| the ledger | `papers/syracuse/ledger/LEDGER.md`, `ledger.json` — read-only for you |
| the Lean package | `lean-syracuse/` — Lean `v4.31.0`, mathlib `fabf563a` |
| the strict library | `lean-syracuse/Syracuse/` — **frozen during a wave**: read it, import it, never edit it |
| the scaffold | `lean-syracuse/scaffold/SyracuseScaffold/` — your files go here |
| the knowledge base | `lean-syracuse/kb/INDEX.md` and `lean-causal/kb/INDEX.md` — read every entry before you start |
| conventions | `lean-syracuse/README.md` |
| mathlib sources | `lean-syracuse/.lake/packages/mathlib/Mathlib/` |

## What you may write


1. The Lean files your dispatch lists, all new, all under `lean-syracuse/scaffold/SyracuseScaffold/`.
2. Your report directory `lean-syracuse/campaign/<your package>/`.

Nothing else. In particular: no edit to any existing file, to the paper, to the ledger, to
the registers, to `lakefile.toml`, to `.lake/`; nothing under `lean/`, `lean-gx/` or `lean-causal/`; no
`git` command that writes (no add, commit, checkout, stash, worktree); no file of another package.
If you believe an existing file has a defect or lacks a lemma you need, prove the lemma in your own
file and report it.

## The layering rule (DEC-138, wave 0)

The package imports **Mathlib only**. Do not add a `[[require]]` and do not import another hub
package (`Causal.*`, `GX.*`, `GFNBounds.*`): a dependency is a ruling, not an agent's choice.

## How you build


```
cd /home/maxbrain/Dropbox/LeanArticles/lean-syracuse
taskset -c 0-11 lake env lean scaffold/SyracuseScaffold/<File>.lean   # typecheck; writes nothing; the loop
taskset -c 0-11 lake build SyracuseScaffold.<Module>                  # at the end, your modules only
```

**Always under `taskset -c 0-11`**: node1's CPUs 12–15 crash native jobs. Never `lake build`
without a module, never `lake build Syracuse` or `SyracuseScaffold`, never `make check`: the
lakefile globs every file, another agent's unfinished one included, and Lake has no build lock. If
`lake build` of your module starts rebuilding `Syracuse.*` or mathlib modules, stop and report:
something upstream moved.

Write your file to disk early and often. If you are interrupted, what is on disk is what survives,
and a successor resumes from it.

## What you write


Every file follows the docstring contract (`lean-causal/kb/entries/0006`): title; the labels, each
as ``**`theo:label`**`` followed by `` — `main.tex:LINE` `` within the first 4000
characters; the paper's sentences quoted in a `>` block, as printed; a
`## Hypothesis checklist`; a `## SCOPE (disclosed)`; the provenance line. Namespace `Syracuse`, the
conventions of `README.md` and `kb/`.

**State first, then prove.** Read the paper block in full, statement and proof (the appendix proofs
included). Write every statement with `sorry -- SORRY(<label>): to prove`,
make the file typecheck, write it to disk; then close the proofs. A proof you cannot close stays as
`sorry -- SORRY(<label>): <the specific mathematical obstruction>`, which is a legitimate outcome.
A statement quietly weakened until it becomes provable is not (`kb/0011`).

**Mark only what is certified in full.** ``**`label`**`` in the module docstring is a claim that
the file proves the paper's statement, with no `sorry` beneath it and no added hypothesis.
Anything less is written `` `label` `` without the mark, and explained in SCOPE.

**Reuse.** Before defining a notion, `grep` the strict library and mathlib for it (`Nat`, `ZMod`, `Nat.Prime`, `padicValNat`, `Finset.sum`, `Function.iterate`, …).

## What you report


End by writing `lean-syracuse/campaign/<your package>/REPORT.json`, valid JSON, of this shape:

```json
{
  "package": "T-syracuse-example",
  "files": ["scaffold/SyracuseScaffold/Example.lean"],
  "builds": true,
  "sorry_count": 0,
  "labels": [
    {
      "label": "theo:example",
      "tex_lines": [167, 184],
      "status": "closed | partial | stated | not-attempted",
      "marked": true,
      "decls": ["Syracuse.Example"],
      "hypotheses": [
        {"paper": "n odd", "here": "weakened", "note": "not used"}
      ],
      "sorries": [
        {"decl": "Syracuse.foo", "obstruction": "needs …"}
      ],
      "findings": ["a sentence about the PAPER the author may want to know, with line numbers"],
      "questions": ["a definition the paper leaves open, and the reading you took"]
    }
  ],
  "extra_decls": ["lemmas of general use you proved, fully qualified"],
  "kb_proposals": ["one line each: what the next session should know"],
  "notes": "anything the master session must know before graduating your files"
}
```

`status`: `closed` — every assertion of the paper's statement is proved, no `sorry`, no added
hypothesis; `partial` — some assertions, or an added hypothesis, or a reading; `stated` — the
statement typechecks and rests on a tagged `sorry`; `not-attempted`.

Your last message to the master session is a short summary of the same: what closed, what did not
and why, the findings, the questions. Do not paste the Lean.

## The audit (DEC-38)


Every authored file is then audited, read-only, by a separate agent, which writes
`lean-syracuse/campaign/<package>/AUDIT-<round>.json`:

```json
{
  "package": "T-syracuse-example", "round": 1, "file": "scaffold/SyracuseScaffold/Example.lean",
  "verdict": "clean | issues",
  "builds": true, "sorry_count_measured": 0,
  "summary": "what was checked: build, #print axioms of every marked decl, fidelity of each marked statement to the paper",
  "issues": [{"severity": "blocker | major | minor", "where": "decl, line", "problem": "…", "fix": "…"}]
}
```

The auditor checks that the Lean *statement* is the paper's (the kernel checks the proof): no
vacuous hypothesis, no definitional trivialisation, no conclusion hidden in a structure field, every
decl the REPORT names exists, the marks match the statuses. A blocker or major issue goes to a
fixer (the author's own package, or a new one), then to a re-audit (round 2). Only a file whose
last audit is clean is graduated by the master session.

## Syracuse specifics

- **The author's own paper.** It is rebuilt from the Lean (STORY.md): an anchor is an assembly
  theorem a story fragment names. Lean ≥ paper, never Lean < paper: a declaration narrower than
  the printed statement is never an anchor.
- **Scope.** the whole paper.
- **Findings** (the DEC-27 rule of gx): when the paper's statement is false as written or omits a
  hypothesis its proof uses, formalize the strongest true statement, prove a counterexample where
  it is false, and report the correction under `findings`. Such a row is `partial`, never `closed`.
