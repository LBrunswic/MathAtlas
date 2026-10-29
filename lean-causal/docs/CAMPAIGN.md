# The campaign — protocol for every agent

The author's decision DEC-9 (2026-09-27): ETT is formalized by parallel agents, each owning
disjoint new files of the scaffold; the master session alone graduates files, runs the gates,
curates the ledger and commits. This file is the whole protocol. Your dispatch names your
package, your labels and your files; everything else is here.

## Where things are

| what | where |
|---|---|
| repository | `/home/maxbrain/Dropbox/LeanArticles` (host `node1`) |
| the paper | `papers/ett/legacy/labeled/ETT.tex` — frozen, read-only, English |
| its macros | `papers/ett/legacy/labeled/alias.tex`, `definition.tex` |
| the ledger | `papers/ett/ledger/LEDGER.md`, `ledger.json` — read-only for you |
| the Lean package | `lean-causal/` — Lean `v4.31.0`, mathlib `fabf563a` |
| the strict library | `lean-causal/Causal/` — **frozen during a wave**: read it, import it, never edit it |
| the scaffold | `lean-causal/scaffold/CausalScaffold/` — your files go here |
| the knowledge base | `lean-causal/kb/INDEX.md` — read every entry before you start |
| conventions | `lean-causal/README.md` |
| mathlib sources | `lean-causal/.lake/packages/mathlib/Mathlib/` |

## What you may write

1. The Lean files your dispatch lists, all new, all under `lean-causal/scaffold/CausalScaffold/`.
2. Your report directory `lean-causal/campaign/<your package>/`.

Nothing else. In particular: no edit to any existing file, to `ETT.tex`, to the ledger, to the
registers, to `lakefile.toml`, to `.lake/`; no `git` command that writes (no add, commit,
checkout, stash, worktree); no file of another package. If you believe an existing file has a
defect or lacks a lemma you need, prove the lemma in your own file and report it.

## How you build

```
cd /home/maxbrain/Dropbox/LeanArticles/lean-causal
lake env lean scaffold/CausalScaffold/<File>.lean      # typecheck; writes nothing; the loop
lake build CausalScaffold.<Module>                     # at the end, your modules only
```

Never `lake build` without a module, never `lake build Causal` or `CausalScaffold`, never
`make check`: the lakefile globs every file, another agent's unfinished one included, and Lake
has no build lock. If `lake build` of your module starts rebuilding `Causal.*` or mathlib
modules, stop and report: something upstream moved.

Write your file to disk early and often. If you are interrupted, what is on disk is what
survives, and a successor resumes from it.

## What you write

Every file follows the docstring contract (`kb/entries/0006`). Namespace `Causal`, the
conventions of `README.md`: everything indexed by an open set (`kb/0001`), past from future by
`dual` (`kb/0002`), weakest sufficient hypotheses (`kb/0007`).

**State first, then prove.** Read the paper block in full, statement and proof. Write every
statement with `sorry -- SORRY(<label>): to prove`, make the file typecheck, write it to disk;
then close the proofs. A proof you cannot close stays as
`sorry -- SORRY(<label>): <the specific mathematical obstruction>`, which is a legitimate
outcome. A statement quietly weakened until it becomes provable is not (`kb/0011`).

**Mark only what is certified in full.** ``**`label`**`` in the module docstring is a claim that
the file proves the paper's statement, with no `sorry` beneath it and no added hypothesis.
Anything less is written `` `label` `` without the mark, and explained in SCOPE.

**Reuse.** Before defining a notion, `grep` the strict library for it. Before proving a lemma of
general topology or measure theory, `grep` mathlib for it.

## What you report

End by writing `lean-causal/campaign/<your package>/REPORT.json`, valid JSON, of this shape:

```json
{
  "package": "WP-1",
  "files": ["scaffold/CausalScaffold/Morphism.lean"],
  "builds": true,
  "sorry_count": 0,
  "labels": [
    {
      "label": "defi:fonction_temps",
      "tex_lines": [1028, 1030],
      "status": "closed | partial | stated | not-attempted",
      "marked": true,
      "decls": ["Causal.Causality.IsTimeFunction"],
      "hypotheses": [
        {"paper": "M second countable", "here": "weakened", "note": "not used"}
      ],
      "sorries": [
        {"decl": "Causal.foo", "obstruction": "needs the closedness of J^+(K), which …"}
      ],
      "findings": ["a sentence about the PAPER the author may want to change, with line numbers"],
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

Your last message to the master session is a short summary of the same: what closed, what did
not and why, the findings, the questions. Do not paste the Lean.
