# The campaign — protocol for every agent

The author's decisions DEC-9 (campaigns of parallel agents) and DEC-38 (each wave a workflow:
authors on disjoint scaffold files, a read-only audit of every file, fixers, a re-audit), applied to
Benzécri by DEC-112 (WP-45). Benzécri is formalized by parallel agents, each owning disjoint new
files of the scaffold; the master session alone graduates files, runs the gates, curates the ledger
and commits. This file is the whole protocol. Your dispatch names your package, your labels and
your files; everything else is here.

## Where things are

| what | where |
|---|---|
| repository | `/home/maxbrain/Dropbox/LeanArticles` (host `node1`; check `hostname`) |
| the paper | `papers/benzecri/legacy/labeled/benzecri1960_ch1.tex` — a TRANSCRIPTION, frozen, read-only, French |
| the scan | `papers/benzecri/sources/bsmf-1960-88-229/benzecri1960.pdf` — PDF page = journal page − 227; read a doubtful passage as a page image, never off the OCR layer |
| the ledger | `papers/benzecri/ledger/LEDGER.md`, `ledger.json` — read-only for you |
| the Lean package | `lean-benzecri/` — Lean `v4.31.0`, mathlib `fabf563a` |
| the strict library | `lean-benzecri/Benzecri/` — **frozen during a wave**: read it, import it, never edit it |
| the scaffold | `lean-benzecri/scaffold/BenzecriScaffold/` — your files go here |
| the knowledge base | `lean-benzecri/kb/` and `lean-causal/kb/INDEX.md` — read every entry before you start |
| conventions | `lean-benzecri/README.md` |
| the Chapter 1 plan | `lean-benzecri/campaign/WP-45-plan/CH1-PLAN.md` |
| mathlib sources | `lean-benzecri/.lake/packages/mathlib/Mathlib/` |

## What you may write

1. The Lean files your dispatch lists, all new, all under `lean-benzecri/scaffold/BenzecriScaffold/`.
2. Your report directory `lean-benzecri/campaign/<your package>/`.

Nothing else. In particular: no edit to any existing file, to the transcription, to the ledger, to
the registers, to `lakefile.toml`, to `.lake/`; nothing under `lean-gx/` or `lean-causal/`; no
`git` command that writes (no add, commit, checkout, stash, worktree); no file of another package.
If you believe an existing file has a defect or lacks a lemma you need, prove the lemma in your own
file and report it.

## The layering rule (DEC-112)

The core imports **Mathlib only**. Do not `import GX.*` or `Causal.*`, and do not add a
`[[require]]`: those belong to the generalisation layers, which will require `lean-gx` git-pinned to
a gated commit (never the reverse — neither `lean-gx` nor `lean-causal` imports this package). When
you need a notion lean-gx already has (`GX.gxGroupoid` in `lean-gx/GX/Structure/Basic.lean`, the
developing theorem in `GX/Structure/Developing.lean`), read it as the template and write the
minimal local version you need, citing the gx original in your docstring; the bridge between the
two is a later module.

## How you build

```
cd /home/maxbrain/Dropbox/LeanArticles/lean-benzecri
taskset -c 0-11 lake env lean scaffold/BenzecriScaffold/<File>.lean   # typecheck; writes nothing; the loop
taskset -c 0-11 lake build BenzecriScaffold.<Module>                  # at the end, your modules only
```

**Always under `taskset -c 0-11`**: node1's CPUs 12–15 crash native jobs. Never `lake build`
without a module, never `lake build Benzecri` or `BenzecriScaffold`, never `make check`: the
lakefile globs every file, another agent's unfinished one included, and Lake has no build lock. If
`lake build` of your module starts rebuilding `Benzecri.*` or mathlib modules, stop and report:
something upstream moved.

Write your file to disk early and often. If you are interrupted, what is on disk is what survives,
and a successor resumes from it.

## What you write

Every file follows the docstring contract (`lean-causal/kb/entries/0006`): title; the labels, each
as ``**`bz…:label`**`` followed by `` — `benzecri1960_ch1.tex:LINE` `` within the first 4000
characters; the paper's sentences quoted in a `>` block, in French, as transcribed; a
`## Hypothesis checklist`; a `## SCOPE (disclosed)`; the provenance line. Namespace `Benzecri`, the
conventions of `README.md` and `kb/0001-conventions.md` (S(E) is the sphere of rays, not ℝPⁿ).

**State first, then prove.** Read the paper block in full, statement and proof (and the scan where
the transcription flags `[sic]`). Write every statement with `sorry -- SORRY(<label>): to prove`,
make the file typecheck, write it to disk; then close the proofs. A proof you cannot close stays as
`sorry -- SORRY(<label>): <the specific mathematical obstruction>`, which is a legitimate outcome.
A statement quietly weakened until it becomes provable is not (`kb/0011`).

**Mark only what is certified in full.** ``**`label`**`` in the module docstring is a claim that
the file proves the paper's statement, with no `sorry` beneath it and no added hypothesis.
Anything less is written `` `label` `` without the mark, and explained in SCOPE.

**Reuse.** Before defining a notion, `grep` the strict library and mathlib for it (`Module.Ray`,
`AffineMap`, `StructureGroupoid`, `ChartedSpace`, `IsCoveringMap`, `ConvexCone`, …).

## What you report

End by writing `lean-benzecri/campaign/<your package>/REPORT.json`, valid JSON, of this shape:

```json
{
  "package": "WP-45a",
  "files": ["scaffold/BenzecriScaffold/Projective/Sphere.lean"],
  "builds": true,
  "sorry_count": 0,
  "labels": [
    {
      "label": "bzdef:c1s1d3_sphere",
      "tex_lines": [167, 184],
      "status": "closed | partial | stated | not-attempted",
      "marked": true,
      "decls": ["Benzecri.Sphere"],
      "hypotheses": [
        {"paper": "E muni de la topologie localement convexe la plus fine", "here": "weakened", "note": "finite dimension"}
      ],
      "sorries": [
        {"decl": "Benzecri.foo", "obstruction": "needs …"}
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
`lean-benzecri/campaign/<package>/AUDIT-<round>.json`:

```json
{
  "package": "WP-45a", "round": 1, "file": "scaffold/BenzecriScaffold/Projective/Sphere.lean",
  "verdict": "clean | issues",
  "builds": true, "sorry_count_measured": 0,
  "summary": "what was checked: build, #print axioms of every marked decl, fidelity of each marked statement to the transcription and the scan",
  "issues": [{"severity": "blocker | major | minor", "where": "decl, line", "problem": "…", "fix": "…"}]
}
```

The auditor checks that the Lean *statement* is the paper's (the kernel checks the proof): no
vacuous hypothesis, no definitional trivialisation, no conclusion hidden in a structure field, every
decl the REPORT names exists, the marks match the statuses. A blocker or major issue goes to a
fixer (the author's own package, or a new one), then to a re-audit (round 2). Only a file whose
last audit is clean is graduated by the master session.

## Benzécri specifics

- **Findings** (the DEC-27 rule of gx): when the paper's statement is false as written or omits a
  hypothesis its proof uses, formalize the strongest true statement, prove a counterexample where
  it is false, and report the correction under `findings`. Such a row is `partial`, never `closed`.
  A *misprint* already flagged `% [sic]` in the transcription is not a finding: formalize the
  evident reading the comment gives, and say so in SCOPE.
- **Implicit hypotheses**: Benzécri's *variété* is a connected, Hausdorff, second-countable
  topological manifold unless he says otherwise (Def. 12 prints « convexe », read « connexe »);
  record each such reading under `questions`.
- **Cited results** (the Fuchsian uniformisation behind the § 3 example, the section of a fibre
  bundle with contractible fibre over a normal base) are formalized when they are on the spine, or
  stated as a named hypothesis only in a stub your dispatch names, then reported as `stated`.
