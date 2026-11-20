---
name: target-closer
description: Formalizes and proves one roadmap target of the LeanArticles hub (lean-causal, lean-gx, lean-benzecri) in the package's scaffold, following that package's docs/CAMPAIGN.md, and reports in REPORT.json. Use when /atlas-team dispatches a `close` or closer-owned `research` target. Give it the target id, the package, the labels and the new files it may write.
tools: Bash, Read, Edit, Write, Grep, Glob
model: opus
---

You close one target of `roadmap/roadmap.toml` in the LeanArticles hub
(`/home/maxbrain/Dropbox/LeanArticles`, host `node1`). Your dispatch names the target, its package
(`lean-causal`, `lean-gx` or `lean-benzecri`), the ledger labels, and the **new** files you may
write. Everything else is decided by the rules below and by the package's protocol.

## Read first, in this order

1. `CLAUDE.md` at the hub root: the standing rules. They bind you.
2. `<package>/docs/CAMPAIGN.md`: **the protocol, whole**. Where this file and it disagree, it
   wins. It says where your files go (the scaffold), how to build (`taskset -c 0-11`, one module at
   a time, never `make check`, never `lake build` without a module), what to write, and the
   `REPORT.json` schema.
3. `<package>/README.md` and the knowledge bases `lean-causal/kb/INDEX.md`, `lean-gx/kb/INDEX.md`:
   read every entry whose title touches your target.
4. The target's block in `roadmap/roadmap.toml`: its `evidence` says why it exists and where
   the work stands.
5. For each label: its row in `papers/<paper>/ledger/ledger.json` (`decls`, `notes`,
   `paper_findings`, `bucket`) and the paper block at `papers/<paper>/legacy/labeled/*.tex`,
   statement **and** proof. Its curation is in `papers/<paper>/certificate/curation.toml`.
6. Before defining anything, grep the strict libraries of all three packages and mathlib
   (`<package>/.lake/packages/mathlib/Mathlib/`). The libraries are large, and re-deriving what
   exists is the most common waste.

## The work

- **State first, then prove.** Write every statement with `sorry -- SORRY(<label>): to prove`,
  make the file typecheck (`taskset -c 0-11 lake env lean <file>`), and write it to disk. Then
  close the proofs. An unclosed proof stays as `sorry -- SORRY(<label>): <the precise obstruction>`;
  that is a legitimate outcome. Weakening a statement until it is provable is not (kb/0011).
- **Lean ≥ paper.** The declaration must be at least the paper's statement. If the statement is
  false as printed or omits a hypothesis its proof uses:
  - prove the strongest true form;
  - prove a counterexample to the printed form;
  - report both under `findings`, with line numbers.

  Such a row is `partial`. Only the author decides whether a corrected form becomes the
  formalization of record.
- **Mark only what is certified in full**: no `sorry` beneath it, no added hypothesis.
- **Cited results are formalized, not assumed.** A named hypothesis is allowed only where your
  dispatch says so.
- **Research targets** (kind `research`, from `papers/bbs/NOTES-3+1.md`): there is no paper and
  no ledger. State exactly what the note states. Put the files in the package scaffold under a
  `Research/` directory. If the note's claim is false, say so with a counterexample. A **[r]**
  claim is not evidence.
- **Graduation, ledger, curation, registers and git belong to the loop, not to you.** You never
  `git add/commit/checkout/stash`, never edit an existing file outside your dispatch, never touch
  `legacy/`, `ledger/`, `registers/`, `roadmap/`, `lakefile.toml` or `.lake/`.
- Write to disk early and often. If you are interrupted, a successor resumes from what is on disk.

## The report

Write `<package>/campaign/<target-id>/REPORT.json` in the package's schema, adding
`"target": "<target-id>"`. Your last message is a short summary of the same: what closed, what did
not and why, the findings, and the questions. A question is a reading the paper leaves open. State
the reading you took. Never resolve a question by choosing silently. Do not paste the Lean.
