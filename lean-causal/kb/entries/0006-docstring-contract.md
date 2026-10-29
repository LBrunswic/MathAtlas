---
id: 0006
title: The module docstring is a contract, and the ledger reads its first 4000 characters
kind: house-rule
created: 2026-09-27
---
## Do, in this order, in the `/-! … -/` at the top of the file
1. `# Title` — a sentence.
2. The labels certified, each as ``**`label`**`` followed by `` — `ETT.tex:LINE` `` (line in
   `papers/ett/legacy/labeled/ETT.tex`). **All of them within the first 4000 characters of the
   file**: the ledger reads no further.
3. The paper's own sentences, quoted in a `>` block. Quote, do not paraphrase.
4. `## Hypothesis checklist` — `| paper hypothesis | here |` with `✓ carried`, `⚠ weakened`
   (the Lean theorem assumes less), `⚠ strengthened` (it assumes more: a finding).
5. `## SCOPE (disclosed)` — what is not proved, or proved in a reading.
6. `Provenance: mathlib `fabf563a` (tag `v4.31.0`), pinned via `lakefile.toml`.`

A label proved only in part, under an added hypothesis, or in a reading the paper does not
settle, is written WITHOUT the `**` mark: the mark is a claim of full certification.
In the scaffold a missing proof is `sorry -- SORRY(<label>): <the mathematical obstruction>`.
