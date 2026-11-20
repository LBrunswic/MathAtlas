---
id: 0004
title: Any bold backticked label in a module's first 4000 characters is a certification mark
kind: pitfall
created: 2026-11-20
---
tools/ledger.py reads every ``**`label`**`` in the first 4000 characters of a strict module as a mark,
prose included (SCOPE bullets, quoted headings): never bold a backticked label that is not certified
in full. T-syr-base's audit caught `lem:base` marked this way. Check with the ledger's
`docstring_label_re` before reporting (T-syr-base).
