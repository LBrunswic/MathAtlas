---
id: 0254
title: Before a hoist, check the ledger rows listing the moved declarations' file
kind: pitfall
created: 2026-11-23
---
A move out of a file in a ledger row's `extra_lean_files` fails `ledger.py check` ('declaration … not found in its listed files') until the paper's `certificate/curation.toml` adds the new file and `ledger_curate.py` rebuilds (T-abs-hoist-dual-cover: ett `lem:Sigma_separe`). Grep the curation files for the moved names before the move.
