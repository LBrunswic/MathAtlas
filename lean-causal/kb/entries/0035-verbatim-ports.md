---
id: 0035
title: A gx → Causal port compiles verbatim; check it by a line-set comparison
kind: pattern
created: 2026-11-20
---
GX.E0 moved under `namespace Causal` (1530 lines) with no shadowing and no proof changed
(T-ett-port-e0). Check a port's faithfulness by comparing the set of source lines with the port's
(every source line present verbatim, the changes listed in the docstring), not by eye; lean-causal
never imports `GX.*`, so restate what the source takes from other gx modules.
