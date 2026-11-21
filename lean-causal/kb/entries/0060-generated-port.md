---
id: 0060
title: Generate a gx → Causal port by line ranges, and check it as verbatim blocks
kind: pattern
created: 2026-11-21
---
Found by T-ett-port-e0-sfa. A script slices the gx file by line ranges into the port file between a hand-written head and tail; the faithfulness check looks for each range as one contiguous verbatim block of the port (stronger than kb 0035's line-set check), and the auditor compares the elaborated types of every constant after the namespace rename. 1724 lines of GX/BTZ/Causality.lean and LocalModel.lean compiled under `namespace Causal` unchanged.
