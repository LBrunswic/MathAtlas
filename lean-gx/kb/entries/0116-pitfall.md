---
id: 0116
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-hs-link-types. Pitfall: `clear h` does not silence the unused-variables linter. A hypothesis the paper's statement carries but the proof does not use must be named `_h` (the strict library's convention), or warningAsError rejects the file at graduation.
