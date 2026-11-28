---
id: 0245
title: When inserting a block before a docstring anchor, the `omit … in` line above the docstring
kind: pattern
created: 2026-11-28
---
Found by T-btz-reg-complete-graduate. When inserting a block before a docstring anchor, the `omit … in` line above the docstring belongs to the following declaration: insert before the omit, or the next declaration silently gains an instance argument (here caught by linter.unusedSectionVars and a failed instance search downstream).
