---
id: 0244
title: Behaviour preservation across a move can be checked mechanically while the old .olean file
kind: pattern
created: 2026-11-28
---
Found by T-btz-reg-complete-graduate. Behaviour preservation across a move can be checked mechanically while the old .olean files are still on disk: readModuleData each old olean and compare every constant's type Expr with the new environment's (`c'.type != c.type`); the only expected absences are on-demand eq_n lemmas and proof-internal match_ auxiliaries.
