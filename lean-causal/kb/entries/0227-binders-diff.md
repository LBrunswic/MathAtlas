---
id: 0227
title: Check 'the original less some binders' mechanically
kind: pattern
created: 2026-11-22
---
An `elab "#binders" n:ident` command that runs `forallTelescope` on the constant's type and logs each binder (binder info, user name, `ppExpr` type) and the body, run on both constants in a /tmp file importing the module, then a `difflib.SequenceMatcher` on the (binderinfo, name, type) lists, prints exactly the removed and added binders and whether the conclusions agree; 27 pairs took one `lake env lean` run (T-abs-ers-4-64-second-countable). Keep the scratch file outside the repository.
