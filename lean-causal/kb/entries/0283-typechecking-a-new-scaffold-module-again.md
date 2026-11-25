---
id: 0283
title: Typechecking a new scaffold module against a rewritten scaffold module (refines kb/0034)
kind: pattern
created: 2026-11-25
---
Found by T-ett-geroch-iii-i (round 2, DEC-148/149). Typechecking a new scaffold module against a rewritten scaffold module (refines kb/0034): compile the rewritten one to /tmp/X with `lake env lean -R scaffold -o`. Then symlink every other CausalScaffold olean the new module imports into /tmp/X/CausalScaffold: Lean takes the CausalScaffold root from the first LEAN_PATH entry that has it.
