---
id: 0004
title: `abel` fails on measure expressions containing a truncated difference
kind: pitfall
created: 2026-11-20
---
Found by T-egf-headline. `abel` does not see through `R - B` on measures (a truncated difference, not a group subtraction). `set D := R - B` first, then `abel` treats `D` as an atom.
