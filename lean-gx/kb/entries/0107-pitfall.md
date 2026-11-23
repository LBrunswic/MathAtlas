---
id: 0107
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-bbs-hs-suspension. Pitfall: in a structure instance `{ a := x,` followed by a line break and `b := y }`, the continuation field must start at a column ≥ the first field's column; otherwise the error is 'unexpected identifier; expected }'. Open with `{` and put one field per line.
