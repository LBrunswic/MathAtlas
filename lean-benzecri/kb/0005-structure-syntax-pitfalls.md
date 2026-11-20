# 0005 — Two syntax pitfalls: structure-instance continuation lines, and `omit … in`

*Found 2026-11-20 by T-bz-universal-cover; recorded by the master session.*

In `{ a := x, b := y,⏎  c := z }` the continuation line must start at or right of the first field's
column (`sepByIndent`), else "unexpected identifier; expected }". And `omit [...] in` goes BEFORE
the docstring, not between the docstring and the declaration.
