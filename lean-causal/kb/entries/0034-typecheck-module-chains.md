---
id: 0034
title: Typechecking a chain of new scaffold modules without lake build
kind: pattern
created: 2026-11-20
---
`lake env lean <file>` writes nothing, but a second new module cannot import the first until it has
an olean. Without `lake build` (which a wave serialises): `lake env lean -R scaffold -o
/tmp/X/CausalScaffold/Port/A.olean scaffold/CausalScaffold/Port/A.lean`, then
`lake env bash -c 'LEAN_PATH=/tmp/X:$LEAN_PATH lean scaffold/CausalScaffold/Port/B.lean'`; nothing
is written in `.lake`. Delete /tmp/X afterwards (T-ett-port-e0).
