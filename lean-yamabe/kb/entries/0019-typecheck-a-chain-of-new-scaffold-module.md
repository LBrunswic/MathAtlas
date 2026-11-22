---
id: 0019
title: Typecheck a chain of new scaffold modules through /tmp oleans, without lake build
kind: pattern
created: 2026-11-22
---
Found by T-yamabe-analysis. Pattern: a chain of new scaffold modules typechecks without lake build through /tmp oleans (lean-causal kb 0034): lake env bash -c 'LEAN_PATH=/tmp/X:$LEAN_PATH lean -R scaffold -o /tmp/X/YamabeScaffold/A.olean scaffold/YamabeScaffold/A.lean'.
