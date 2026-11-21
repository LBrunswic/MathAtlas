---
id: 0150
title: `pgrep -f "lake build"` matches the waiting shell itself
kind: pitfall
created: 2026-11-21
---
An until-loop `until ! pgrep -f "lake build"; do sleep 60; done` never ends: the shell running it has `lake build` in its own command line, and `[l]ake build` matches it too. Watch the build log's tail, or use `pgrep -x lake` (T-ett-measures-e0).
