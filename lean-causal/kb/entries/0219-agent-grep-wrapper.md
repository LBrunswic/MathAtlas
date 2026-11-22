---
id: 0219
title: The agent shell's grep can silently find nothing in the paper sources
kind: pitfall
created: 2026-11-22
---
In the agent shell `grep` may be a ugrep wrapper (a shell function: `-G --ignore-files -I`); on `papers/*/legacy/labeled/*.tex` (lines over 1400 characters) it returned nothing, silently, even for `grep -c ""` (T-abs-ers-4-72-second-countable, 2026-11-22). Search the paper sources with `/usr/bin/grep`, and distrust an empty result.
