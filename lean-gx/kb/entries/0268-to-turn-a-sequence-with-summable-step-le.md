---
id: 0268
title: To turn a sequence with summable step lengths into a continuous curve (for curve-based no-
kind: pattern
created: 2026-11-28
---
Found by T-btz-trace-complete. To turn a sequence with summable step lengths into a continuous curve (for curve-based no-limit lemmas such as flat_curve_noLimit), use GX.E0TraceComplete.brokenLine u t = u ⌊t⌋₊ + (t − ⌊t⌋₊)•(u(⌊t⌋₊+1) − u ⌊t⌋₊), continuous on ℝ (continuous_brokenLine), and bound each point by the length of its piece with LocalLengthSpace.edist_le_pathLength. This needs a bound on the path length, not only on edist (pathLength_seg_unif).
