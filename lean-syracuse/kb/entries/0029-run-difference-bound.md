---
id: 0029
title: The difference at the end of an ascending run is 3^q times a nonpositive sum, bounded sharply
kind: pattern
created: 2026-11-21
---
Found by T-syr-no-circuit (`Syracuse.NoCircuit`). On a cycle of least period n ≥ 2, A_{q+i} − A_{q+i+1} at the end of a run of q ascending indices is 3^q times an explicit sum of nonpositive terms (`noCircuit_diff_eq`, `noCircuitSum`). Bound it by induction on the window with one `nlinarith` step (`noCircuitSum_bound`); the bound is sharp, attained at (−5, −7).
