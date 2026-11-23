---
id: 0087
title: Pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-perf-cor-yamabe. `hq.mul (tendsto_const_nhds.add hrem)` fails to elaborate (the constant of tendsto_const_nhds is an unassigned metavariable). State `have h1 : Tendsto (fun i => 1 + f i) l (𝓝 (1 + 0)) := tendsto_const_nhds.add hrem` first, then `hq.mul h1` and `convert … using 2; norm_num`.
