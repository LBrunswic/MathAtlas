---
id: 0053
title: pitfall:
kind: pitfall
created: 2026-11-23
---
Found by T-perf-main. pitfall: an eventual bound near a limit is Filter.Tendsto.eventually_le_const (hv : v < u) (h : Tendsto f l (nhds v)) : eventually f <= u. It is a to_dual name, absent from grep for 'theorem ...eventually_le_const'; use it with filter_upwards.
