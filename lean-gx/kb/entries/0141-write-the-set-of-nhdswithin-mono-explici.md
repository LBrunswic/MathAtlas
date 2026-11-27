---
id: 0141
title: Write the set of nhdsWithin_mono explicitly
kind: pitfall
created: 2026-11-27
---
Found by T-bbs-remark-readings. in nhdsWithin_mono, write the set as (Ioi a) explicitly (show Ioi a ⊆ {a}ᶜ from …); a lambda binder (hy : a < y) elaborates the set as Real.lt a and NeBot of 𝓝[>] a is not found.
