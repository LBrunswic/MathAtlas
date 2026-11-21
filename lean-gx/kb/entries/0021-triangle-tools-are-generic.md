---
id: 0021
title: TroyanovTriangle's generic lemmas sit in namespace GX.SphTriangle: reuse them for s-gons
kind: pattern
created: 2026-11-21
---
Found by T-gx-troyanov-polygon. `sheet`, `qOf`, `cplx_qOf`, `homeoComplex_apex`, `sphConeDev_lift`, `arg_div_mem_up`, `re_pos_of_polarFold_im`, `gfun_add`, `convex_gfun_nonneg`, … live in `GX.SphTriangle` but mention no triangle; `GX.SphPolygon.PolyDouble` reuses them, re-proving only what is stated for `Fin 3`.
