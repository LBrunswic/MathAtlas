# 0047 — Does theorem X use lemma Y? A proof-term dependency probe

*Found 2026-11-21 by T-bz-result-b-proj; recorded by the master session.*

Does theorem X use lemma Y (the OQ-dependency question of a roadmap [r] point)? Copy the module to /tmp and append a small `elab` command. It walks Expr.getUsedConstants over each constant's type and value (ConstantInfo.value? (allowOpaque := true)) from X and reports which watched names it reaches. Run the copy with `lake env lean /tmp/…`, which writes nothing in the package. T-bz-result-b-proj used it for OQ-71/OQ-75.
