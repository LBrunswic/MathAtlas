# 0065 — Finitely supported sums: define sommeF := Finsupp.lsum ℝ (fun _ => LinearMap.id)

*Found 2026-11-28 by T-bz-c3-sommes; recorded by the master session.*

Finitely supported sums: define sommeF := Finsupp.lsum ℝ (fun _ => LinearMap.id) to get map_add/map_sub/map_smul for free; Submodule.mem_iSup_iff_exists_finsupp and iSupIndep_def + Finsupp.add_sum_erase' give iSupIndep ↔ injectivity on families (eq_zero_of_iSupIndep, iSupIndep_of_injOn).
