# 0029 — A loop moved by an automorphism g, contracted in P and carried back

*Found 2026-11-21 by T-bz-c2-theoreme; recorded by the master session.*

Use Mathlib's `simply_connected_iff_loops_nullhomotopic` and `isSimplyConnected_iff_exists_homotopy_refl_forall_mem`, then map the homotopy back with `Path.Homotopic.map` by g⁻¹. Close the base-point mismatch g⁻¹ • g • x = x with a subst lemma (`path_homotopic_refl_of_eq`), not with `Path.cast` (`theoreme_deuxieme`).
