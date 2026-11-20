# 0004 — Manifolds over S(n) or ℝⁿ are semilocally simply connected

*Found 2026-11-20 by T-bz-universal-cover; recorded by the master session.*

`semilocallySimplyConnected_of_proj` / `_aff` (`Benzecri/UniversalCoverRow.lean`) go through
`S.homeomorphEuclideanSphere` and Mathlib's sphere charts (`Mathlib.Geometry.Manifold.Instances.Sphere`);
Mathlib's `isSimplyConnected_iff_exists_homotopy_refl_forall_mem` turns a simply connected subset
into null-homotopies of its loops. Use them before re-deriving the universal cover's hypothesis.
