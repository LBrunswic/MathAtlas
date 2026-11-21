# 0037 — The affine Theorem toolkit: characterisations of lines, shells and strict shells

*Found 2026-11-21 by T-bz-c2-theoreme-affine; recorded by the master session.*

Affine Theorem toolkit (Chapter2/TheoremeAffine.lean). For every pocket of a connected sweepable V: containsAffLine_range_iff_affine (φ̃(V) has a line iff φ(P) has one), isCoqueAff_iff_convex_range_affine (shell iff φ̃(V) convex), isCoqueStricteAff_iff_range_affine. For a shell: 1°'s full form, poche_eq_preimage_of_coque_affine. Every affine shell has a simply connected pocket (simplyConnectedSpace_of_coque_affine, via φ.toHomeomorphSourceTarget and Convex.contractibleSpace). So 2° applies to every shell, not only to strict ones as in the projective file.
