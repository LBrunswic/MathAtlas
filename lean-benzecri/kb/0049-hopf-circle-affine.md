# 0049 — The Hopf circle as a compact locally affine 1-manifold

*Found 2026-11-21 by T-bz-result-b; recorded by the master session.*

The Hopf circle ]0, ∞[ / 2^ℤ as a compact locally AFFINE 1-manifold (`Applications/ResultB.lean`: resultBHopfAffGroup, resultB_nonVacuite_hopf_aff). Its generator is GXAut.ofOpens demiDroiteOuverte with (LinearEquiv.smulOfNeZero ℝ _ 2 two_ne_zero).toAffineEquiv, membership by mul_pos_iff_of_pos_left. No projOfAff is involved, so the kb/0045 instance clash does not arise. The quotient is compact (the fundamental domain [1, 2]), T2 (Mathlib instance), connected (the Quotient instance, once SimplyConnectedSpace of ]0, ∞[ is in context) and second countable. Second countability comes from ContinuousConstSMul.secondCountableTopology, a theorem, not an instance.
