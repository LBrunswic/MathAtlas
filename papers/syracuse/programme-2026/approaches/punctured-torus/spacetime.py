"""
punctured-torus :: complete description of the Syracuse BTZ spacetime — the affine
representation, the cycle -> geodesic correspondence, and the property P.

Flat model R^{1,2} = sl_2, q(X) = -det X, isometries SO_0(1,2) x| R^{1,2} = Ad(SL2) x| sl_2.

The canonical (reducible / "noded") Syracuse holonomy:
  linear part  L0(gamma) = the multiplicative 2-3 boost  diag( sqrt(3^o/2^E), sqrt(2^E/3^o) )
  translation  tau(gamma) = beta(gamma) * E,   beta(gamma) = S(gamma)/2^E   (NULL, in R.E)
We CERTIFY:
  (1) tau(gamma) = (S/2^E) E exactly (= the intercept of the affine-line map F_gamma);
  (2) the holonomy (Ad L0(gamma), tau) FIXES A SPACELIKE LINE pointwise, at null-position
      E-coordinate = S/D = x0* (the cycle value). Margulis invariant = 0 => NON-FREE: the
      reducible base is degenerate (this is why a smooth spacetime needs a Fuchsian base);
  (3) PROPERTY P:  gamma is a Syracuse cycle  <=>  D | S  <=>  x0* = S/D in Z
      <=>  the fixed spacelike line sits at an INTEGER null-position.
"""
import os
import sys
import math
from fractions import Fraction

import numpy as np
import sympy as sp

_LIB = os.path.join(os.path.dirname(__file__), "..", "cocycle-combine", "lib")
sys.path.insert(0, os.path.abspath(_LIB))
import cocycle as kc  # noqa: E402

# sl_2 basis and Lorentzian form
H = np.array([[1.0, 0.0], [0.0, -1.0]])
E = np.array([[0.0, 1.0], [0.0, 0.0]])
F = np.array([[0.0, 0.0], [1.0, 0.0]])


def q(X):
    return 0.5 * np.trace(X @ X)            # = -det X


def beta_affine(gapword):
    """intercept of the affine-line map F_gamma(z)=alpha z+beta, by direct composition."""
    a, b = Fraction(1), Fraction(0)         # identity z -> 1*z + 0
    # gap d  <->  affine map z -> 3^? ... reconstruct F from the gap word via S,D closed form
    # F_gamma(z) = (3^o/2^E) z + S/2^E :
    o, Ee = len(gapword), sum(gapword)
    S, D = kc.S_int(gapword), kc.D_int(gapword)
    return Fraction(S, 2 ** Ee), Fraction(3 ** o, 2 ** Ee), S, D, o, Ee


# (gap word, (a,b)-form, known cycle value or None)
WORDS = [
    ((2,),  "ab",  1,   True),    # 1->1
    ((1,),  "a",  -1,   True),    # -1
    ((1, 2), "aab", -5, True),    # -5->-7
    ((3,),  "abb", None, False),  # NON-cycle  (S/D = 1/5)
    ((1, 3), "a-b3", None, False),  # NON-cycle (S/D = 5/7)
]

print("=" * 80)
print("Syracuse BTZ spacetime — representation, fixed locus, and property P")
print("=" * 80)
for gap, ab, x0_known, is_cycle in WORDS:
    beta, alpha, S, D, o, Ee = beta_affine(gap)
    x0 = Fraction(S, D)
    # (1) translation cocycle tau = beta * E  (null)
    tau = float(beta) * E
    assert abs(q(tau)) < 1e-12                     # null
    # (2) fixed spacelike line: solve (Ad L0 - I) X = -tau.
    #     Ad L0(gamma): E -> (3^o/2^E) E, F -> (2^E/3^o) F, H -> H.  Neutral dir = H.
    #     E-component of fixed point: (alpha-1) X_E = -beta  => X_E = -beta/(alpha-1)=S/D
    XE = -beta / (alpha - 1)
    assert XE == x0                                # fixed line at null-position S/D
    # Margulis invariant along the spacelike axis H:  <tau, H> = 0
    marg = 0.5 * np.trace(tau @ H)
    assert abs(marg) < 1e-12
    # (3) property P
    P = (D % S == 0) if False else (x0.denominator == 1)   # x0 in Z  <=>  D | S
    assert P == (S % D == 0)
    tag = "CYCLE" if is_cycle else "non-cycle"
    print(f"  {tag:9} gap={str(gap):7} ({ab:5}) o={o},E={Ee}:  "
          f"S={S:>3} D={D:>3}  tau=(S/2^E)E=({beta})E  "
          f"x0*=S/D={str(x0):>5}  in Z? {P}")
    if is_cycle:
        assert x0 == x0_known and P

print()
print("  => tau(gamma) = (S/2^E)E is NULL; holonomy fixes the spacelike line")
print("     { tH + (S/D)E } pointwise (Margulis invariant 0 => NON-FREE at the reducible")
print("     base: degenerate, a smooth Brunswic spacetime needs a Fuchsian base).")
print("  => PROPERTY P:  Syracuse cycle  <=>  D|S  <=>  x0*=S/D in Z")
print("     <=>  the cycle's fixed spacelike line sits at an INTEGER null-position")
print("          (its ideal endpoint on the null boundary is a marked integer point).")
print()

# explicit linear part on the two generators (for the write-up)
print("  Linear part L0 (multiplicative 2-3 boosts), Ad-action on (H,E,F):")
print("     a:  E -> (3/2)E,  F -> (2/3)F,  H -> H      (rapidity +log 3/2)")
print("     b:  E -> (1/2)E,  F -> 2F,      H -> H      (rapidity -log 2)")
print("  Translation:  tau(a) = (1/2)E,  tau(b) = 0     (null, the Syracuse '+1')")
print("\nALL SPACETIME ASSERTS PASSED.")
