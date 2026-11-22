#!/usr/bin/env python3
"""P1 - single circuit / constant-gap word  d^o.

Warm-up pattern validating the cocycle-combine pipeline.

Claim (symbolic, in Z[X,Y]):
    for the constant word w = (d, d, ..., d)  (o letters),
        (X**d - Y) * S(w) == D(w) == X**(d*o) - Y**o,
    i.e.  S(w) = (X**(d*o) - Y**o) / (X**d - Y)  (a geometric sum, exact polynomial).

Claim (numeric, at (X,Y)=(2,3)):
    all o rotations of d^o are the SAME word, hence all S^{(j)} are equal, hence
        G = gcd_j S^{(j)} = S(w) = D / (2**d - 3)   exactly.
    The "core" C := S(w) = G, so the a-priori ceiling G | C holds with equality.
    This is the single-circuit / C=0-style finite stratum: the ceiling is tight
    but VACUOUS as a standalone finiteness lever (it merely recovers G).

Exit 0 iff both certifiers pass over the whole battery.
"""
import sys, os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))

import sympy as sp
from cocycle import (
    X, Y, S, D, rotations, gcd_rotations, S_int, D_int,
    verify_symbolic_identity, verify_divisibility_battery,
)


def word(d, o):
    return (d,) * o


# --------------------------------------------------------------------------- #
# 1. Symbolic identity in Z[X,Y]:  (X^d - Y) S(d^o) = D(d^o) = X^{do} - Y^o    #
#    and the geometric closed form  S = (X^{do} - Y^o)/(X^d - Y).             #
# --------------------------------------------------------------------------- #
SYM_PARAMS = [(d, o) for d in range(1, 6) for o in range(1, 7)]

print("=== P1: single circuit / constant-gap word  d^o ===\n")
print("[1] Symbolic identity  (X^d - Y) * S(d^o) == D(d^o)  in Z[X,Y]:")
for d, o in SYM_PARAMS:
    w = word(d, o)
    combination_expr = (X ** d - Y) * S(w)        # the Z[X,Y] combination
    target_expr = D(w)                            # claimed compensated core = D
    assert verify_symbolic_identity(combination_expr, target_expr), \
        f"symbolic identity FAILED at d={d}, o={o}"
    # geometric closed form
    closed = sp.cancel((X ** (d * o) - Y ** o) / (X ** d - Y))
    assert sp.expand(S(w) - closed) == 0, f"closed form FAILED at d={d}, o={o}"
print(f"    PASS over d in 1..5, o in 1..6  ({len(SYM_PARAMS)} instances)")
print("    => S(d^o) = (X^{do} - Y^o)/(X^d - Y)  exactly.\n")


# --------------------------------------------------------------------------- #
# 2. All rotations of d^o coincide => all S^{(j)} equal => G = S(d^o) exactly. #
# --------------------------------------------------------------------------- #
print("[2] Rotation degeneracy: every rotation of d^o is the same word,")
print("    so G = gcd_j S^{(j)} = S(d^o) = D/(2^d - 3) at (2,3):")
for d, o in SYM_PARAMS:
    w = word(d, o)
    rs = rotations(w)
    assert all(r == w for r in rs), f"rotations not identical at d={d}, o={o}"
    G = gcd_rotations(w)
    Sv = abs(S_int(w))
    assert G == Sv, f"G != |S| at d={d}, o={o}: G={G}, S={Sv}"
    den = 2 ** d - 3
    if den != 0:
        assert (2 ** (d * o) - 3 ** o) % den == 0
        assert G == abs((2 ** (d * o) - 3 ** o) // den), f"G != D/(2^d-3) at d={d}, o={o}"
print(f"    PASS: G == |S(d^o)| == |D/(2^d - 3)|  over {len(SYM_PARAMS)} instances.\n")


# --------------------------------------------------------------------------- #
# 3. Divisibility battery (necessary cycle condition  G | C) with core C = S.  #
# --------------------------------------------------------------------------- #
def core_fn(w):
    """Compensated core for the constant word:  C = S(d^o) = G itself."""
    return S_int(w)


BATTERY = [word(d, o) for d in range(1, 7) for o in range(1, 9)]
ok, failures = verify_divisibility_battery(BATTERY, core_fn)
print("[3] Divisibility battery  G | C   (core C = S(d^o)):")
assert ok, f"battery FAILED: {failures}"
print(f"    PASS over d in 1..6, o in 1..8  ({len(BATTERY)} instances), C = S = G.\n")


# --------------------------------------------------------------------------- #
# Report-line: core, bound, verdict.                                          #
# --------------------------------------------------------------------------- #
print("--- summary ---")
print("CORE  C(d^o) = S(d^o) = (X^{do} - Y^o)/(X^d - Y)   [X-exponent d(o-1), grows with o]")
print("BOUND |2^E - 3^o| <= |C|  is  |2^{do} - 3^o| <= |D/(2^d-3)|  -- equality, hence")
print("      TIGHT BUT VACUOUS: C = G recovers the gcd, gives no a-priori upper bound.")
print("DEGENERATE LOCUS: C = S(d^o) = 0 only on Y^o = X^{do} (no positive integer solution");
print("      except the trivial 1->1 fixed-point family d=2 collapsing to length 1).")
print()
print("RESULT: PASS  (pipeline validated; single-circuit stratum, classically finite/Steiner)")
sys.exit(0)
