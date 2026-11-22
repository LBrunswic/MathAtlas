#!/usr/bin/env python3
"""P2 -- single-defect circuit  tau = d^a e d^b.

Pattern (PATTERNS.md, Tier 1):
    tau = d^a e d^b   (a copies of d, one e, then b copies of d),
    length o = a + b + 1, gap-sum E = (a+b) d + e.

Claim (compensation found).  The o cyclic rotations of tau are exactly the words
    rho_i = d^i e d^{o-1-i},   i = 0, ..., o-1
(the single defect e slides through all o positions).  Writing the constant runs
as geometric sums (P1 closed form S(d^m) = (X^{dm}-Y^m)/(X^d-Y)) one gets

    S(rho_i) = S(d^o) + (X^{e-d} - 1) * T_i,    T_i = sum_{k=i+1}^{o-1} X^{kd} Y^{o-1-k},

so consecutive rotations differ by a single monomial of the tail telescope:

    S(rho_i) - S(rho_{i+1}) = (X^{e-d} - 1) * X^{(i+1)d} * Y^{o-2-i}.

Taking the LAST consecutive pair i = o-2 kills the Y-power (Y^0 = 1):

    C_poly := S(rho_{o-2}) - S(rho_{o-1}) = X^{(o-2)d} (X^e - X^d)         (*)

a pure power of X times the defect factor (X^e - X^d).  The only non-X-power
content is (X^{e-d}-1): its X-exponent is |e-d|, INDEPENDENT of a, b (hence of o
and E).  This is the prize the rationale asked for.

GCD consequence at (X,Y)=(2,3).  G = gcd_j S^{(j)}(tau) divides the combination (*),
i.e. G | 2^{(o-2)d}(2^e - 2^d).  G is odd, so it is coprime to the 2-power and

    G  |  2^{|e-d|} - 1   (the odd part of |2^e - 2^d|).

Therefore, on a genuine cycle (where G = |2^E - 3^o|):

    |2^E - 3^o|  <=  2^{|e-d|} - 1      (unless e = d).

The ceiling depends ONLY on |e-d| -- not on a, b, o, or E.

Degenerate locus C == 0:  e = d, i.e. tau = d^o is the pure circuit (P1).
"""

import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))

from cocycle import (  # noqa: E402
    X, Y, S, gcd_rotations,
    verify_symbolic_identity, verify_divisibility_battery,
)
import sympy as sp  # noqa: E402


# --------------------------------------------------------------------------- #
# Word builders                                                               #
# --------------------------------------------------------------------------- #
def tau_word(a, b, d, e):
    """The single-defect circuit  d^a e d^b."""
    return (d,) * a + (e,) + (d,) * b


def rho(i, o, d, e):
    """The i-th canonical rotation  d^i e d^{o-1-i}  (defect at gap-position i)."""
    return (d,) * i + (e,) + (d,) * (o - 1 - i)


# --------------------------------------------------------------------------- #
# The compensating combination and its core                                   #
# --------------------------------------------------------------------------- #
def combination_expr(a, b, d, e):
    """C_poly = S(rho_{o-2}) - S(rho_{o-1})  (last consecutive rotation pair)."""
    o = a + b + 1
    return S(rho(o - 2, o, d, e)) - S(rho(o - 1, o, d, e))


def target_expr(a, b, d, e):
    """Claimed core  X^{(o-2)d}(X^e - X^d) = X^{(o-1)d}(X^{e-d}-1)."""
    o = a + b + 1
    return X ** ((o - 2) * d) * (X ** e - X ** d)


def core_fn(word):
    """Numeric core for the battery: the COMBINATION value at (2,3).

    The battery checks G | core; here core = S(rho_{o-2}) - S(rho_{o-1}) at (2,3),
    which equals 2^{(o-2)d}(2^e - 2^d).  (G odd => G | 2^{|e-d|}-1, the read-off bound.)
    """
    # recover (a,b,d,e) is unnecessary: evaluate the polynomial combination at (2,3)
    # word is tau = d^a e d^b -> identify d, e, a, b
    a, b, d, e = _decode(word)
    return int(target_expr(a, b, d, e).subs({X: 2, Y: 3}))


def _decode(word):
    """Recover (a, b, d, e) from a tau = d^a e d^b word."""
    o = len(word)
    # the defect is the unique letter differing from the surrounding constant run;
    # tau always has the form d..d e d..d; find the odd-one-out position.
    # d = the majority/run value; locate e as the entry whose neighbours are equal d.
    # Robust approach: d is word[0] if a>0 else word[-1]; handle a=0 / b=0.
    from collections import Counter
    cnt = Counter(word)
    # d is the most common letter (a+b copies vs 1 copy of e), unless a+b==1 tie.
    if len(cnt) == 1:
        d = word[0]; e = word[0]
        # pure circuit: pick defect position arbitrarily a=o-1,b=0
        return o - 1, 0, d, e
    (mc, _), = cnt.most_common(1)[:1] and [cnt.most_common(1)[0]] or [(word[0], 0)]
    d = cnt.most_common(1)[0][0]
    # find index of the single non-d letter
    idxs = [i for i, x in enumerate(word) if x != d]
    if len(idxs) != 1:
        # tie (a+b==1): treat first letter as defect-leading; choose e=word that breaks
        # fall back: defect = word with the value appearing once
        once = [x for x, c in cnt.items() if c == 1]
        if once:
            ei = word.index(once[0]); e = once[0]; d = [x for x in word if x != e][0]
            a = ei; b = o - 1 - ei
            return a, b, d, e
        # genuine tie of two distinct singletons (o==2): pick word[1] as defect
        d = word[0]; e = word[1]
        return 0, 0, d, e
    ei = idxs[0]
    e = word[ei]
    a = ei
    b = o - 1 - ei
    return a, b, d, e


# --------------------------------------------------------------------------- #
# Certification                                                               #
# --------------------------------------------------------------------------- #
def main():
    # 1. Symbolic identity over a grid of (a,b,d,e), incl. e<d, a=0, b=0.
    sym_cases = [
        (a, b, d, e)
        for a in range(0, 6)
        for b in range(0, 6)
        for d in range(1, 4)
        for e in range(1, 6)
        if (a + b + 1) >= 2 and e != d
    ]
    # also a few pure-defect-free (e==d) -> target is 0 polynomial; identity still holds
    sym_cases += [(2, 3, 1, 1), (3, 2, 2, 2)]

    sym_ok = True
    sym_fail = None
    for (a, b, d, e) in sym_cases:
        comb = combination_expr(a, b, d, e)
        tgt = target_expr(a, b, d, e)
        if not verify_symbolic_identity(comb, tgt):
            sym_ok = False
            sym_fail = (a, b, d, e, sp.factor(sp.expand(comb - tgt)))
            break

    # 2. Divisibility battery at (2,3) over wide ranges of a,b,d,e.
    instances = [
        tau_word(a, b, d, e)
        for a in range(0, 8)
        for b in range(0, 8)
        for d in range(1, 5)
        for e in range(1, 8)
        if e != d and (a + b + 1) >= 2
    ]
    bat_ok, failures = verify_divisibility_battery(instances, core_fn)

    # 3. Read off the ceiling: G | 2^{|e-d|} - 1.  Confirm directly too.
    ceil_ok = True
    ceil_fail = None
    for (a, b, d, e) in [(2, 3, 1, 4), (3, 3, 1, 5), (5, 0, 3, 7),
                         (6, 6, 1, 9), (0, 5, 1, 2), (2, 4, 2, 1)]:
        tau = tau_word(a, b, d, e)
        G = gcd_rotations(tau)
        oddcore = 2 ** abs(e - d) - 1
        if oddcore != 0 and oddcore % G != 0:
            ceil_ok = False
            ceil_fail = (a, b, d, e, G, oddcore)
            break

    # ----- report -----
    print("=" * 70)
    print("P2  single-defect circuit  tau = d^a e d^b")
    print("=" * 70)
    print("Combination :  S(rho_{o-2}) - S(rho_{o-1})   [last consecutive rotation pair]")
    print("               rho_i = d^i e d^{o-1-i},  o = a+b+1")
    print("Core C_poly :  X^{(o-2)d} (X^e - X^d) = X^{(o-1)d}(X^{e-d}-1)")
    print("GCD bound   :  |2^E - 3^o| <= 2^{|e-d|} - 1     (e != d)")
    print("              -- X-exponent of the non-X-power core is |e-d|,")
    print("                 INDEPENDENT of a, b (hence of o, E).")
    print("Degenerate  :  C == 0  <=>  e = d  (pure circuit d^o, P1).")
    print("-" * 70)
    print(f"symbolic identity : {'PASS' if sym_ok else 'FAIL ' + str(sym_fail)}")
    print(f"divisibility batt : {'PASS' if bat_ok else 'FAIL ' + str(failures[:5])}"
          f"   ({len(instances)} instances)")
    print(f"ceiling check     : {'PASS' if ceil_ok else 'FAIL ' + str(ceil_fail)}")
    print("-" * 70)

    ok = sym_ok and bat_ok and ceil_ok
    print("RESULT:", "PASS (compensation certified)" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
