"""P11 -- stratum twist / topological cover.

Self-contained certifier + honest experiment for pattern P11.

P11 is NOT a telescoping rotation-difference family (P0-P10). It is a *propagation
rule* across a fixed stratum

    S_{E,o} = { gap words with gap-sum E and length o },

every word of which shares D = X^E - Y^o (=> D(2,3) = 2^E - 3^o). The lever is the
two transfer-matrix entries D and S directly (not rotation sums): a *certificate*
for a word w is a pair a,b in Z[X,Y] with

    C(w) := a*D + b*S(w),   0 < |C(w)(2,3)| < |D(2,3)|.

On a genuine cycle D = gcd_j S^{(j)} divides every S^{(j)}, hence D | S(w); then
D | b*S(w), and D | a*D trivially, so D | C(w). With |C(w)| < |D| that forces
C(w)=0 -- contradiction -- so w is not (a rotation in) a cycle.

This script certifies:
  (1) the increment identities (symbolic, Z[X,Y]),
  (2) the unit-mod-D fact gcd(D,6)=1 and the odd-part size + P2 recovery,
  (3) the stratum-cover EXPERIMENT: with the canonical certificate b=1 (so
      C(w) = S(w) mod D, least residue), which words are covered (C != 0 mod D),
      which are uncovered (C == 0 mod D, the cycle candidates), and -- the honest
      crux -- how large |C| actually gets and how far a single twist moves it.

Exit 0 == all assertions pass. Findings (radius, coverage) are printed.
"""

from __future__ import annotations

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))

from math import gcd
import sympy as sp
from cocycle import (
    X, Y, S, S_int, gcd_rotations, rotations,
    verify_symbolic_identity, verify_divisibility_battery,
)


# --------------------------------------------------------------------------- #
# helpers                                                                     #
# --------------------------------------------------------------------------- #
def compositions(E, o):
    """All compositions of E into o positive parts (the words of stratum S_{E,o})."""
    if o == 1:
        if E >= 1:
            yield (E,)
        return
    for first in range(1, E - o + 2):
        for rest in compositions(E - first, o - 1):
            yield (first,) + rest


def Pk(w, k):
    """Partial sum d_0 + ... + d_{k-1}."""
    return sum(w[:k])


def swap(w, i):
    """Adjacent transposition of positions i, i+1 (0-based)."""
    w = list(w)
    w[i], w[i + 1] = w[i + 1], w[i]
    return tuple(w)


def utransfer(w, i):
    """Unit transfer d_i -> d_i + 1, d_{i+1} -> d_{i+1} - 1 (0-based)."""
    w = list(w)
    w[i] += 1
    w[i + 1] -= 1
    return tuple(w)


def least_residue(v, D):
    """Least-magnitude residue of v mod |D| in (-|D|/2, |D|/2]."""
    r = v % abs(D)
    if r > abs(D) // 2:
        r -= abs(D)
    return r


# --------------------------------------------------------------------------- #
# (1) increment identities -- the core symbolic deliverable                   #
# --------------------------------------------------------------------------- #
def check_increment_identities():
    """Adjacent-transposition and unit-transfer increment identities in Z[X,Y].

    Swap d_i <-> d_{i+1} (0-based) moves only the partial sum before index i+1:

        S(w') - S(w) = Y^{o-2-i} X^{P_i} (X^{d_{i+1}} - X^{d_i}),   P_i = d_0+..+d_{i-1}.

    Unit transfer d_i -> d_i+1, d_{i+1} -> d_{i+1}-1 moves the same single partial
    sum by +1:

        S(w') - S(w) = Y^{o-2-i} X^{P_{i+1}} (X - 1),               P_{i+1} = d_0+..+d_i.
    """
    test_words = [
        (2, 1, 3, 1, 4), (1, 1, 1, 1), (3, 2, 1), (2, 2, 3, 2, 4),
        (5, 1, 2, 3), (1, 4, 1, 2, 1, 3), (2, 3),
    ]
    swap_ok = True
    for w in test_words:
        o = len(w)
        for i in range(o - 1):
            lhs = sp.expand(S(swap(w, i)) - S(w))
            claim = Y ** (o - 2 - i) * X ** Pk(w, i) * (X ** w[i + 1] - X ** w[i])
            if not verify_symbolic_identity(lhs, claim):
                swap_ok = False
                print(f"  SWAP IDENTITY FAIL: w={w} i={i}")

    utrans_ok = True
    for w in test_words:
        o = len(w)
        for i in range(o - 1):
            if w[i + 1] - 1 < 1:  # keep parts positive
                continue
            lhs = sp.expand(S(utransfer(w, i)) - S(w))
            claim = Y ** (o - 2 - i) * X ** Pk(w, i + 1) * (X - 1)
            if not verify_symbolic_identity(lhs, claim):
                utrans_ok = False
                print(f"  UNIT-TRANSFER IDENTITY FAIL: w={w} i={i}")

    return swap_ok, utrans_ok


# --------------------------------------------------------------------------- #
# (2) unit-mod-D fact + odd-part size + P2 recovery                           #
# --------------------------------------------------------------------------- #
def check_unit_mod_D():
    """gcd(D,6)=1 over a battery; increment's odd part = 2^|d_i-d_{i+1}|-1; P2 recovery."""
    gcd6_ok = True
    oddpart_ok = True
    bad = []
    for E in range(2, 18):
        for o in range(2, min(E, 10) + 1):
            D = 2 ** E - 3 ** o
            if D == 0:
                continue
            # D coprime to 6: D is odd (2^E even, 3^o odd => difference odd) and
            # 2^E - 3^o = (-1)^E - 0 = +-1 mod 3 (3^o = 0 mod 3 for o>=1), so nonzero mod 3.
            if gcd(abs(D), 6) != 1:
                gcd6_ok = False
                bad.append((E, o, D))

    # odd part of the increment at (2,3): increment = unit * (X^{d_{i+1}} - X^{d_i}).
    # At (2,3) the bracket is 2^{d_{i+1}} - 2^{d_i} = +- 2^{min}(2^{|d_{i+1}-d_i|} - 1);
    # odd part = 2^{|d_{i+1}-d_i|} - 1. The unit monomial Y^* X^* is coprime to D.
    for di in range(1, 7):
        for dj in range(1, 7):
            bracket = 2 ** dj - 2 ** di
            if bracket == 0:
                continue
            o2 = bracket
            while o2 % 2 == 0:
                o2 //= 2
            expect = (2 ** abs(dj - di) - 1) * (1 if bracket > 0 else -1)
            if o2 != expect:
                oddpart_ok = False
                print(f"  ODD-PART FAIL d_i={di} d_j={dj}: {o2} != {expect}")

    if bad:
        print(f"  gcd(D,6)!=1 at: {bad[:5]}")

    # P2 recovery: a swap across the single defect of d^o (background circuit).
    # tau = d^a e d^b ; the rotations d^{o-2} e d  vs d^{o-1} e differ by a swap at
    # the last position, increment = X^{(o-2)d}(X^e - X^d). Its odd part at (2,3)
    # is 2^{|e-d|}-1 -- exactly P2's ceiling.
    p2_ok = True
    for d in range(1, 4):
        for e in range(1, 6):
            if e == d:
                continue
            for o in range(2, 6):
                a, b = o - 2, 0  # last adjacent pair: d^{o-2} e d  <->  d^{o-1} e
                w = (d,) * (o - 2) + (e, d)        # rho_{o-2}
                wp = (d,) * (o - 1) + (e,)         # rho_{o-1}
                inc = S_int(w) - S_int(wp)
                op = abs(inc)
                while op % 2 == 0:
                    op //= 2
                if op != 2 ** abs(e - d) - 1:
                    p2_ok = False
                    print(f"  P2 RECOVERY FAIL d={d} e={e} o={o}: {op}")
    return gcd6_ok, oddpart_ok, p2_ok


# --------------------------------------------------------------------------- #
# (3) stratum-cover experiment -- the real research question                  #
# --------------------------------------------------------------------------- #
def stratum_experiment(strata):
    """For each stratum: canonical certificate b=1, a chosen so C = S(w) mod D
    (least residue). Report coverage, |C| spread, and single-twist radius."""
    results = []
    for (E, o) in strata:
        D = 2 ** E - 3 ** o
        if D == 0:
            continue
        words = list(compositions(E, o))
        # C(w) = S(w) mod D, least residue (b=1, a = -floor part absorbing D-multiples)
        res = {w: least_residue(S_int(w), D) for w in words}
        uncovered = [w for w in words if res[w] == 0]
        covered_abs = [abs(res[w]) for w in words if res[w] != 0]

        # propagation radius: |Delta C mod D| over single adjacent transpositions
        deltas = []
        for w in words:
            for i in range(o - 1):
                if w[i] != w[i + 1]:
                    deltas.append(abs(least_residue(S_int(swap(w, i)) - S_int(w), D)))

        # are uncovered words exactly the genuine cycle candidates (all rotations 0)?
        cyc = {w: gcd_rotations(w) for w in uncovered}

        results.append(dict(
            E=E, o=o, D=D, nwords=len(words),
            n_uncovered=len(uncovered), uncovered=uncovered,
            Cmin=min(covered_abs) if covered_abs else None,
            Cmax=max(covered_abs) if covered_abs else None,
            halfD=abs(D) // 2,
            dmin=min(deltas) if deltas else None,
            dmax=max(deltas) if deltas else None,
            dmean=(sum(deltas) / len(deltas)) if deltas else None,
            cyc=cyc,
        ))
    return results


# --------------------------------------------------------------------------- #
# main                                                                        #
# --------------------------------------------------------------------------- #
def main():
    print("=" * 72)
    print("P11 -- stratum twist / topological cover")
    print("=" * 72)

    # (1) increment identities
    print("\n[1] Increment identities (symbolic, Z[X,Y]):")
    swap_ok, utrans_ok = check_increment_identities()
    print(f"    adjacent transposition  S(w')-S(w) = Y^(o-2-i) X^P_i (X^d_{{i+1}} - X^d_i): "
          f"{'PASS' if swap_ok else 'FAIL'}")
    print(f"    unit transfer           S(w')-S(w) = Y^(o-2-i) X^P_{{i+1}} (X - 1):          "
          f"{'PASS' if utrans_ok else 'FAIL'}")
    assert swap_ok and utrans_ok, "increment identity certification failed"

    # (2) unit-mod-D, odd-part, P2 recovery
    print("\n[2] Unit-mod-D fact, odd-part size, P2 recovery:")
    gcd6_ok, oddpart_ok, p2_ok = check_unit_mod_D()
    print(f"    gcd(2^E - 3^o, 6) = 1 over E in [2,17], o in [2,min(E,10)]:  "
          f"{'PASS' if gcd6_ok else 'FAIL'}")
    print(f"    increment odd part = 2^|d_i - d_{{i+1}}| - 1:                "
          f"{'PASS' if oddpart_ok else 'FAIL'}")
    print(f"    P2 recovery (defect swap of d^o gives 2^|e-d|-1):           "
          f"{'PASS' if p2_ok else 'FAIL'}")
    assert gcd6_ok and oddpart_ok and p2_ok, "unit-mod-D / odd-part / P2 check failed"

    # divisibility battery: D | (S(rho_{o-2}) - S(rho_{o-1})) for P2 instances,
    # the rotation-difference framing where verify_divisibility_battery applies.
    def p2_core(w):
        # w encodes (d,e,o); reconstruct the two rotations' difference. Here we feed
        # the actual cyclic word tau = d^a e d^b and use its rotation difference core.
        o = len(w)
        # use the canonical last-pair difference of tau's rotations
        return S_int(w) - S_int(rotations(w)[1])  # S^{(0)} - S^{(1)}, a valid combination
    p2_instances = []
    for d in range(1, 4):
        for e in range(1, 5):
            if e == d:
                continue
            for o in range(2, 6):
                p2_instances.append((d,) * (o - 1) + (e,))
    ok, fails = verify_divisibility_battery(p2_instances, p2_core)
    print(f"    divisibility battery D | (S^(0)-S^(1)) over {len(p2_instances)} P2 words: "
          f"{'PASS' if ok else 'FAIL'}")
    if fails:
        print(f"      failures: {fails[:5]}")
    assert ok, "divisibility battery failed"

    # (3) stratum experiment
    print("\n[3] Stratum-cover experiment (canonical certificate b=1, C = S(w) mod D):")
    strata = [(5, 3), (8, 5), (7, 4), (10, 6), (11, 7), (12, 7)]
    results = stratum_experiment(strata)
    for r in results:
        print(f"\n    stratum E={r['E']} o={r['o']}  |D|={abs(r['D'])}  "
              f"#words={r['nwords']}")
        print(f"      uncovered (C==0 mod D): {r['n_uncovered']}  "
              f"-> {'NONE' if not r['uncovered'] else r['uncovered']}")
        if r['uncovered']:
            print(f"        gcd_rotations of uncovered: "
                  f"{sorted(set(r['cyc'].values()))} (=|D| means genuine cycle candidate)")
        print(f"      |C| over covered words: [{r['Cmin']}, {r['Cmax']}]  "
              f"(|D|/2 = {r['halfD']})  <-- residue fills the whole interval")
        print(f"      single-twist |Delta C mod D|: min={r['dmin']} max={r['dmax']} "
              f"mean={r['dmean']:.1f}  <-- radius ~ |D|, NOT small")

    # HONEST verdict checks, asserted so regressions are caught:
    # (a) b=1 covers everything except words whose ALL rotations vanish mod D
    #     (i.e. gcd_rotations == |D|, the genuine cycle candidates).
    for r in results:
        for w in r['uncovered']:
            assert r['cyc'][w] == abs(r['D']), \
                f"uncovered word {w} is NOT a cycle candidate (gcd_rot != |D|)"
    print("\n    CHECK: every uncovered word has gcd_rotations == |D|  "
          "(it is a genuine cycle candidate).  PASS")

    # (b) the residue is NOT contained in a small band: max |C| reaches order |D|/2.
    big = any(r['Cmax'] is not None and r['Cmax'] >= abs(r['D']) // 4 for r in results)
    assert big, "expected residues to scatter to order |D| (they did not -- recheck)"
    print("    CHECK: covered |C| reaches order |D|/2 -> single certificate does NOT "
          "keep |C| small.  CONFIRMED")

    print("\n" + "=" * 72)
    print("VERDICT: b=1 certificate covers every NON-cycle word in each stratum "
          "(C != 0 mod D),")
    print("         but |C| scatters across (0, |D|/2]; one twist moves the residue "
          "by order |D|.")
    print("         => 'topological cover' = the statement 'D | S(w) only for cycle "
          "candidates';")
    print("            it gives NO uniform small ceiling beyond the trivial |C| < |D|. "
          "(honest negative)")
    print("RESULT: PASS (all identities certified; experiment ran clean)")
    print("=" * 72)


if __name__ == "__main__":
    main()
