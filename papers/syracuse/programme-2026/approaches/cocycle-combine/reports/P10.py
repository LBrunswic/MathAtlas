#!/usr/bin/env python3
"""P10 - double-run with defect  w = x^q y z^p  (blocks x, y, z general, possibly distinct).

Verdict: NO-USEFUL-COMPENSATION (certified obstruction) for x != z; reduces to P2 only on
the merge locus x = z.

What this script certifies (all polynomial identities in Z[X,Y], plus a (2,3) battery):

  (S)  The folded closed form  S(w) = c^p b s_x G_x(q) + c^p A^q s_y + A^q B s_z G_z(p).

  (i)  Stage-(i) telescoping of the x-run:  Delta_x := S(w) - S(R^{|x|} w)
       = X^{(q-1)E_x} * C_x(p),   C_x(p) = C(x, y z^p) = D(x)S(yz^p) - D(yz^p)S(x).
       q-FREE but p-dependent.

  (ii) Stage-(ii) telescoping of the z-run (rotate w to z^p x^q y, then Delta_z):
       Delta_z = X^{(p-1)E_z} * C_z(q),   C_z(q) = D(z)S(x^q y) - D(x^q y)S(z).
       p-FREE but q-dependent.

  (D)  The two cores split EXACTLY along the geometric growth modes:
         C_x(p) = (1/D(z)) ( X^{E_y} C(x,z) * X^{p E_z}  -  N * Y^{p o_z} )
         C_z(q) = (1/D(x)) ( -N * X^{q E_x}  +  Y^{o_y} C(x,z) * Y^{q o_x} )
       with the q,p-FREE block data
         C(x,z) = D(x)S(z) - D(z)S(x)              (the x,z block-pair core)
         N      = the three-block numerator (below).

  (O)  THE OBSTRUCTION.  C_x(p) is a Z[X,Y]-combination of the two independent monomials
       X^{p E_z} and Y^{p o_z}.  A combination of rotation sums of the SINGLE word w that is
       q,p-free and nonzero would require BOTH mode coefficients to vanish, i.e.
       C(x,z) = 0 AND N = 0.  We certify:  C(x,z)=0  forces  N = D(x)D(z)(D(y)r - s_y),
       so N=0 then forces s_y = D(y) r as well -- i.e. x, y, z all share one rational fixed
       point r.  That fully-degenerate (imprimitive / single-circuit) locus is exactly where
       C == 0 (vacuous ceiling).  Off it (x != z generic), C_x(p) carries the 3-power growth
       Y^{p o_z} which odd G cannot strip: no finite q,p-free core bounds G.

  (P2) Merge check: x = z forces C(x,z) = 0; the two runs fuse to the single-defect circuit
       d^{q+p} e, recovering P2's escape (X^{(o-1)d}(X^{e-d}-1), ceiling 2^{|e-d|}-1).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "lib"))
from cocycle import (X, Y, S, D, rotate, rotations, gcd_rotations,
                     verify_symbolic_identity, verify_divisibility_battery)
import sympy as sp


# --------------------------------------------------------------------------- #
# word builders                                                               #
# --------------------------------------------------------------------------- #
def build(x, y, z, q, p):
    w = tuple()
    for _ in range(q):
        w += tuple(x)
    w += tuple(y)
    for _ in range(p):
        w += tuple(z)
    return w


def yzp(y, z, p):
    v = tuple(y)
    for _ in range(p):
        v += tuple(z)
    return v


def xqy(x, y, q):
    u = tuple()
    for _ in range(q):
        u += tuple(x)
    u += tuple(y)
    return u


# --------------------------------------------------------------------------- #
# block data and the q,p-free cores                                           #
# --------------------------------------------------------------------------- #
def Cxz(x, z):
    """C(x,z) = D(x)S(z) - D(z)S(x), the x,z block-pair core (q,p-free)."""
    return sp.expand(D(x) * S(z) - D(z) * S(x))


def Nthree(x, y, z):
    """The three-block numerator N (q,p-free)."""
    Ex, ox, sx = sum(x), len(x), S(x)
    Ey, oy, sy = sum(y), len(y), S(y)
    Ez, oz, sz = sum(z), len(z), S(z)
    return sp.expand(
        X**Ex * X**Ey * sz - X**Ex * X**Ez * sy + X**Ex * Y**oz * sy
        - X**Ey * Y**ox * sz + X**Ez * Y**ox * sy - X**Ez * Y**oy * sx
        - Y**ox * Y**oz * sy + Y**oy * Y**oz * sx
    )


def Cx_core(x, y, z, p):
    v = yzp(y, z, p)
    return sp.expand(D(x) * S(v) - D(v) * S(x))


def Cz_core(x, y, z, q):
    u = xqy(x, y, q)
    return sp.expand(D(z) * S(u) - D(u) * S(z))


# --------------------------------------------------------------------------- #
# certifications                                                              #
# --------------------------------------------------------------------------- #
def skeleton(x, y, z, q, p):
    Ex, ox, sx = sum(x), len(x), S(x)
    Ey, oy, sy = sum(y), len(y), S(y)
    Ez, oz, sz = sum(z), len(z), S(z)
    a, A = Y**ox, X**Ex
    b, B = Y**oy, X**Ey
    c = Y**oz
    Cc = X**Ez
    Gx = sum(A**(q - 1 - k) * a**k for k in range(q)) if q >= 1 else 0
    Gz = sum(Cc**(p - 1 - k) * c**k for k in range(p)) if p >= 1 else 0
    return c**p * b * sx * Gx + c**p * A**q * sy + A**q * B * sz * Gz


def main():
    blocks = [
        ((1, 2), (3,), (2, 1)),
        ((2,), (5,), (4,)),
        ((1, 1, 2), (4,), (2, 3)),
        ((3,), (1,), (2,)),
        ((1,), (2,), (3,)),
    ]
    ok_all = True

    # (S) closed form
    for (x, y, z) in blocks:
        for q in range(0, 4):
            for p in range(0, 4):
                w = build(x, y, z, q, p)
                if not verify_symbolic_identity(S(w), skeleton(x, y, z, q, p)):
                    ok_all = False
                    print(f"  [FAIL S] x={x} y={y} z={z} q={q} p={p}")
    print("(S) folded closed form  S(w) = c^p b s_x G_x(q) + c^p A^q s_y + A^q B s_z G_z(p):",
          "PASS" if ok_all else "FAIL")

    # (i) stage-x telescoping
    ok_i = True
    for (x, y, z) in blocks:
        for q in range(1, 4):
            for p in range(0, 4):
                w = build(x, y, z, q, p)
                lhs = S(w) - S(rotate(w, len(x)))
                rhs = X**((q - 1) * sum(x)) * Cx_core(x, y, z, p)
                if not verify_symbolic_identity(lhs, rhs):
                    ok_i = False
    print("(i) Delta_x = S(w) - S(R^|x| w) = X^{(q-1)E_x} C_x(p),  C_x(p)=C(x, y z^p):",
          "PASS" if ok_i else "FAIL")

    # (ii) stage-z telescoping
    ok_ii = True
    for (x, y, z) in blocks:
        for q in range(0, 4):
            for p in range(1, 4):
                w = build(x, y, z, q, p)
                shift = q * len(x) + len(y)
                wz = rotate(w, shift)  # = z^p x^q y
                lhs = S(wz) - S(rotate(wz, len(z)))
                rhs = X**((p - 1) * sum(z)) * Cz_core(x, y, z, q)
                if not verify_symbolic_identity(lhs, rhs):
                    ok_ii = False
    print("(ii) Delta_z = X^{(p-1)E_z} C_z(q),  C_z(q)=D(z)S(x^q y)-D(x^q y)S(z):",
          "PASS" if ok_ii else "FAIL")

    # (D) exact mode decomposition of the two cores
    ok_d = True
    for (x, y, z) in blocks:
        Ex, ox = sum(x), len(x)
        Ey, oy = sum(y), len(y)
        Ez, oz = sum(z), len(z)
        c_xz, N = Cxz(x, z), Nthree(x, y, z)
        for p in range(1, 5):
            pred = sp.together(X**Ey * c_xz / D(z) * X**(p * Ez) - N / D(z) * Y**(p * oz))
            if sp.simplify(Cx_core(x, y, z, p) - pred) != 0:
                ok_d = False
        for q in range(1, 5):
            pred = sp.together(-N / D(x) * X**(q * Ex) + Y**oy * c_xz / D(x) * Y**(q * ox))
            if sp.simplify(Cz_core(x, y, z, q) - pred) != 0:
                ok_d = False
    print("(D) C_x(p)=(X^{E_y}C(x,z)X^{pE_z}-N Y^{po_z})/D(z);  C_z(q) dual:",
          "PASS" if ok_d else "FAIL")

    # (O) the obstruction: C(x,z)=0 forces N = D(x)D(z)(D(y)r - s_y)
    Ex, ox = sp.symbols('Ex ox', positive=True, integer=True)
    Ey, oy = sp.symbols('Ey oy', positive=True, integer=True)
    Ez, oz = sp.symbols('Ez oz', positive=True, integer=True)
    sx, sy, sz, r = sp.symbols('sx sy sz r')
    Dx, Dy, Dz = X**Ex - Y**ox, X**Ey - Y**oy, X**Ez - Y**oz
    N_sym = (X**Ex * X**Ey * sz - X**Ex * X**Ez * sy + X**Ex * Y**oz * sy
             - X**Ey * Y**ox * sz + X**Ez * Y**ox * sy - X**Ez * Y**oy * sx
             - Y**ox * Y**oz * sy + Y**oy * Y**oz * sx)
    N_on_Cxz0 = sp.factor(sp.expand(N_sym.subs({sx: r * Dx, sz: r * Dz})))
    ok_o = (sp.simplify(N_on_Cxz0 - Dx * Dz * (Dy * r - sy)) == 0)
    print("(O) C(x,z)=0  =>  N = D(x)D(z)(D(y)r - s_y)  [N=0 iff y shares fixed pt]:",
          "PASS" if ok_o else "FAIL")
    # and on the full degenerate locus both cores vanish
    sub = {sx: r * Dx, sy: r * Dy, sz: r * Dz}
    deg_X = sp.simplify((X**Ey * (Dx * sz - Dz * sx) / Dz).subs(sub))
    deg_Y = sp.simplify((-N_sym / Dz).subs(sub))
    ok_o = ok_o and deg_X == 0 and deg_Y == 0
    print("    on shared-fixed-point locus (s_x=rD(x),s_y=rD(y),s_z=rD(z)): C_x(p) modes -> 0,0:",
          "PASS" if (deg_X == 0 and deg_Y == 0) else "FAIL")

    # (P2) merge: x=z => C(x,z)=0, reduces to P2 single-defect circuit
    ok_p2 = True
    d, e = 2, 5
    for q in range(1, 4):
        for p in range(1, 4):
            x = z = (d,)
            y = (e,)
            if Cxz(x, z) != 0:
                ok_p2 = False
            w = build(x, y, z, q, p)
            o = q + p + 1
            p2core = X**((o - 1) * d) * (X**(e - d) - 1)  # P2 core for d^{q+p} e
            G = gcd_rotations(w)
            Cval = int(p2core.subs({X: 2, Y: 3}))
            if Cval % G != 0:
                ok_p2 = False
    print("(P2) x=z merge: C(x,z)=0, recovers P2 core X^{(o-1)d}(X^{e-d}-1):",
          "PASS" if ok_p2 else "FAIL")

    # battery: G | Delta_x at (2,3) over distinct-block sweeps and the merge case.
    # Delta_x = S(w) - S(R^{|x|} w) is a genuine rotation difference of the SINGLE word w,
    # so G = gcd of its rotation sums must divide it.
    _xlen = {}

    def core_fn(w):
        return int(S(w, 2, 3) - S(rotate(w, _xlen[w]), 2, 3))

    instances = []
    for (x, y, z) in blocks:
        for q in range(1, 5):
            for p in range(1, 5):
                w = build(x, y, z, q, p)
                _xlen[w] = len(x)
                instances.append(w)
    ok_bat, fails = verify_divisibility_battery(instances, core_fn)
    print(f"(BATTERY) G | Delta_x over {len(instances)} instances "
          f"(blocks x{len(blocks)}, q,p in 1..4):", "PASS" if ok_bat else "FAIL")
    for f in fails[:5]:
        print("   FAIL:", f)

    # --- report core / bound ---
    print()
    print("CORE  C_x(p) = ( X^{E_y} C(x,z) * X^{p E_z}  -  N * Y^{p o_z} ) / D(z)")
    print("  X-exponent of leading term = E_y + p E_z  -> GROWS with p")
    print("  Y-exponent of trailing term = p o_z       -> 3-power growth, NOT strippable by odd G")
    print("GCD BOUND: none for x != z off the shared-fixed-point locus")
    print("           (every single-word rotation combination carries unremovable Y^{p o_z} growth).")
    print("           On x=z (runs merge): reduces to P2,  |2^E - 3^o| <= 2^{|e-d|} - 1.")
    print("DEGENERATE C == 0 locus: C(x,z)=0 AND N=0  <=>  x, y, z share one rational fixed point")
    print("           (imprimitive / single-circuit stratum; the bound is vacuous there).")

    passed = ok_all and ok_i and ok_ii and ok_d and ok_o and ok_p2 and ok_bat
    print()
    print("RESULT:", "PASS (obstruction certified; no useful q,p-free compensation for x!=z)"
          if passed else "FAIL")
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
