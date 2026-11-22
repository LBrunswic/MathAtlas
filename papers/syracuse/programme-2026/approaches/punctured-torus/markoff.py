"""
punctured-torus :: Stage 1 keystone — locate the Syracuse holonomy in the
once-punctured-torus character variety (the Markoff/Fricke cubic), and scaffold the
Stage-2 deformation off the reducible locus.

Generators (F2 = pi_1(Sigma_{1,1}), the two affine maps):
    a : z |-> (3z+1)/2   ->  A = [[3,1],[0,2]]   (homogeneous; det 6, tr 5)
    b : z |-> z/2        ->  B = [[1,0],[0,2]]   (homogeneous; det 2, tr 3)
SL2 normalisation divides by sqrt(det): tr_SL2 = tr/sqrt(det).

We CERTIFY (asserts):
  (1) trace coordinates (x,y,z) = (tr A, tr B, tr AB) = (5/sqrt6, 3/sqrt2, 7/(2 sqrt3));
  (2) tr[A,B] = +2 exactly  => REDUCIBLE locus (shared fixed point oo), cubic level set
      x^2+y^2+z^2-xyz = 4;
  (3) the Fricke identity tr[A,B] = x^2+y^2+z^2-xyz-2 holds;
  (4) the commutator [A,B] is a NON-TRIVIAL PARABOLIC (unipotent, translation by 1/4) =>
      genuine cusp/puncture at oo in the degenerate model;
  (5) SUB-MARKOFF: both generator traces < 3 = the Markoff minimum trace on the cusped
      hyperbolic locus, so the generators cannot uniformise a cusped hyperbolic punctured
      torus directly (obstruction motivating the Stage-2 target choice);
  (6) per-cycle cross-check vs structure.md C1/C4/C11 and hyperbolic_model.py:
      cumulative matrix of a cycle word has trace = 2^E+3^o, det = 2^E*3^o, eigenvalue
      gap = |D|, attracting fixed point x0 = S/D, length ell = |log(2^E/3^o)|.

Stage-2 SCAFFOLDING (target-agnostic): deform(t) conjugates B by C_t = [[1,0],[t,1]],
opening the shared fixed point oo (B_t fixes 0 and 1/t, not oo) and leaving the reducible
locus for t != 0; track_cycle(word, t) follows a cycle's (trace, x0, ell, reducible?).
The actual target geometry is NOT chosen here -- see TODO(stage-2 target).
"""
import os
import sys
import math

import sympy as sp

# reuse the trusted cocycle kernel (S, D, verify_symbolic_identity, ...)
_LIB = os.path.join(os.path.dirname(__file__), "..", "cocycle-combine", "lib")
sys.path.insert(0, os.path.abspath(_LIB))
import cocycle as kc  # noqa: E402  (S, D, X, Y, verify_symbolic_identity, ...)

# --------------------------------------------------------------------------- #
# Generators (homogeneous integer matrices) and SL2 traces                    #
# --------------------------------------------------------------------------- #
A = sp.Matrix([[3, 1], [0, 2]])     # a : z -> (3z+1)/2
B = sp.Matrix([[1, 0], [0, 2]])     # b : z -> z/2


def sl2_trace(M):
    """trace of the det-1 normalisation M / sqrt(det M)."""
    return sp.nsimplify(M.trace() / sp.sqrt(M.det()))


def commutator(P, Q):
    return P * Q * P.inv() * Q.inv()


print("=" * 76)
print("STAGE 1 KEYSTONE — Syracuse holonomy on the Markoff/Fricke cubic")
print("=" * 76)

x = sl2_trace(A)
y = sl2_trace(B)
z = sl2_trace(A * B)
print(f"  trace coordinates  (x,y,z) = (tr A, tr B, tr AB)")
print(f"     x = tr A  = {x} = {float(x):.5f}")
print(f"     y = tr B  = {y} = {float(y):.5f}")
print(f"     z = tr AB = {z} = {float(z):.5f}")

# (1) exact values
assert sp.simplify(x - sp.Rational(5) / sp.sqrt(6)) == 0
assert sp.simplify(y - sp.Rational(3) / sp.sqrt(2)) == 0
assert sp.simplify(z - sp.Rational(7) / (2 * sp.sqrt(3))) == 0

# (2)+(3) Fricke identity and the reducible level set
fricke_rhs = sp.simplify(x**2 + y**2 + z**2 - x * y * z - 2)
comm = commutator(A, B)
tr_comm = sp.simplify(comm.trace())               # scalar-normalisation invariant
print(f"\n  Fricke  x^2+y^2+z^2-xyz-2 = {fricke_rhs}")
print(f"  tr[A,B] (from matrices)  = {tr_comm}")
assert fricke_rhs == 2, fricke_rhs
assert tr_comm == 2, tr_comm
level = sp.simplify(x**2 + y**2 + z**2 - x * y * z)
assert level == 4, level
print(f"  => REDUCIBLE locus tr[A,B]=2 ; cubic level set x^2+y^2+z^2-xyz = {level}")

# (4) commutator is a non-trivial parabolic (the cusp)
print(f"\n  commutator [A,B] = {comm.tolist()}  (z -> z + 1/4)")
assert comm == sp.Matrix([[1, sp.Rational(1, 4)], [0, 1]]), comm.tolist()
assert comm[0, 0] == 1 and comm[1, 1] == 1 and comm[1, 0] == 0   # unipotent upper-tri
assert comm[0, 1] != 0                                           # non-trivial translation
print("  => non-trivial PARABOLIC fixing oo : genuine cusp/puncture in the degenerate model")

# (5) sub-Markoff obstruction (Markoff minimum trace on cusped-hyperbolic locus = 3)
print(f"\n  sub-Markoff?  generator traces vs Markoff minimum 3:")
print(f"     tr A = {float(x):.4f} < 3,  tr B = {float(y):.4f} < 3,  tr AB = {float(z):.4f} < 3")
assert float(x) < 3 and float(y) < 3 and float(z) < 3
print("  => generators are SUB-MARKOFF: too short to uniformise a cusped hyperbolic")
print("     punctured torus directly (no real deformation at fixed (x,y) reaches tr[A,B]=-2;")
print("     discriminant of z^2 - (xy)z + (x^2+y^2) = 0 is negative):")
disc = sp.simplify((x * y) ** 2 - 4 * (x**2 + y**2))
print(f"        disc = (xy)^2 - 4(x^2+y^2) = {disc} = {float(disc):.4f} < 0")
assert float(disc) < 0, disc

# --------------------------------------------------------------------------- #
# (6) per-cycle cross-check vs structure.md and hyperbolic_model.py            #
# --------------------------------------------------------------------------- #
print()
print("=" * 76)
print("Per-cycle cross-check: cumulative matrix trace/det/gap/x0 vs 2^E,3^o and S/D")
print("=" * 76)

# (a,b)-word -> gap word, and the known cycle value x0
CYCLES = [
    ("ab",  (2,),   1),    # 1->1
    ("a",   (1,),  -1),    # -1
    ("aab", (1, 2), -5),   # -5->-7
]
GEN = {"a": A, "b": B}


def cumulative_matrix(abword, gens=GEN):
    """G = M_{w_n} ... M_{w_1} (apply a then b ... left to right), homogeneous."""
    G = sp.eye(2)
    for c in abword:
        G = gens[c] * G
    return G


for abword, gapword, x0_known in CYCLES:
    G = cumulative_matrix(abword)
    o = abword.count("a")
    E = len(abword)
    tr = G.trace()
    det = G.det()
    eigs = sorted(int(e) for e in G.eigenvals())          # {3^o, 2^E}
    gap = abs(eigs[1] - eigs[0])
    Dval = kc.D_int(gapword)                                # 2^E - 3^o
    Sval = kc.S_int(gapword)
    x0 = sp.Rational(Sval, Dval)
    ell = math.log((2 ** E) / (3 ** o))
    print(f"  cycle {abword:<4} gap={gapword!s:<6} (o={o},E={E}): "
          f"tr={tr} =? 2^E+3^o={2**E + 3**o}  det={det} =? {2**E * 3**o}  "
          f"gap={gap} =? |D|={abs(Dval)}")
    print(f"        x0 = S/D = {Sval}/{Dval} = {x0} =? known {x0_known}   "
          f"ell=|log(2^E/3^o)|={abs(ell):.5f}")
    assert tr == 2 ** E + 3 ** o
    assert det == 2 ** E * 3 ** o
    assert gap == abs(Dval)
    assert x0 == x0_known

# symbolic reuse: certify generic period trace = X^E + Y^o via the kernel certifier
print("\n  symbolic (Z[X,Y]) certification that tr M(w) = X^E + Y^o (structure.md C1/C11):")


def M_gap(d):
    """structure.md transfer matrix for a single gap letter d."""
    return sp.Matrix([[kc.Y, 0], [1, kc.X ** d]])


for _, gapword, _ in CYCLES:
    Mw = sp.eye(2)
    for d in gapword:
        Mw = Mw * M_gap(d)
    E = sum(gapword)
    o = len(gapword)
    ok = kc.verify_symbolic_identity(sp.expand(Mw.trace()), kc.X ** E + kc.Y ** o)
    print(f"     gap {gapword!s:<6}: tr M(w) == X^{E} + Y^{o} ?  {ok}")
    assert ok

# --------------------------------------------------------------------------- #
# Stage-2 SCAFFOLDING (target-agnostic) : deform off the reducible locus       #
# --------------------------------------------------------------------------- #
# TODO(stage-2 target): the actual target geometry (singular-flat / Lorentzian /
# lengthened-Fuchsian) is NOT chosen here. This is only the framework: a path that
# opens the shared fixed point oo and leaves the reducible locus, plus a cycle tracker.


def deform_sym(t):
    """Exact (sympy) deformed pair: conjugate B by C_t = [[1,0],[t,1]]."""
    t = sp.nsimplify(t)
    Ct = sp.Matrix([[1, 0], [t, 1]])
    return A, Ct * B * Ct.inv()


def tr_comm_sym(t):
    """Exact tr[A, B_t] (used only for the few assert/print checks)."""
    At, Bt = deform_sym(t)
    return sp.simplify(commutator(At, Bt).trace())


# --- fast float paths for the plot loop -------------------------------------
import numpy as np  # noqa: E402

_Af = np.array([[3.0, 1.0], [0.0, 2.0]])
_Bf = np.array([[1.0, 0.0], [0.0, 2.0]])


def deform_f(t):
    Ct = np.array([[1.0, 0.0], [float(t), 1.0]])
    return _Af, Ct @ _Bf @ np.linalg.inv(Ct)


def tr_comm_f(t):
    Af, Bf = deform_f(t)
    C = Af @ Bf @ np.linalg.inv(Af) @ np.linalg.inv(Bf)
    return float(np.trace(C))


def track_cycle(abword, t):
    """Float tracker: (trace, det, x0, ell, reducible?) for a cycle word under deform."""
    Af, Bf = deform_f(t)
    gens = {"a": Af, "b": Bf}
    G = np.eye(2)
    for c in abword:
        G = gens[c] @ G
    w, V = np.linalg.eig(G)
    k = int(np.argmax(np.abs(w)))
    x0 = V[0, k] / V[1, k]
    lam = sorted(np.abs(w), reverse=True)
    ell = math.log(lam[0] / lam[1]) if lam[1] > 0 else float("nan")
    return dict(trace=float(np.trace(G)), det=float(np.linalg.det(G)),
                x0=x0, ell=ell, reducible=abs(tr_comm_f(t) - 2) < 1e-9)


print()
print("=" * 76)
print("Stage-2 scaffolding sanity (target NOT yet chosen)")
print("=" * 76)
assert tr_comm_sym(0) == 2                      # t=0 reproduces reducible Syracuse (exact)
assert tr_comm_sym(sp.Rational(1)) != 2         # t!=0 leaves the reducible locus (exact)
print(f"  tr[A,B_t] (exact):  t=0 -> {tr_comm_sym(0)} (reducible)   "
      f"t=1 -> {tr_comm_sym(1)}   t=2 -> {tr_comm_sym(2)}")
for t in (0.0, 0.5, 1.0):
    info = track_cycle("ab", t)
    print(f"  cycle 'ab' @ t={t}:  trace={info['trace']:.4f}  x0={np.real(info['x0']):+.5f}  "
          f"ell={info['ell']:.5f}  reducible={info['reducible']}")
base = track_cycle("ab", 0.0)
assert abs(np.real(base["x0"]) - 1) < 1e-9 and abs(base["ell"] - math.log(4 / 3)) < 1e-9

# --------------------------------------------------------------------------- #
# optional plot                                                               #
# --------------------------------------------------------------------------- #
try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    ts = np.linspace(-2.5, 2.5, 121)
    trc = [tr_comm_f(t) for t in ts]
    x0s, ells = [], []
    for t in ts:
        info = track_cycle("ab", float(t))
        x0s.append(float(np.real(info["x0"])))
        ells.append(info["ell"])

    fig, ax = plt.subplots(1, 3, figsize=(13, 4))
    ax[0].plot(ts, trc); ax[0].axhline(2, color="r", ls="--", lw=.8, label="reducible (=2)")
    ax[0].axhline(-2, color="g", ls=":", lw=.8, label="cusped Fuchsian (=-2)")
    ax[0].set_title(r"$\mathrm{tr}[A,B_t]$ along the deformation"); ax[0].set_xlabel("t")
    ax[0].legend(fontsize=8)
    ax[1].plot(ts, x0s); ax[1].axhline(1, color="r", ls="--", lw=.8)
    ax[1].set_title(r"cycle $1\to1$: attracting fixed point $x_0(t)$"); ax[1].set_xlabel("t")
    ax[2].plot(ts, ells); ax[2].axhline(math.log(4 / 3), color="r", ls="--", lw=.8)
    ax[2].set_title(r"cycle $1\to1$: length $\ell(t)$"); ax[2].set_xlabel("t")
    fig.suptitle("Stage-2 deformation scaffolding (target geometry not yet chosen)")
    fig.tight_layout()
    out = os.path.join(os.path.dirname(__file__), "markoff_deformation.png")
    fig.savefig(out, dpi=130)
    print(f"\n  [plot written to {out}]")
except Exception as e:
    print(f"\n  [plot skipped: {e}]")

print("\nALL KEYSTONE ASSERTS PASSED.")
