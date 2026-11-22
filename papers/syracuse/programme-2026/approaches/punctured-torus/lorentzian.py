"""
punctured-torus :: Stage 2 (target = LORENTZIAN, flat / Margulis-spacetime model).

Minkowski 3-space  R^{2,1} = sl_2(R),  with the (Ad-invariant) Lorentzian form
    q(X) = -det(X) = 1/2 tr(X^2),     <X,Y> = 1/2 tr(XY)      (signature (2,1)).
A linear isometry is Ad(g), g in SL_2 (=> Ad : SL_2 -> SO(2,1)); an affine isometry is
X |-> Ad(g)X + u(g) with u : Gamma -> sl_2 a translation cocycle
(u(gh) = u(g) + Ad(g)u(h)). Closed geodesics <-> conjugacy classes; the signed Lorentzian
length is the MARGULIS INVARIANT  alpha(gamma) = <u(gamma), x0(gamma)>, x0 = neutral
(eigenvalue-1) vector of Ad(rho(gamma)). Properness (a genuine Margulis spacetime) <=>
all alpha(gamma) same sign (Goldman-Labourie-Margulis).

We compute two things on the known cycles 1->1, -1, -5->-7:
  (A) SPECTRAL picture (rigorous, no deformation): Ad of the cycle's SL_2 element has
      eigenvalues {2^E/3^o, 1, 3^o/2^E}; rapidity (spacelike length) = |log(2^E/3^o)| = ell
      (= the hyperbolic length); the neutral axis is spacelike. Null coordinates
      (u,v)=(2^E,3^o): the Lorentzian "interval" is D = 2^E-3^o and criticality 2^E~3^o is
      the LIGHT CONE u=v.
  (B) MARGULIS invariant for the natural realization: linear part rho0 = the diagonal
      (multiplicative 2-3) holonomy, translation cocycle u = the velocity of turning on the
      Syracuse "+1". FINDING: u lands in the null E-direction (orthogonal to the spacelike
      axis H), so alpha(gamma) == 0 identically -- the naive flat-Lorentzian realization is
      DEGENERATE: the "+1" is a lightlike translation. (Consistent with criticality = light
      cone; tells us a non-degenerate model needs a non-abelian linear part or the curved
      AdS route.)
"""
import math
import numpy as np

# ---- generators and cycle cumulative matrices (homogeneous) ----------------
A = np.array([[3.0, 1.0], [0.0, 2.0]])     # a : z -> (3z+1)/2
B = np.array([[1.0, 0.0], [0.0, 2.0]])     # b : z -> z/2
GEN = {"a": A, "b": B}


def cumulative(abword):
    G = np.eye(2)
    for c in abword:
        G = GEN[c] @ G
    return G


# ---- Minkowski = sl_2 ------------------------------------------------------
H = np.array([[1.0, 0.0], [0.0, -1.0]])
E = np.array([[0.0, 1.0], [0.0, 0.0]])
Fm = np.array([[0.0, 0.0], [1.0, 0.0]])
BASIS = [H, E, Fm]


def mink(X, Y):
    return 0.5 * np.trace(X @ Y)


def qform(X):
    return 0.5 * np.trace(X @ X)            # = -det(X)


def Ad_matrix(g):
    """matrix of Ad(g): sl_2 -> sl_2 in the basis (H,E,F)."""
    gi = np.linalg.inv(g)
    cols = []
    for Xb in BASIS:
        Y = g @ Xb @ gi
        cols.append([Y[0, 0], Y[0, 1], Y[1, 0]])   # coords (a,b,c) of aH+bE+cF
    return np.array(cols).T


def neutral_vector(g):
    """eigenvalue-1 vector of Ad(g): the traceless part of g (Ad fixes g and I)."""
    return g - 0.5 * np.trace(g) * np.eye(2)


CYCLES = [("ab", 1, 2, 1), ("a", 1, 1, -1), ("aab", 2, 3, -5)]

print("=" * 78)
print("(A) SPECTRAL Minkowski picture of the cycle elements")
print("=" * 78)
for word, o, Ee, x0_known in CYCLES:
    G = cumulative(word)
    det = 2 ** Ee * 3 ** o
    Gh = G / math.sqrt(det)
    adeig = sorted(np.linalg.eigvals(Ad_matrix(Gh)).real, reverse=True)
    expect = sorted([2 ** Ee / 3 ** o, 1.0, 3 ** o / 2 ** Ee], reverse=True)
    x0 = neutral_vector(Gh)
    fixed_err = np.max(np.abs(Gh @ x0 @ np.linalg.inv(Gh) - x0))
    rap = math.log(max(2 ** Ee / 3 ** o, 3 ** o / 2 ** Ee))
    ell = abs(math.log(2 ** Ee / 3 ** o))
    print(f"  cycle {word:<4}(o={o},E={Ee}):  Ad eigenvalues {[round(v,4) for v in adeig]}")
    print(f"        expected {{2^E/3^o,1,3^o/2^E}} = {[round(v,4) for v in expect]}  "
          f"match={np.allclose(adeig, expect)}")
    print(f"        neutral axis x0 fixed by Ad? err={fixed_err:.1e}   "
          f"q(x0)={qform(x0):+.5f} ({'spacelike' if qform(x0) > 0 else 'non-spacelike'})")
    print(f"        rapidity=|log(2^E/3^o)|={rap:.5f} =? hyperbolic length ell={ell:.5f}  "
          f"{np.isclose(rap, ell)}")
    print(f"        null coords (2^E,3^o)=({2**Ee},{3**o}): interval D=2^E-3^o="
          f"{2**Ee - 3**o}, |D| small <=> near light cone 2^E=3^o")
    assert np.allclose(adeig, expect) and fixed_err < 1e-9 and np.isclose(rap, ell)

print()
print("=" * 78)
print("(B) MARGULIS invariant: diagonal linear part + Syracuse-'+1' cocycle")
print("=" * 78)
# linear part rho0 = diagonal (multiplicative 2-3) holonomy, normalised to SL2
rho0 = {
    "a": np.diag([math.sqrt(3 / 2), math.sqrt(2 / 3)]),   # z -> (3/2) z
    "b": np.diag([math.sqrt(1 / 2), math.sqrt(2.0)]),     # z -> (1/2) z
}
# translation cocycle u = d/ds of turning on the '+1' of a (b has no affine constant)
u_gen = {"a": 0.5 * E, "b": np.zeros((2, 2))}


def rho0_word(abword):
    G = np.eye(2)
    for c in abword:
        G = rho0[c] @ G
    return G


def u_word(abword):
    """cocycle u(w_1..w_n) = sum_k Ad(rho0(w_1..w_{k-1})) u(w_k)."""
    total = np.zeros((2, 2))
    prefix = np.eye(2)
    for c in abword:
        total = total + prefix @ u_gen[c] @ np.linalg.inv(prefix)
        prefix = rho0[c] @ prefix
    return total


for word, o, Ee, _ in CYCLES:
    g = rho0_word(word)
    x0 = neutral_vector(g)                    # neutral axis of the diagonal part = H-dir
    nx = math.sqrt(abs(qform(x0))) if qform(x0) != 0 else 1.0
    u = u_word(word)
    alpha = mink(u, x0) / nx
    print(f"  cycle {word:<4}:  u(gamma)={np.round(u,4).tolist()}   "
          f"q(u)={qform(u):+.2e} (null⇔0)   <u,axis>=alpha={alpha:+.2e}")
    assert abs(qform(u)) < 1e-9            # the '+1' cocycle is LIGHTLIKE
    assert abs(alpha) < 1e-9              # => Margulis invariant vanishes identically
print("\n  => '+1' translation is NULL (E-direction) ⟂ spacelike axis H : alpha(gamma)≡0.")
print("     The naive flat-Lorentzian model is DEGENERATE (lightlike cocycle); a")
print("     non-degenerate Margulis spacetime needs a NON-abelian linear part, or the")
print("     curved AdS route (Mess, two reps).  Null '+1' ⇔ criticality = light cone.")

print()
print("=" * 78)
print("(C) Identification in Brunswic, arXiv:2108.12631 — the puncture is EXTREME BTZ")
print("=" * 78)
# Theorem 1 applies to Sigma* = once-punctured torus: genus g=1, s=1 marked point.
g, s = 1, 1
print(f"  Cauchy surface Sigma* = once-punctured torus: genus g={g}, s={s} marked point;")
print(f"  2-2g-s = {2 - 2 * g - s} < 0  =>  Theorem 1 applies (moduli = T Teich(Sigma*),")
print(f"  real dim 6g-6+4s = {6 * g - 6 + 4 * s}).")
assert 2 - 2 * g - s < 0
# puncture holonomy = commutator of the actual Syracuse SL2 holonomy
A2 = np.array([[3.0, 1.0], [0.0, 2.0]])
B2 = np.array([[1.0, 0.0], [0.0, 2.0]])
K = A2 @ B2 @ np.linalg.inv(A2) @ np.linalg.inv(B2)        # [A,B]
adK_eig = np.linalg.eigvals(Ad_matrix(K))
print(f"  puncture holonomy [A,B] = {np.round(K, 4).tolist()}")
print(f"     Ad([A,B]) eigenvalues = {np.round(adK_eig, 4).tolist()}  "
      f"(all 1 => PARABOLIC: the cusp holonomy, Brunswic p.7)")
assert np.allclose(adK_eig, 1.0)
fixedE = K @ E @ np.linalg.inv(K)
print(f"     Ad([A,B]) E = {np.round(fixedE, 4).tolist()} (= E)   q(E)={qform(E):.1f} (NULL axis)")
assert np.allclose(fixedE, E) and abs(qform(E)) < 1e-12
print("  => parabolic linear holonomy fixing the null line R.E, with translation S in R.E")
print("     = EXTREME BTZ (the Lorentzian cusp). So Syracuse = a point of T Teich(Sigma_{1,1})")
print("        with ONE extreme BTZ at the puncture;  D=2^E-3^o = Minkowski interval,")
print("        S = the null BTZ translation datum (the tangent-to-Teichmuller fibre).")

print("\nALL LORENTZIAN ASSERTS PASSED.")
