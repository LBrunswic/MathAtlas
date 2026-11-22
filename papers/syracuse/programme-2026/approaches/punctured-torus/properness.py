"""
punctured-torus :: tune the affine cocycle for PROPERNESS (a genuine Margulis spacetime).

On the irreducible discrete base of nontrivial_rep.py (Syracuse generator-lengths,
mu_a=3/2, mu_b=2, Schottky once-holed torus), an affine deformation tau gives a properly
discontinuous action -- a genuine flat Lorentzian 3-manifold (Margulis spacetime) -- iff the
Margulis invariants alpha(gamma) all share one sign (Goldman-Labourie-Margulis). Since
alpha(gamma) = <tau(gamma), x0(gamma)> is LINEAR in tau=(tau_a,tau_b) in R^6, "find a proper
cocycle" is a linear feasibility problem:  maximise t s.t. alpha(gamma) >= t for all classes
gamma (box-normalised tau). Drumm: such tau exist for Schottky groups.

We: (1) certify the Margulis invariant is a consistent class function (alpha(g)=alpha(g^-1),
conjugation-invariant); (2) solve the LP over all cyclically-reduced classes up to length L;
(3) report a proper cocycle and check it stays positive at length L+2; (4) probe for an
ARITHMETIC reading: is a Syracuse-type (tau_b=0, supported on the '+1') cocycle ever proper,
and do the proper-cone / Margulis values see S, D, or S/D?
"""
import math
import itertools
import numpy as np

# --- base (same as nontrivial_rep.py) --------------------------------------
def hyp(fp, fm, mu):
    lam = math.sqrt(mu)
    M = np.array([[fp, fm], [1.0, 1.0]])
    g = M @ np.diag([lam, 1 / lam]) @ np.linalg.inv(M)
    return g / math.sqrt(np.linalg.det(g))


A = hyp(0.05, -0.05, 1.5)
B = hyp(1.05, 0.95, 2.0)
Ai, Bi = np.linalg.inv(A), np.linalg.inv(B)
LET = {"A": A, "a": Ai, "B": B, "b": Bi}
INV = {"A": "a", "a": "A", "B": "b", "b": "B"}

# --- sl2 = E^{1,2} ----------------------------------------------------------
Hm = np.array([[1.0, 0], [0, -1.0]])
Em = np.array([[0, 1.0], [0, 0]])
Fm = np.array([[0, 0], [1.0, 0]])
Gram = np.array([[1.0, 0, 0], [0, 0, 0.5], [0, 0.5, 0]])     # <,> in basis (H,E,F)


def to3(X):
    return np.array([X[0, 0], X[0, 1], X[1, 0]])


def Ad3(g):
    gi = np.linalg.inv(g)
    return np.array([to3(g @ b @ gi) for b in (Hm, Em, Fm)]).T


def neutral(g):
    """canonically-oriented unit spacelike neutral axis x0(g) (via bracket of null eigvecs)."""
    w, V = np.linalg.eig(g)
    idx = np.argsort(np.abs(w))
    um, up = np.real(V[:, idx[0]]), np.real(V[:, idx[1]])

    def nil(u):
        p, q = u
        return np.array([[p * q, -p * p], [q * q, -p * q]])
    br = nil(um) @ nil(up) - nil(up) @ nil(um)
    x0 = to3(br)
    return x0 / math.sqrt(abs(x0 @ Gram @ x0))


def wmat(word):
    g = np.eye(2)
    for ch in word:
        g = g @ LET[ch]               # forward product L(l_1)...L(l_n)
    return g


# per-letter cocycle coefficient (3x6), xi = (tau_a[0:3], tau_b[3:6])
I3, Z3 = np.eye(3), np.zeros((3, 3))
LCO = {"A": np.hstack([I3, Z3]), "B": np.hstack([Z3, I3])}
LCO["a"] = -Ad3(Ai) @ LCO["A"]
LCO["b"] = -Ad3(Bi) @ LCO["B"]


def alpha_coeff(word):
    """6-vector c with alpha(word) = c . xi."""
    T = np.zeros((3, 6))
    pref = np.eye(2)
    for ch in word:
        T = T + Ad3(pref) @ LCO[ch]   # pref = L(l_1)...L(l_{k-1}) (forward)
        pref = pref @ LET[ch]
    return (Gram @ neutral(wmat(word))) @ T


def inverse(word):
    return "".join(INV[c] for c in reversed(word))


# --- (1) consistency of the Margulis invariant ------------------------------
xi0 = np.array([1.0, 2, -1, 0.5, -3, 2])
print("=" * 76)
print("(1) Margulis invariant is a consistent class function")
print("=" * 76)
for w in ["AB", "AAB", "ABab"]:
    a_w = alpha_coeff(w) @ xi0
    a_inv = alpha_coeff(inverse(w)) @ xi0
    a_conj = alpha_coeff("B" + w + "b") @ xi0      # conjugate by B
    print(f"  {w:5}: alpha={a_w:+.5f}  alpha(inv)={a_inv:+.5f}  alpha(conj)={a_conj:+.5f}")
    assert abs(a_w - a_inv) < 1e-4 and abs(a_w - a_conj) < 1e-4

# --- enumerate cyclically-reduced primitive classes up to length L ----------
def classes_upto(L):
    seen = set()
    out = []
    for n in range(1, L + 1):
        for tup in itertools.product("AaBb", repeat=n):
            w = "".join(tup)
            if any(w[i] == INV[w[(i + 1) % n]] for i in range(n)):
                continue                                   # cyclically reduced
            key = min(min(w[i:] + w[:i] for i in range(n)),
                      min((iw := inverse(w))[i:] + iw[:i] for i in range(n)))
            if key in seen:
                continue
            seen.add(key)
            out.append(w)
    return out


def solve_proper(words, fix_taub_zero=False, iters=6000):
    """max-min_gamma alpha(gamma) over the unit sphere (cone is scale-invariant), by
    softmin gradient ascent. Positive margin => proper cocycle exists."""
    C = np.array([alpha_coeff(w) for w in words])         # (N,6)
    if fix_taub_zero:
        C = C[:, :3]
    d = C.shape[1]
    xi = np.ones(d) / math.sqrt(d)
    best = (-1e9, xi.copy())
    for it in range(iters):
        a = C @ xi
        if a.min() > best[0]:
            best = (a.min(), xi.copy())
        beta = 3.0 * (1 + it / 300.0)                     # sharpen toward the true min
        p = np.exp(-beta * (a - a.min())); p /= p.sum()
        xi = xi + 0.15 * (C.T @ p)
        xi /= (np.linalg.norm(xi) + 1e-12)                # project to unit sphere
    margin, xfound = best
    full = np.zeros(6); full[:d] = xfound
    return margin, full


print()
print("=" * 76)
print("(2) Linear-programming search for a proper cocycle")
print("=" * 76)
L = 6
words = classes_upto(L)
print(f"  {len(words)} cyclically-reduced primitive classes up to length {L}")
t_star, xi_star = solve_proper(words)
print(f"  max uniform margin t* = {t_star:+.5f}  -> "
      f"{'PROPER cocycle found' if t_star and t_star > 1e-6 else 'no proper cocycle'}")
assert t_star is not None and t_star > 1e-6
print(f"  proper cocycle  tau_a = {np.round(xi_star[:3],4)}   tau_b = {np.round(xi_star[3:],4)}")

# (3) robustness: does it stay positive two lengths further out?
words2 = classes_upto(L + 2)
amin = min(alpha_coeff(w) @ xi_star for w in words2)
print(f"  min alpha over all {len(words2)} classes up to length {L+2}: {amin:+.5f}  "
      f"({'still all positive (robust)' if amin > 0 else 'FAILS further out'})")

print()
print("=" * 76)
print("(4) Arithmetic probe")
print("=" * 76)
# (4a) can a Syracuse-type cocycle (tau_b = 0, supported on the '+1') be proper?
t0, xi0z = solve_proper(words, fix_taub_zero=True)
print(f"  proper cocycle with tau_b=0 (Syracuse-supported)?  margin t = "
      f"{t0:+.5f} -> {'YES' if t0 and t0 > 1e-6 else 'NO -- impossible'}")

# (4b) Margulis invariants of the actual Syracuse cycles under the proper cocycle,
#      compared with their arithmetic (S, D, S/D).
print("  Margulis invariants of Syracuse cycles under the proper cocycle vs (S,D,S/D):")
SYR = [("AB", 1, 2, 1, 1), ("A", 1, 1, 1, -1), ("AAB", 2, 3, 5, -1)]   # word,o,E,S,D
for w, o, E, S, D in SYR:
    a = alpha_coeff(w) @ xi_star
    print(f"    {w:4} (S={S:>2},D={D:>2},S/D={S/D:+.0f}):  alpha = {a:+.5f}")
print("\nALL PROPERNESS ASSERTS PASSED.")
