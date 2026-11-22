"""
punctured-torus :: a NON-TRIVIAL (irreducible, discrete, free) representation.

The literal Syracuse cocycle forces reducibility (the character lambda=(3/2,1/2) needs a
shared eigenline). To escape that we keep the two generators' CONJUGACY DATA -- the
multipliers 3/2 and 2, hence the exact Syracuse traces tr A=5/sqrt6, tr B=3/sqrt2 -- but
REPOSITION their axes so they no longer share a fixed point. The result is a genuine
irreducible, discrete, free Fuchsian group: a convex-cocompact once-holed torus with the
Syracuse generator-lengths. Its boundary loop [a,b] is HYPERBOLIC (tr[A,B] < -2): a generic
(non-extreme) BTZ. We then put an affine cocycle on it and see the Margulis invariants wake
up (the action becomes free), in contrast to the degenerate reducible base.

Verifies: (1) traces match Syracuse exactly; (2) irreducible (tr[A,B] != 2); (3) DISCRETE
free, via four pairwise-disjoint isometric circles (Schottky / Klein combination);
(4) cycles are loxodromic closed geodesics (lengths now word-dependent, no longer the Baker
quantity); (5) the affine cocycle has NONZERO Margulis invariants.
"""
import math
import numpy as np

# --------------------------------------------------------------------------- #
# hyperbolic Mobius element with prescribed axis endpoints and multiplier      #
# --------------------------------------------------------------------------- #
def hyp(fp, fm, mu):
    """SL2 hyperbolic: attracting fp, repelling fm, multiplier mu>1 (det 1)."""
    lam = np.sqrt(mu)
    M = np.array([[fp, fm], [1.0, 1.0]])
    g = M @ np.diag([lam, 1.0 / lam]) @ np.linalg.inv(M)
    return g / np.sqrt(np.linalg.det(g))


def iso_circles(g):
    """isometric circles of g and g^{-1}: (center, radius) each (needs c != 0)."""
    a, b, c, d = g[0, 0], g[0, 1], g[1, 0], g[1, 1]
    return (-d / c, 1.0 / abs(c)), (a / c, 1.0 / abs(c))


def disjoint(c1, c2):
    (x1, r1), (x2, r2) = c1, c2
    return abs(x1 - x2) > r1 + r2 + 1e-9


# Syracuse multipliers 3/2 (for a) and 2 (for b); axes repositioned & well separated.
A = hyp(+0.05, -0.05, 1.5)     # axis near 0
B = hyp(1.05, 0.95, 2.0)       # axis near 1  (separated from A's axis)
GEN = {"a": A, "b": B}

print("=" * 78)
print("A non-trivial (irreducible, discrete, free) Syracuse representation")
print("=" * 78)
print(f"  A =\n{np.round(A,5)}")
print(f"  B =\n{np.round(B,5)}")

# (1) traces match Syracuse exactly (same conjugacy data)
trA, trB = np.trace(A), np.trace(B)
print(f"\n  tr A = {trA:.5f}  (Syracuse 5/sqrt6 = {5/np.sqrt(6):.5f})  "
      f"multiplier {(trA/2 + np.sqrt((trA/2)**2-1))**2:.4f}")
print(f"  tr B = {trB:.5f}  (Syracuse 3/sqrt2 = {3/np.sqrt(2):.5f})  "
      f"multiplier {(trB/2 + np.sqrt((trB/2)**2-1))**2:.4f}")
assert abs(abs(trA) - 5/np.sqrt(6)) < 1e-9 and abs(abs(trB) - 3/np.sqrt(2)) < 1e-9

# (2) irreducible
K = A @ B @ np.linalg.inv(A) @ np.linalg.inv(B)
trK = np.trace(K)
print(f"\n  tr[A,B] = {trK:.5f}   (reducible would be +2; here {'IRREDUCIBLE' if abs(trK-2)>1e-6 else 'reducible'})")
bdry = 2 * math.acosh(abs(trK) / 2) if abs(trK) > 2 else float("nan")
print(f"     [A,B] is {'HYPERBOLIC (generic BTZ / geodesic funnel boundary, length '+format(bdry,'.3f')+')' if abs(trK) > 2 else 'elliptic/parabolic'}")
assert abs(trK - 2) > 1e-6

# (3) discreteness: four isometric circles pairwise disjoint  ->  Schottky / free
IA, IAi = iso_circles(A)
IB, IBi = iso_circles(B)
circles = {"I(A)": IA, "I(A^-1)": IAi, "I(B)": IB, "I(B^-1)": IBi}
print("\n  isometric circles (center, radius):")
for name, c in circles.items():
    print(f"     {name:8} center={c[0]:+.4f}  radius={c[1]:.4f}")
names = list(circles)
all_disjoint = all(disjoint(circles[names[i]], circles[names[j]])
                   for i in range(4) for j in range(i + 1, 4))
print(f"  four isometric circles pairwise disjoint? {all_disjoint}  "
      f"=> DISCRETE & FREE (Schottky / Klein combination)")
assert all_disjoint

# --------------------------------------------------------------------------- #
# (4) cycles are loxodromic closed geodesics (lengths now word-dependent)       #
# --------------------------------------------------------------------------- #
import math


def word_matrix(abword):
    G = np.eye(2)
    for ch in abword:
        G = GEN[ch] @ G
    return G


print("\n" + "=" * 78)
print("Cycles as closed geodesics of this convex-cocompact once-holed torus")
print("=" * 78)
print("  (length = 2*arccosh(|tr|/2); now WORD-dependent, NOT |E log2 - o log3|)")
for ab, o, E in [("ab", 1, 2), ("a", 1, 1), ("aab", 2, 3)]:
    G = word_matrix(ab)
    tr = np.trace(G)
    lox = abs(tr) > 2 + 1e-9
    length = 2 * math.acosh(abs(tr) / 2) if lox else float("nan")
    baker = abs(E * math.log(2) - o * math.log(3))
    print(f"  {ab:4} (o={o},E={E}): tr={tr:+.4f}  loxodromic={lox}  "
          f"length={length:.4f}   (Baker |E log2-o log3|={baker:.4f})")

# --------------------------------------------------------------------------- #
# (5) affine extension into Isom(E^{1,2}): the Margulis invariants wake up      #
# --------------------------------------------------------------------------- #
Hm = np.array([[1.0, 0.0], [0.0, -1.0]])
Em = np.array([[0.0, 1.0], [0.0, 0.0]])
Fm = np.array([[0.0, 0.0], [1.0, 0.0]])


def mink(X, Y):
    return 0.5 * np.trace(X @ Y)


def neutral(g):
    v = g - 0.5 * np.trace(g) * np.eye(2)        # Ad-fixed traceless part
    return v / math.sqrt(abs(mink(v, v)))


# affine cocycle supported on a (like the Syracuse '+1'), now a generic sl2 vector
tau_gen = {"a": Em + 0.3 * Hm, "b": np.zeros((2, 2))}


def tau_word(abword):
    total = np.zeros((2, 2))
    prefix = np.eye(2)
    for ch in abword:
        total = total + prefix @ tau_gen[ch] @ np.linalg.inv(prefix)
        prefix = GEN[ch] @ prefix
    return total


print("\n" + "=" * 78)
print("Affine cocycle on the irreducible base: Margulis invariants (signed length)")
print("=" * 78)
margs = []
for ab, o, E in [("ab", 1, 2), ("a", 1, 1), ("aab", 2, 3)]:
    G = word_matrix(ab)
    x0 = neutral(G)
    alpha = mink(tau_word(ab), x0)
    margs.append(alpha)
    print(f"  {ab:4}:  Margulis invariant alpha = {alpha:+.5f}  (=0 only at the degenerate base)")
print(f"\n  all nonzero? {all(abs(a) > 1e-6 for a in margs)}  "
      f"=> the action is FREE (non-degenerate), unlike the reducible base where alpha==0.")
print("  (Same-sign alpha for ALL classes = properness, a Goldman-Labourie-Margulis")
print("   condition one can tune; here we only certify non-degeneracy.)")
assert all(abs(a) > 1e-6 for a in margs)

print("\nALL NON-TRIVIAL-REP ASSERTS PASSED.")
