"""
punctured-torus :: mapping the degeneration locus of the Syracuse cocycle.

At the reducible base every Margulis invariant vanishes (the cocycle tau ~ S is null). Push
off the reducible base by a generic linear-part deformation L_t, KEEPING the Syracuse cocycle
(tau(a)=1/2 E, tau(b)=0). Then alpha_t(gamma)=O(t); the FIRST-ORDER Margulis invariant
    dot_alpha(gamma) = d/dt|_0 <tau_t(gamma), x0_t(gamma)>
is a concrete number per class. We tabulate it against the arithmetic (S, D, S/D, cycle?) to
see whether the wall (where dot_alpha changes sign / vanishes) carries a footprint of D|S.
"""
import math
import itertools
from fractions import Fraction as Fr
import numpy as np

# --- sl2 = E^{1,2} ----------------------------------------------------------
Hm = np.array([[1.0, 0], [0, -1.0]])
Em = np.array([[0, 1.0], [0, 0]])
Fm = np.array([[0, 0], [1.0, 0]])
Gram = np.array([[1.0, 0, 0], [0, 0, 0.5], [0, 0.5, 0]])


def to3(X):
    return np.array([X[0, 0], X[0, 1], X[1, 0]])


def Ad3(g):
    gi = np.linalg.inv(g)
    return np.array([to3(g @ b @ gi) for b in (Hm, Em, Fm)]).T


def neutral(g):
    w, V = np.linalg.eig(g)
    idx = np.argsort(np.abs(w))
    um, up = np.real(V[:, idx[0]]), np.real(V[:, idx[1]])

    def nil(u):
        p, q = u
        return np.array([[p * q, -p * p], [q * q, -p * q]])
    br = nil(um) @ nil(up) - nil(up) @ nil(um)
    x0 = to3(br)
    return x0 / math.sqrt(abs(x0 @ Gram @ x0))


# --- reducible base (diagonal 2-3 skeleton) + generic deformation ----------
L0 = {"a": np.diag([math.sqrt(1.5), math.sqrt(2 / 3)]),
      "b": np.diag([math.sqrt(0.5), math.sqrt(2.0)])}
# Syracuse cocycle: tau(a)=1/2 E (null), tau(b)=0
TAU = {"a": 0.5 * Em, "b": np.zeros((2, 2))}


def Lt(t, Ma, Mb):
    def nz(g):
        return g / math.sqrt(abs(np.linalg.det(g)))
    return {"a": nz(L0["a"] @ (np.eye(2) + t * Ma)),
            "b": nz(L0["b"] @ (np.eye(2) + t * Mb))}


def alpha_at(word, t, Ma, Mb):
    L = Lt(t, Ma, Mb)
    g = np.eye(2)
    tau = np.zeros((2, 2))
    for ch in word:
        tau = tau + g @ TAU[ch] @ np.linalg.inv(g)        # Ad(prefix) tau(letter)
        g = g @ L[ch]
    x0 = neutral(g)                                       # 3-vector (H,E,F coords)
    return to3(tau) @ Gram @ x0                            # <tau, x0>


def dot_alpha(word, Ma, Mb, h=1e-4):
    return (alpha_at(word, h, Ma, Mb) - alpha_at(word, -h, Ma, Mb)) / (2 * h)


# several generic traceless deformation directions to test robustness
DIRS = [
    (1.0 * Em + 0.6 * Fm + 0.3 * Hm, 0.4 * Em + 1.0 * Fm - 0.2 * Hm),
    (0.2 * Em - 0.9 * Fm + 0.5 * Hm, 1.1 * Em + 0.3 * Fm + 0.7 * Hm),
    (-0.7 * Em + 0.4 * Fm - 1.0 * Hm, 0.5 * Em - 0.6 * Fm + 0.2 * Hm),
    (1.0 * Hm, 1.0 * Hm),                                  # Cartan (axis-preserving) direction
]
Ma, Mb = DIRS[0]


# --- arithmetic of an (a,b)-word -------------------------------------------
def arithmetic(word):
    al, be = Fr(1), Fr(0)
    for ch in word:
        m, c = (Fr(3, 2), Fr(1, 2)) if ch == "a" else (Fr(1, 2), Fr(0))
        al, be = m * al, m * be + c
    o, E = word.count("a"), len(word)
    D = 2 ** E - 3 ** o
    S = int(be * 2 ** E)
    x0star = Fr(S, D)
    return o, E, S, D, x0star


# --- positive primitive classes (dedup by rotation) up to length L ----------
def classes(L):
    seen, out = set(), []
    for n in range(1, L + 1):
        for tup in itertools.product("ab", repeat=n):
            w = "".join(tup)
            key = min(w[i:] + w[:i] for i in range(n))
            if key in seen:
                continue
            seen.add(key)
            # skip non-primitive (proper power)
            if any(n % d == 0 and w == (w[:d] * (n // d)) for d in range(1, n) if n % d == 0):
                continue
            out.append(w)
    return out


import statistics


def corr(u, v):
    mu, mv = statistics.mean(u), statistics.mean(v)
    su = sum((a - mu) ** 2 for a in u); sv = sum((b - mv) ** 2 for b in v)
    return sum((a - mu) * (b - mv) for a, b in zip(u, v)) / math.sqrt(su * sv) if su * sv > 0 else 0.0


WORDS = classes(8)
ARI = {w: arithmetic(w) for w in WORDS}          # (o,E,S,D,S/D)

print("=" * 82)
print("First-order Margulis invariant (direction 0) vs arithmetic")
print("=" * 82)
print(f"{'word':10}{'o,E':>6}{'S':>5}{'D':>6}{'S/D':>8}{'cycle':>7}{'dot_alpha':>13}")
rows = []
for w in WORDS:
    o, E, S, D, x0 = ARI[w]
    da = dot_alpha(w, Ma, Mb)
    cyc = (D != 0 and S % D == 0)
    rows.append((w, o, E, S, D, x0, cyc, da))
    if len(w) <= 4 or cyc:
        print(f"{w:10}{f'{o},{E}':>6}{S:>5}{D:>6}{str(x0):>8}{('YES' if cyc else ''):>7}{da:>13.5f}")

print("\n" + "=" * 82)
print("Robustness across deformation directions: corr(dot_alpha, *)")
print("=" * 82)
print(f"  {'dir':>4} {'corr S/D':>10} {'corr S':>10} {'corr 1/D':>10} {'corr E':>9} {'all>0?':>8}")
for k, (Mak, Mbk) in enumerate(DIRS):
    da = [dot_alpha(w, Mak, Mbk) for w in WORDS]
    sd = [float(ARI[w][4]) for w in WORDS]
    Sv = [ARI[w][2] for w in WORDS]
    iD = [1.0 / ARI[w][3] for w in WORDS]
    Ev = [ARI[w][1] for w in WORDS]
    pos = all(x > -1e-9 for w, x in zip(WORDS, da) if w != "b")
    print(f"  {k:>4} {corr(sd,da):>+10.4f} {corr(Sv,da):>+10.4f} {corr(iD,da):>+10.4f} "
          f"{corr(Ev,da):>+9.4f} {str(pos):>8}")

print("\n  cycles' dot_alpha (dir 0):", {r[0]: round(r[7], 3) for r in rows if r[6]})
print("  any class with dot_alpha==0 (dir 0)?", [r[0] for r in rows if abs(r[7]) < 1e-6])


def spearman(u, v):
    def ranks(z):
        order = sorted(range(len(z)), key=lambda i: z[i])
        r = [0] * len(z)
        for rank, i in enumerate(order):
            r[i] = rank
        return r
    return corr(ranks(u), ranks(v))


print("\n" + "=" * 82)
print("Is the S/D footprint clean or outlier-driven? (direction 0)")
print("=" * 82)
da0 = [dot_alpha(w, *DIRS[0]) for w in WORDS]
sd0 = [float(ARI[w][4]) for w in WORDS]
beta0 = [ARI[w][2] / 2 ** ARI[w][1] for w in WORDS]       # beta = S/2^E (cocycle value)
absd = [abs(x) for x in sd0]
print(f"  Pearson  corr(dot,S/D)={corr(sd0,da0):+.4f}  corr(dot,|S/D|)={corr(absd,da0):+.4f}  "
      f"corr(dot,beta=S/2^E)={corr(beta0,da0):+.4f}")
print(f"  Spearman corr(dot,S/D)={spearman(sd0,da0):+.4f}  corr(dot,|S/D|)={spearman(absd,da0):+.4f}  "
      f"corr(dot,beta)={spearman(beta0,da0):+.4f}")
top = sorted(WORDS, key=lambda w: -abs(dot_alpha(w, *DIRS[0])))[:8]
print("  largest |dot_alpha| classes:  word (o,E)  S  D  S/D  dot_alpha")
for w in top:
    o, E, S, D, x0 = ARI[w]
    print(f"     {w:9} ({o},{E})  S={S:<4} D={D:<5} S/D={str(x0):>8}  dot={dot_alpha(w,*DIRS[0]):+.4f}")
