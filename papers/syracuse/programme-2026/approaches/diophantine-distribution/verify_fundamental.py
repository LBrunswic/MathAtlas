"""Numerical checks for the claims in fundamental.md.

Conventions (project-wide): gap word w = (d_0,...,d_{o-1}), d_k >= 1.
e_k = d_0+...+d_{k-1} (e_0=0), E = e_o = sum d_k = |w|, o = len(w).
D(w) = 2^E - 3^o,  S(w) = sum_{k=0}^{o-1} 2^{e_k} 3^{o-1-k}.
Accelerated (odd-to-odd) Syracuse step with gap d: x -> (3x+1)/2^d.
"""
from fractions import Fraction
import itertools, math, random

def chars(w):
    o = len(w); E = sum(w); e = 0
    S = 0
    for k in range(o):
        S += (2**e) * (3**(o-1-k))
        e += w[k]
    D = 2**E - 3**o
    return S, D, E, o

def Fw(x, w):
    """apply the word-map exactly over Q (Fraction)."""
    for d in w:
        x = Fraction(3*x + 1, 2**d)
    return x

# ---- Claim FS1: affine map F_w(x) = (3^o/2^E) x + S/2^E, fixed point S/D ----
def check_affine(w):
    S, D, E, o = chars(w)
    for x in [Fraction(0), Fraction(1), Fraction(-3,5), Fraction(7)]:
        lhs = Fw(x, w)
        rhs = Fraction(3**o, 2**E)*x + Fraction(S, 2**E)
        assert lhs == rhs, (w, x, lhs, rhs)
    star = Fraction(S, D)
    assert Fw(star, w) == star, (w, "fixed point", star, Fw(star,w))
    return True

# ---- Claim FS3: the set {x : accelerated word = w, a_o odd} is a single
#      residue class mod 2^{E+1}; fundamental sol x* = S/D lies in it. ----
def accel_word(x, o):
    """return (word, a_o) for the first o accelerated steps of odd x, or None
       if a non-odd / 0 shows up."""
    w = []
    for _ in range(o):
        if x % 2 == 0:
            return None
        t = 3*x + 1
        d = 0
        while t % 2 == 0:
            t //= 2; d += 1
        w.append(d); x = t
    return tuple(w), x

def check_coset(w):
    S, D, E, o = chars(w)
    M = 2**(E+1)
    # brute force residues mod M that yield word w with a_o odd
    good = []
    for r in range(M):
        if r % 2 == 0:    # a_0 must be odd
            continue
        res = accel_word(r if r % 2 == 1 else r, o)
        # use a representative that is odd & positive in this class? just test r
        aw = accel_word(r, o)
        if aw is not None and aw[0] == w and aw[1] % 2 == 1:
            good.append(r)
    # x* mod M (x* is a 2-adic integer; D is odd so invertible mod M)
    star_mod = (S * pow(D, -1, M)) % M
    assert good == [star_mod], (w, good, star_mod, "spacing", M)
    return star_mod, M

# ---- Claim FS4: S/D = eta/(beta-3), eta in [2^-p, 2^p] ----
def check_imbalance(w):
    S, D, E, o = chars(w)
    beta = 2**(Fraction(E, o))  # not rational in general; use float for beta-3
    betaf = 2.0**(E/o)
    # balanced word sum S(wbar) = sum beta^k 3^{o-1-k} = (2^E-3^o)/(beta-3) = D/(beta-3)
    Sbar = sum((betaf**k) * (3**(o-1-k)) for k in range(o))
    assert abs(Sbar - D/(betaf-3)) < 1e-6*max(1,abs(Sbar)), (w, Sbar, D/(betaf-3))
    eta = S / Sbar
    # x* = eta/(beta-3)
    assert abs(Fraction(S,D) - eta/(betaf-3)) < 1e-6*max(1,abs(S/D)), w
    # p = max_k |e_k - (E/o) k|
    e = 0; p = 0.0; e_k=[0]
    for k in range(o):
        e += w[k]; e_k.append(e)
    p = max(abs(e_k[k] - (E/o)*k) for k in range(o+1))
    assert 2**(-p) - 1e-9 <= eta <= 2**p + 1e-9, (w, eta, p, 2**(-p), 2**p)
    return eta, p

if __name__ == "__main__":
    tests = [(1,), (2,1), (1,2,2,2,2), (1,1,1,4,1,1,1), (3,1,2), (1,1,1,1,1)]
    # add random words
    random.seed(0)
    for _ in range(2000):
        o = random.randint(1,6)
        tests.append(tuple(random.randint(1,4) for _ in range(o)))
    for w in tests:
        check_affine(w)
        check_imbalance(w)
    print("FS1 (affine + fixed point) : OK on", len(tests), "words")
    print("FS4 (imbalance eta in [2^-p,2^p]) : OK on", len(tests), "words")
    # coset check only for small E (brute force 2^{E+1})
    cnt = 0
    for w in tests:
        if sum(w)+1 <= 16:
            star, M = check_coset(w); cnt += 1
    print("FS3 (coset spacing 2^{E+1}, x*=S/D in it) : OK on", cnt, "small words")
    # show the seed cycles
    for w in [(1,), (2,1)]:
        S,D,E,o = chars(w)
        print(f"  w={w}: S={S} D={D} x*=S/D={Fraction(S,D)}  (cycle start)")
