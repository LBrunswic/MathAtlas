"""Leverage check: Filaseta-Schinzel 2004 vs the >=2-growing-gap NO-GO.

Filaseta & Schinzel, "On testing the divisibility of lacunary polynomials by
cyclotomic polynomials," Math. Comp. 73 (2004) 957-965.
  Cor. 1: if f in Z[x] has N nonzero terms and is divisible by SOME cyclotomic,
          then there is m with  gamma(m) := 2 + sum_{p|m}(p-2) <= N  and  Phi_m | f;
          moreover every prime p|m is <= N, and for p^e||m, e <= floor(log deg f/log p)+1.

This script tests, on OUR object (the cocycle reduced unit-combination polynomials
for the symmetric family W_a = d^a e1 d^a e2 d^a), exactly WHERE FS does and does
not bite.  Every assertion below is a VERIFIED fact; the headline conclusion is the
HONEST one: FS does NOT control the no-go ceiling, because that ceiling is carried by
a single irreducible NON-HOMOGENEOUS bivariate factor of growing degree -- not by a
cyclotomic factor FS can constrain.

What is verified (defects d=1, e1=3, e2=4 and a cross-check d=1,e1=2,e2=3; a=2..8):

  T1  The reduced adjacent-difference P_a(X,Y) factors as (linear unit Y-X = Phi_1^h,
      value 1 at (2,3)) times ONE irreducible bivariate factor Q_a whose total degree
      AND term count BOTH GROW, and whose value at (2,3) carries the ENTIRE 6-free
      ceiling.  So sixfree(P_a(2,3)) = sixfree(Q_a(2,3)) grows.
  T2  WRONG OBJECT: the Y=1 slice P_a(x,1) is sparse (N=6 terms, constant) but its
      cyclotomic factors are SPURIOUS for the (2,3) ceiling -- at a=3 the slice has a
      Phi_2 = x+1 factor that is NOT a bivariate factor and contributes no factor 5 to
      the ceiling (which is 23).  FS applied to the slice therefore says nothing about
      sixfree(P_a(2,3)).
  T3  FS Cor.1 radical bound, in our notation, HOLDS on the slice (it must -- it is a
      theorem): every cyclotomic factor index m of P_a(x,1) satisfies gamma(m) <= N and
      every prime p|m is <= N.  But the indices that occur ({1,2,3}) are exactly the
      small ones FS PERMITS, so FS forbids nothing.
  T4  CORRECT GATE = homogeneous Zsygmondy: among homogeneous cyclotomics Phi_n^h(2,3)
      = 3^{phi(n)} Phi_n(2/3) (the primitive parts of 3^n - 2^n), the only 6-smooth one
      is n=1 (Phi_1^h(2,3) = 2-3 = -1).  Phi_2^h=5, Phi_3^h=19, Phi_4^h=13, Phi_6^h=7,
      ... each carries a primitive prime > 3.  So the true sixfree-collapse target at
      (2,3) is {1}, NOT the univariate-at-2 set {1,2,6}.  Since P_a is non-homogeneous
      it has no Phi_n^h factor beyond the linear unit -- the ceiling is non-cyclotomic.
  T5  FS-friendliest regime still grows: the SPARSEST 2-term combos (S^(0)-S^(1)) have
      a FIXED 5-term bivariate shape of GROWING degree, yet their 6-free value at (2,3)
      GROWS (305,691,1625,3979,10145,26851,...).  Lacunarity does not buy collapse.

Run from repo root:  python3 ideas/cocycle-combinatorics/checks/lit_filaseta_schinzel.py
"""
import sys
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, rotate, gcd_rotations  # trusted kernel
X, Y = sp.symbols("X Y")


# --------------------------------------------------------------------------- #
# helpers                                                                     #
# --------------------------------------------------------------------------- #
def sym_word(a, d=1, e1=3, e2=4):
    """The symmetric >=2-growing-gap family d^a e1 d^a e2 d^a."""
    return (d,) * a + (e1,) + (d,) * a + (e2,) + (d,) * a


def sixfree(n):
    n = abs(int(n))
    if n == 0:
        return 0
    for p in (2, 3):
        while n % p == 0:
            n //= p
    return n


def strip_monomial(poly):
    """Reduced polynomial: divide out the overall X^p Y^q monomial prefactor."""
    poly = sp.expand(poly)
    if poly == 0:
        return poly
    p = sp.Poly(poly, X, Y)
    pm = min(m[0] for m in p.monoms())
    qm = min(m[1] for m in p.monoms())
    return sp.expand(poly / (X ** pm * Y ** qm))


def nterms_bivar(poly):
    poly = sp.expand(poly)
    return 0 if poly == 0 else len(sp.Poly(poly, X, Y).monoms())


def nterms_univ(poly):
    f = sp.expand(sp.expand(poly).subs(Y, 1))
    return 0 if f == 0 else len(sp.Poly(f, X).monoms())


def gamma(m):
    """FS index weight gamma(m) = 2 + sum_{p|m}(p-2)."""
    return 2 + sum(p - 2 for p in sp.primefactors(m))


def cyclotomic_index(univ_factor):
    """If `univ_factor` (in X) is +- a cyclotomic polynomial, return its index n; else None."""
    fp = sp.Poly(sp.expand(univ_factor), X)
    dg = fp.degree()
    if dg < 1:
        return None
    for n in range(1, 4000):
        if sp.totient(n) != dg:
            continue
        ph = sp.cyclotomic_poly(n, X)
        if sp.expand(univ_factor - ph) == 0 or sp.expand(univ_factor + ph) == 0:
            return n
    return None


def homogenize(univ_factor):
    """Y^{deg} f(X/Y): the homogeneous companion, evaluated cleanly at (2,3)."""
    dg = sp.Poly(univ_factor, X).degree()
    return sp.expand(Y ** dg * univ_factor.subs(X, X / Y))


ALL_OK = True
DEFECTS = [(1, 3, 4), (1, 2, 3)]   # (d, e1, e2): primary + cross-check
RANGE = range(2, 9)                # a = 2..8


# --------------------------------------------------------------------------- #
# T1  -- the (2,3) ceiling is carried by ONE growing irreducible bivariate     #
#         factor; the unit factor Y-X contributes 1                            #
# --------------------------------------------------------------------------- #
print("== T1: reduced P_a = (unit Y-X) * (irreducible Q_a of GROWING deg & #terms); "
      "sixfree(P_a(2,3))=sixfree(Q_a(2,3)) grows ==")
t1 = True
for (d, e1, e2) in DEFECTS:
    degs, nts, sfs = [], [], []
    for a in RANGE:
        W = sym_word(a, d, e1, e2)
        red = strip_monomial(sp.expand(Spoly(rotate(W, 0)) - Spoly(rotate(W, a + 1))))
        facs = sp.factor_list(red)[1]
        # exactly one linear unit factor with value +-1 at (2,3); one big factor
        units = [f for f, mlt in facs if abs(int(f.subs({X: 2, Y: 3}))) == 1]
        big = max(facs, key=lambda fm: sp.Poly(fm[0], X, Y).total_degree())[0]
        ceil = sixfree(int(red.subs({X: 2, Y: 3})))
        ceil_big = sixfree(int(big.subs({X: 2, Y: 3})))
        if not units or ceil != ceil_big:
            t1 = False
        degs.append(sp.Poly(big, X, Y).total_degree())
        nts.append(nterms_bivar(big))
        sfs.append(ceil)
    grows = all(degs[i] < degs[i + 1] for i in range(len(degs) - 1)) and \
            all(nts[i] < nts[i + 1] for i in range(len(nts) - 1)) and \
            sfs[-1] > sfs[0]
    t1 = t1 and grows
    print(f"  d,e1,e2={d,e1,e2}: deg(Q_a)={degs}  #terms(Q_a)={nts}")
    print(f"                   sixfree ceiling={sfs}  (deg, #terms, ceiling all grow: {grows})")
print(f"  T1 holds: {t1}\n")
ALL_OK &= t1


# --------------------------------------------------------------------------- #
# T2  -- the Y=1 slice is the WRONG object: sparse, but its cyclotomic factors  #
#         are SPURIOUS for the (2,3) ceiling                                    #
# --------------------------------------------------------------------------- #
print("== T2: Y=1 slice sparse (N=6) but its cyclotomic factors are SPURIOUS for the ceiling ==")
t2 = True
# (a) slice term count is a small CONSTANT while bivariate degree grows
slice_N = []
for a in RANGE:
    W = sym_word(a, 1, 3, 4)
    red = strip_monomial(sp.expand(Spoly(rotate(W, 0)) - Spoly(rotate(W, a + 1))))
    slice_N.append(nterms_univ(red))
if len(set(slice_N)) != 1:
    t2 = False
print(f"  slice term count N(P_a(x,1)) over a=2..8: {slice_N}  (constant: {len(set(slice_N))==1})")
# (b) at a=3 the slice has a Phi_2=x+1 factor that is NOT a bivariate factor,
#     and the ceiling 23 has no factor 5 (=Phi_2^h(2,3)) -> the slice Phi_2 is spurious
a = 3
W = sym_word(a, 1, 3, 4)
red = strip_monomial(sp.expand(Spoly(rotate(W, 0)) - Spoly(rotate(W, a + 1))))
slice_idx = sorted(set(i for f, m in sp.factor_list(sp.expand(red.subs(Y, 1)))[1]
                       for i in [cyclotomic_index(f)] if i is not None))
bivar_idx = sorted(set(i for f, m in sp.factor_list(red)[1]
                       for i in [cyclotomic_index(f.subs(Y, 1))] if i is not None))
ceil3 = sixfree(int(red.subs({X: 2, Y: 3})))
spurious = (2 in slice_idx) and (2 not in bivar_idx) and (ceil3 % 5 != 0)
t2 = t2 and spurious
print(f"  a=3 slice cyclotomic indices={slice_idx}, bivariate cyclotomic indices={bivar_idx}")
print(f"  a=3 ceiling={ceil3} (not divisible by 5=Phi_2^h(2,3)) -> slice Phi_2 is SPURIOUS: {spurious}")
print(f"  T2 holds: {t2}\n")
ALL_OK &= t2


# --------------------------------------------------------------------------- #
# T3  -- FS Corollary 1 radical bound HOLDS on the slice (consistency), but     #
#         only permits the small indices -> forbids nothing                     #
# --------------------------------------------------------------------------- #
print("== T3: FS Cor.1 in our notation -- cyclotomic factor index m of P_a(x,1) has "
      "gamma(m)<=N and primes(m)<=N ==")
t3 = True
for a in RANGE:
    W = sym_word(a, 1, 3, 4)
    red = strip_monomial(sp.expand(Spoly(rotate(W, 0)) - Spoly(rotate(W, a + 1))))
    f = sp.expand(red.subs(Y, 1))
    N = nterms_univ(red)
    degf = sp.Poly(f, X).degree()
    idxs = [i for fac, m in sp.factor_list(f)[1] for i in [cyclotomic_index(fac)] if i is not None]
    for m in idxs:
        ok = gamma(m) <= N and all(p <= N for p in sp.primefactors(m))
        # exponent bound e <= floor(log degf/log p)+1
        for p in sp.primefactors(m):
            e = sp.multiplicity(p, m)
            ok = ok and e <= (sp.floor(sp.log(degf) / sp.log(p)) + 1)
        if not ok:
            t3 = False
    print(f"  a={a}: N={N}, cyclotomic indices={sorted(set(idxs))}, "
          f"gamma={[gamma(m) for m in sorted(set(idxs))]} (all <= N: {all(gamma(m)<=N for m in idxs)})")
print(f"  FS bound holds throughout (it is a theorem); indices are the SMALL ones FS permits.")
print(f"  T3 holds: {t3}\n")
ALL_OK &= t3


# --------------------------------------------------------------------------- #
# T4  -- the CORRECT collapse gate is homogeneous: Phi_n^h(2,3) 6-smooth iff n=1 #
# --------------------------------------------------------------------------- #
print("== T4: homogeneous gate -- Phi_n^h(2,3) (primitive parts of 3^n-2^n) is 6-smooth "
      "ONLY for n=1 ==")
t4 = True
row = []
for n in range(1, 31):
    val = int(homogenize(sp.cyclotomic_poly(n, X)).subs({X: 2, Y: 3}))
    sf = sixfree(val)
    row.append((n, sf))
    smooth = (sf == 1)
    if (n == 1) != smooth:
        t4 = False
print(f"  (n, sixfree Phi_n^h(2,3)) for n=1..10: {row[:10]}")
print(f"  6-smooth (sixfree==1) holds iff n==1 over n=1..30: {t4}")
print(f"  => true (2,3)-collapse target is {{1}}, NOT the univariate-at-2 set {{1,2,6}}.")
print(f"  T4 holds: {t4}\n")
ALL_OK &= t4


# --------------------------------------------------------------------------- #
# T5  -- FS-friendliest regime: the SPARSEST combo (S^(0)-S^(1)) is a fixed     #
#         5-term shape of growing degree, yet its 6-free value GROWS            #
# --------------------------------------------------------------------------- #
print("== T5: sparsest 2-term combo S^(0)-S^(1): fixed 5-term shape, GROWING degree, "
      "GROWING sixfree ==")
t5 = True
nts5, degs5, sfs5 = [], [], []
for a in RANGE:
    W = sym_word(a, 1, 3, 4)
    red = strip_monomial(sp.expand(Spoly(rotate(W, 0)) - Spoly(rotate(W, 1))))
    big = max(sp.factor_list(red)[1], key=lambda fm: sp.Poly(fm[0], X, Y).total_degree())[0]
    nts5.append(nterms_bivar(big))
    degs5.append(sp.Poly(big, X, Y).total_degree())
    sfs5.append(sixfree(int(red.subs({X: 2, Y: 3}))))
fixed_shape = len(set(nts5)) == 1
deg_grows = all(degs5[i] < degs5[i + 1] for i in range(len(degs5) - 1))
sf_grows = all(sfs5[i] < sfs5[i + 1] for i in range(len(sfs5) - 1))
t5 = fixed_shape and deg_grows and sf_grows
print(f"  #terms(big factor)={nts5} (fixed: {fixed_shape})")
print(f"  deg(big factor)={degs5} (grows: {deg_grows})")
print(f"  sixfree(combo(2,3))={sfs5} (grows: {sf_grows})")
print(f"  => lacunarity does NOT buy cyclotomic collapse; growth is non-cyclotomic.")
print(f"  T5 holds: {t5}\n")
ALL_OK &= t5


# --------------------------------------------------------------------------- #
print("=" * 72)
print(f"FILASETA-SCHINZEL leverage check: {'ALL VERIFIED FACTS PASS' if ALL_OK else 'FAILED'}")
print("VERDICT: FS does NOT control the no-go ceiling.  The ceiling is carried by a")
print("         single irreducible NON-HOMOGENEOUS bivariate factor of growing degree;")
print("         the only sparse univariate shadow (Y=1 slice) is the WRONG object and")
print("         FS merely PERMITS its small cyclotomic factors.  The correct collapse")
print("         gate is homogeneous (Zsygmondy on 3^n-2^n): only n=1 is 6-smooth, so the")
print("         no-go reduces to an S-unit/primitive-divisor value problem, not a")
print("         cyclotomic-divisibility test FS can answer.")
sys.exit(0 if ALL_OK else 1)
