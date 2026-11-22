"""Gen 8 (2026-06-08) -- EXPLORATION for the validity-gap bridge.

THE ONE QUESTION: can the reversal sum S(W^R) -- equivalently the clean reversal
core S(W)-S(W^R) -- be expressed within the rotation lattice/module of W,
    L := span_{Z[1/6]} { S^{(j)}(W) : 0 <= j < o } ?
If S(W^R) is a *valid* combination of rotation sums (scalar or unit/monomial
coefficients), then G | core and the Zsygmondy divergence of the core is G-relevant.

EXPLORATORY (prints structure).  Probes:
  (Q0) reconcile the reversal core for W=C(a,2a)=e1 d^a e2 d^{2a}.
  (Q1) congruence mod D: are all rotation sums mutually == mod D(W)?  is S(W^R)?
  (Q2) pure SCALAR Q-linear: is S(W^R) in Q-span of {S^{(j)}}?  (strictest lattice)
  (Q3) unit/monomial combination: is S(W^R) in Q-span of { X^p Y^q S^{(j)} } over a
       bounded monomial box?  (the program's "valid rotation combination" notion)

Linear-algebra membership is done by modular rank over a large prime (fast; this is a
search -- any clean uniform relation found is certified symbolically in the cert script).

Run:  python3 ideas/cocycle-combinatorics/checks/reversal_lattice_explore.py
"""
import sys
import sympy as sp

sys.path.insert(0, "approaches/cocycle-combine/lib")
from cocycle import S as Spoly, D as Dpoly, rotations  # trusted kernel
X, Y = sp.symbols("X Y")

d = 1
P = 2_000_003  # large prime for modular rank


def cyc_word(e1, e2, a):
    return (e1,) + (d,) * a + (e2,) + (d,) * (2 * a)


def sixfree(n):
    n = abs(int(n))
    if n == 0:
        return 0
    for p in (2, 3):
        while n % p == 0:
            n //= p
    return n


def covec(poly):
    """coefficient dict {(i,j): int} of a Z[X,Y] polynomial."""
    pol = sp.Poly(sp.expand(poly), X, Y)
    return {m: int(c) for m, c in zip(pol.monoms(), pol.coeffs())}


def mod_rank(vectors, monos):
    """rank over GF(P) of the matrix whose rows are coeff-vectors (dicts) over `monos`."""
    idx = {m: k for k, m in enumerate(monos)}
    rows = []
    for v in vectors:
        row = [0] * len(monos)
        for m, c in v.items():
            row[idx[m]] = c % P
        rows.append(row)
    # Gaussian elimination mod P
    r = 0
    ncol = len(monos)
    for col in range(ncol):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][col] % P != 0:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][col], P - 2, P)
        rows[r] = [(x * inv) % P for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] % P != 0:
                f = rows[i][col]
                rows[i] = [(a - f * b) % P for a, b in zip(rows[i], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


def in_span(atoms, target):
    """is target (poly) in the Q-span of atoms (polys)?  via modular rank."""
    vt = covec(target)
    avs = [covec(a) for a in atoms]
    monos = sorted({m for v in avs + [vt] for m in v})
    rank_A = mod_rank(avs, monos)
    rank_Ab = mod_rank(avs + [vt], monos)
    return rank_A == rank_Ab


pr = lambda *a: print(*a, flush=True)

pr("============ Q0: reconcile the reversal core on the CYCLIC word ============")
for a in (2, 3):
    e1, e2 = 3, 4
    W = cyc_word(e1, e2, a)
    WR = tuple(reversed(W))
    core = sp.expand(Spoly(W) - Spoly(WR))
    pr(f"  a={a}: W={W}  W^R={WR}")
    pr(f"        S(W)-S(W^R) = {sp.factor(core)}")
    pr(f"        sixfree(core@(2,3)) = {sixfree(core.subs({X: 2, Y: 3}))}")
pr("")

pr("============ Q1: congruence mod D(W) ============")
for a in (2, 3, 4):
    e1, e2 = 3, 4
    W = cyc_word(e1, e2, a)
    WR = tuple(reversed(W))
    DW = sp.Poly(Dpoly(W), X)
    Ss = [sp.expand(Spoly(r)) for r in rotations(W)]
    res = [sp.div(sp.Poly(sp.expand(s - Ss[0]), X), DW)[1].as_expr() for s in Ss]
    all_cong = all(r == 0 for r in res)
    rev_cong = sp.div(sp.Poly(sp.expand(Spoly(WR) - Ss[0]), X), DW)[1].as_expr()
    pr(f"  a={a}: all rotations mutually == mod D : {all_cong}")
    pr(f"         S(W^R) - S^(0) == 0 mod D : {rev_cong == 0}")
pr("")

pr("============ Q2: pure SCALAR Q-linear membership (strict lattice) ============")
for a in (2, 3, 4, 5):
    e1, e2 = 3, 4
    W = cyc_word(e1, e2, a)
    WR = tuple(reversed(W))
    Ss = [sp.expand(Spoly(r)) for r in rotations(W)]
    pr(f"  a={a}: S(W^R) in Q-span of rotation sums (scalar coeffs): {in_span(Ss, sp.expand(Spoly(WR)))}")
pr("")

pr("============ Q3: unit/monomial combination over bounded box ============")
for a in (2, 3):
    e1, e2 = 3, 4
    W = cyc_word(e1, e2, a)
    WR = tuple(reversed(W))
    Ss = [sp.expand(Spoly(r)) for r in rotations(W)]
    target = sp.expand(Spoly(WR))
    E = sum(W); o = len(W)
    found = False
    for (pmax, qmax) in [(2, 1), (4, 2), (6, 3), (E, o), (E + o, o + 4)]:
        atoms = [sp.expand(X ** p * Y ** q * s)
                 for s in Ss for p in range(pmax + 1) for q in range(qmax + 1)]
        ok = in_span(atoms, target)
        pr(f"  a={a} box(pmax={pmax},qmax={qmax},#atoms={len(atoms)}): representable: {ok}")
        if ok:
            found = True
            break
    pr(f"  --> a={a}: monomial-combination bridge found: {found}")
pr("")
pr("done.")
