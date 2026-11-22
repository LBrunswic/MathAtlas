"""Generate the Section-2 table for the `polynomial-root` approach.

Construction (the abstract Fox-derivative cocycle; see report.tex Section 1):

    F2 = <u,v>,   chi : F2 -> Lambda = Z[X^,Y^],  chi(u)=X, chi(v)=Y
    S  = chi o d_u    (d_u = Fox derivative w.r.t. u)

For a positive word w = x_1...x_E over {u,v},

    S(w) = sum_{k : x_k = u} X^{a_k} Y^{b_k},
           a_k = #{i<k : x_i=u},  b_k = #{i<k : x_i=v}.

Type:  E = |w|,  o = e_u(w);  chi(w) = X^o Y^{E-o};  d = gcd(E,o).

Reparametrisation.  Put (o, E-o) = d*(o', m') with (o',m') primitive, and pick
(a,b) with o'b - m'a = 1 (extended Euclid).  Then

    s = X^{o'} Y^{m'}   (so s^d = chi(w)),    t = X^a Y^b,
    X = s^b t^{-m'},     Y = s^{-a} t^{o'},

is a unimodular change of monomial basis, and

    Lambda / (1 - chi(w))  =  Z[t,t^{-1}, s] / (s^d - 1)  =:  R_d.

This script computes, for one cyclic-class representative per necklace with
E + o <= 6, the data of the two report tables, and certifies S against the
cocycle law  S(ab) = S(a) + chi(a) S(b)  (an independent oracle for chi o d_u).

Relation to cocycle-combine: lib/cocycle.py:S is the SAME functional in the
gap-word encoding with the opposite role assignment (its X<->our Y, its Y<->our
X, plus a word reversal).  We keep our own letter-word kernel here and certify
it intrinsically by the cocycle law rather than reconcile the two conventions.
"""

from __future__ import annotations

from math import gcd, lcm
from itertools import combinations, product
import csv
import os
import sympy as sp

try:
    import numpy as _np
except Exception:                      # pragma: no cover
    _np = None

X, Y, s, t = sp.symbols("X Y s t")


# --------------------------------------------------------------------------- #
# The cocycle S = chi o d_u on positive letter words                          #
# --------------------------------------------------------------------------- #
def chi(w):
    """chi(w) = X^{e_u} Y^{e_v}."""
    return X ** w.count("u") * Y ** w.count("v")


def S(w):
    """S(w) = sum_{k: x_k=u} X^{#u before k} Y^{#v before k}, in Z[X,Y]."""
    expr, au, av = sp.Integer(0), 0, 0
    for ch in w:
        if ch == "u":
            expr += X ** au * Y ** av
            au += 1
        else:
            av += 1
    return sp.expand(expr)


def cocycle_residual(a, b):
    """S(ab) - [S(a) + chi(a) S(b)]; must be 0 for every split (the Fox law)."""
    return sp.expand(S(a + b) - (S(a) + chi(a) * S(b)))


# --------------------------------------------------------------------------- #
# Reparametrisation to R_d = Z[t,t^{-1},s]/(s^d - 1)                           #
# --------------------------------------------------------------------------- #
def egcd(a, b):
    """(g, x, y) with a*x + b*y = g."""
    if b == 0:
        return (a, 1, 0)
    g, x1, y1 = egcd(b, a % b)
    return (g, y1, x1 - (a // b) * y1)


def reparam_params(E, o):
    d = gcd(E, o)
    op, mp = o // d, (E - o) // d           # (o', m'), primitive
    g, x, y = egcd(op, mp)                   # op*x + mp*y = 1
    assert g == 1
    a, b = -y, x                             # det [[op,mp],[a,b]] = op*b - mp*a = 1
    # (a,b) is unique only mod (op,mp); normalise t = X^a Y^b to the user's
    # "t = Y X^* Y^*" shape, i.e. smallest positive Y-exponent b.
    if mp == 0:
        a = 0                                # op = 1, b = 1 already => t = Y
    else:
        b_target = ((b - 1) % mp) + 1        # b in {1,...,mp}
        j = (b_target - b) // mp
        a, b = a + j * op, b + j * mp
    assert op * b - mp * a == 1 and b >= 1
    return d, op, mp, a, b


def reduce_mod_sd(expr, d):
    """Reduce a Laurent expr in (s,t) modulo s^d - 1 (collapse s-exponents mod d)."""
    expr = sp.expand(expr)
    if expr == 0:
        return sp.Integer(0)
    out = sp.Integer(0)
    for term in expr.as_ordered_terms():
        pd = term.as_powers_dict()
        se, te = int(pd.get(s, 0)), int(pd.get(t, 0))
        coeff = sp.simplify(term / (s ** se * t ** te))
        out += coeff * s ** (se % d) * t ** te
    return sp.expand(out)


def reparametrise(w, E, o):
    """Return (params, S in (t,s) reduced mod s^d-1)."""
    d, op, mp, a, b = reparam_params(E, o)
    Xst, Yst = s ** b * t ** (-mp), s ** (-a) * t ** op
    # the basis is unimodular and inverts s = X^{o'}Y^{m'}, t = X^a Y^b
    assert sp.simplify(Xst ** op * Yst ** mp - s) == 0
    assert sp.simplify(Xst ** a * Yst ** b - t) == 0
    S_ts = reduce_mod_sd(S(w).subs({X: Xst, Y: Yst}), d)
    return (d, op, mp, a, b), S_ts


# --------------------------------------------------------------------------- #
# Arithmetic: cyclotomic-monomial structure, Galois group, Mahler measure     #
# --------------------------------------------------------------------------- #
def cyclotomic_monomial(factor, nmax=8, pqmax=4):
    """If factor(X,Y) == Phi_n(X^p Y^q) for primitive (p,q)>=0, small n, return
    (n, p, q); else None.  This is the correct 'univariate shadow': the factor is
    a cyclotomic polynomial evaluated at a single primitive monomial."""
    fac = sp.expand(factor)
    for n in range(1, nmax + 1):
        for p in range(0, pqmax + 1):
            for q in range(0, pqmax + 1):
                if (p == 0 and q == 0) or gcd(p, q) != 1:
                    continue
                if sp.expand(fac - sp.cyclotomic_poly(n, X ** p * Y ** q)) == 0:
                    return (n, p, q)
    return None


def factor_structure(w):
    """(content, [(kind, data, mult)]) for the factors of S(w)."""
    Sxy = S(w)
    if Sxy == 0:
        return (sp.Integer(0), [])
    cont, facs = sp.factor_list(Sxy)
    out = []
    for f, m in facs:
        f = sp.expand(f)
        if f in (X, Y):
            out.append(("monomial", f, m))
        else:
            cm = cyclotomic_monomial(f)
            out.append(("cyclotomic", cm, m) if cm else ("other", f, m))
    return (cont, out)


def galois_mahler_roots(w):
    """Galois group of the splitting field of S(w) over Q, its Mahler measure,
    and a root description -- read off the cyclotomic-monomial factorisation."""
    _, facs = factor_structure(w)
    others = [d for (k, d, m) in facs if k == "other"]
    cyc = [d for (k, d, m) in facs if k == "cyclotomic"]      # d = (n,p,q)
    if others:
        return ("non-cyclotomic: " + str(others), None, None, "see factor")
    # roots: each Phi_n(X^p Y^q) factor => X^p Y^q is a primitive n-th root of 1
    root_desc = []
    for (n, p, q) in cyc:
        mon = (("X^%d" % p if p else "") + ("Y^%d" % q if q else "")) or "1"
        root_desc.append(f"{mon} in mu_{n}^prim")
    ns = [n for (n, p, q) in cyc if n > 2]      # Phi_1, Phi_2 give rational roots
    N = lcm(*ns) if ns else 1
    gal = "1 (trivial)" if N in (1, 2) else f"(Z/{N}Z)* ~ order {int(sp.totient(N))}"
    mahler = 1     # monomial x cyclotomic => Mahler measure exactly 1
    return (gal, mahler, N, "; ".join(root_desc) if root_desc else "none")


# --------------------------------------------------------------------------- #
# Enumeration: one representative per cyclic class, E + o <= 6                 #
# --------------------------------------------------------------------------- #
def rotations(w):
    return [w[i:] + w[:i] for i in range(len(w))]


def canonical(w):
    return min(rotations(w))


def class_reps(E, o):
    seen, reps = set(), []
    for pos in combinations(range(E), o):
        wl = ["v"] * E
        for p in pos:
            wl[p] = "u"
        c = canonical("".join(wl))
        if c not in seen:
            seen.add(c)
            reps.append(c)
    return sorted(reps)


def class_size(w):
    return len(set(rotations(w)))           # number of distinct words in the necklace


def all_reps():
    out = []
    for E in range(1, 6):
        for o in range(1, E + 1):
            if E + o <= 6:
                for w in class_reps(E, o):
                    out.append((E, o, w))
    return out


# --------------------------------------------------------------------------- #
# Coprime catalogue: gcd(E,o)=1, so d=1 and R_1 = Z[t,t^{-1}].                 #
# The closure substitution is X -> t^{-(E-o)}, Y -> t^{o}; a monomial          #
# X^a Y^b maps to t^{b o - a (E-o)}, and S(w) becomes a one-variable Laurent   #
# polynomial, cleared to P_w(t) in Z[t] (well defined up to a power of t).     #
# --------------------------------------------------------------------------- #
_PHI = {tuple(sp.Poly(sp.cyclotomic_poly(n, t), t).all_coeffs()): n
        for n in range(1, 301)}


def t_coeffs(w, E, o):
    """Ascending coefficient list of the cleared P_w(t) in Z[t] (R_1 image)."""
    exps, au, av = [], 0, 0
    for ch in w:
        if ch == "u":
            exps.append(av * o - au * (E - o))
            au += 1
        else:
            av += 1
    mn = min(exps)
    deg = max(exps) - mn
    coeffs = [0] * (deg + 1)
    for e in exps:
        coeffs[e - mn] += 1                 # index = exponent of t
    return coeffs                           # ascending; P = sum coeffs[i] t^i


def mahler(coeffs_desc):
    """Mahler measure |lead| * prod max(1,|root|), coeffs highest-degree first."""
    if len(coeffs_desc) <= 1:
        return 1.0
    lead = abs(coeffs_desc[0])
    if _np is not None:
        rts = _np.roots(coeffs_desc)
        m = float(lead)
        for r in rts:
            ar = abs(r)
            if ar > 1.0:
                m *= ar
        return m
    p = sp.Poly(coeffs_desc, t)
    m = float(lead)
    for r in p.nroots(n=20):
        ar = abs(complex(r))
        if ar > 1.0:
            m *= ar
    return m


def galois_name(fac_poly):
    """Galois group of an irreducible factor over Q, for small degree; else None."""
    d = fac_poly.degree()
    if d <= 1:
        return "1"
    if d > 6:
        return None
    fn = getattr(sp, "galois_group", None)
    if fn is None:
        try:
            from sympy.polys.numberfields.galoisgroups import galois_group as fn
        except Exception:
            return None
    try:
        G, _ = fn(fac_poly, by_name=True)
        return str(G).split(".")[-1]
    except Exception:
        try:
            G, _ = fn(fac_poly)
            return f"order {G.order()}"
        except Exception:
            return None


def analyze(w, E, o):
    """Full record for one coprime necklace."""
    coeffs = t_coeffs(w, E, o)
    deg = len(coeffs) - 1
    M = mahler(coeffs[::-1])
    expr = sp.expand(sum(c * t ** i for i, c in enumerate(coeffs)))
    _, facs = sp.factor_list(sp.Poly(expr, t)) if deg >= 1 else (1, [])
    parts, noncyc = [], []
    for f, m in facs:
        fp = sp.Poly(f, t)
        n = _PHI.get(tuple(fp.all_coeffs()))
        if n is not None:
            s = f"\\Phi_{{{n}}}"
        else:
            s = "(" + sp.sstr(fp.as_expr()) + ")"
            noncyc.append(fp)
        parts.append(s + (f"^{{{m}}}" if m > 1 else ""))
    is_cyc = abs(M - 1.0) < 1e-6
    # Littlewood core: P_w / (1+t+...+t^{o-1}) has coefficients in {-1,0,1};
    # moreover R_w(1)=1, so R_w = 1 + (t-1) Q_w with Q_w a 0/1 polynomial.
    go = sp.Poly([1] * o, t)
    R, rem = sp.div(sp.Poly(expr, t), go)
    assert rem.is_zero, (w, "1+...+t^{o-1} does not divide P_w")
    rmax = max((abs(int(c)) for c in R.all_coeffs()), default=0)
    Q, qrem = sp.div(R - sp.Poly(1, t), sp.Poly([1, -1], t))     # (R_w - 1)/(t-1)
    assert qrem.is_zero, (w, "R_w(1) != 1")
    return {
        "w": w, "E": E, "o": o, "deg": deg, "mahler": M, "cyclotomic": is_cyc,
        "poly": sp.sstr(expr), "factor": "\\,".join(parts) if parts else "1",
        "rcore": sp.sstr(R.as_expr()), "rmax": rmax, "qcore": sp.sstr(Q.as_expr()),
        "noncyc": noncyc, "ncdeg": max((p.degree() for p in noncyc), default=0),
    }


def coprime_necklaces(nmax):
    out = []
    for E in range(1, nmax):
        for o in range(1, E + 1):
            if E + o <= nmax and gcd(E, o) == 1:
                for w in class_reps(E, o):
                    out.append((E, o, w))
    return out


def build_catalogue(nmax=20):
    recs = [analyze(w, E, o) for (E, o, w) in coprime_necklaces(nmax)]
    recs.sort(key=lambda r: (r["E"] + r["o"], r["o"], r["w"]))
    return recs


def write_csv(recs, path):
    with open(path, "w", newline="") as fh:
        wr = csv.writer(fh)
        wr.writerow(["word", "E", "o", "deg_P", "mahler", "cyclotomic",
                     "noncyc_deg", "P_w(t)", "R_w(t)=P_w/(1+..+t^{o-1})",
                     "Q_w(t)=(R_w-1)/(t-1)", "factorisation"])
        for r in recs:
            wr.writerow([r["w"], r["E"], r["o"], r["deg"], f"{r['mahler']:.6f}",
                         int(r["cyclotomic"]), r["ncdeg"], r["poly"], r["rcore"],
                         r["qcore"], r["factor"].replace("\\,", " ").replace("\\", "")])


# Full table floats are generated and \input at document level: \input of bare
# rows *inside* a tabular trips a "Misplaced \noalign" before booktabs rules.
_SUMMARY_HEAD = r"""\begin{table}[h]
\centering\footnotesize
\renewcommand{\arraystretch}{1.1}
\setlength{\tabcolsep}{4.5pt}
\begin{tabular}{@{}cccccc@{\qquad}cccccc@{}}
\toprule
$(E,o)$ & cl. & cy. & nc. & min & max & $(E,o)$ & cl. & cy. & nc. & min & max\\
\midrule
"""
_SUMMARY_FOOT = r"""\bottomrule
\end{tabular}
\caption{All $64$ coprime types ($\gcd(E,o)=1$, $E+o\le20$), in two side-by-side blocks
of $32$: number of cyclic classes (cl.), how many are cyclotomic (cy.) and non-cyclotomic
(nc.), the smallest Mahler measure $>1$ in the type (min; ``--'' if none), and the largest
Mahler measure (max).}\label{tab:summary}
\end{table}
"""

_HIGHLIGHT_HEAD = r"""\begin{table}[h]
\centering\small
\renewcommand{\arraystretch}{1.2}
\begin{tabular}{@{}llcccl@{}}
\toprule
$w$ & $(E,o)$ & $\deg P_w$ & $\deg_{\mathrm{nc}}$ & $\mathrm{M}$ & class\\
\midrule
"""
_HIGHLIGHT_FOOT = r"""\bottomrule
\end{tabular}
\caption{The $24$ coprime classes of smallest Mahler measure $>1$: word, type, degree of
$P_w$, degree of its non-cyclotomic factor, Mahler measure, and the nature of that factor
(Lehmer's polynomial; a Salem number $=$ reciprocal with one root off the unit circle; a
Pisot number; or ``$k$ ext.'' $=$ $k$ roots outside the circle).}\label{tab:highlights}
\end{table}
"""


def write_summary_table(recs, path):
    by_type = {}
    for r in recs:
        by_type.setdefault((r["E"], r["o"]), []).append(r)
    cells = []
    for (E, o) in sorted(by_type):
        g = by_type[(E, o)]
        ncyc = sum(1 for r in g if r["cyclotomic"])
        nnon = len(g) - ncyc
        nonM = [r["mahler"] for r in g if not r["cyclotomic"]]
        minM = f"{min(nonM):.4f}" if nonM else "--"
        maxM = f"{max(r['mahler'] for r in g):.4f}"
        cells.append(f"$({E},{o})$ & {len(g)} & {ncyc} & {nnon} "
                     f"& ${minM}$ & ${maxM}$")
    half = (len(cells) + 1) // 2                 # two type-blocks side by side
    left, right = cells[:half], cells[half:]
    empty = " & & & & &"
    body = "".join(f"{left[i]} & {right[i] if i < len(right) else empty} \\\\\n"
                   for i in range(half))
    with open(path, "w") as fh:
        fh.write(_SUMMARY_HEAD + body + _SUMMARY_FOOT)
    return len(cells)


def classify(fp, M):
    """Label the non-cyclotomic factor: Lehmer / Salem / Pisot / multi-root."""
    c = [int(x) for x in fp.all_coeffs()]
    recip = c == c[::-1]
    nout = 0
    if _np is not None:
        nout = sum(1 for r in _np.roots(c) if abs(r) > 1 + 1e-9)
    if abs(M - 1.17628081825) < 1e-5:
        return "Lehmer"
    if nout == 1 and recip:
        return "Salem"
    if nout == 1:
        return "Pisot"
    return f"{nout} ext."


def write_highlight_table(recs, path, topn=24):
    non = sorted((r for r in recs if not r["cyclotomic"]),
                 key=lambda r: (r["mahler"], r["E"] + r["o"], r["w"]))[:topn]
    body = ""
    for r in non:
        nc = r["noncyc"][0] if r["noncyc"] else None
        note = classify(nc, r["mahler"]) if nc is not None else "--"
        body += (f"$\\mathtt{{{r['w']}}}$ & $({r['E']},{r['o']})$ & "
                 f"${r['deg']}$ & ${r['ncdeg']}$ & ${r['mahler']:.5f}$ & "
                 f"{note} \\\\\n")
    with open(path, "w") as fh:
        fh.write(_HIGHLIGHT_HEAD + body + _HIGHLIGHT_FOOT)
    return non


# --------------------------------------------------------------------------- #
# The known 3n+1 cycles as words of the accelerated T-map                      #
#   u : x -> (3x+1)/2   (odd step),     v : x -> x/2   (even step).            #
# The parity sequence of each cyclic T-orbit is a positive word; its fixed     #
# point F_w(x)=x is the cycle value, and the type (E,o) gives D = 2^E - 3^o.   #
# --------------------------------------------------------------------------- #
CYCLE_WORDS = [("u", -1), ("uv", 1), ("uuv", -5), ("uuuuvuuuvvv", -17)]


def fixed_point(w):
    """Fixed point of the affine word map (u:(3x+1)/2, v:x/2): the cycle value."""
    a, b = sp.Integer(1), sp.Integer(0)
    for ch in w:
        if ch == "u":
            a, b = sp.Rational(3, 2) * a, sp.Rational(3, 2) * b + sp.Rational(1, 2)
        else:
            a, b = sp.Rational(1, 2) * a, sp.Rational(1, 2) * b
    return sp.nsimplify(b / (1 - a))


def P_poly(w):
    E, o = len(w), w.count("u")
    c = t_coeffs(w, E, o)
    return sp.Poly(sum(ci * t ** i for i, ci in enumerate(c)), t)


def T_XY(w):
    """Companion cocycle T = chi.d_v in Z[X,Y]: sum over v-positions of X^a Y^b."""
    expr, au, av = sp.Integer(0), 0, 0
    for ch in w:
        if ch == "v":
            expr += X ** au * Y ** av
            av += 1
        else:
            au += 1
    return sp.expand(expr)


def T_poly(w):
    """T = chi.d_v reduced to Z[t] (coprime), cleared -- the companion of P_w = S."""
    E, o = len(w), w.count("u")
    exps, au, av = [], 0, 0
    for ch in w:
        if ch == "v":
            exps.append(o * av - (E - o) * au)
            av += 1
        else:
            au += 1
    if not exps:
        return sp.Poly(0, t)
    mn = min(exps)
    coeffs = [0] * (max(exps) - mn + 1)
    for e in exps:
        coeffs[e - mn] += 1
    return sp.Poly(sum(c * t ** i for i, c in enumerate(coeffs)), t)


def latex_factor(P):
    """LaTeX factorisation of P over Q, labelling cyclotomic factors Phi_n."""
    _, facs = sp.factor_list(P)
    parts = []
    for f, m in facs:
        fp = sp.Poly(f, t)
        n = _PHI.get(tuple(fp.all_coeffs()))
        s = f"\\Phi_{{{n}}}" if n else "\\bigl(" + sp.latex(fp.as_expr()) + "\\bigr)"
        parts.append(s + (f"^{{{m}}}" if m > 1 else ""))
    return "\\,".join(parts) if parts else "1"


def write_cycle_block(path):
    head = (r"\begin{table}[h]\centering\small\renewcommand{\arraystretch}{1.25}"
            "\n\\begin{tabular}{@{}llccc@{}}\n\\toprule\n"
            r"word $w$ & cycle & $(E,o)$ & $D=2^{E}-3^{o}$ & $\mathrm{M}(P_w)$\\"
            "\n\\midrule\n")
    rows, eqs = "", []
    for w, xval in CYCLE_WORDS:
        E, o = len(w), w.count("u")
        D = 2 ** E - 3 ** o
        assert fixed_point(w) == xval                      # cycle value is exact
        rec = analyze(w, E, o)
        Mtxt = "1" if rec["cyclotomic"] else f"{rec['mahler']:.5f}"
        rows += (f"$\\mathtt{{{w}}}$ & $\\{{{xval}\\}}$ & $({E},{o})$ & "
                 f"${D}$ & ${Mtxt}$\\\\\n")
        P = P_poly(w)
        if P.degree() >= 1:
            eqs.append((xval, sp.latex(P.as_expr()), latex_factor(P)))
    foot = (r"\bottomrule" "\n\\end{tabular}\n"
            r"\caption{The four known cycles of the $3n+1$ map on $\mathbb{Z}$, read as words"
            r" of the accelerated $T$-map ($u:x\mapsto(3x+1)/2$, $v:x\mapsto x/2$): the cycle"
            r" value $x$ (fixed point of the word map), the type, $D=2^E-3^o$, and the Mahler"
            r" measure of $P_w$.}\label{tab:cycles}" "\n\\end{table}\n")
    blocks = [f"P_{{{xval}}}(t) &= {plat}\\\\\n &= {flat}." for xval, plat, flat in eqs]
    eqlines = "\\begin{align*}\n" + "\\\\[4pt]\n".join(blocks) + "\n\\end{align*}\n"
    with open(path, "w") as fh:
        fh.write(head + rows + foot + eqlines)
    return [(w, x, fixed_point(w)) for w, x in CYCLE_WORDS]


def Rw_coeffs(w):
    """Coefficient tuple (descending) of the Littlewood core R_w = P_w/g_o."""
    o = w.count("u")
    R, rem = sp.div(P_poly(w), sp.Poly([1] * o, t))
    assert rem.is_zero
    return tuple(int(c) for c in R.all_coeffs())


def complement(w):
    return w.translate(str.maketrans("uv", "vu"))


def build_R_cores(here, EMAX=16):
    """Catalogue the distinct cores R_w over coprime necklaces with E<=EMAX, and
    write R_cores.csv + cores_table.tex (distinct cores of small degree)."""
    from collections import defaultdict
    bucket = defaultdict(list)
    for E in range(1, EMAX + 1):
        for o in range(1, E + 1):
            if gcd(E, o) == 1:
                for w in class_reps(E, o):
                    bucket[Rw_coeffs(w)].append((E, o, w))
    rows = []
    for c, ws in bucket.items():
        Mc = mahler(list(c))
        rows.append({"coeffs": c, "deg": len(c) - 1, "M": Mc, "cyc": abs(Mc - 1) < 1e-7,
                     "fib": len(ws), "ntypes": len({(E, o) for E, o, w in ws}),
                     "ex": min(w for E, o, w in ws)})
    rows.sort(key=lambda r: (r["deg"], -r["fib"]))
    neck = sum(len(v) for v in bucket.values())
    distinct, ncyc = len(rows), sum(1 for r in rows if r["cyc"])
    upto_recip = len({min(c, c[::-1]) for c in bucket})
    selfrec = [r for r in rows if tuple(r["coeffs"]) == tuple(r["coeffs"])[::-1]]
    n_selfrec, n_selfrec_cyc = len(selfrec), sum(1 for r in selfrec if r["cyc"])
    with open(os.path.join(here, "R_cores.csv"), "w", newline="") as fh:
        wr = csv.writer(fh)
        wr.writerow(["R_w(t)", "deg", "mahler", "cyclotomic", "fibre", "n_types", "example"])
        for r in rows:
            wr.writerow([sp.sstr(sp.Poly(list(r["coeffs"]), t).as_expr()), r["deg"],
                         f"{r['M']:.6f}", int(r["cyc"]), r["fib"], r["ntypes"], r["ex"]])
    head = (r"\begin{table}[h]\centering\small\renewcommand{\arraystretch}{1.2}"
            "\n\\begin{tabular}{@{}lcccc@{}}\n\\toprule\n"
            r"core $R_w(t)$ & $\deg$ & $\mathrm{M}$ & cyclotomic & fibre\\"
            "\n\\midrule\n")
    body = ""
    for r in (x for x in rows if x["deg"] <= 4):
        Mt = "1" if r["cyc"] else f"{r['M']:.4f}"
        body += (f"${sp.latex(sp.Poly(list(r['coeffs']), t).as_expr())}$ & ${r['deg']}$ & "
                 f"${Mt}$ & {'yes' if r['cyc'] else 'no'} & ${r['fib']}$\\\\\n")
    foot = (r"\bottomrule" "\n\\end{tabular}\n"
            r"\caption{The distinct cores $R_w$ of degree $\le4$, over all $%d$ coprime"
            r" necklaces with $E\le%d$ ($%d$ distinct cores, $%d$ of them cyclotomic). Each"
            r" recurs across a whole fibre of necklaces; cyclotomic cores dominate. Cores come"
            r" in reciprocal pairs (e.g.\ $t^3-t^2+1$ and $t^3-t+1$), self-reciprocal ones"
            r" single.}\label{tab:cores}" "\n\\end{table}\n") % (neck, EMAX, distinct, ncyc)
    with open(os.path.join(here, "cores_table.tex"), "w") as fh:
        fh.write(head + body + foot)
    return {"neck": neck, "distinct": distinct, "upto_recip": upto_recip,
            "ncyc": ncyc, "selfrec": n_selfrec, "selfrec_cyc": n_selfrec_cyc,
            "EMAX": EMAX}


# --------------------------------------------------------------------------- #
# Self-checks and report                                                      #
# --------------------------------------------------------------------------- #
def selftest():
    assert S("u") == 1 and S("v") == 0                       # generators pin chi o d_u
    for n in range(1, 7):                                    # cocycle law: independent oracle
        for tup in product("uv", repeat=n):
            w = "".join(tup)
            for k in range(1, n):
                assert cocycle_residual(w[:k], w[k:]) == 0, (w, k)
    assert S("uvuv") == 1 + X * Y                            # worked examples
    assert S("uuvv") == 1 + X
    assert S("uuu") == 1 + X + X ** 2
    assert S("uuuu") == 1 + X + X ** 2 + X ** 3
    assert reparametrise("uvuv", 4, 2)[1] == 1 + s
    assert sp.expand(reparametrise("uuvv", 4, 2)[1] * t - (t + s)) == 0   # 1 + s/t
    assert cyclotomic_monomial(1 + X * Y) == (2, 1, 1)       # NOT Phi_4(z): the fix
    assert cyclotomic_monomial(1 + X + X ** 2) == (3, 1, 0)
    for (E, o) in [(3, 2), (7, 3), (7, 6), (9, 4), (11, 7)]:  # g_o | P_w, core Littlewood
        go = sp.Poly([1] * o, t)                             # 1 + t + ... + t^{o-1}
        for w in class_reps(E, o):
            R, rem = sp.div(P_poly(w), go)
            assert rem.is_zero, (w, o)                        # full cyclotomic factor divides
            assert max(abs(int(c)) for c in R.all_coeffs()) <= 1, (w, o)  # R in {-1,0,1}
            assert R.eval(1) == 1                             # R_w(1) = 1
            Q, qr = sp.div(R - sp.Poly(1, t), sp.Poly([1, -1], t))   # (R_w-1)/(t-1)
            assert qr.is_zero and all(int(c) in (0, 1) for c in Q.all_coeffs())  # Q_w 0/1
    for (E, o) in [(5, 2), (7, 3), (8, 3), (11, 4)]:         # core reflection symmetries
        for w in class_reps(E, o):
            r = Rw_coeffs(w)
            assert Rw_coeffs(w[::-1]) == r[::-1], w           # reverse   -> reciprocal R_w
            assert Rw_coeffs(complement(w)) == r[::-1], w     # complement-> reciprocal R_w
    for (E, o) in [(3, 2), (5, 2), (7, 3), (8, 3), (11, 7)]:  # cohomology: Crowell-Fox + Alexander
        chiw = X ** o * Y ** (E - o)
        for w in class_reps(E, o):
            assert sp.expand((X - 1) * S(w) + (Y - 1) * T_XY(w) - (chiw - 1)) == 0   # Crowell-Fox
            P, Tt = P_poly(w), T_poly(w)
            R, _ = sp.div(P, sp.Poly([1] * o, t))
            g = sp.gcd(P, Tt)
            assert sp.expand(g.as_expr() / g.LC() - R.as_expr() / R.LC()) == 0       # R_w = gcd(S,T)
    for w, x in CYCLE_WORDS:                                 # cycle values are exact
        assert fixed_point(w) == x, (w, x)
    print("selftest OK: cocycle law to length 6; P_w = g_o(1+(t-1)Q_w) with Q_w 0/1; "
          "Crowell-Fox + R_w = gcd(chi.d_u, chi.d_v); cycle values match\n")


def small_table():
    """The original E+o<=6 illustration (Section-1 worked examples)."""
    for (E, o, w) in all_reps():
        gal, mh, N, roots = galois_mahler_roots(w)
        print(f"w={w:<6} (E,o)=({E},{o}) chi={chi(w)} S={S(w)} "
              f"Mahler={mh} Galois={gal}")


def main():
    import os
    selftest()
    here = os.path.dirname(os.path.abspath(__file__))
    NMAX = 20
    recs = build_catalogue(NMAX)
    n = len(recs)
    ncyc = sum(1 for r in recs if r["cyclotomic"])
    print(f"Coprime catalogue gcd(E,o)=1, E+o<={NMAX}: {n} cyclic classes")
    print(f"  cyclotomic (Mahler=1): {ncyc}    non-cyclotomic (Mahler>1): {n-ncyc}")

    nonc = [r for r in recs if not r["cyclotomic"]]
    first = min(nonc, key=lambda r: (r["E"] + r["o"], r["E"], r["w"]))
    fgal = galois_name(first["noncyc"][0]) if first["noncyc"] else "--"
    print(f"  first non-cyclotomic necklace: w={first['w']} (E,o)=({first['E']},"
          f"{first['o']})  factor={first['factor']}  Mahler={first['mahler']:.6f}"
          f"  Galois(noncyc)={fgal}")
    minEo = min(r["E"] + r["o"] for r in nonc)
    print(f"  => every coprime necklace with E+o<={minEo-1} is cyclotomic; "
          f"first non-cyclotomic at E+o={minEo}")
    gmin = min(nonc, key=lambda r: r["mahler"])
    gmax = max(recs, key=lambda r: r["mahler"])
    print(f"  smallest Mahler>1: {gmin['mahler']:.6f} at w={gmin['w']} "
          f"(E,o)=({gmin['E']},{gmin['o']})")
    print(f"  largest  Mahler  : {gmax['mahler']:.6f} at w={gmax['w']} "
          f"(E,o)=({gmax['E']},{gmax['o']})")
    rmax_all = max(r["rmax"] for r in recs)
    print(f"  Littlewood core R_w = P_w/(1+..+t^(o-1)): max|coeff| over all "
          f"{n} classes = {rmax_all}  (=> R_w in {{-1,0,1}})")

    write_csv(recs, os.path.join(here, "coprime_catalogue.csv"))
    ntypes = write_summary_table(recs, os.path.join(here, "summary_table.tex"))
    hl = write_highlight_table(recs, os.path.join(here, "highlight_table.tex"))
    write_cycle_block(os.path.join(here, "cycle_block.tex"))
    cores = build_R_cores(here, EMAX=16)
    print(f"  wrote coprime_catalogue.csv ({n} rows), summary_table.tex "
          f"({ntypes} types), highlight_table.tex ({len(hl)} rows), cycle_block.tex")
    print(f"  cores: {cores['neck']} coprime necklaces (E<={cores['EMAX']}) -> "
          f"{cores['distinct']} distinct R_w ({cores['upto_recip']} up to reciprocal, "
          f"{cores['ncyc']} cyclotomic); wrote R_cores.csv + cores_table.tex")
    print(f"  duality locus: {cores['selfrec']} self-reciprocal cores "
          f"({cores['selfrec_cyc']} cyclotomic + {cores['selfrec']-cores['selfrec_cyc']} "
          f"non-cyclotomic/Salem incl. Lehmer)")
    print("\nKnown-cycle polynomials:")
    for w, xval in CYCLE_WORDS:
        E, o = len(w), w.count("u")
        print(f"  {w:14s} x={xval:<3} (E,o)=({E},{o}) D={2**E-3**o:<5} "
              f"P_w = {sp.factor(P_poly(w).as_expr())}")
    print("\nSmallest-Mahler non-cyclotomic necklaces:")
    for r in hl[:12]:
        print(f"  {r['w']:<14} (E,o)=({r['E']},{r['o']}) deg={r['ncdeg']:<2} "
              f"Mahler={r['mahler']:.5f}  factor={r['factor']}")


if __name__ == "__main__":
    main()
