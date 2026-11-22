#!/usr/bin/env python3
"""Decide Syracuse word families by the places/elimination method (approaches/places-elimination).

A cycle word w satisfies D(w) | S(w) with D = 2^E - 3^o coprime to 6.  For a family, the run
coordinates are 6-units at (X,Y) = (2,3); if the incidence variety V(D,S) does not dominate the
character torus (r = 1), a resultant R(X,Y) lies in the ideal (D,S) and every cycle of the family
has |D| | sixfree(R(2,3)).  |D| grows geometrically, so finitely many members remain and are
checked exactly.  If r >= 2 there is no polynomial core (the Vojta/Levin regime) and only bounded
searches and rational-line subfamilies can be decided.

Usage
  decide_family.py tworun D E1 E2 [--lean]       the Lean family d^a e1 d^a e2 d^a
  decide_family.py family SPEC [--lean NAME]     one-parameter family, SPEC tokens separated by spaces:
        g:<block>:<m>:<c>   block (comma list) repeated m*a+c times
        f:<word>            fixed spacer word (comma list)
      e.g.  "g:1:1:0 f:2 g:1:1:0 f:3 g:1:1:0"   (= tworun 1 2 3)
  decide_family.py twoword U V [--box N] [--lines P]   u^a v^b, U and V comma lists

Every exact claim is re-checked by integer arithmetic (gcd(D_a,S_a) | R(2,3) for a <= 40).
"""
import sys, argparse
from math import gcd
from fractions import Fraction
import sympy as sp

X, Y, z, s = sp.symbols('X Y z s')

# ---------- exact integer side ----------
def SD(w):
    o, E, e, S = len(w), sum(w), 0, 0
    for k, d in enumerate(w):
        S += 2 ** e * 3 ** (o - 1 - k); e += d
    return S, 2 ** E - 3 ** o

def sixfree(n):
    n = abs(n)
    for p in (2, 3):
        while n and n % p == 0: n //= p
    return n

def parse_word(t): return [int(x) for x in t.split(',') if x != '']

def parse_spec(spec):
    toks = []
    for t in spec.split():
        k = t.split(':')
        if k[0] == 'g': toks.append(('g', parse_word(k[1]), int(k[2]), int(k[3])))
        elif k[0] == 'f': toks.append(('f', parse_word(k[1])))
        else: raise SystemExit('bad token ' + t)
    return toks

def word_of(toks, a):
    w = []
    for t in toks:
        w += t[1] * (t[2] * a + t[3]) if t[0] == 'g' else t[1]
    return w

# ---------- symbolic side ----------
def Ssym(word):
    S = sp.Integer(0)
    for d in reversed(word):          # S(d::w) = Y^len w + X^d S(w)
        S = Y ** 0 * S  # placeholder for clarity
    S, L = sp.Integer(0), 0
    for d in reversed(word):
        S = Y ** L + X ** d * S; L += 1
    return sp.expand(S)

def slope(block):
    return Fraction(sum(block), len(block))

def family_forms(toks):
    """Homogeneous forms (D, G) in [z:s] for an r = 1 family, with G = S * prod(X^E-Y^o)."""
    grows = [t for t in toks if t[0] == 'g' and t[2] > 0]
    lam = slope(grows[0][1]); p, q = lam.numerator, lam.denominator
    # z = X^{p a}, s = Y^{q a}
    Sw, Lw, Ew = sp.Integer(0), sp.Integer(1), sp.Integer(1)   # S, Y^len, X^sum of suffix
    dens = []
    for t in reversed(toks):
        if t[0] == 'f':
            Sb, Yb, Xb = Ssym(t[1]), Y ** len(t[1]), X ** sum(t[1])
        else:
            beta, m, c = t[1], t[2], t[3]
            Eb, ob = sum(beta), len(beta); k = Eb // p
            Xn = X ** (Eb * c) * z ** (m * k); Yn = Y ** (ob * c) * s ** (m * k)
            den = X ** Eb - Y ** ob; dens.append(den)
            Sb, Yb, Xb = Ssym(beta) * (Xn - Yn) / den, Yn, Xn
        Sw = Lw * Sb + Xb * Sw; Lw = Yb * Lw; Ew = Xb * Ew
    Dn = sp.expand(Ew - Lw)
    G = sp.expand(sp.cancel(Sw * sp.Mul(*set(dens))))
    return Dn, G, (p, q)

def resultant_core(Dn, G):
    f = sp.expand(Dn.subs(s, 1)); g = sp.expand(G.subs(s, 1))
    if sp.degree(f, z) <= 0 or sp.degree(g, z) <= 0:
        return None
    return sp.factor(sp.resultant(f, g, z))

def EO(toks):
    """E(a) = E0 + E1 a, o(a) = o0 + o1 a."""
    w0, w1 = word_of(toks, 0), word_of(toks, 1)
    return sum(w0), sum(w1) - sum(w0), len(w0), len(w1) - len(w0)

def growth_a0(toks, c, amax=10 ** 4):
    """Smallest a0 with g(a0) > c, where g is the dominant-sign difference: then growth() in
    TwoRun.lean propagates g(a) > c to all a >= a0 (needs base_dom >= base_other >= 1)."""
    E0, E1, o0, o1 = EO(toks)
    if E1 == 0 and o1 == 0: return None
    two_dom = 2 ** E1 > 3 ** o1
    for a in range(amax):
        D = 2 ** (E0 + E1 * a) - 3 ** (o0 + o1 * a)
        gval = D if two_dom else -D
        if gval > c: return a
    return None

def decide_one_param(toks, verbose=True):
    grows = [t for t in toks if t[0] == 'g' and t[2] > 0]
    out = {}
    slopes = sorted({slope(t[1]) for t in grows})
    out['slopes'] = [str(x) for x in slopes]
    if len(slopes) != 1:
        out['r'] = 2
        out['verdict'] = ('r >= 2: growing blocks of different slopes -> V(D,S) dominates the '
                          'character torus, no polynomial core (Vojta/Levin regime)')
        return out
    out['r'] = 1
    Dn, G, pq = family_forms(toks)
    R = resultant_core(Dn, G)
    out['core'] = str(R)
    R23 = int(R.subs({X: 2, Y: 3})) if R is not None else 0
    out['ceiling'] = sixfree(R23)
    if R23 == 0:
        # D and G share a factor h along the family: a cycle forces D/h | G/h, so the ceiling
        # applies to D' = D/h.  Its growth is checked numerically only (flagged as such).
        h = sp.gcd(Dn, G)
        Dp, Gp = sp.cancel(Dn / h), sp.cancel(G / h)
        out['common_factor_h'] = str(sp.factor(h))
        Rp = resultant_core(Dp, Gp)
        Rp23 = int(Rp.subs({X: 2, Y: 3})) if Rp is not None else 0
        out['ceiling_for_D/h'] = sixfree(Rp23)
        E0, E1, o0, o1 = EO(toks)
        p_, q_ = pq
        def Dprime(a):
            val = sp.nsimplify(Dp.subs({X: 2, Y: 3, z: sp.Integer(2) ** (p_ * a), s: sp.Integer(3) ** (q_ * a)}))
            return sixfree(sp.fraction(val)[0])
        scan = [Dprime(a) for a in range(0, 30)]
        out['sixfree(D/h) for a<30 (numeric)'] = scan[:8] + ['...']
        cyc = [a for a in range(30) if (lambda S_, D_: D_ != 0 and S_ % D_ == 0)(*SD(word_of(toks, a)))]
        out['cycles_found(a<30)'] = cyc
        if Rp23 == 0 or all(v <= 1 for v in scan[5:]):
            out['verdict'] = ('degenerate: D/h does not grow (or R(D/h,G/h)(2,3) = 0) - the family '
                              'contains an identity-type subfamily; cycles listed above')
        else:
            a0 = next((a for a in range(30) if all(v > abs(Rp23) for v in scan[a:])), None)
            out['verdict'] = ('degenerate, reduced: cycle => sixfree(D/h) | %d; numerically none for a >= %s '
                              '(growth of D/h checked to a=29 only, not proved)' % (sixfree(Rp23), a0))
        return out
    c = out['ceiling']
    # sanity: gcd(D_a,S_a) | R(2,3) on every member (not only cycles)
    out['sanity_gcd_divides_ceiling_a<=40'] = all(
        R23 % sixfree(gcd(*SD(word_of(toks, a)))) == 0 for a in range(41))
    a0 = growth_a0(toks, abs(R23))
    out['a0'] = a0
    cycles = [a for a in range(a0) if (lambda S_, D_: D_ != 0 and S_ % D_ == 0)(*SD(word_of(toks, a)))]
    out['cycles_found(a<a0)'] = [(a, word_of(toks, a), SD(word_of(toks, a))[0] // SD(word_of(toks, a))[1])
                                for a in cycles]
    out['verdict'] = ('DECIDED: cycles exactly at a in %s; none for a >= %d (|D_a| > |R(2,3)| = %d)'
                      % ([a for a in cycles], a0, abs(R23)))
    return out

# ---------- Lean emission (twoRunWord family, uses Syracuse.TwoRun) ----------
def lean_tworun(d, e1, e2, a0, cycles):
    """Lean instance for `Syracuse.TwoRun`.  If small members are cycles, they are recorded with
    `decide` and exclusion is stated from a1 = max(cycles) + 1."""
    name = f"{d}_{e1}_{e2}"
    if not cycles:
        return f"""/-- `{d}^a {e1} {d}^a {e2} {d}^a`: emitted by `decide_family.py tworun {d} {e1} {e2}`
(ceiling `sixfree R* = {sixfree(4**e1*(2**d-2**e2)**3+3*2**e2*(2**d-2**e1)**3)}`, `a₀ = {a0}`). -/
theorem noCycle_{name} : ∀ a, ¬ Dz (w {d} {e1} {e2} a) ∣ Sz (w {d} {e1} {e2} a) :=
  noCycle_of_check {a0} (by norm_num) (by norm_num) (by decide)
    (by intro a ha; interval_cases a; all_goals decide)
    (by simp [Rz, Rstar, g, Dz_twoRun])
"""
    a1 = max(cycles) + 1
    facts = "\n".join(
        f"theorem cycle_{name}_{a} : Dz (w {d} {e1} {e2} {a}) ∣ Sz (w {d} {e1} {e2} {a}) := by decide"
        for a in cycles)
    small = ("(by intro a h1 h2; omega)" if a1 >= a0 else
             "(by intro a h1 h2; interval_cases a; all_goals decide)")
    return f"""/-- `{d}^a {e1} {d}^a {e2} {d}^a`: emitted by `decide_family.py tworun {d} {e1} {e2}`.
Cycles at `a ∈ {cycles}`, none for `a ≥ {a1}`. -/
{facts}

theorem noCycle_{name} : ∀ a, {a1} ≤ a → ¬ Dz (w {d} {e1} {e2} a) ∣ Sz (w {d} {e1} {e2} a) :=
  noCycle_ge_of_check {a1} {max(a0, a1)} (by norm_num) (by norm_num) (by decide)
    {small}
    (by simp [Rz, Rstar, g, Dz_twoRun])
"""

def tworun_spec(d, e1, e2):
    return [('g', [d], 1, 0), ('f', [e1]), ('g', [d], 1, 0), ('f', [e2]), ('g', [d], 1, 0)]

def decide_tworun(d, e1, e2):
    Rz = 4 ** e1 * (2 ** d - 2 ** e2) ** 3 + 3 * 2 ** e2 * (2 ** d - 2 ** e1) ** 3
    toks = tworun_spec(d, e1, e2)
    out = {'R*(2^d,2^e1,2^e2,3)': Rz, 'ceiling sixfree': sixfree(Rz)}
    if Rz == 0:
        out['verdict'] = 'pure circuit e1 = e2 = d: degenerate (no defect)'
        return out, None
    # same a0 rule as TwoRun.g: -D if d = 1 else D
    a0 = next(a for a in range(10 ** 4)
              if (lambda D_: (-D_ if d == 1 else D_))(SD(word_of(toks, a))[1]) > abs(Rz))
    cyc = [a for a in range(a0) if SD(word_of(toks, a))[0] % SD(word_of(toks, a))[1] == 0]
    out['a0'] = a0; out['cycles_found(a<a0)'] = cyc
    out['verdict'] = 'DECIDED: cycles at a in %s, none for a >= %d' % (cyc, a0)
    return out, (lean_tworun(d, e1, e2, a0, cyc) if d >= 1 and e1 >= 1 else None)

# ---------- two words u^a v^b ----------
def decide_twoword(u, v, box, lines):
    out = {'slopes': (str(slope(u)), str(slope(v)))}
    out['r'] = 2
    out['note'] = ('two independent exponents: run coordinates (P^1)^2 (equal slopes) or 2-dim '
                   'affine (different slopes); V(D,S) dominates -> no polynomial core for the whole '
                   'family (Vojta/Levin regime)')
    cyc = []
    for a in range(box + 1):
        for b in range(box + 1):
            w = u * a + v * b
            if not w: continue
            S_, D_ = SD(w)
            if D_ != 0 and S_ % D_ == 0: cyc.append((a, b, S_ // D_))
    out['cycles_in_box(a,b<=%d)' % box] = cyc
    if slope(u) == slope(v):
        decided = []
        for p in range(1, lines + 1):
            for q in range(1, lines + 1):
                if gcd(p, q) != 1: continue
                for a0 in range(p):
                    for b0 in range(q):
                        toks = [('g', u, p, a0), ('g', v, q, b0)]
                        r = decide_one_param(toks)
                        decided.append(((p, q, a0, b0), r.get('ceiling'), r['verdict'][:60]))
        out['rational_lines (a,b)=(p t+a0, q t+b0)'] = decided
    else:
        out['rational_lines'] = 'different slopes: every line is itself r = 2; nothing decidable elementarily'
    return out

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    t = sub.add_parser('tworun'); t.add_argument('d', type=int); t.add_argument('e1', type=int)
    t.add_argument('e2', type=int); t.add_argument('--lean', action='store_true')
    f = sub.add_parser('family'); f.add_argument('spec')
    w = sub.add_parser('twoword'); w.add_argument('u'); w.add_argument('v')
    w.add_argument('--box', type=int, default=12); w.add_argument('--lines', type=int, default=3)
    A = ap.parse_args()
    if A.cmd == 'tworun':
        out, lean = decide_tworun(A.d, A.e1, A.e2)
        cross = decide_one_param(tworun_spec(A.d, A.e1, A.e2))
        out['general-route ceiling (cross-check)'] = cross.get('ceiling')
        for k, x in out.items(): print(f'{k}: {x}')
        if A.lean and lean: print('\n' + lean)
    elif A.cmd == 'family':
        for k, x in decide_one_param(parse_spec(A.spec)).items(): print(f'{k}: {x}')
    else:
        for k, x in decide_twoword(parse_word(A.u), parse_word(A.v), A.box, A.lines).items():
            if isinstance(x, list) and len(x) > 12:
                print(f'{k}: ({len(x)} entries)'); [print('   ', y) for y in x]
            else: print(f'{k}: {x}')

if __name__ == '__main__':
    main()
