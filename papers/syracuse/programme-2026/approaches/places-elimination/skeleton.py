#!/usr/bin/env python3
"""Skeleton compiler: uniform-in-the-words theorems for r = 1 skeleton families.

A skeleton is a list of slots:  S  (a spacer word)  or  B:k:m:c  (a growing block of size k times
the common slope (p, q), repeated m*a + c times).  A family instance assigns actual words: blocks
beta_i with |beta_i| = k_i p, len beta_i = k_i q, and arbitrary spacers sigma_j.

The closed form depends on the words only through their cocycle data
    S(beta_i), S(sigma_j), 2^{|sigma_j|}, 3^{len sigma_j}, 2^p, 3^q,
so the resultant of D and (prod D(beta_i)) S in the run coordinates [z:s] = [2^{pa} : 3^{qa}] is a
universal polynomial Res_sigma in that data.  Every cycle member has D | c * Res' (6-units removed).

  skeleton.py compile "B:1:1:0 S B:1:1:0 S" NAME OUT.lean   emit the Lean file for the skeleton
  skeleton.py show    "B:1:1:0 S B:1:1:0 S"                 print D, G, and the factored resultant
  skeleton.py check   "B:1:1:0 S B:1:1:0 S" [N]             random instances: gcd(D,S) | ceiling
"""
import sys, random
from math import gcd
import sympy as sp

def parse(shape):
    out = []
    for t in shape.split():
        if t == 'S': out.append(('S',))
        else:
            _, k, m, c = t.split(':'); out.append(('B', int(k), int(m), int(c)))
    return out

class Skel:
    def __init__(self, shape):
        self.slots = parse(shape)
        self.z, self.s, self.P, self.Q = sp.symbols('zz ss PP QQ')
        self.blocks = [i for i, t in enumerate(self.slots) if t[0] == 'B']
        self.spacers = [i for i, t in enumerate(self.slots) if t[0] == 'S']
        self.Sb = {i: sp.Symbol('Sb%d' % n) for n, i in enumerate(self.blocks)}
        self.Ss = {i: sp.Symbol('Ss%d' % n) for n, i in enumerate(self.spacers)}
        self.Ps = {i: sp.Symbol('Ps%d' % n) for n, i in enumerate(self.spacers)}
        self.Qs = {i: sp.Symbol('Qs%d' % n) for n, i in enumerate(self.spacers)}
        self.vars = [self.z, self.s, self.P, self.Q] + [self.Sb[i] for i in self.blocks] + \
            [x for i in self.spacers for x in (self.Ss[i], self.Ps[i], self.Qs[i])]
        self.N = sum(t[1] * t[2] for t in self.slots if t[0] == 'B')
        self.build()

    def seg(self, i):
        t = self.slots[i]
        if t[0] == 'S':
            return (self.Ss[i], self.Qs[i], self.Ps[i])
        _, k, m, c = t
        Xn = self.P ** (k * c) * self.z ** (k * m); Yn = self.Q ** (k * c) * self.s ** (k * m)
        return (self.Sb[i] * (Xn - Yn) / (self.P ** k - self.Q ** k), Yn, Xn)

    def build(self):
        Sw, Yw, Xw = sp.Integer(0), sp.Integer(1), sp.Integer(1)
        for i in reversed(range(len(self.slots))):
            Sb, Yb, Xb = self.seg(i)
            Sw = Yw * Sb + Xb * Sw; Yw = Yb * Yw; Xw = Xb * Xw
        from math import lcm
        self.Lk = lcm(*[self.slots[i][1] for i in self.blocks]) if self.blocks else 1
        self.mu = self.P ** self.Lk - self.Q ** self.Lk
        self.D = sp.expand(Xw - Yw)
        self.G = sp.expand(sp.cancel(Sw * self.mu))

    def certificate(self):
        z, s = self.z, self.s
        f = sp.Poly(self.D.subs(s, 1), z); g = sp.Poly(self.G.subs(s, 1), z)
        n, m = f.degree(), g.degree()
        assert n == self.N, (n, self.N)
        # Sylvester-type matrix: columns z^j f (j < m) and z^j g (j < n), rows z^0 .. z^{n+m-1}
        L = n + m
        fc = f.all_coeffs()[::-1]; gc = g.all_coeffs()[::-1]
        M = sp.zeros(L, L)
        for j in range(m):
            for i, c in enumerate(fc): M[i + j, j] = c
        for j in range(n):
            for i, c in enumerate(gc): M[i + j, m + j] = c
        # adjugate column: x_i = cofactor(0, i) gives M x = det(M) e_0
        cof = [sp.expand(M.cofactor(0, i, method='berkowitz')) for i in range(L)]
        R = sp.expand(sum(M[0, i] * cof[i] for i in range(L)))
        Az = sp.expand(sum(cof[i] * z ** i for i in range(m)))
        Bz = sp.expand(sum(cof[m + i] * z ** i for i in range(n)))
        assert sp.expand(Az * f.as_expr() + Bz * g.as_expr() - R) == 0
        # homogenise: s^e R = A D + B G with A, B homogeneous
        e = n + m - 1
        Ah = sp.expand(sp.Poly(Az, z).homogenize(s).as_expr() * s ** (m - 1 - sp.Poly(Az, z).degree()) if Az != 0 else 0)
        Bh = sp.expand(sp.Poly(Bz, z).homogenize(s).as_expr() * s ** (n - 1 - sp.Poly(Bz, z).degree()) if Bz != 0 else 0)
        assert sp.expand(Ah * self.D + Bh * self.G - s ** e * R) == 0
        # split R = c * mono * R'
        coeff, facs = sp.factor_list(R)
        units = set([self.P, self.Q] + [self.Ps[i] for i in self.spacers] + [self.Qs[i] for i in self.spacers])
        mono, rest = sp.Integer(1), sp.Integer(1)
        for fac, ex in facs:
            if fac in units: mono *= fac ** ex
            else: rest *= fac ** ex
        # pull 2,3-powers out of the integer content
        c = int(coeff); sgn = 1 if c > 0 else -1; c = abs(c); u23 = 1
        for pr in (2, 3):
            while c % pr == 0: c //= pr; u23 *= pr
        # identity:  s^e * mono * u23 * (sgn*c*R') = A D + B G   with R' = rest
        self.cert = dict(e=e, mono=mono, u23=u23, c=sgn * c, Rp=sp.expand(rest), A=Ah, B=Bh, R=R)
        return self.cert

    # numeric evaluation for a concrete instance
    def data(self, words, p, q):
        val = {self.P: 2 ** p, self.Q: 3 ** q}
        for i, w in zip(range(len(self.slots)), words):
            if self.slots[i][0] == 'B':
                val[self.Sb[i]] = SD(w)[0]
            else:
                val[self.Ss[i]] = SD(w)[0]; val[self.Ps[i]] = 2 ** sum(w); val[self.Qs[i]] = 3 ** len(w)
        return val

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

def random_instance(sk, rng):
    p, q = rng.choice([(1, 1), (2, 1), (3, 2), (3, 1), (5, 3), (4, 3)])
    words = []
    for t in sk.slots:
        if t[0] == 'S':
            words.append([rng.randint(1, 4) for _ in range(rng.randint(1, 2))])
        else:
            k = t[1]
            # a positive word with sum k p and length k q (needs k p >= k q)
            L, E = k * q, k * p
            w = [1] * L
            for _ in range(E - L): w[rng.randrange(L)] += 1
            words.append(w)
    return words, p, q

def word_of(sk, words, a):
    out = []
    for t, w in zip(sk.slots, words):
        out += w if t[0] == 'S' else w * (t[2] * a + t[3])
    return out

def check(shape, n=200):
    sk = Skel(shape); cert = sk.certificate(); rng = random.Random(11); bad = deg = tot = 0
    for _ in range(n):
        words, p, q = random_instance(sk, rng)
        val = sk.data(words, p, q)
        ceil = int(cert['c'] * cert['Rp'].subs(val))
        if ceil == 0: deg += 1; continue
        for a in range(0, 12):
            W = word_of(sk, words, a)
            if not W: continue
            S, D = SD(W); g = sixfree(gcd(S, D)); tot += 1
            if ceil % g: bad += 1
    print('shape %-28s N=%d  instances=%d degenerate(ceiling 0)=%d members=%d violations=%d'
          % (shape, sk.N, n, deg, tot, bad))

# ------------------------------------------------------------------ Lean emission
def lean_expr(e):
    s = sp.sstr(sp.expand(e)).replace('**', '^')
    return s


CHUNK = 30
def lean_def(name, e, vlist, doc=None):
    terms = sp.Add.make_args(sp.expand(e))
    chunks = [terms[i:i + CHUNK] for i in range(0, len(terms), CHUNK)] or [(sp.Integer(0),)]
    out = []; names = []
    if len(chunks) == 1:
        out.append(('/-- %s -/\n' % doc if doc else '') + 'def %s (%s : R) : R := %s' % (name, vlist, lean_expr(sp.Add(*chunks[0]))))
        return '\n\n'.join(out), [name]
    for j, ch in enumerate(chunks):
        nm = '%s_%d' % (name, j); names.append(nm)
        out.append('def %s (%s : R) : R := %s' % (nm, vlist, lean_expr(sp.Add(*ch))))
    out.append(('/-- %s -/\n' % doc if doc else '') + 'def %s (%s : R) : R := %s' % (name, vlist, ' + '.join('%s %s' % (nm, vlist) for nm in names)))
    return '\n\n'.join(out), [name] + names

def emit(shape, name, out):
    sk = Skel(shape); cert = sk.certificate()
    nb = len(sk.blocks); ns = len(sk.spacers)
    bn = ['β%d' % j for j in range(nb)]; sn = ['σ%d' % j for j in range(ns)]
    # word definition, left-associated over the slots
    parts = []; bi = si = 0; slotname = []
    for t in sk.slots:
        if t[0] == 'S': parts.append(sn[si]); slotname.append(sn[si]); si += 1
        else:
            parts.append('wpow %s (%d * a + %d)' % (bn[bi], t[2], t[3])); slotname.append(bn[bi]); bi += 1
    wordbody = ' ++ '.join(parts)
    vlist = ' '.join(str(v) for v in sk.vars)
    args_words = ' '.join(bn + sn)
    # substitution: the variables at a generic (X, Y)
    def subst(XY):
        X, Y = XY
        sub = ['(%s ^ (p * a))' % X, '(%s ^ (q * a))' % Y, '(%s ^ p)' % X, '(%s ^ q)' % Y]
        sub += ['(S %s %s %s)' % (X, Y, b) for b in bn]
        for sj in sn:
            sub += ['(S %s %s %s)' % (X, Y, sj), '(%s ^ %s.sum)' % (X, sj), '(%s ^ %s.length)' % (Y, sj)]
        return ' '.join(sub)
    hyps = ' '.join('(h%ds : %s.sum = %d * p) (h%dl : %s.length = %d * q)' %
                    (j, bn[j], sk.slots[sk.blocks[j]][1], j, bn[j], sk.slots[sk.blocks[j]][1]) for j in range(nb))
    hnames = ' '.join('h%ds h%dl' % (j, j) for j in range(nb))
    hsimp = ', '.join('h%ds, h%dl' % (j, j) for j in range(nb))
    Lk = sk.Lk
    mu_lean = 'X ^ (%d * p) - Y ^ (%d * q)' % (Lk, Lk)
    # coefficients for the linear combination: S(word) = sum_i Y^{len after} X^{sum before} S(seg_i)
    lens, sums = [], []
    bi = 0
    for t, nm in zip(sk.slots, slotname):
        if t[0] == 'S':
            lens.append('%s.length' % nm); sums.append('%s.sum' % nm)
        else:
            k, m, c = t[1], t[2], t[3]
            lens.append('((%d * a + %d) * (%d * q))' % (m, c, k)); sums.append('((%d * a + %d) * (%d * p))' % (m, c, k))
    lc_terms = []
    bi = 0
    for idx, (t, nm) in enumerate(zip(sk.slots, slotname)):
        if t[0] != 'B': continue
        after = ' + '.join(lens[idx + 1:]) or '0'; before = ' + '.join(sums[:idx]) or '0'
        kk = t[1]; r = Lk // kk
        others = '(' + ' + '.join('X ^ (%d * p) * Y ^ (%d * q)' % (kk * j, kk * (r - 1 - j)) for j in range(r)) + ')'
        lc_terms.append('(%s * Y ^ (%s) * X ^ (%s)) * r%d' % (others, after, before, bi)); bi += 1
    lc = ' + '.join(lc_terms)
    rels = '\n'.join(
        '  have r%d := wpow_rel X Y %s (%d * a + %d)\n  rw [h%ds, h%dl] at r%d\n'
        '  have d%d : D X Y %s = X ^ (%d * p) - Y ^ (%d * q) := by simp [D, h%ds, h%dl]\n  rw [d%d] at r%d'
        % (j, bn[j], sk.slots[sk.blocks[j]][2], sk.slots[sk.blocks[j]][3], j, j, j,
           j, bn[j], sk.slots[sk.blocks[j]][1], sk.slots[sk.blocks[j]][1], j, j, j, j) for j in range(nb))
    drw = ', '.join('d%d' % j for j in range(nb))
    # exponents of s^e * mono at (2,3)
    mono = cert['mono']; e = cert['e']
    two_exp = []; three_exp = ['q * a * %d' % e]
    for fac, ex in sp.factor_list(mono)[1] if mono != 1 else []:
        if fac == sk.P: two_exp.append('p * %d' % ex)
        elif fac == sk.Q: three_exp.append('q * %d' % ex)
        else:
            nm = str(fac); j = int(nm[2:]); w = sn[j]
            (two_exp if nm.startswith('Ps') else three_exp).append('%s.%s * %d' % (w, 'sum' if nm.startswith('Ps') else 'length', ex))
    u23 = cert['u23']
    e2 = sp.multiplicity(2, u23) if u23 > 1 else 0; e3 = sp.multiplicity(3, u23) if u23 > 1 else 0
    if e2: two_exp.append(str(e2))
    if e3: three_exp.append(str(e3))
    two_exp = ' + '.join(two_exp) or '0'; three_exp = ' + '.join(three_exp)
    data23 = subst(('(2 : ℤ)', '(3 : ℤ)')).replace('(S (2 : ℤ) (3 : ℤ) ', '(Sz ')
    # D at (2,3) as a difference of exponentials in a, for finiteness
    E0 = ' + '.join(['%s.sum' % w for w in sn] + ['%d * %d * p' % (t[1], t[3]) for t in sk.slots if t[0] == 'B']) or '0'
    O0 = ' + '.join(['%s.length' % w for w in sn] + ['%d * %d * q' % (t[1], t[3]) for t in sk.slots if t[0] == 'B']) or '0'
    N = sk.N
    dD, nD = lean_def('Du', sk.D, vlist, '`D` in the universal data.')
    dG, nG = lean_def('Gu', sk.G, vlist, '`(∏ D(βᵢ)) · S` in the universal data.')
    dR, nR = lean_def('Rp', cert['Rp'], vlist, "The ceiling polynomial `R'`.")
    dA, nA = lean_def('Au', cert['A'], vlist)
    dB, nB = lean_def('Bu', cert['B'], vlist)
    defs = '\n\n'.join([dD, dG, dR, dA, dB])
    unf = ' '.join(nA + nD + nB + nG + nR); unfD = ' '.join(nD); unfG = ' '.join(nG)
    txt = f'''import Syracuse.Approaches.R1.Skeleton

/-!
# Skeleton `{shape}` (generated by `skeleton.py compile`)

Uniform in the words: blocks `{', '.join(bn)}` with `|βᵢ| = kᵢ p`, `len βᵢ = kᵢ q`; spacers
`{', '.join(sn)}` arbitrary. Degree `N = {N}`. Every cycle member `W(a)` satisfies
`D(W(a)) ∣ {cert['c']} · R'(data)` (`ceiling`), and if that number is nonzero only finitely many `a`
give cycles (`finite`). `R'` is the resultant of `D` and `(∏ D(βᵢ)) S` in `[2^{{pa}} : 3^{{qa}}]`
with its `6`-unit factors removed.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 40000000
set_option maxRecDepth 20000

namespace Syracuse.R1.Skel.{name}

open Syracuse Syracuse.CocycleCombine Filter

/-- The family member. -/
def word ({args_words} : Word) (a : ℕ) : Word := {wordbody}

section Ring
variable {{R : Type*}} [CommRing R]

{defs}

/-- **Universal certificate** (`ring`). -/
theorem certificate ({vlist} : R) :
    ss ^ {e} * ({lean_expr(cert['mono'] * cert['u23'])}) * ({cert['c']} * Rp {vlist}) =
      Au {vlist} * Du {vlist} + Bu {vlist} * Gu {vlist} := by
  unfold {unf}; ring

variable (X Y : R) (p q a : ℕ) ({args_words} : Word)

theorem closedD {hyps} :
    D X Y (word {args_words} a) = Du {subst(('X', 'Y'))} := by
  simp only [word, D, List.sum_append, List.length_append, wpow_sum, wpow_length, {hsimp}]
  unfold {unfD}; ring

theorem closedS {hyps} :
    ({mu_lean}) * S X Y (word {args_words} a) = Gu {subst(('X', 'Y'))} := by
{rels}
  simp only [word, S_append, List.sum_append, List.length_append, wpow_sum, wpow_length, {hsimp}]
  unfold {unfG}
  linear_combination {lc}

end Ring

/-- **Ceiling, uniform in the words.** -/
theorem ceiling {{p q : ℕ}} {{{args_words} : Word}} (a : ℕ) {hyps}
    (hpos : (word {args_words} a).Pos) (hc : IsCycleWord (word {args_words} a)) :
    Dz (word {args_words} a) ∣ {cert['c']} * Rp {data23} := by
  obtain ⟨hne, hdvd⟩ := hc
  have hD := closedD (2 : ℤ) 3 p q a {args_words} {hnames}
  have hS := closedS (2 : ℤ) 3 p q a {args_words} {hnames}
  have hcert := certificate {data23}
  have hG : Dz (word {args_words} a) ∣ Gu {data23} := by
    rw [← hS]; exact dvd_mul_of_dvd_right hdvd _
  have hDu : Dz (word {args_words} a) ∣ Du {data23} := by rw [Dz, ← hD]
  have h6 : Dz (word {args_words} a) ∣ 2 ^ ({two_exp}) * 3 ^ ({three_exp}) * ({cert['c']} * Rp {data23}) := by
    have : (2 : ℤ) ^ ({two_exp}) * 3 ^ ({three_exp}) * ({cert['c']} * Rp {data23}) =
        Au {data23} * Du {data23} + Bu {data23} * Gu {data23} := by
      rw [← hcert]; ring
    rw [this]; exact dvd_add (dvd_mul_of_dvd_right hDu _) (dvd_mul_of_dvd_right hG _)
  exact dvd_of_isCoprime_six_of_dvd (cop6 hpos hne) _ _ h6

/-- **Finiteness, uniform in the words**, whenever the ceiling is nonzero. -/
theorem finite {{p q : ℕ}} {{{args_words} : Word}} {hyps} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpos : ∀ a, (word {args_words} a).Pos) (hR : {cert['c']} * Rp {data23} ≠ 0) :
    {{a | IsCycleWord (word {args_words} a)}}.Finite := by
  apply finite_of_ceiling (c := {cert['c']} * Rp {data23}) hR (E₀ := {E0}) (o₀ := {O0})
    (α := p * {N}) (β := q * {N}) (by omega) (by omega)
  · intro a
    simp only [Dz, word, D, List.sum_append, List.length_append, wpow_sum, wpow_length, {hsimp}]
    ring
  · intro a hc
    exact ceiling a {hnames} (hpos a) hc

end Syracuse.R1.Skel.{name}
'''
    open(out, 'w').write(txt)
    print('wrote', out)

if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'show':
        sk = Skel(sys.argv[2]); c = sk.certificate()
        print('N =', sk.N); print('D =', sk.D); print('G =', sp.factor(sk.G))
        print('Res =', sp.factor(c['R'])); print("ceiling = %s * (%s)" % (c['c'], sp.factor(c['Rp'])))
    elif cmd == 'check':
        check(sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 200)
    elif cmd == 'compile':
        emit(sys.argv[2], sys.argv[3], sys.argv[4])
