#!/usr/bin/env python3
"""Decide the two-exponent family u^a x v^b y (a, b >= 0), on either side of log2 3.

This is the effective form of Lean `R1/Straddle.lean` (`twoExp_cycles_of_matveev`). It is complete
**conditional on Matveev's theorem** (`CycleGcd.MatveevTwoThree c0`), which is published.

  1. Degenerate loci.  C(u, x v^b y) = 0 is one value of b, or every b (`twoExp_zero_u`); there W
     is a cycle iff u is (`twoExp_degenerate_u`).  The same holds for v.
  2. Off the loci, the two ceilings (`twoExp_ceiling_real`, sharpened by 1/|D(v)|) give
        |D(W)| <= k_u G_v^b,   |D(W)| <= k_v G_u^a,   G = max(2^{|.|}, 3^{len .}).
     Since max(2^E, 3^O)^2 >= 2^{a+b} G_u^a G_v^b, either
        |Lam| >= 1 and a + b <= N1 = 2 + log2(k_u k_v), or
        |Lam| <  1 and ||O l|| <= |Lam| <= C 2^{-(a+b)/2} <= C 2^{-(O-mu)/(2 lam)},
     where Lam = E - O l, l = log2 3, C = (4/ln 2) sqrt(k_u k_v), lam = max(len u, len v), and
     mu = len x + len y.
  3. Matveev gives O <= O_max.  For q_k <= O < q_{k+1} (convergents of l),
     ||O l|| >= ||q_k l|| (best approximation), so the block is excluded once
     ||q_k l|| > C 2^{-(q_k - mu)/(2 lam)}.  The surviving O are < O_small.
  4. Enumerate exactly every (a, b) with a + b <= N1 or O(a, b) < O_small.

Usage:  decide_twoexp.py U X V Y      (comma lists; X, Y may be '' or '-')
        decide_twoexp.py --selftest [N]   random families checked against brute force
"""
import sys, math, random
from math import log2
import mpmath as mp

mp.mp.dps = 80
ELL = mp.log(3) / mp.log(2)
C0 = 1.4 * 30 ** 5 * 2 ** 4.5 * math.log(2) * math.log(3)   # Matveev, two logarithms


def SD(w):
    o, E, e, S = len(w), sum(w), 0, 0
    for k, d in enumerate(w):
        S += 2 ** e * 3 ** (o - 1 - k); e += d
    return S, 2 ** E - 3 ** o


def wedge(p, q):
    Sp, Dp = SD(p); Sq, Dq = SD(q)
    return Dp * Sq - Dq * Sp


def cycle(w):
    S, D = SD(w)
    return len(w) > 0 and S % D == 0


def coeffs(u, x, v, y):
    """tα, tβ of Lean `twoExp_linear`: D(v) C(u, x v^b y) = tα 2^{b|v|} - tβ 3^{b len v}."""
    Su, Du = SD(u); Sv, Dv = SD(v); Sx, _ = SD(x); Sy, _ = SD(y)
    ta = Du * 2 ** sum(x) * (3 ** len(y) * Sv + Sy * Dv) - Dv * Su * 2 ** (sum(x) + sum(y))
    tb = (Du * 2 ** sum(x) * 3 ** len(y) * Sv - Du * 3 ** len(y) * Sx * Dv
          - Dv * Su * 3 ** (len(x) + len(y)))
    return ta, tb


def v2(n):
    n = abs(n); k = 0
    while n % 2 == 0: n //= 2; k += 1
    return k


def zero_locus(ta, tb, w):
    """{b | ta 2^{b|w|} = tb 3^{b len w}}: 'all', a one-element list, or []."""
    if ta == 0 and tb == 0: return 'all'
    if ta == 0 or tb == 0: return []
    d = v2(tb) - v2(ta)
    if d < 0 or d % sum(w): return []
    b = d // sum(w)
    return [b] if ta * 2 ** (b * sum(w)) == tb * 3 ** (b * len(w)) else []


def word(u, x, v, y, a, b):
    return u * a + x + v * b + y


def convergents(qmax):
    """(p_k, q_k) of l = log2 3 until q_k > qmax."""
    out, h0, h1, k0, k1, r = [], 0, 1, 1, 0, ELL
    while True:
        an = int(mp.floor(r))
        h0, h1 = h1, an * h1 + h0
        k0, k1 = k1, an * k1 + k0
        out.append((h1, k1))
        if k1 > qmax: return out
        r = 1 / (r - an)


def decide(u, x, v, y, verbose=False):
    assert u and v and all(d >= 1 for d in u + x + v + y)
    _, Du = SD(u); _, Dv = SD(v)
    ta_u, tb_u = coeffs(u, x, v, y)          # locus in b
    ta_v, tb_v = coeffs(v, y, u, x)          # locus in a
    Zb, Za = zero_locus(ta_u, tb_u, v), zero_locus(ta_v, tb_v, u)
    # log2 k_u, log2 k_v computed on the integers (no float overflow)
    lku = log2(abs(ta_u) + abs(tb_u)) - log2(abs(Dv)) if (ta_u or tb_u) else None
    lkv = log2(abs(ta_v) + abs(tb_v)) - log2(abs(Du)) if (ta_v or tb_v) else None
    lam, mu = max(len(u), len(v)), len(x) + len(y)
    res = dict(locus_b=Zb, locus_a=Za, u_cycle=cycle(u), v_cycle=cycle(v))
    if Za == 'all' or Zb == 'all':
        res['finite'] = None          # every pair degenerate on one side
        return res
    N1 = max(0, math.floor(2 + lku + lkv + 1e-9))
    logC = math.log2(4 / math.log(2)) + 0.5 * (lku + lkv) + 1e-9
    # Matveev: |Lam| ln2 > exp(-c0 (1 + ln E)), E < 2 O + 1 when |Lam| < 1
    def matveev_ok(O):
        return (-C0 * (1 + math.log(2 * O + 1))) / math.log(2) - math.log2(math.log(2)) < \
            logC - (O - mu) / (2 * lam)
    O_max = 1
    while matveev_ok(O_max): O_max *= 2
    lo, hi = O_max // 2, O_max                         # last O where a cycle is not excluded
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        lo, hi = (mid, hi) if matveev_ok(mid) else (lo, mid)
    O_max = hi
    cv = convergents(O_max)
    O_small = 1
    for k, (p, q) in enumerate(cv):
        if q > O_max: break
        q_next = cv[k + 1][1] if k + 1 < len(cv) else O_max + 1
        delta = abs(q * ELL - p)
        bound = mp.mpf(2) ** (logC - (q - mu) / (2 * lam))
        if not delta > bound:
            O_small = q_next                              # block [q, q_next) not excluded
    res.update(N1=N1, O_max=O_max, O_small=O_small, n_conv=len(cv))
    cycles = []
    amax = max(N1, O_small // len(u) + 1); bmax = max(N1, O_small // len(v) + 1)
    for a in range(amax + 1):
        for b in range(bmax + 1):
            O = a * len(u) + b * len(v) + mu
            if not (a + b <= N1 or O < O_small): continue
            if a in (Za or []) or b in (Zb or []): continue
            W = word(u, x, v, y, a, b)
            if cycle(W): cycles.append((a, b))
    res['finite'] = cycles
    return res


def brute(u, x, v, y, box):
    _, _ = SD(u), SD(v)
    ta_u, tb_u = coeffs(u, x, v, y); ta_v, tb_v = coeffs(v, y, u, x)
    out = []
    for a in range(box + 1):
        for b in range(box + 1):
            W = word(u, x, v, y, a, b)
            if not W or not cycle(W): continue
            if wedge(u, x + v * b + y) == 0 or wedge(v, y + u * a + x) == 0: continue
            out.append((a, b))
    return out


def selftest(n, box=14, seed=1):
    rng = random.Random(seed)
    bad = 0; tot = 0; side = {'same': 0, 'straddle': 0}
    for _ in range(n):
        rw = lambda lo: [rng.randint(1, 3) for _ in range(rng.randint(lo, 3))]
        u, v, x, y = rw(1), rw(1), rw(0), rw(0)
        r = decide(u, x, v, y)
        if r['finite'] is None: continue
        su = 2 ** sum(u) > 3 ** len(u); sv = 2 ** sum(v) > 3 ** len(v)
        side['same' if su == sv else 'straddle'] += 1
        bf = brute(u, x, v, y, box)
        dec = [p for p in r['finite'] if p[0] <= box and p[1] <= box]
        tot += len(bf)
        for b in range(6):
            assert SD(v)[1] * wedge(u, x + v * b + y) == \
                coeffs(u, x, v, y)[0] * 2 ** (b * sum(v)) - coeffs(u, x, v, y)[1] * 3 ** (b * len(v))
        if sorted(bf) != sorted(dec):
            bad += 1; print('MISMATCH', u, x, v, y, bf, r)
    print(f'selftest: {n} families ({side}), {tot} off-locus cycles in box {box}, mismatches {bad}')
    return bad


def main():
    if sys.argv[1:2] == ['--selftest']:
        sys.exit(1 if selftest(int(sys.argv[2]) if len(sys.argv) > 2 else 200) else 0)
    p = lambda t: [] if t in ('', '-') else [int(c) for c in t.split(',')]
    u, x, v, y = map(p, sys.argv[1:5])
    r = decide(u, x, v, y)
    print(f'family  ({",".join(map(str,u))})^a [{",".join(map(str,x))}] ({",".join(map(str,v))})^b [{",".join(map(str,y))}]')
    print(f'  u cycle word: {r["u_cycle"]}   v cycle word: {r["v_cycle"]}')
    print(f'  locus C(u, x v^b y) = 0 at b in {r["locus_b"]};  C(v, y u^a x) = 0 at a in {r["locus_a"]}')
    if r['finite'] is None:
        print('  a whole side is degenerate: W is a cycle iff u (resp. v) is'); return
    print(f'  N1 = {r["N1"]},  O_max (Matveev) = {r["O_max"]:.3e},  O_small = {r["O_small"]}'
          f'  ({r["n_conv"]} convergents)')
    print(f'  off-locus cycle pairs (a, b): {r["finite"]}')


if __name__ == '__main__':
    main()
