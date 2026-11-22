#!/usr/bin/env python3
"""Chart of pattern intersections for Syracuse gap words.

Every positive cyclic gap word (necklace) up to a length bound is tested against six pattern
classes. Membership means: some rotation of the word has the class's shape, with growing exponents
>= 2 and total fixed material (letters of all base words and spacers) at most BUDGET.

  A  w^a w'              one growing block                        -> R1/WPow, decideR1
  B  skeleton            >= 2 blocks, one shared exponent a,       -> R1/Skel, R1 classification
                         equal block slopes |beta|/len beta
  C  tower (depth 2)     (u^a v)^b y, v != []                     -> R1/Nested, R1/Tower
  D  two exponents       u^a x v^b y, a != b, u, v primitive      -> R1/TwoExp (u, v on the same side)
     (same side)         and not powers of a common word
  X  two exponents       the same shape, u and v straddling       -> R1/Straddle (conditional on
     (straddling)        log2 3                                      Matveev), decide_twoexp.py
  E  few descents        at most 2 gaps >= 2 (m-cycle, m <= 2)    -> Steiner / Simons-de Weger
  F  balanced            Christoffel-type balanced words          -> Knight (Christoffel.lean)

Output: JSON with per-region counts and shortest witnesses (with the decomposition found).
"""
import itertools, json, sys
from fractions import Fraction

BUDGET = int(sys.argv[1]) if len(sys.argv) > 1 else 4
LMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 10
GMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 3
CLASSES = ['A', 'B', 'C', 'D', 'X', 'E', 'F']
NAMES = {'A': "w^a w'", 'B': 'skeleton (>=2 blocks, one exponent)', 'C': "tower (u^a v)^b y",
         'D': "u^a x v^b y, same side", 'X': "u^a x v^b y, straddling", 'E': 'few descents (m <= 2)', 'F': 'balanced (Christoffel)'}

def rotations(w):
    return [tuple(w[i:] + w[:i]) for i in range(len(w))]

def canon(w):
    return min(rotations(list(w)))

def primitive(u):
    n = len(u)
    return all(not (n % d == 0 and u == u[:d] * (n // d)) for d in range(1, n))

def SD(w):
    o, E, e, S = len(w), sum(w), 0, 0
    for k, d in enumerate(w):
        S += 2 ** e * 3 ** (o - 1 - k); e += d
    return S, 2 ** E - 3 ** o

def fmt(parts):
    out = []
    for p in parts:
        if isinstance(p, tuple) and len(p) == 3 and isinstance(p[0], str):
            body = ','.join(map(str, p[1]))
            out.append('(%s)^%s' % (body, p[2]) if len(p[1]) > 1 else '%s^%s' % (body, p[2]))
        elif p:
            out.append(' '.join(map(str, p)))
    return ' '.join(out)

def is_pow_prefix(r, u, a):
    return tuple(r[:len(u) * a]) == tuple(u) * a

def mem_A(w):
    for r in rotations(w):
        n = len(r)
        for lu in range(1, BUDGET + 1):
            u = r[:lu]
            if not primitive(list(u)): continue
            a = 1
            while (a + 1) * lu <= n and is_pow_prefix(r, u, a + 1): a += 1
            if a >= 2:
                v = r[a * lu:]
                if lu + len(v) <= BUDGET:
                    return fmt([('pow', u, a), v])
    return None

def slope(u): return Fraction(sum(u), len(u))

def mem_B(w):
    # s0 b1^a s1 b2^a s2 with two blocks, or three blocks with spacers, all blocks equal slope
    n = len(w)
    for r in rotations(w):
        for a in range(2, n // 2 + 1):
            for l1 in range(1, BUDGET):
                for l2 in range(1, BUDGET - l1 + 1):
                    rest = BUDGET - l1 - l2
                    if a * (l1 + l2) > n: continue
                    for s0 in range(0, rest + 1):
                        for s1 in range(0, rest - s0 + 1):
                            s2 = n - s0 - s1 - a * (l1 + l2)
                            if s2 < 0 or s0 + s1 + s2 > rest: continue
                            i = s0; b1 = r[i:i + l1]
                            if not primitive(list(b1)): continue
                            if not is_pow_prefix(r[i:], b1, a): continue
                            i += a * l1; S1 = r[i:i + s1]; i += s1
                            b2 = r[i:i + l2]
                            if not primitive(list(b2)): continue
                            if not is_pow_prefix(r[i:], b2, a): continue
                            if slope(b1) != slope(b2): continue
                            if b1 == b2 and s1 == 0: continue  # that is just b1^{2a}
                            return fmt([r[:s0], ('pow', b1, a), S1, ('pow', b2, a), r[n - s2:]])
    return None

def mem_C(w):
    n = len(w)
    for r in rotations(w):
        for lu in range(1, BUDGET):
            for lv in range(1, BUDGET - lu + 1):
                for a in range(2, n):
                    blk = lu * a + lv
                    if 2 * blk > n: break
                    u = r[:lu]
                    if not is_pow_prefix(r, u, a): continue
                    v = r[lu * a:lu * a + lv]
                    unit = tuple(u) * a + tuple(v)
                    if not primitive(list(u)) or not primitive(list(unit)): continue
                    b = 1
                    while (b + 1) * blk <= n and tuple(r[:(b + 1) * blk]) == unit * (b + 1): b += 1
                    if b >= 2:
                        y = r[b * blk:]
                        if lu + lv + len(y) <= BUDGET:
                            return '(%s %s)^%d %s' % (fmt([('pow', u, a)]), ' '.join(map(str, v)), b, ' '.join(map(str, y)))
    return None

def mem_twoexp(w, want_same):
    n = len(w)
    for r in rotations(w):
        for lu in range(1, BUDGET):
            for lv in range(1, BUDGET - lu + 1):
                for lx in range(0, BUDGET - lu - lv + 1):
                    u = r[:lu]
                    if not primitive(list(u)): continue
                    a = 1
                    while (a + 1) * lu <= n and is_pow_prefix(r, u, a + 1): a += 1
                    for aa in range(2, a + 1):
                        i = aa * lu; x = r[i:i + lx]; i += lx
                        v = r[i:i + lv]
                        if len(v) < lv or not primitive(list(v)) or v == u: continue
                        b = 1
                        while i + (b + 1) * lv <= n and is_pow_prefix(r[i:], v, b + 1): b += 1
                        for bb in range(2, b + 1):
                            if bb == aa: continue
                            y = r[i + bb * lv:]
                            if lu + lv + lx + len(y) <= BUDGET:
                                same = (2 ** sum(u) > 3 ** len(u)) == (2 ** sum(v) > 3 ** len(v))
                                if same == want_same:
                                    return fmt([('pow', u, aa), x, ('pow', v, bb), y])
    return None

def mem_E(w):
    m = sum(1 for d in w if d >= 2)
    return ('m = %d' % m) if m <= 2 else None

def mem_F(w):
    n = len(w); ww = list(w) * 2
    for L in range(1, n):
        sums = {sum(ww[i:i + L]) for i in range(n)}
        if max(sums) - min(sums) > 1: return None
    return 'balanced'

TESTS = {'A': mem_A, 'B': mem_B, 'C': mem_C, 'D': lambda w: mem_twoexp(w, True), 'X': lambda w: mem_twoexp(w, False), 'E': mem_E, 'F': mem_F}

def necklaces():
    seen = set()
    for L in range(2, LMAX + 1):
        for w in itertools.product(range(1, GMAX + 1), repeat=L):
            c = canon(w)
            if c in seen: continue
            seen.add(c)
            if not primitive(list(c)): continue   # powers of shorter words: skip (same cycle)
            yield list(c)

regions = {}
for w in necklaces():
    mem = {k: TESTS[k](w) for k in CLASSES}
    key = ''.join(k for k in CLASSES if mem[k])
    S, D = SD(w)
    rec = {'w': w, 'how': {k: v for k, v in mem.items() if v}, 'cycle': D != 0 and S % D == 0}
    regions.setdefault(key, []).append(rec)
out = {'budget': BUDGET, 'lmax': LMAX, 'gmax': GMAX, 'names': NAMES, 'regions': {}}
for key, recs in regions.items():
    recs.sort(key=lambda r: (len(r['w']), r['w']))
    out['regions'][key] = {'count': len(recs), 'witnesses': recs[:4],
                           'cycles': [r['w'] for r in recs if r['cycle']][:4]}
json.dump(out, open('chart_data.json', 'w'), indent=1)
tot = sum(v['count'] for v in out['regions'].values())
print('primitive necklaces:', tot)
for key in sorted(out['regions'], key=lambda k: -out['regions'][k]['count']):
    v = out['regions'][key]
    w0 = v['witnesses'][0]
    print('%-7s %6d  e.g. %-24s %s %s' % (key or '(none)', v['count'], ','.join(map(str, w0['w'])),
          '; '.join('%s: %s' % kv for kv in w0['how'].items()), ' CYCLES:' + str(v['cycles']) if v['cycles'] else ''))
