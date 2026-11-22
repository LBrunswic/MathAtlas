#!/usr/bin/env python3
"""Bridge between decide_family.py specs and the Lean decision procedure `Syracuse.R1.decideR1`.

  r1_lean.py lit SPEC           print the Lean `Family` literal for a one-parameter r = 1 SPEC
  r1_lean.py suite N SEED OUT   write a Lean file with N random r = 1 families (`#eval decideR1`)
                                plus a JSON of brute-force cycle sets for a <= 30
  r1_lean.py check OUT.json LEANOUT   compare Lean's printed verdicts with the brute force

SPEC tokens as in decide_family.py:  g:<block>:<m>:<c>   f:<word>
"""
import sys, json, random
from fractions import Fraction
from math import gcd

def parse_word(t): return [int(x) for x in t.split(',') if x]

def parse_spec(spec):
    toks = []
    for t in spec.split():
        k = t.split(':')
        toks.append(('g', parse_word(k[1]), int(k[2]), int(k[3])) if k[0] == 'g' else ('f', parse_word(k[1])))
    return toks

def SD(w):
    o, E, e, S = len(w), sum(w), 0, 0
    for k, d in enumerate(w):
        S += 2 ** e * 3 ** (o - 1 - k); e += d
    return S, 2 ** E - 3 ** o

def word_of(toks, a):
    w = []
    for t in toks:
        w += t[1] * (t[2] * a + t[3]) if t[0] == 'g' else t[1]
    return w

def is_cycle(w):
    if not w: return False
    S, D = SD(w)
    return S % D == 0

def to_lean(toks):
    grows = [t for t in toks if t[0] == 'g']
    if grows:
        lam = Fraction(sum(grows[0][1]), len(grows[0][1]))
        for t in grows:
            assert Fraction(sum(t[1]), len(t[1])) == lam, 'not r = 1: slopes differ'
        p, q = lam.numerator, lam.denominator
    else:
        p, q = 1, 1
    segs = []
    for t in toks:
        if t[0] == 'f':
            segs.append('.fixed [%s]' % ', '.join(map(str, t[1])))
        else:
            k = sum(t[1]) // p
            segs.append('.grow [%s] %d %d %d' % (', '.join(map(str, t[1])), k, t[2], t[3]))
    return '⟨%d, %d, [%s]⟩' % (p, q, ', '.join(segs))

def brute(toks, amax=30):
    return [a for a in range(amax + 1) if is_cycle(word_of(toks, a))]

def random_family(rng):
    # one slope: pick a block, then other growing blocks of the same slope
    base = [rng.randint(1, 3) for _ in range(rng.randint(1, 2))]
    lam = Fraction(sum(base), len(base))
    blocks = [base]
    for _ in range(rng.randint(0, 2)):
        for _try in range(50):
            b = [rng.randint(1, 4) for _ in range(rng.randint(1, 3))]
            if Fraction(sum(b), len(b)) == lam:
                blocks.append(b); break
    toks = []
    for b in blocks:
        if rng.random() < 0.7:
            toks.append(('f', [rng.randint(1, 5) for _ in range(rng.randint(1, 3))]))
        toks.append(('g', b, rng.randint(1, 2), rng.randint(0, 1)))
    if rng.random() < 0.5:
        toks.append(('f', [rng.randint(1, 5) for _ in range(rng.randint(1, 2))]))
    return toks

def spec_str(toks):
    return ' '.join(('g:%s:%d:%d' % (','.join(map(str, t[1])), t[2], t[3])) if t[0] == 'g'
                    else 'f:' + ','.join(map(str, t[1])) for t in toks)

def main():
    cmd = sys.argv[1]
    if cmd == 'lit':
        print(to_lean(parse_spec(sys.argv[2])))
    elif cmd == 'suite':
        n, seed, out = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
        rng = random.Random(seed)
        fams = [random_family(rng) for _ in range(n)]
        # add the named samples
        named = ['g:1:1:0 f:2 g:1:1:0 f:3 g:1:1:0', 'g:3:1:0 f:1 g:3:1:0 f:2 g:3:1:0',
                 'g:1,2:1:0 f:1 g:1,2:2:0 f:4', 'g:2:1:0 f:1 g:2:1:1 f:3', 'g:1,3:1:0 g:2:1:0',
                 'g:1,2:1:0', 'g:2:1:0', 'g:1:1:0', 'g:1:1:0 f:2,1,1,4', 'g:1,1,2:1:0 f:1,1,4']
        fams = [parse_spec(x) for x in named] + fams
        lines = ['import Syracuse.Approaches.R1.Decide', '', 'open Syracuse.R1', '']
        meta = []
        for i, toks in enumerate(fams):
            lines.append('#eval (%d, decideR1 (%s : Family))' % (i, to_lean(toks)))
            meta.append({'i': i, 'spec': spec_str(toks), 'brute': brute(toks)})
        open(out + '.lean', 'w').write('\n'.join(lines) + '\n')
        json.dump(meta, open(out + '.json', 'w'), indent=0)
        print('wrote', out + '.lean', len(fams), 'families')
    elif cmd == 'check':
        meta = json.load(open(sys.argv[2]))
        import re
        out = open(sys.argv[3]).read()
        verd = {}
        for m in re.finditer(r'\((\d+), Syracuse\.R1\.Verdict\.(finite|allFrom) (.*?)\)\s*$', out, re.M):
            verd[int(m.group(1))] = (m.group(2), m.group(3))
        bad = 0
        for e in meta:
            kind, args = verd[e['i']]
            nums = [int(x) for x in re.findall(r'\d+', args)]
            if kind == 'finite':
                lean_set = [a for a in range(31) if a in nums]
            else:
                b, rest = nums[0], nums[1:]
                lean_set = [a for a in range(31) if a >= b or a in rest]
            ok = lean_set == e['brute']
            bad += not ok
            if not ok or e['i'] < 10:
                print('%3d %-45s lean=%s %s  brute(a<=30)=%s %s' % (e['i'], e['spec'], kind, args,
                      e['brute'], 'OK' if ok else 'MISMATCH'))
        print('families:', len(meta), 'mismatches:', bad)

if __name__ == '__main__':
    main()
