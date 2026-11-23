"""kb/0227's pair check. Run from lean-causal/:
    lake env lean campaign/T-abs-curves-free-cauchy/Probe_Binders.lean > /tmp/binders.out 2>&1
    python3 -I campaign/T-abs-curves-free-cauchy/binders_diff.py /tmp/binders.out \
        campaign/T-abs-curves-free-cauchy/binders_pairs.json /tmp/binders_diff.json
prints, per (original, new) pair, the removed and added binders and whether the conclusions agree."""
import json, re, difflib, sys
recs = {}
txt = open(sys.argv[1]).read()
# messages may span lines; each starts with "BINDERS {"
dec = json.JSONDecoder()
for line in txt.split('\n'):
    if line.startswith('BINDERS '):
        j, _ = dec.raw_decode(line[len('BINDERS '):])
        recs[j['name']] = j
pairs = json.load(open(sys.argv[2]))
def norm(t): return re.sub(r'\s+', ' ', t)
out = []
for a, b in pairs:
    A, B = recs[a], recs[b]
    la = [(x[0], x[1], norm(x[2])) for x in A['binders']]
    lb = [(x[0], x[1], norm(x[2])) for x in B['binders']]
    sm = difflib.SequenceMatcher(a=la, b=lb, autojunk=False)
    rem, add = [], []
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op in ('delete', 'replace'): rem += la[i1:i2]
        if op in ('insert', 'replace'): add += lb[j1:j2]
    same = norm(A['concl']) == norm(B['concl'])
    out.append({'orig': a, 'new': b, 'removed': rem, 'added': add, 'concl_equal': same,
                'concl_orig': None if same else A['concl'], 'concl_new': None if same else B['concl']})
    fmt = lambda L: ', '.join(f"{x[0][0]}{x[1]} : {x[2]}{x[0][1]}" for x in L)
    print(f"{a.replace('Causal.','')}  ->  {b.replace('Causal.','')}\n   removed: {fmt(rem)}\n   added:   {fmt(add)}\n   conclusion equal: {same}")
    if not same: print('   ORIG:', A['concl'], '\n   NEW: ', B['concl'])
json.dump(out, open(sys.argv[3], 'w'), indent=1, ensure_ascii=False)
