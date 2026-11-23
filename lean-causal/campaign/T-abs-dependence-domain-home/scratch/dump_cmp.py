import sys
def load(p):
    d={}
    dup=0
    for l in open(p,encoding="utf-8"):
        f=l.rstrip("\n").split("\t")
        if f[0] in d: dup+=1
        d.setdefault(f[0],[]).append(f)
    return d,dup
a,da=load(sys.argv[1]); b,db=load(sys.argv[2])
print("entries", sum(len(v) for v in a.values()), sum(len(v) for v in b.values()), "names", len(a), len(b), "dups", da, db)
print("removed:", sorted(set(a)-set(b)))
print("added:", sorted(set(b)-set(a)))
FIELDS=["name","module","kind","levels","typehash","telescope","valuehash","red","prot","nc","internal"]
moved=[]; diffs=[]
for n in sorted(set(a)&set(b)):
    ra=sorted(a[n]); rb=sorted(b[n])
    ma={r[1] for r in ra}; mb={r[1] for r in rb}
    if ma!=mb: moved.append((n, sorted(ma), sorted(mb)))
    # compare fields other than module
    fa=sorted(tuple(r[2:]) for r in ra); fb=sorted(tuple(r[2:]) for r in rb)
    if fa!=fb:
        for x,y in zip(fa,fb):
            for i,(u,v) in enumerate(zip(x,y)):
                if u!=v: diffs.append((n, FIELDS[i+2], u, v))
        if len(fa)!=len(fb): diffs.append((n,"count",len(fa),len(fb)))
print("moved module:", len(moved))
for m in moved: print("  ", m)
print("field diffs:", len(diffs))
for d in diffs: print("  ", d)
