import json,re,sys,os,glob,tomllib
HERE=os.path.dirname(os.path.abspath(__file__))
ROOT=os.path.dirname(os.path.dirname(HERE))
# Every paper with a generated ledger: hub.toml's order first, then any ledger hub.toml does not
# curate yet (build.py gives it a placeholder card), so a newly counted paper cannot be left out.
_hub=list(tomllib.load(open(os.path.join(HERE,"hub.toml"),"rb"))["paper"])
_led=sorted(os.path.basename(os.path.dirname(os.path.dirname(f))) for f in glob.glob(os.path.join(ROOT,"papers","*","ledger","ledger.json")))
PAPERS=[p for p in _hub if p in _led]+[p for p in _led if p not in _hub]
SPLIT=24
def clean(s):
    s=re.sub(r"\\label\{[^}]*\}","",s); s=re.sub(r"(?m)^\s*%.*$","",s)
    return re.sub(r"\n{3,}","\n\n",s).strip()
def title_of(cmd):
    m=re.match(r"\s*\\(?:sub)?section\*?\{(.*)",cmd)
    t=m[1] if m else cmd
    depth=0;out=""
    for ch in t:
        if ch=="{":depth+=1
        if ch=="}":
            if depth==0:break
            depth-=1
        out+=ch
    out=re.sub(r"\\label\{[^}]*\}","",out)
    out=re.sub(r"~?\\ref\{[^}]*\}","",out)
    out=out.replace("$\\BTZ$","BTZ").replace("$(G,X)$","(G,X)").replace("$","")
    out=re.sub(r"\\(AdS|dS|HS)\b",r"\1",out)   # BBS's text macros in section titles
    out=re.sub(r"\s+"," ",out)
    return out.strip()
data={}
for p in PAPERS:
    L=json.load(open(f"{ROOT}/papers/{p}/ledger/ledger.json"))
    root=L["paper"]["root"]; rows=L["statements"]
    srcs={}; heads={}
    for f in L["paper"]["files"]:
        t=open(os.path.join(root,f),encoding="utf-8",errors="replace").read().split("\n"); srcs[f]=t
        heads[f]=[(i+1,("sec" if re.match(r"\s*\\(section|chapter)",l) else "sub"),title_of(l)) for i,l in enumerate(t) if re.match(r"\s*\\(section|subsection|chapter)\*?\{",l)]
    enddoc={f:next((i+1 for i,l in enumerate(t) if l.strip().startswith("\\end{document}")),10**9) for f,t in srcs.items()}
    def sec_of(r):
        if r["line"]>enddoc[r["file"]]:
            return (10**8,"sec","After \\end{document} (drafts, terminal)"),None
        hs=[h for h in heads.get(r["file"],[]) if h[0]<=r["line"]]
        s=[h for h in hs if h[1]=="sec"]; sb=[h for h in hs if h[1]=="sub"]
        sec=s[-1] if s else (0,"sec",os.path.basename(r["file"]).replace(".tex","").split("_",1)[-1].replace("_"," ").title())
        sub=sb[-1] if sb and sb[-1][0]>sec[0] else None
        return sec,sub
    tmp=[]
    for r in rows:
        sec,sub=sec_of(r); tmp.append((r,sec,sub))
    # count per section
    from collections import Counter,OrderedDict
    cnt=Counter((r["file"],sec[0]) for r,sec,sub in tmp)
    blocks=OrderedDict(); nodes=[]
    for r,sec,sub in tmp:
        key=(r["file"],sec[0]); bid=f"{r['file']}:{sec[0]}"; btitle=sec[2]
        if cnt[key]>SPLIT and sub:
            bid+=f":{sub[0]}"; btitle=f"{sec[2]} › {sub[2]}"
        if bid not in blocks: blocks[bid]={"id":bid,"title":btitle,"order":(r["file"],sec[0],sub[0] if sub and cnt[key]>SPLIT else 0)}
        src=srcs[r["file"]]; a,b=r["tex_span"]; tex=clean("\n".join(src[a-1:b]))
        if len(tex)>1400: tex=tex[:1400]+" …"
        nodes.append({"id":r["label"],"block":bid,"kind":r["kind"],"num":r["number"],"title":r["title"] or "",
            "bucket":r.get("bucket") or "","lean":r.get("lean_proved") or "","nl":r["nl_status"] or "","line":r["line"],
            "deps":[d for d in r["deps"] if d!=r["label"]],"decls":(r.get("decls") or [])[:12],"ndecls":len(r.get("decls") or []),
            "findings":r.get("paper_findings") or [],"notes":(r.get("notes") or "")[:600],"twin":r.get("twin_of") or "","tex":tex})
    ids={n["id"] for n in nodes}
    for n in nodes: n["deps"]=[d for d in n["deps"] if d in ids]
    bl=sorted(blocks.values(),key=lambda b:(PAPERS and str(b["order"][0]),b["order"][1],b["order"][2]))
    for b in bl: del b["order"]
    md=open(f"{ROOT}/papers/{p}/ledger/LEDGER.md",encoding="utf-8").read()
    c=re.search(r"\*\*Closure: (\d+) of (\d+)\.\*\*",md)
    data[p]={"blocks":bl,"nodes":nodes,"closed":int(c[1]),"target":int(c[2])}
    print(p,len(bl),[ (b["title"][:30],sum(1 for n in nodes if n["block"]==b["id"])) for b in bl],file=sys.stderr)
json.dump(data,open(sys.argv[1],"w"),ensure_ascii=False,separators=(",",":"))

# paper macros for MathJax: \newcommand / \renewcommand / \def / \DeclareMathOperator from every legacy file
def braced(s,i):
    assert s[i]=="{"; d=0
    for j in range(i,len(s)):
        if s[j]=="{": d+=1
        elif s[j]=="}":
            d-=1
            if d==0: return s[i+1:j],j+1
    return None,len(s)
for p in PAPERS:
    L=json.load(open(f"{ROOT}/papers/{p}/ledger/ledger.json"))
    root=L["paper"]["root"]; mac={}
    files=set(L["paper"]["files"])
    for dp,_,fs in os.walk(os.path.dirname(root.rstrip("/"))):
        for f in fs:
            if f.endswith((".tex",".sty")): files.add(os.path.join(dp,f))
    for f in sorted(files):
        fp=f if os.path.isabs(f) else os.path.join(root,f)
        try: s=open(fp,encoding="utf-8",errors="replace").read()
        except OSError: continue
        s=re.sub(r"(?m)(?<!\\)%.*$","",s)
        for m in re.finditer(r"\\(?:re)?newcommand\*?\s*\{?\\([A-Za-z]+)\}?\s*(?:\[(\d)\])?\s*(?:\[[^\]]*\])?\s*(?=\{)",s):
            body,_=braced(s,m.end())
            if body is None or len(body)>200 or "\\ensuremath" in body and False: continue
            body=body.replace("\\ensuremath","").replace("\\xspace","")
            mac[m[1]]=[body,int(m[2])] if m[2] else body
        for m in re.finditer(r"\\DeclareMathOperator\*?\s*\{?\\([A-Za-z]+)\}?\s*(?=\{)",s):
            body,_=braced(s,m.end())
            if body is not None: mac[m[1]]="\\operatorname{"+body+"}"
        for m in re.finditer(r"\\def\\([A-Za-z]+)\s*(?=\{)",s):
            body,_=braced(s,m.end())
            if body is not None and len(body)<200: mac.setdefault(m[1],body)
    for bad in ["section","label","ref","cite","emph","textbf","begin","end","item","newline","\\"]:
        mac.pop(bad,None)
    data[p]["macros"]=mac
    print(p,"macros",len(mac),file=sys.stderr)
json.dump(data,open(sys.argv[1],"w"),ensure_ascii=False,separators=(",",":"))
