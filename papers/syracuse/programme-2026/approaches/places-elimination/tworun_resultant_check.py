import sympy as sp
from math import gcd
X,Y,u,v=sp.symbols('X Y u v')
# blocks: ('run',d,m) = d^(m*a) ; ('e',e) = single gap
def sym(blocks):
    S=sp.Integer(0); L=sp.Integer(1); Xs=sp.Integer(1)   # S, Y^len, X^sum of word so far (word = prefix)
    # build right-to-left: S(b w) = Ylen(w) S(b) + Xsum(b) S(w)
    Sw=sp.Integer(0); Yw=sp.Integer(1); Xw=sp.Integer(1)
    for b in reversed(blocks):
        if b[0]=='run':
            d,m=b[1],b[2]; Sb=(v**m-u**m)/(X**d-Y); Yb=u**m; Xb=v**m
        else:
            Sb=sp.Integer(1); Yb=Y; Xb=X**b[1]
        Sw=Yw*Sb+Xb*Sw; Yw=Yb*Yw; Xw=Xb*Xw
    return sp.cancel(Sw), Xw-Yw
def word(blocks,a):
    w=[]
    for b in blocks: w+= [b[1]]*(b[2]*a) if b[0]=='run' else [b[1]]
    return w
def SD(w):
    o=len(w); E=sum(w); e=0; S=0
    for k,d in enumerate(w): S+=2**e*3**(o-1-k); e+=d
    return S,2**E-3**o
def sixfree(n):
    n=abs(n)
    for p in (2,3):
        while n and n%p==0: n//=p
    return n
for (d,e1,e2) in [(1,2,3),(2,1,3),(1,3,2),(2,3,1),(3,1,2)]:
    B=[('run',d,1),('e',e1),('run',d,1),('e',e2),('run',d,1)]
    S,D=sym(B)
    num,den=sp.fraction(sp.together(S))
    F=sp.Poly(sp.expand(D),u,v); G=sp.Poly(sp.expand(num),u,v)
    R=sp.resultant(sp.expand(D).subs(v,1),sp.expand(num).subs(v,1),u)
    R=sp.factor(R); R23=int(R.subs({X:2,Y:3}))
    ok=True; gs=[]
    for a in range(1,26):
        Si,Di=SD(word(B,a)); g=sixfree(gcd(Si,Di)); gs.append(g)
        if R23!=0 and R23%g!=0: ok=False
    print((d,e1,e2),'deg',F.total_degree(),G.total_degree(),'sixfree Res(2,3)=',sixfree(R23),'gcd|Res for a<=25:',ok,'max gcd',max(gs),'|D| at a=25 ~ 10^%d'%len(str(abs(SD(word(B,25))[1]))))
