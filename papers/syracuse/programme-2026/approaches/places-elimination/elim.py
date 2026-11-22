import sympy as sp
X,Y=sp.symbols('X Y')
P={}  # parameter -> (u,t) = (Y^p, X^p)
def coords(p):
    if p not in P: P[p]=sp.symbols(f'u_{p} t_{p}')
    return P[p]
def sym(blocks):
    Sw=sp.Integer(0); Yw=sp.Integer(1); Xw=sp.Integer(1)
    for b in reversed(blocks):
        if b[0]=='run':
            d,p=b[1],b[2]; u,t=coords(p); Sb=(t**d-u)/(X**d-Y); Yb=u; Xb=t**d
        else: Sb=sp.Integer(1); Yb=Y; Xb=X**b[1]
        Sw=Yw*Sb+Xb*Sw; Yw=Yb*Yw; Xw=Xb*Xw
    num,_=sp.fraction(sp.together(sp.cancel(Sw)))
    return sp.expand(num), sp.expand(Xw-Yw)
def elim(name,blocks):
    P.clear(); G,D=sym(blocks)
    params=[s for p in P for s in P[p]]
    z=sp.Symbol('z'); sat=z*sp.Mul(*params)-1   # work in the torus: u,t invertible
    gb=sp.groebner([D,G,sat],z,*params,X,Y,order='lex'); params=params+[z]
    base=[g for g in gb.exprs if not (g.free_symbols & set(params))]
    print(f'{name:28s} params={len(P)}  elimination ideal ∩ Q[X,Y]:', [sp.factor(g) for g in base] or 'ZERO')
elim('d^a e1 d^a e2 d^a (Lean)', [('run',1,'a'),('e',2),('run',1,'a'),('e',3),('run',1,'a')])
elim('1^a 3 2^a  (two gap values)', [('run',1,'a'),('e',3),('run',2,'a')])
elim('1^a 2 1^b 3 (two lengths)', [('run',1,'a'),('e',2),('run',1,'b'),('e',3)])
