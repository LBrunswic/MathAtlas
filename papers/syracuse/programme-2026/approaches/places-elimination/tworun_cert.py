import sympy as sp
P,Q1,Q2,Y,u,v=sp.symbols('P Q1 Q2 Y u v')
D=Q1*Q2*v**3-Y**2*u**3
G=P*Q1*u*v**2+P*Y*u**2*v-Q1*Q2*u*v**2+Q1*Q2*v**3-Q1*Y*u**2*v-Y**2*u**3
f=sp.Poly(D.subs(v,1),u); g=sp.Poly(G.subs(v,1),u)
a=sp.symbols('a0:3'); b=sp.symbols('b0:3')
A=sum(a[i]*u**i for i in range(3)); B=sum(b[i]*u**i for i in range(3))
R=sp.resultant(f.as_expr(),g.as_expr(),u)
eqs=sp.Poly(sp.expand(A*f.as_expr()+B*g.as_expr()-R),u).all_coeffs()
sol=sp.solve(eqs,a+b,dict=True)[0]
Ah=sp.expand(sum(sp.factor(sol[a[i]])*u**i*v**(2-i) for i in range(3)))
Bh=sp.expand(sum(sp.factor(sol[b[i]])*u**i*v**(2-i) for i in range(3)))
print('polynomial?', all(sp.fraction(sp.together(sol[s]))[1]==1 for s in a+b))
chk=sp.expand(Ah*D+Bh*G - v**5*sp.expand(R)); print('identity ok:',chk==0)
Rs=sp.factor(R); print('R =',Rs)
print('A =',Ah); print('B =',Bh)
