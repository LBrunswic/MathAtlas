# polynomial-root

## Idea

Abstract away the cocycle/Collatz viewpoint and study the underlying algebra directly. On the
free group $F_2=\langle u,v\rangle$ take the universal character $\chi\colon F_2\to
\mathbb{Z}[X^{\pm1},Y^{\pm1}]$, $\chi(u)=X$, $\chi(v)=Y$, and define the **word cocycle**
$$ S \;=\; \chi\circ\partial_u \colon \mathbb{Z}[F_2]\to \mathbb{Z}[X^{\pm1},Y^{\pm1}], $$
where $\partial_u$ is the Fox derivative with respect to $u$. The **type** of a word is
$(E,o)$ with $E=e_u(w)+e_v(w)=|w|$ and $o=e_u(w)$, so $\chi(w)=X^oY^{E-o}$.

Reduce $S(w)$ modulo the closure ideal $(1-\chi(w))$ and reparametrise the monomial lattice:
with $d=\gcd(E,o)$ and $(o,E-o)=d\,(o',m')$ primitive, set $s=X^{o'}Y^{m'}$ (so $\chi(w)=s^d$)
and a complementary $t=X^aY^b$ ($o'b-m'a=1$, normalised to $t=Y\,X^{*}Y^{*}$). Then
$$ \mathbb{Z}[X^{\pm1},Y^{\pm1}]/(1-\chi(w)) \;\cong\; R_d:=\mathbb{Z}[t,t^{-1},s]/(s^d-1). $$
Every word lands as a Laurent polynomial in $R_d$. **The approach is to study, systematically
and across words, the roots, factorisations, Galois groups and Mahler measures of these
polynomials** (specialise $s\mapsto\zeta$ over the $d$-th roots of unity to get genuine
one-variable polynomials over $\mathbb{Z}[\zeta_d]$).

The self-contained construction is in [`report.tex`](report.tex) / `report.pdf` (§1), and §2
catalogues the coprime case $\gcd(E,o)=1$ (then $d=1$, $R_1=\mathbb{Z}[t,t^{-1}]$): all $1233$
classes with $E+o\le 20$, generated and cross-checked by [`gen_table.py`](gen_table.py), full
data in [`coprime_catalogue.csv`](coprime_catalogue.csv). Early payoff: the smallest Mahler
measure $>1$ that occurs is **Lehmer's number** $1.17628\ldots$, realised by a short word of
type $(12,7)$ — the construction surfaces the deepest known small-Mahler object on its own.

## Why it might work

1. **It is the right invariant object.** By Prop. 1.8 of the report, the class of $S(w)$ in
   $\mathbb{Z}[X^{\pm1},Y^{\pm1}]/(1-\chi(w))$ depends only on the conjugacy class of $w$, up
   to a monomial unit. So a *cyclic word* (= a potential cycle) is faithfully an element of
   $R_d$ up to monomials — exactly the data whose arithmetic (roots on the torus, Mahler
   measure, splitting field) is monomial-invariant.
2. **It separates the algebra from the $2$–$3$ arithmetic.** Specialising $(X,Y)\mapsto(2,3)$
   recovers the integer cocycle of [`cocycle-combine`](../cocycle-combine/RATIONALE.md), where
   $S(w)/(\chi(w)-1)$ is the cycle's rational fixed point. Cyclotomic factors and Mahler
   measure $1$ are precisely what force the arithmetic ceilings there; keeping $(X,Y)$ formal
   lets us *classify* which words are cyclotomic before any transcendence input.
3. **It is computable and stratified.** $S(w)$ has exactly $o$ monomials; factorisation,
   roots, Galois groups and Mahler measure are mechanical (sympy). The natural stratification
   is by type $(E,o)$ and by $d=\gcd(E,o)$, giving a concrete frontier (Mahler-$1$ vs
   Mahler-$\gt 1$) to push outward word by word.

## Known prior art / why it isn't obviously dead

- **Fox calculus** (Fox 1953; Crowell–Fox): $S=\chi\circ\partial_u$ is a genuine $1$-cocycle on
  the free group — rigorous here, unlike the cautious "dictionary" framing in
  [`cocycle-combine/structure`](../cocycle-combine/structure/structure.md), because $F_2$ is
  free. The reparametrisation to $R_d=\mathbb{Z}[t^{\pm1},s]/(s^d-1)$ and the systematic
  root/Galois study **do not appear** in the existing notes; this is the new content.
- **cocycle-combine** has the same functional in gap-word form with the opposite role
  assignment ($X\leftrightarrow 2$, $Y\leftrightarrow 3$) and certified identities C1–C9; its
  §8 already *observes* (uncertified) that structured cores are Mahler-$1$ (cyclotomic). This
  approach turns that observation into the organising question.
- **Cyclotomic/Alexander–Mahler machinery** (Silver–Williams; Lehmer's problem; Bang–Zsygmondy
  for primitive divisors of $\Phi_n(2)$) is the toolkit for the Mahler-$\gt 1$ regime once
  words leave the cyclotomic frontier at $E+o\ge 7$.
- Not obviously dead: the construction is exact and invariant, the small-word table is fully
  cyclotomic (machine-verified), and there is a sharp, concrete next target (type $(4,3)$).
  The honest barrier inherited from `cocycle-combine` remains — on a cycle the gcd equals
  $|2^E-3^o|$, so the algebra can only *re-express* a size bound, not beat transcendence
  theory for free. The bet is that the root/Galois classification organises this cheaply.
