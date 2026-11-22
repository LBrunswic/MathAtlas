# Berstel–Reutenauer 2011 — Noncommutative Rational Series

- **Source file:** `sources/[Encyclopedia of Mathematics and its Applications №137] Jean Berstel, Christophe Reutenauer - Noncommutative Rational Series with Applications.pdf`
- **Full citation:** J. Berstel, C. Reutenauer, *Noncommutative Rational Series with Applications*, Encyclopedia of Mathematics and its Applications **137**, Cambridge Univ. Press, 2011.
- **Feeds:** **C10** (and **C1**); the *rank-as-complexity* candidate for thread §8; threads §1, §3.

## What it says (relevant part only)

A formal series $S:A^*\to K$ is **recognizable** iff it has a *linear representation*
$(\lambda,\mu,\gamma)$, $\mu:A^*\to K^{n\times n}$ a monoid morphism, $S(w)=\lambda\,\mu(w)\,\gamma$
(Def. p. 10). **Schützenberger (Thm 7.1, p. 17):** recognizable $=$ rational. The **rank** of $S$ is
$\dim_K(S\circ K\langle A\rangle)$; **Thm 1.6 (Carlyle–Paz/Fliess, p. 31):** rank $=$ rank of the
**Hankel matrix** $H(x,y)=(S,xy)$ $=$ the minimal dimension of a linear representation. **Prop. 2.1
(p. 32):** a representation is *minimal* iff the rows $\{\lambda\mu(w)\}$ span $K^{1\times n}$
(accessible) and the cols $\{\mu(w)\gamma\}$ span $K^{n\times1}$ (co-accessible); minimal
representations are unique up to similarity (**Thm 2.4, p. 33**). **Cor. 3.7 (p. 38):** rank $\ge n$ is
witnessed by a nonzero $n\times n$ Hankel minor. **Cor. 3.5 (p. 38):** a rank-$n$ series obeys a
length-$n$ linear recurrence on coefficients $(S,cw)=\sum_{p\in P}\alpha_{c,p}(S,pw)$. Hadamard products
preserve recognizability (**Thm 5.5, p. 14**). Equality of rational series is decidable (rank-$n$ series
vanishing on words of length $\le n-1$ is $0$). Continuant polynomials and their continued-fraction /
**Wedderburn reversal** identity $p(a_1..a_n)p(a_{n-1}..a_1)=p(a_1..a_{n-1})p(a_n..a_1)$ are in Ch. 10 §2
(p. 174). **No Sturmian/Christoffel/Markoff content** (index pp. 231–236).

## How it connects here

This is the textbook home of **C1/C10**. Our $M(w)=\prod\big(\begin{smallmatrix}Y&0\\1&X^{d}\end{smallmatrix}\big)$
makes $S$ a recognizable series over $K=\mathbb Z[X,Y]$ with the rank-2 representation $\lambda=(0,1)$,
$\gamma=(1,0)^\top$. Prop. 2.1 certifies **minimality directly**: rows $\lambda\mu(\varepsilon)=(0,1)$,
$\lambda\mu(d)=(1,X^d)$ span ($\det=-1$); cols $(1,0)^\top,(Y,1)^\top$ span ($\det=1$) — exactly the two
$\pm1$ determinants in **C10**. So *complexity $=$ rank*, and $S$ has minimal complexity $2$. Tools this
hands the program: (a) **Cor. 3.5** rank-2 recurrence — every $(S,cw)$ is a $2$-term combination of
$(S,w)$ and $(S,d_0w)$, a lever to handle whole word families at once (thread §1); (b) decidability of
$C(u,v)\equiv0$ — the rank-drop / Steiner stratum (§4) is finitely checkable (length $\le1$ suffices);
(c) Hadamard with a filter/specialization stays recognizable; (d) the **continuant/Wedderburn**
reversal identity is a rational-series mirror of C9's reverse-$=$-rotation and suggests a
continued-fraction form for $\Phi=S/D$ (thread §3). The negative finding pins where the
combinatorics-on-words must come from: not here — the Christoffel-words book.

## Open thread it touches

§8 (cocycle complexity): "rank of the Hankel matrix" is one concrete complexity candidate; the rank of
$S$ is fixed at $2$, so the discriminating complexity must live in the **core** $C$ / parametrized
families, not in $S$ itself. §3 (transfer-matrix bridge) via continuants. Chase: Berstel–Lauve–
Reutenauer–Saliola, *Christoffel words* (the missing word-complexity side); Reutenauer, *Free Lie
Algebras* (residuals/derivatives).
