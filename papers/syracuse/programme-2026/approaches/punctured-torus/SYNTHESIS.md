# The geometric picture, consolidated

A single coherent account of the `punctured-torus` approach, organized as: **homography
choice → free-group representation → quotient manifold → cycle interpretations**, then the
unifying layer structure and the honest bottom line. Definite choices are made; alternatives
are noted in passing. All quantitative claims are certified by the scripts named.

---

## 1. Homography choice

The two Syracuse maps are homographies (Möbius transformations) of the projective line:
$$
a:\,z\mapsto\frac{3z+1}{2}\ \leftrightarrow\ A=\begin{pmatrix}3&1\\0&2\end{pmatrix},
\qquad
b:\,z\mapsto\frac{z}{2}\ \leftrightarrow\ B=\begin{pmatrix}1&0\\0&2\end{pmatrix},
\qquad \det A=6,\ \det B=2 .
$$
This choice is **forced** by the dynamics — they are the two branches of the accelerated map.
The homography of a whole word is the **transfer matrix** (structure.md C1, transpose convention)
$$
M(w)=\begin{pmatrix}3^{o}&0\\ S&2^{E}\end{pmatrix},\qquad \det M=2^{E}3^{o},\quad
\operatorname{tr}M=2^{E}+3^{o},\quad \lambda_1-\lambda_2=2^E-3^o=D .
$$
Because $\det A,\det B\in\{2^a3^b\}$, the homographies live in $\mathrm{PGL}_2(\mathbb{Z}[\tfrac16])$
and have **three faces** (one per place of $\{2,3,\infty\}$): the real face acts on $\mathbb{H}$
(or the Klein conic in $\mathbb{RP}^2$); the $2$- and $3$-adic faces act on the Bruhat–Tits
trees $T_2,T_3$.

## 2. The free-group representation

$F_2=\langle a,b\rangle=\pi_1(\Sigma_{1,1})$ (once-punctured torus). The **canonical
representation** $\rho:F_2\to\mathrm{PGL}_2$ is $a\mapsto A,\ b\mapsto B$. Two structural facts
fix its nature:

- **It is reducible.** $A,B$ are upper-triangular: they share the fixed point $\infty$, so
  $\operatorname{tr}[A,B]=+2$ and the image lies in the Borel/affine subgroup. The off-diagonal
  entry of $M(w)$ is the cocycle $S$ — a **Magnus $1$-cocycle** $S=\chi\circ\partial_a$ for the
  multiplicative character $\lambda(a)=\tfrac32,\lambda(b)=\tfrac12$, the unique class (up to
  scale) in $H^1(F_2,\mathbb{R}_\lambda)$ (markoff-coordinates, admissible-representations).
- **The fundamental dichotomy.** The character $\lambda$ is nontrivial, so realising $S$
  literally as a geometric translation *forces* a shared eigenline, i.e. *forces reducibility*.
  Hence: the **canonical (reducible) rep carries the full Syracuse arithmetic but is geometrically
  degenerate**; every **irreducible (genuine) rep is non-degenerate but cannot carry the literal
  $S$**. This dichotomy is the spine of everything below.

The affine/Lorentzian dressing adds the translation cocycle: $\rho=(L,\tau)$ into
$\mathrm{Isom}(\mathbb{E}^{1,2})=\mathrm{PSL}_2\ltimes\mathfrak{sl}_2$, with $\tau(\gamma)=\tfrac{S}{2^E}E$
(null). The arithmetic dressing is $\rho:F_2\to\mathrm{PGL}_2(\mathbb{Z}[\tfrac16])$.

## 3. The quotient manifold

The canonical reducible $\rho$ has **no smooth quotient**: the group is elementary (common
fixed point $\infty$), the action on $\mathbb{E}^{1,2}$ is non-free (Margulis $\equiv0$), and one
gets only a per-cycle cylinder / a cusp at $\infty$. A genuine quotient requires *leaving the
reducible locus*, and there are three complementary **resolutions**, each capturing one
algebraic layer:

| resolution | manifold | captures |
|---|---|---|
| **(a) real Fuchsian** (nontrivial_rep) | convex-cocompact **once-holed torus** $\Gamma\backslash\mathbb{H}$, generic-BTZ funnel boundary | the **length** layer — generators of length $\log\tfrac32,\log2$ |
| **(b) flat Lorentzian** (brunswic-spacetime) | future-complete **BTZ spacetime** $\Gamma\backslash\Omega$, $\simeq\Sigma_{1,1}\times\mathbb{R}$, extreme/generic BTZ at the puncture | the **cocycle** layer — $\tau=S$, endpoint $S/D$, interval $D$ |
| **(c) $S$-arithmetic** (the building) | $\Gamma\backslash(\mathbb{H}\times T_2\times T_3)$, adelically $\mathbb{H}\times\prod_pT_p$ | the **integrality** layer — valuations $E,o$ and $D\mid S$ at $p\mid D$ |

None of (a)–(c) carries the literal cocycle $S$ *and* is smooth; that is the price of the
dichotomy. They are an **atlas**, not rivals: (a) is the multiplicative skeleton, (b) the
additive "$+1$", (c) the divisibility.

## 4. Cycle geometric interpretations

A Syracuse cycle is a primitive conjugacy class $\gamma$ (cyclically reduced word) with
$D(\gamma)\mid S(\gamma)$. Every interpretation converges on the **single invariant**
$$
\boxed{\,x_0^\ast=\frac{S}{D}\ \ (\text{the fixed point / ideal endpoint}),\qquad
\gamma\text{ is a cycle}\iff x_0^\ast\in\mathbb{Z}.}
$$
Its per-model dressing:

| model | a cycle is … | length / interval | endpoint |
|---|---|---|---|
| $\mathbb{H}=\mathrm{Aff}_+(\mathbb{R})$ | a **vertical geodesic** $\mathrm{Re}=x_0^\ast$ | $\ell=\lvert E\log2-o\log3\rvert$ | $x_0^\ast=S/D\in\partial\mathbb{H}$ |
| $\mathbb{E}^{1,2}=\mathfrak{sl}_2$ | a **spacelike geodesic** | interval $D=2^E-3^o$; criticality $=$ light cone | null endpoint $S/D$ |
| BTZ spacetime | a closed spacelike geodesic with **integer ideal endpoint** | — | $S/D\in\mathbb{Z}$ |
| building $T_2\times T_3$ | a **closed orbit** | $\ell_{T_2}=E$, $\ell_{T_3}=o$ | integral at $p\mid D$ |

The real geometry *sees the value* $x_0^\ast=S/D$ (the first-order Margulis invariant ranks
with $\lvert S/D\rvert$ at Spearman $\approx0.9$, degeneration.py) but is **blind to its
integrality**; the integrality is exactly the closing-up condition the $p$-adic factors ($p\mid D$)
do see.

## 5. The unifying layer structure

The homography $M(w)=\big(\begin{smallmatrix}3^o&0\\S&2^E\end{smallmatrix}\big)$ has three pieces,
and each geometry reads one:
$$
\underbrace{\text{diagonal }(3^o,2^E)}_{\text{multiplicative / lengths}\ \to\ \text{(a),}\ \mathbb{H},T_2,T_3}
\quad
\underbrace{\text{off-diagonal }S}_{\text{additive / endpoint}\ \to\ \text{(b),}\ \tau,\ S/D}
\quad
\underbrace{D\mid S\ \text{at }p\mid D}_{\text{integrality}\ \to\ \text{(c),}\ p\text{-adic}} .
$$
Dynamics live at the homography's own primes $\{2,3,\infty\}$; the **cycle/integrality condition
lives at the complementary primes $p\mid D$** (all $\ge5$, since $\gcd(D,6)=1$) — the precise
reason the real-Lorentzian picture cannot close the problem.

## 6. Bottom line

The geometry **faithfully reformulates the Collatz cycle problem down to one continuous invariant
and one discrete question**: build the homography $M(w)$, read its fixed point $x_0^\ast=S/D$
(the ideal endpoint, visible in every model), and ask whether it is an integer. "No nontrivial
cycle" $=$ "no closed geodesic but the trivial one has an integer ideal endpoint." Everything
real-geometric reaches $S/D$; the integrality $D\mid S$ is the residual arithmetic core, native
to the $p$-adic ($p\mid D$) layer.
