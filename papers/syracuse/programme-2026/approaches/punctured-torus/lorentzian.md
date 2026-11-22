# Lorentzian (flat / Margulis-spacetime) model — Stage 2

**Target chosen:** flat Lorentzian. **Certified by** [`lorentzian.py`](lorentzian.py)
(`ALL LORENTZIAN ASSERTS PASSED`). Rationale: our generators are *literally affine*, so the
canonical Lorentzian home is the **Margulis-spacetime** picture — affine isometries of
Minkowski $3$-space — exactly the "affine deformation of a free group" regime
(Drumm–Goldman–Margulis) cited in [`RATIONALE.md`](RATIONALE.md). It also has **no length
floor**, dissolving the sub-Markoff obstruction that blocked the hyperbolic target.

## The model

$$\mathbb{R}^{2,1}=\mathfrak{sl}_2(\mathbb{R}),\qquad q(X)=-\det X=\tfrac12\operatorname{tr}X^2,
\quad\langle X,Y\rangle=\tfrac12\operatorname{tr}(XY)\ \ (\text{signature }(2,1)).$$
Linear isometries $=\operatorname{Ad}(g)$, $g\in\mathrm{SL}_2$ (so
$\operatorname{Ad}:\mathrm{SL}_2\to\mathrm{SO}(2,1)$); affine isometries
$X\mapsto\operatorname{Ad}(g)X+u(g)$ with a translation cocycle $u:\Gamma\to\mathfrak{sl}_2$
($u(gh)=u(g)+\operatorname{Ad}(g)u(h)$). Closed geodesics $\leftrightarrow$ conjugacy
classes; the signed Lorentzian length is the **Margulis invariant**
$\alpha(\gamma)=\langle u(\gamma),x^0(\gamma)\rangle$, $x^0$ the neutral
(eigenvalue-$1$) vector of $\operatorname{Ad}\rho(\gamma)$. Properness (a genuine spacetime)
$\iff$ all $\alpha(\gamma)$ share one sign (Goldman–Labourie–Margulis).

## (A) Spectral picture — clean and positive (verified on all 3 cycles)

For a cycle's $\mathrm{SL}_2$ element (normalised; eigenvalues $\sqrt{2^E/3^o}^{\pm1}$),
$$\operatorname{Ad}\ \text{has eigenvalues}\ \Big\{\tfrac{2^E}{3^o},\,1,\,\tfrac{3^o}{2^E}\Big\},
\qquad \text{rapidity}=\big|\log\tfrac{2^E}{3^o}\big|=\ell\ (\text{the hyperbolic length}).$$
The neutral axis $x^0=G-\tfrac{\operatorname{tr}G}{2}I$ is **spacelike** ($q(x^0)\gt0$). In
**null coordinates** $(u,v)=(2^E,3^o)$ the Lorentzian data is transparent:
$$\operatorname{tr}=u+v=2^E+3^o,\quad \det=uv=2^E3^o,\quad
\boxed{D=2^E-3^o=u-v=\text{the Lorentzian interval}},$$
and **criticality $2^E\approx3^o$ is the light cone $u=v$** — a positive cycle ($|D|$ small,
critical band) is a geodesic *grazing the light cone*. Checked: $1\to1$ $(4,3)$, $-1$
$(2,3)$, $-5\to-7$ $(8,9)$.

## (B) The Margulis invariant vanishes — the "+1" is lightlike (the surprise)

Take the natural realization: linear part $\rho_0=$ the **diagonal (multiplicative $2$–$3$)
holonomy** ($a\mapsto\operatorname{diag}(\tfrac32,1)$, $b\mapsto\operatorname{diag}(\tfrac12,1)$,
normalised), and translation cocycle $u=$ the velocity of turning on the Syracuse "$+1$"
($u(a)=\tfrac12E$, $u(b)=0$). Then on every cycle:
$$u(\gamma)\in\mathbb{R}\!\cdot\!E\ (\text{the null line}),\qquad q(u(\gamma))=0,\qquad
\alpha(\gamma)=\langle u(\gamma),x^0\rangle\equiv 0.$$
Because $x^0=H$ for the diagonal linear part and $\langle E,H\rangle=0$. Two consequences:

- **$u$ *is* the cocycle $S$.** $u(\gamma)=\big(\tfrac12\sum_{\text{a-steps}}\prod_{\text{preceding}}w\big)E$
  with per-step weights $w(a)=\tfrac32,\ w(b)=\tfrac12$ — the **same transport law as
  $S$** (structure.md C5), i.e. the Magnus cocycle realised in the null direction. So the
  Syracuse cocycle $S$ is the **lightlike Margulis translation part**, and its lightlikeness
  is the geometric face of criticality $2^E\approx3^o$.
- **The naive flat model is degenerate.** A null translation cocycle gives vanishing Margulis
  invariant — no proper Margulis spacetime from the abelian (diagonal) linear part. The
  arithmetic is *all in the cocycle*, and the cocycle is *on the light cone*.

## Where this points

The vanishing is the recurring theme made precise: the Syracuse **linear holonomy is
degenerate (abelian / reducible / parabolic) and all content lives in the null cocycle $S$.**
A non-degenerate Lorentzian realization must therefore either
1. **make the linear part non-abelian** (deform the diagonal $\langle2,3\rangle$ off the
   Cartan into a Fuchsian $\mathrm{SO}(2,1)$ pair — then $x^0(\gamma)$ rotates away from $H$,
   $\langle u(\gamma),x^0(\gamma)\rangle\not\equiv0$, and properness becomes a real
   sign-condition to compare against $D\mid S$); or
2. **go to the curved AdS route** (Mess: $\mathrm{PSL}_2\times\mathrm{PSL}_2$, two reps —
   e.g. the two characters $w\mapsto Y^o$ and $w\mapsto X^E$ as the left/right reps); or
3. **embrace the null/parabolic regime** — treat $S$ as a horocyclic/lightlike datum (a
   BTZ-type or parabolic Lorentzian structure) where the light-cone grazing is the point.

Stage 3 ("geometrize $D\mid S$") now has a concrete shape: $D=2^E-3^o$ is the Lorentzian
interval and $S$ is the null translation; $D\mid S$ couples the interval to the cocycle —
the candidate geometric statement is about the Margulis invariant / properness once the
linear part is made non-abelian (route 1).
