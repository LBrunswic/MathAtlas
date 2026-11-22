# The Syracuse BTZ spacetime — a complete description

Companion to [`brunswic-spacetime.md`](brunswic-spacetime.md); claims tagged ✅ are
certified in [`spacetime.py`](spacetime.py) / [`lorentzian.py`](lorentzian.py).
Framework: Brunswic, [arXiv:2108.12631](https://arxiv.org/abs/2108.12631); Mess; Bonsante.

## 0. The flat model

$\mathbb{E}^{1,2}=\mathfrak{sl}_2(\mathbb{R})$, $q(X)=-\det X=\tfrac12\operatorname{tr}X^2$
(signature $(1,2)$, the timelike direction is the elliptic generator $E-F$). Isometries
$\mathrm{Isom}_0=\mathrm{SO}_0(1,2)\ltimes\mathbb{R}^{1,2}=\mathrm{PSL}_2(\mathbb{R})\ltimes\mathfrak{sl}_2$,
acting by $X\mapsto\operatorname{Ad}(g)X+v$. Basis $(H,E,F)$ with $H$ spacelike,
$E,F$ null ($q(E)=q(F)=0$), $\langle E,F\rangle=\tfrac12$, $\langle E,H\rangle=0$.

## 1. The associated representation

$\rho:\pi_1(\Sigma_{1,1})=F_2=\langle a,b\rangle\to\mathrm{PSL}_2(\mathbb{R})\ltimes\mathfrak{sl}_2$,
$\rho(\gamma)=(L(\gamma),\tau(\gamma))$.

**Translation cocycle (the arithmetic, base-free) ✅.** Reading off the affine-line map
$F_\gamma(z)=\tfrac{3^o}{2^E}z+\tfrac{S}{2^E}$,
$$\boxed{\ \tau(\gamma)=\frac{S(\gamma)}{2^{E(\gamma)}}\,E\ \in\ \mathbb{R}\!\cdot\!E\ \ (\text{null}),\qquad
\tau(a)=\tfrac12E,\ \tau(b)=0.\ }$$
So **the Magnus/Syracuse cocycle $S$ is literally the (lightlike) translation part**, a
crossed homomorphism for whichever linear part $L$ we put underneath.

**Linear part — two choices:**

- **Canonical / reducible (the "noded" base).** $L_0=$ the multiplicative $2$–$3$ skeleton,
  $\operatorname{Ad}L_0$ a boost fixing $H$: on $(H,E,F)$, $a:(H,\tfrac32E,\tfrac23F)$,
  $b:(H,\tfrac12E,2F)$. This is the honest Syracuse holonomy; it is **abelian / reducible**
  ($\operatorname{tr}[A,B]=+2$, sub-Markoff), a boundary point of $\mathrm{Teich}(\Sigma_{1,1})$.
- **Smooth (Brunswic) base.** Any genuine Fuchsian uniformisation $L\in\mathrm{Teich}(\Sigma_{1,1})$
  of the cusped once-punctured torus ($L(a),L(b)$ hyperbolic, $L([a,b])$ parabolic). Then
  $(\,L,\,\tau\,)$ is a point of $T\,\mathrm{Teich}(\Sigma_{1,1})$ — Brunswic Thm 1.

The puncture $[a,b]$ is **parabolic** ($\operatorname{Ad}$ unipotent, fixing the null line
$\mathbb{R}E$) ✅ — the **extreme BTZ** (Lorentzian cusp).

## 2. The spacetime and its causal structure

For a Fuchsian base $L$, Mess/Bonsante give the **maximal globally hyperbolic domain**
$\Omega\subset\mathbb{E}^{1,2}$ — the regular domain with lightlike support planes (the
future of the initial singularity) — and
$$M=\rho(F_2)\backslash\Omega,$$
a GH Cauchy-maximal Cauchy-compact flat spacetime, BTZ-extended at the cusp
($\mathrm{Ext}_{BTZ}$, Brunswic Thm 2) to a singular $\mathbb{E}^{1,2}_0$-manifold whose one
singular line is the extreme BTZ at the puncture.

**Future-completeness.** $\Omega$ carries a regular **cosmological time** $T:M\to(0,+\infty)$;
$M$ is **future-complete** ($T\to+\infty$) and **past-incomplete**, with an **initial
singularity** at $T\to0$ — an $\mathbb{R}$-tree dual to the measured geodesic lamination
encoded by the cocycle $\tau$. The extreme-BTZ line is a **white hole**
($\mathrm{d}s_0^2=-2\,\mathrm{d}\tau\,\mathrm{d}r+\mathrm{d}r^2+r^2\mathrm{d}\theta^2$) on the
initial-singularity side; the time orientation (white- vs black-hole) is fixed by the **sign
of the "$+1$"** ($\tau(a)=+\tfrac12E$, future-pointing null). Cauchy surface $\simeq\Sigma_{1,1}$.

## 3. The map {Syracuse trajectories/cycles} → {geodesics}

$$\{\text{primitive cyclic gap-words }\gamma\}\ \xrightarrow{\ \cong\ }\
\{\text{free homotopy classes of closed curves on }\Sigma_{1,1}\}\
\xrightarrow{\ \text{axis}\ }\ \{\text{closed geodesics of }M\}.$$
A class with $L(\gamma)$ **hyperbolic** $\mapsto$ a closed **spacelike** geodesic (its axis,
direction the neutral vector $x^0(\gamma)=G-\tfrac{\operatorname{tr}G}{2}I$, $q(x^0)\gt0$ ✅;
$\operatorname{Ad}$-spectrum $\{2^E/3^o,1,3^o/2^E\}$, length $\ell=|\log\tfrac{2^E}{3^o}|$).
A class conjugate into $[a,b]$ (parabolic) $\mapsto$ the BTZ singular line.

## 4. Property P — what singles out the cycles

At the **reducible base** the holonomy $(\operatorname{Ad}L_0(\gamma),\tau(\gamma))$ **fixes a
spacelike line pointwise** ✅:
$$\operatorname{Fix}=\{\,tH+x_0^\ast\,E:\ t\in\mathbb{R}\,\},\qquad
x_0^\ast=\frac{S(\gamma)}{D(\gamma)}\ \ (\text{the cycle value}),$$
because $\tau$ is null ($\langle\tau,x^0\rangle=0$ — the **Margulis invariant vanishes**, the
degeneracy of the reducible base; a Fuchsian base lifts it to a genuine spacelike axis of
nonzero Lorentzian length). The null-position of this fixed/limit line — equivalently the
geodesic's **ideal endpoint on the null boundary** $\partial_\infty=\mathbb{R}\cup\{\infty\}$
(the lightcone at infinity, on which the BTZ cusp sits at $\infty$) — is exactly
$x_0^\ast=S/D$. Hence:

> **Property P (certified ✅).** A class $\gamma$ is a **Syracuse cycle**
> $\iff D(\gamma)\mid S(\gamma)\iff x_0^\ast=S/D\in\mathbb{Z}$
> $\iff$ **its closed spacelike geodesic has an *integer* ideal endpoint** on the null
> boundary — i.e. its fixed/limit spacelike line sits at an **integer null-position**, a
> marked point of the integer lattice $\mathbb{Z}\subset\partial_\infty$ in the parabolic
> (BTZ-cusp) orbit.

Checked: cycles `ab,a,aab` give $x_0^\ast=1,-1,-5\in\mathbb{Z}$; non-cycles `abb`,`(1,3)`
give $\tfrac15,\tfrac57\notin\mathbb{Z}$.

**In words.** Every conjugacy class is a closed spacelike geodesic; the Collatz cycle
problem is the question of *which* of these geodesics close up over the **integer points of
the null boundary attached to the BTZ cusp.** "No nontrivial positive cycle" $=$ "no closed
spacelike geodesic, other than the trivial one, has a positive integer ideal endpoint."

## 5. Status and the honest gap

- ✅ Representation, null cocycle $\tau=(S/2^E)E$, extreme-BTZ puncture, the geodesic
  correspondence, and property P (integer ideal endpoint) — all certified at the reducible
  base.
- ⚠️ At the reducible base the action is **non-free** (Margulis $\equiv0$); it is the noded
  boundary point of $T\,\mathrm{Teich}$, not a smooth spacetime. A smooth Brunswic spacetime
  needs an **interior Fuchsian base** $L$ carrying $\tau=S$; under that lift the endpoints
  become two finite ideal points and the Margulis length turns on. **Open:** does the
  multiplicative $2$–$3$ skeleton pick a *canonical* Fuchsian base, or is the base a free
  modulus with $S$ the only arithmetic input? Does "integer ideal endpoint" survive the lift
  as a clean condition (a BTZ-extension / Cauchy-completeness statement, Brunswic Thm 2–3)?
