# Markoff coordinates of the Syracuse holonomy (Stage 1 keystone)

**Certified by** [`markoff.py`](markoff.py) (every numeric/algebraic claim below is an
`assert` there; run it, it prints `ALL KEYSTONE ASSERTS PASSED`). Reuses the cocycle
kernel [`../cocycle-combine/lib/cocycle.py`](../cocycle-combine/lib/cocycle.py) and the
certified identities of [`../cocycle-combine/structure/structure.md`](../cocycle-combine/structure/structure.md).

## Setup

$F_2=\pi_1(\Sigma_{1,1})=\langle a,b\rangle$ with the two affine maps as homogeneous
matrices, normalised into $\mathrm{SL}_2$ by dividing by $\sqrt{\det}$:
$$a:z\mapsto\tfrac{3z+1}{2}\ \to\ A=\begin{pmatrix}3&1\\0&2\end{pmatrix},\quad
b:z\mapsto\tfrac{z}{2}\ \to\ B=\begin{pmatrix}1&0\\0&2\end{pmatrix},\qquad
\operatorname{tr}_{\mathrm{SL}_2}=\tfrac{\operatorname{tr}}{\sqrt{\det}}.$$

## 1. Trace coordinates and the Fricke identity

$$\big(x,y,z\big)=\big(\operatorname{tr}A,\operatorname{tr}B,\operatorname{tr}AB\big)
=\Big(\tfrac{5}{\sqrt6},\ \tfrac{3}{\sqrt2},\ \tfrac{7}{2\sqrt3}\Big)
\approx(2.0412,\ 2.1213,\ 2.0207).$$

Fricke (Cohn 1972, [`cohn1972-markoff-forms.md`](../cocycle-combine/structure/notes/cohn1972-markoff-forms.md)):
$\operatorname{tr}[A,B]=x^2+y^2+z^2-xyz-2$. Evaluated here:
$$\boxed{\ \operatorname{tr}[A,B]=+2\ \text{exactly}\ },\qquad x^2+y^2+z^2-xyz=4.$$

## 2. The holonomy is the *reducible* point of the character variety

$\operatorname{tr}[A,B]=2$ is exactly the **reducibility criterion** for a representation
$F_2\to\mathrm{SL}_2$ (the two matrices share an eigenvector). Here they share
$(1,0)^\top$ — the common fixed point $\infty$ — as expected from the
[earlier degeneration finding](STATUS.md): the Syracuse affine holonomy sits on the
$2$-sheet $x^2+y^2+z^2-xyz=4$ of the cubic, the **reducible locus**, not on the
Markoff/Teichmüller sheet $x^2+y^2+z^2-xyz=0$ ($\operatorname{tr}[A,B]=-2$).

## 3. The commutator is a genuine cusp (parabolic)

$$[A,B]=\begin{pmatrix}1&\tfrac14\\0&1\end{pmatrix}:\ z\mapsto z+\tfrac14,$$
a **non-trivial unipotent/parabolic** fixing $\infty$. So in the degenerate model the
puncture is realised as a genuine cusp at $\infty$; the two generator-axes and the
commutator parabolic have all collided into the single boundary point $\infty$. The
affine model is the **reducible, cusped degenerate point** of the deformation space.

## 4. The obstruction: the generators are *sub-Markoff*

All three trace coordinates are $\lt 3$. But $3$ is the **minimum trace** of a simple
closed geodesic on the cusped hyperbolic once-punctured torus (the Markoff minimum,
attained only by the three systoles of the modular/hexagonal torus, trace $=3\cdot1$).
Since $a,b$ are primitive (a free basis), they are simple closed curves; trace $\lt3$
means:

> **The Syracuse generators cannot be the generators of a discrete faithful (Fuchsian)
> representation of the *cusped, finite-area* hyperbolic punctured torus** — they are too
> short.

A direct check confirms a fixed-$(x,y)$ deformation cannot even *reach* the cusped sheet:
solving $z^2-(xy)z+(x^2+y^2)=0$ (the condition $\operatorname{tr}[A,B]=-2$ at the Syracuse
$x,y$) has discriminant $(xy)^2-4(x^2+y^2)=-\tfrac{191}{12}\lt0$ — **no real $z$**.

**Scope of the obstruction.** It bites only the *finite-area cusped* hyperbolic target.
It does **not** rule out: (i) an *infinite-area* Schottky free group (no trace lower
bound, but short generators force the axes very far apart — constrained), (ii) a
**singular-flat / translation** structure (no length lower bound at all), or (iii) a
**Lorentzian** (AdS / Margulis-spacetime) structure — the affine-deformation regime that
is the natural home of affine generators. This is precisely why the Stage-2 target is a
real choice, and why "choose your geometry" (the approach's spine) is forced here rather
than optional.

## 5. Per-cycle consistency with the cocycle kernel

For each known cycle the cumulative homogeneous matrix $G$ of the period word reproduces
the certified `structure.md` invariants (C1/C4/C11) and the
[`hyperbolic_model.py`](hyperbolic_model.py) geodesic data:

| cycle | $(o,E)$ | $\operatorname{tr}G=2^E{+}3^o$ | $\det G=2^E3^o$ | gap $=\lvert D\rvert$ | $x_0=S/D$ | $\ell=\lvert\log(2^E/3^o)\rvert$ |
|---|---|---|---|---|---|---|
| $1\to1$ (`ab`)   | $(1,2)$ | $7$  | $12$ | $1$ | $1$  | $\log\tfrac43=0.2877$ |
| $-1$ (`a`)       | $(1,1)$ | $5$  | $6$  | $1$ | $-1$ | $\log\tfrac32=0.4055$ |
| $-5\to-7$ (`aab`)| $(2,3)$ | $17$ | $72$ | $1$ | $-5$ | $\log\tfrac89=0.1178$ |

The generic identity $\operatorname{tr}M(w)=X^E+Y^o$ is re-certified for these words by the
kernel's `verify_symbolic_identity` (a $\mathbb Z[X,Y]$ check).

## 6. Stage-2 scaffolding and what it shows (target-agnostic)

`deform(t)` conjugates $B$ by $C_t=\big(\begin{smallmatrix}1&0\\t&1\end{smallmatrix}\big)$,
opening $\infty$: $B_t$ fixes $0$ and $1/t$, so for $t\neq0$ the pair is irreducible
($\operatorname{tr}[A,B_t]\neq2$). The plot [`markoff_deformation.png`](markoff_deformation.png)
along this path shows two things that **shape the Stage-2 design**:

- **$\operatorname{tr}[A,B_t]$ is a parabola bottoming at $+2$ and never reaches $-2$** —
  this naive (trace-non-increasing) path provably cannot reach the cusped-Fuchsian sheet.
- **The trivial cycle's length collapses to $0$ (its matrix goes *elliptic*) for
  $t\gtrsim0.1$.** Reason: $\operatorname{tr}G=7$ sits barely above the hyperbolicity
  threshold $2\sqrt{\det}=2\sqrt{12}\approx6.93$, so any axis-separating deformation tips
  the short cycle element into rotation. This is the geometric face of criticality
  ($2^E\!\approx\!3^o$) / sub-Markoffness: **the cycle geodesics are critically short.**

**Consequence:** a usable Stage-2 deformation must *increase* the generator/cycle traces
(lengthen the geodesics), not merely separate the axes — or must target a geometry with no
hyperbolic length floor (singular-flat / Lorentzian). The framework (`deform`,
`track_cycle`) is in place; the **target geometry is deliberately not yet chosen**
(`TODO(stage-2 target)` in `markoff.py`).
