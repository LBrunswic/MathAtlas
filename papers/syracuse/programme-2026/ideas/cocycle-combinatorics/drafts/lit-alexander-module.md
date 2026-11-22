# Leverage R1: the Crowell derived module / multivariable Alexander module of $\chi$

**Promise:** medium–high. R1 is the *named* theory of $\ker(1-\chi)$, and it delivers what the
roadmap asked: an **exact module presentation** of $\mathcal I_D$ as the Crowell derived /
2‑variable Alexander module of the abelianization $\psi:W\to\langle X,Y\rangle$, its
**Alexander matrix** (= $\chi$‑evaluated Fox Jacobian), and its **elementary / order ideals**. The
headline new objects are the **second Magnus/Fox cocycle $T$** ($=\chi$‑evaluated $\partial/\partial x_0$),
the **binary fundamental formula $D=(X{-}1)T-(Y{-}1)S$**, and the rigorous placement of $\langle D\rangle$,
the cores, and C8 inside the **Fitting filtration**. The honest verdict on the *prize* (a finer
elementary ideal that constrains reducibility) is **negative but decisive**: the Fitting filtration of
the rank‑2 state module **terminates at the cores** ($E_0=I_2$), there is *no* $E_k$ finer than the
cores, and the multivariable order ideal is *non‑informative* (Alexander polynomial $=1$ for primitive
shapes) — the arithmetic content $\langle D\rangle$ is a rank‑1 *evaluation* phenomenon. This **closes**
the carried open question (§5) and upgrades "cores are complete" from heuristic to "cores $=$ top
Fitting ideal, filtration stops there."

**Status:** read in full; dictionary built; all 13 transfers verified on the kernel
(`checks/lit_alexander_module.py`, exit 0). **Last iterated:** 2026-06-08.

**Sources (real, complete; read in full).**
- R. H. Crowell, *The derived module of a homomorphism*, Adv. Math. **6** (1971) 210–238 — the primary
  reference is **closed access** (verified via unpaywall: no open copy). Its theory is read in full
  through the rigorous modern re‑derivation:
- A. Kontogeorgis, P. Paramantzoglou, *A non-commutative differential module approach to Alexander
  modules*, arXiv:1904.06665 — [`sources/noncomm-diff-alexander-1904.06665.pdf`](../sources/noncomm-diff-alexander-1904.06665.pdf).
  Defines Crowell's derived module $\mathscr A_\psi$ of $\psi:G\to H$ (eq. 1), its **free resolution**
  $\mathbb Z[H]^s\xrightarrow{Q_\psi}\mathbb Z[H]^r\to\mathscr A_\psi\to0$ (eq. 2) with
  $Q_\psi=\big((\psi\circ\pi)(\partial R_i/\partial x_j)\big)$ the **$\psi$‑evaluated Fox Jacobian**
  (eq. 3), the augmentation‑ideal identity $\ker\delta=\mathbb Z[H]\otimes_{\mathbf A}I_{\mathbf A}$
  (p. 4), and the Crowell exact sequence (eq. 6).
- A. Dimca, L. Maxim, *Multivariable Alexander invariants of hypersurface complements*,
  arXiv:math/0506324 — [`sources/maxim-multivariable-alexander-0506324.pdf`](../sources/maxim-multivariable-alexander-0506324.pdf).
  §2.1: the **$i$‑th elementary ideal** $\mathcal E_i(A)=$ ideal of the $(n{-}i)\times(n{-}i)$ minors of
  an $n\times m$ presentation matrix; **$\Delta_i$** $=$ gcd‑generator (characteristic / Alexander
  polynomial); **order ideal $\mathcal E_0$** with $\sqrt{\mathcal E_0}=\sqrt{\operatorname{Ann}}$;
  $\Delta_{i+1}\mid\Delta_i$; multivariable→1‑variable specialization (§2.4).
- Livingston/Gardner, *Knot Groups and the Alexander Polynomial* §6.4 —
  [`sources/livingston-6-4.pdf`](../sources/livingston-6-4.pdf). **Fox's Algorithm**: Alexander matrix
  $=$ Fox Jacobian, evaluate by abelianization, delete a column, $\det=$ Alexander polynomial; and the
  multivariable $\to t$ specialization on the trefoil.

---

## 1. What the sources prove (the derived module, with citations)

**Crowell's derived module (Kontogeorgis–Paramantzoglou, eqs. 1–3).** For a homomorphism
$\psi:G\to H$, a **$\psi$‑derivation** is $\partial:G\to M$ ($M$ a left $\mathbb Z[H]$‑module) with
$$\partial(g_1g_2)=\partial(g_1)+\psi(g_1)\,\partial(g_2). \tag{1}$$
The **derived module** $\mathscr A_\psi$ (a.k.a. the **Alexander module**) is the left
$\mathbb Z[H]$‑module $\bigoplus_{g\in G}\mathbb Z[H]\,dg$ modulo $d(g_1g_2)-dg_1-\psi(g_1)dg_2$; it is
**universal** for $\psi$‑derivations ($d:G\to\mathscr A_\psi$). For a presentation
$G=\langle x_1,\dots,x_r\mid R_1,\dots,R_s\rangle$ there is a free resolution
$$\mathbb Z[H]^s\xrightarrow{\,Q_\psi\,}\mathbb Z[H]^r\longrightarrow\mathscr A_\psi\longrightarrow0,
  \qquad Q_\psi=\Big((\psi\circ\pi)\tfrac{\partial R_i}{\partial x_j}\Big)_{i,j}. \tag{2,3}$$
So **the Alexander matrix is the $\psi$‑evaluated Fox Jacobian of the relators.** Crowell further
identifies $\mathscr A_\psi$ with the **augmentation module** $\ker\delta=\mathbb Z[H]\otimes_{\mathbf A}I_{\mathbf A}$
($I_{\mathbf A}=$ augmentation ideal), the non‑commutative analogue of the module of differentials, and
proves the **Crowell exact sequence** $0\to(R)^{\mathrm{ab}}\to\mathscr A_\psi\to I_H\to0$ (eq. 6).

**Elementary ideals (Dimca–Maxim §2.1).** For a f.g. module $A$ over a Noetherian UFD $R$ with
$n\times m$ presentation matrix, $\mathcal E_i(A)=\langle(n{-}i)\times(n{-}i)\text{ minors}\rangle$
($\mathcal E_i=R$ for $i\ge n$, $=0$ for $n{-}i\gt m$); $\Delta_i=\gcd\mathcal E_i$ (the $i$‑th
characteristic/Alexander polynomial); $\mathcal E_i\subseteq\mathcal E_{i+1}$ so
$\Delta_{i+1}\mid\Delta_i$; the **order ideal** is $\mathcal E_0$ with
$\sqrt{\mathcal E_0}=\sqrt{\operatorname{Ann}A}$. (Crowell–Fox knot convention: the order ideal is the
**first nonzero** elementary ideal, $E_1=\langle$maximal minors$\rangle$ for a deficiency‑1
presentation, with $\Delta_1$ the Alexander polynomial.)

---

## 2. Dictionary — our $W,S,\Phi,\chi,D$, cores $\leftrightarrow$ the Alexander module

Set $E=\#0=|w|$, $o=\#1=\operatorname{len}w$. The kernel uses **gap** words
$(d_0,\dots,d_{n-1})$, the run‑length encoding of the binary word
$1\,0^{d_0}1\,0^{d_1}\cdots1\,0^{d_{n-1}}$ ($1=x_1$ odd, $0=x_0$ even).

| Crowell / Alexander (their notation) | Ours (STRUCTURE §1–§3) | status |
|---|---|---|
| group $G$ with presentation | free **monoid** $W=\{x_0,x_1\}^\ast$ | correspond (**mismatch:** monoid, no inverses — see below) |
| abelianization $\psi:G\to H$ | $\psi:W\to H=\langle X,Y\rangle\cong\mathbb Z^2$, $x_0\mapsto t_1{=}X$, $x_1\mapsto t_2{=}Y$ | **correspond — MULTIVARIABLE, $t_1{=}X,t_2{=}Y$** |
| group ring $\mathbb Z[H]$ | $\mathbb Z[X^{\pm1},Y^{\pm1}]$ | correspond |
| $\psi$‑evaluated Fox derivative $(\psi\circ\pi)\partial/\partial x_j$ | $\chi$‑cocycles $S=\chi\partial_{x_1}$, $T=\chi\partial_{x_0}$ (up to units $Y^{o-1},Y^{o}$) | **correspond — the key match** |
| Magnus/Fox Jacobian $Q_\psi$ | the Magnus matrix $\Phi$; its off‑diagonal $=S$ (and the dual $=T$) | correspond |
| $\psi$‑derivation rule (1) | cocycle rule $S(uv)=Y^{o_v}S(u)+X^{E_u}S(v)$ | correspond (reconciled by the $Y^{o-1}$ normalization) |
| derived module $\mathscr A_\psi=\mathbb Z[H]\otimes_\psi I_W$ | $\mathbb Z[H]\,dx_0\oplus\mathbb Z[H]\,dx_1\cong I_H=\langle X{-}1,Y{-}1\rangle$ (free, rank 2) | correspond (**character‑augmentation module**) |
| augmentation value $\psi(w)-1$ | $\chi(w)-1=1-X^EY^{-o}=-D/Y^o$, i.e. $\langle1-\chi(w)\rangle=\langle D\rangle$ | correspond |
| Crowell map $\theta:dw\mapsto\psi(w)-1$ | $\theta(dw)=(X{-}1)T-(Y{-}1)S=D$ (the **binary fundamental formula**) | **correspond — NEW (both cocycles)** |
| Fitting‑0 $\mathcal E_0=I_2$ of a state matrix | core ideal $\langle C(u,v)\rangle$, $C=2\times2$ minors of $[D,S]$ | **correspond — cores $=$ top Fitting ideal** |
| the single relation among $2\times2$ minors | **C8** Grassmann–Plücker syzygy | correspond |
| Alexander polynomial $\Delta_1=\gcd\mathcal E_1$ | $\gcd_{\mathbb Z[X,Y]}(T,S)$ | **correspond — NEW invariant** (see §4) |

**Mismatches, stated honestly.**
1. **Free monoid, not free group.** $W$ has no inverses; Crowell's theory is stated for groups. But the
   derived‑module *presentation* (eqs. 1–3) needs only the product rule, which holds on the free monoid,
   so $\mathscr A_\psi$, the Fox‑Jacobian matrix, and the elementary ideals carry over verbatim. The
   inverse rule $\partial(g^{-1})=-g^{-1}\partial g$ is the one absent piece (= our reversal$=$transpose
   dead end, L1·1 RE‑3 / lit‑fox §2). So we live in the *positive / one‑sided* corner of Alexander theory.
2. **$\psi$ vs $\chi$.** The structure note's $\chi$ ($x_1\mapsto Y^{-1}$) is $\psi$ ($x_1\mapsto Y$)
   twisted by the $\mathbb Z[Y^{\pm}]$‑automorphism $Y\mapsto Y^{-1}$ and cleared by the unit $Y^{o-1}$;
   it changes nothing at the **ideal** level (units), so we use $\psi$ ($t_1{=}X,t_2{=}Y$) for the
   matrices and read $\langle1-\chi(w)\rangle=\langle D\rangle$ for the augmentation.
3. **Rank‑1 specialization $X{=}2,Y{=}3$.** The single prime pair collapses the multivariable invariants
   (§4): the polynomial order ideal becomes trivial; $\langle D\rangle$ survives only after evaluation.
   Same rank‑1 degeneration flagged in L1·1.

---

## 3. The relation extracted (in OUR notation)

### 3.1 The second cocycle $T$ and the binary fundamental formula (NEW, verified AM1)

The Magnus matrix sees only $x_1$ ($\Phi(x_0)$ off‑diagonal $=0$), so $S=\chi(\partial w/\partial x_1)\cdot Y^{o-1}$
is *one* Fox derivative. The **second** $\chi$‑cocycle is the $x_0$‑derivative
$$T(w)=\sum_{i:\,b_i=0}X^{\#0\text{ before }i}\,Y^{\#1\text{ after }i}=Y^{o}\,\chi(\partial w/\partial x_0),
  \qquad\text{(cf. }S=\sum_{i:\,b_i=1}\!\cdots=Y^{o-1}\chi(\partial w/\partial x_1)).$$
Telescoping $\alpha_X(w)-\varepsilon_Y(w)$ over the two atoms $\alpha_X(b_i)-\varepsilon_Y(b_i)\in\{X{-}1,\,1{-}Y\}$ gives the **binary Fox fundamental formula**
$$\boxed{\,D(w)=(X-1)\,T(w)-(Y-1)\,S(w)\,}\qquad\bigl(=\theta(dw)=\chi(w)-1\text{ up to the unit }Y^{o}\bigr).$$
This is the **2‑variable refinement** of the gap formula $D=\sum_d S_d(X^d-Y)$ (lit‑fox §3): it keeps
**both** Fox derivatives $\partial_{x_0},\partial_{x_1}$ explicit against the **two atoms** $X{-}1$ and
$Y{-}1$ — the genuine Crowell presentation $\theta(dx_0)=X{-}1,\ \theta(dx_1)=Y{-}1$. It realizes $D$ as
the **Crowell‑map image of the universal derivation $dw$**, i.e. the **$\chi$‑augmentation value**, not
as a determinant.

### 3.2 Where $\langle D\rangle$ sits: the order ideal question (verified AM2–AM4)

The free derived module $\mathscr A_\psi\cong I_H=\langle X{-}1,Y{-}1\rangle$ has **order ideal
$\langle X{-}1,Y{-}1\rangle$** (the augmentation ideal), and $D=(X^E{-}1)-(Y^o{-}1)\in\langle X{-}1,Y{-}1\rangle$.
So $\langle D\rangle$ is **NOT** the order ideal of the (free) module. Precisely:

- **Single cyclic relator $w$** (impose $w=1$, the cycle relation): Alexander matrix $=$ the
  $\chi$‑Fox‑Jacobian row $(\,\chi\partial_{x_0}w,\ \chi\partial_{x_1}w\,)\sim(T,S)$. Crowell–Fox (2
  generators, 1 relator): $E_0=I_2=0$, **order ideal $E_1=\langle T(w),S(w)\rangle$**, $E_2=R$. By the
  fundamental formula **$D\in E_1$**, but $\Delta_1=\gcd(T,S)$ does **not** equal $D$ (§4), so
  $\langle D\rangle\subsetneq E_1$ over $\mathbb Z[X,Y]$. $\langle D\rangle$ is instead the **order of the
  rank‑1 abelianized cycle image $H_1$** (the augmentation value $\theta(dw)$), the analogue of the
  "$\Delta_0$ / order of torsion," not of the knot Alexander polynomial $\Delta_1$.
- **Evaluated, on a cycle:** the **rotation‑family** state matrix $[\,D(w^{(j)}),S(w^{(j)})\,]_j$ (all
  $D(w^{(j)})=D$) has $E_1=\langle D,\{S^{(j)}\}\rangle$. At $(2,3)$ on a **cycle word**
  ($G=\gcd_jS^{(j)}=|D|$) this is $\langle\gcd(D,\{S^{(j)}\})\rangle=\langle|D|\rangle$. **So
  $\langle D\rangle$ IS the evaluated order ideal $E_1$ of the rotation family on a genuine cycle**
  (verified on all $12$ cycle words up to length 4). This is exactly the structure note's $G=|D|$.

### 3.3 Cores $=E_0=I_2$; C8 is the Plücker syzygy (verified AM5)

For a family $w_1,\dots,w_m$, the state matrix $P=[\,D(w_i),S(w_i)\,]\in\mathbb Z[X,Y]^{m\times2}$ presents
the Alexander module $\operatorname{coker}P$. Its Fitting ideals:
$$E_0(\operatorname{coker}P)=I_2(P)=\langle C(w_i,w_j)\rangle\ (\text{the **core ideal**}),\qquad
  E_1(P)=I_1(P)=\langle D(w_i),S(w_i)\rangle.$$
Thus **the cores are exactly the order ideal $E_0=$ Fitting‑0 $=I_2$**, and the **C8** relation
$D(u)C(v,w)+D(v)C(w,u)+D(w)C(u,v)=0$ is the **Grassmann–Plücker syzygy** among the $2\times2$ minors —
the unique relation of a rank‑2 ($2$‑column) Alexander matrix. On cycle words every core is divisible by
$|D|$ ($E_0\subseteq\langle D\rangle$, all $12$ words), and $C(u,v)=0\iff$ the state vectors are
proportional $\iff$ same fixed point $S/D$ ($\iff$ rank drop $\Rightarrow E_0=0$, order ideal jumps to
$E_1$).

---

## 4. The new‑handle verdict (verified AM3, AM6) — honest

**The multivariable Alexander polynomial $\Delta_1(w)=\gcd_{\mathbb Z[X,Y]}(T,S)$ detects imprimitivity:**
$$\Delta_1(w)=\begin{cases}1,& w\text{ primitive (minimal period)},\\[2pt]
  \dfrac{X^{|w|}-Y^{o}}{X^{|u|}-Y^{o_u}}=\sum_{i=0}^{k-1}X^{i|u|}Y^{(k-1-i)o_u},& w=u^{k}\ (u\text{ primitive}).
\end{cases}$$
(verified symbolically: $\Delta_1((2,1)^2)=X^3{+}Y^2$ a proper factor of $D=X^6{-}Y^4$;
$\Delta_1((1)^3)=X^2{+}XY{+}Y^2$; $\Delta_1=1$ on every primitive test word). So for **primitive**
shapes — which is what a *minimal* Collatz cycle is — the Alexander polynomial is **trivial**, giving no
constraint; it only sees the *period* of imprimitive shapes (which reduce to their root).

**Do higher elementary ideals $E_k$ give a new handle? No — and for a structural reason (verified AM6).**
The state / Alexander matrix has **only 2 columns** (rank $\le2$: the single prime pair $(2,3)$). Hence
the entire Fitting filtration is exhausted by **just two** ideals,
$$E_1=I_1=\langle D,S\rangle\quad(\text{the ceiling/cocycle layer}),\qquad
  E_0=I_2=\langle\text{cores}\rangle\quad(\text{the Plücker layer}),$$
with $I_3=0$ (no $3\times3$ minor). **There is no $E_k$ finer than the cores.** And the multivariable
order ideal is *non‑informative*: $\gcd_{\mathbb Z[X,Y]}(D,\{S^{(j)}\})=1$ for primitive shapes, so the
principal $\langle D\rangle$ exists **only after the rank‑1 evaluation** $X{=}2,Y{=}3$ — exactly the
rank‑$\ge2$ degeneration that killed the informative Magnus determinant in L1·1.

**Net.** $\langle D\rangle$ is *not* the polynomial order ideal — it is the **$\chi$‑augmentation value**
$\theta(dw)$ (the order of the rank‑1 cycle homology), and it equals the **evaluated** rotation‑family
$E_1$ on a cycle. The cores are the **top Fitting ideal $E_0$**; the Fitting filtration **terminates
there**, so the cores/C8 are the *complete* determinantal obstruction — there is **no new scalar
exclusion handle** from higher $E_k$. This is an honest null on the prize, but it **closes** the carried
open question (STRUCTURE §5) and makes the module presentation **exact**.

---

## 5. Verification — `checks/lit_alexander_module.py` (exit 0, 13/13 PASS)

Battery: 93 words (80 random, $1\le n\le6$, gaps $1\le d\le5$, seed fixed) + 13 hand words; all
symbolic $\mathbb Z[X,Y]$ identities where possible; the $12$ cycle words ($G=|D|$) up to length 4 for
the evaluated claims. Robust kernel‑path insertion (confirmed from `/tmp`).

| Check | Claim | Result |
|---|---|---|
| AM1a | $S$ rebuilt from the binary word $=$ kernel $S$ | PASS |
| AM1b | **binary fundamental formula** $D=(X{-}1)T-(Y{-}1)S$ (2nd cocycle $T$) | PASS |
| AM2 | $\chi$‑augmentation $\langle1-\chi(w)\rangle=\langle D\rangle$ ($1-\chi(w)=-D/Y^o$) | PASS |
| AM3a | primitive shape $\Rightarrow\Delta_1=\gcd(T,S)=1$ (order ideal $E_1=\langle T,S\rangle$) | PASS |
| AM3b | imprimitive $w=u^k\Rightarrow\Delta_1=(X^{|w|}{-}Y^{o})/(X^{|u|}{-}Y^{o_u})$ ($\langle D\rangle\subsetneq E_1$) | PASS |
| AM3c | $D\in E_1$ with explicit cofactors $(X{-}1),-(Y{-}1)$ | PASS |
| AM4 | rotation‑family $E_1=\langle D\rangle$ at $(2,3)$ on cycle words | PASS |
| AM5a | cores $=2\times2$ minors $=E_0=I_2$ (Fitting‑0) | PASS |
| AM5b | C8 Plücker syzygy $=0$ (rank‑2 Grassmann relation) | PASS |
| AM5c | every core divisible by $|D|$ on cycle words ($E_0\subseteq\langle D\rangle$) | PASS |
| AM5d | core $=0\iff$ proportional state vectors (same fixed point $S/D$) | PASS |
| AM6a | Fitting filtration terminates at cores (2 columns; $I_3=0$) | PASS |
| AM6b | multivariable order ideal trivial: $\gcd_{\mathbb Z[X,Y]}(D,\{S^{(j)}\})=1$ (primitive) | PASS |

---

## 6. Proposed structure update (STRUCTURE.md §2 / §5)

- **§2 (the $\chi$‑augmentation quotient).** Adopt the exact identification: $\mathcal I_D$ is read inside
  the **Crowell derived / 2‑variable Alexander module** $\mathscr A_\psi$ of $\psi:W\to\langle X,Y\rangle$
  ($t_1{=}X,t_2{=}Y$); $\mathscr A_\psi\cong I_H=\langle X{-}1,Y{-}1\rangle$ is the
  **character‑augmentation module**. Record the **second cocycle $T=\chi\partial_{x_0}$** and the
  **binary fundamental formula $D=(X{-}1)T-(Y{-}1)S=\theta(dw)=\chi(w)-1$** as the canonical
  $\mathcal I_D$‑membership identity, refining the gap formula. State that **$\langle D\rangle$ is the
  augmentation value / rank‑1 order, not the module's order ideal** (the latter is
  $\langle X{-}1,Y{-}1\rangle$ free / $\langle T,S\rangle$ per relator).
- **§3 (the cores).** Promote "cores $=$ Plücker module" to **cores $=$ the top Fitting ideal
  $E_0=I_2$** of the rank‑2 state matrix, with C8 $=$ the Grassmann–Plücker syzygy; **the Fitting
  filtration terminates at $E_0$** (2 columns), so the cores/C8 are the complete determinantal
  obstruction.
- **§5 (open points).** **Close** the carried question "is $\langle D\rangle$ the order ideal and do
  higher $E_k$ help?": $\langle D\rangle$ is the *evaluated* rotation‑family $E_1$ (not the polynomial
  order ideal); higher $E_k$ **collapse** (rank‑2 / rank‑1 evaluation) — **no new handle** at the
  elementary‑ideal level. The only remaining finer route is a genuine **rank‑$\ge2$ enrichment** (two
  coprime moduli), the same open door L1·1 left.

**Promise rating: medium** — exact presentation + a new cocycle/identity + a *closed* open question, but
an honest null on a new exclusion lever. **Status: folded‑ready** (verified).

---

## 7. Open questions / probes (feeding R2 / R3 / R4)

- [ ] **(R2 — Alexander $=$ our $\chi$‑Fox‑Jacobian)** The single‑relator order ideal is
  $E_1=\langle T,S\rangle$ with $\Delta_1=\gcd(T,S)$ detecting imprimitivity. Is there a **rank‑2
  enrichment** (track $\{2,3\}$ *and* a second coprime pair, a $2$‑generator target $H$ of rank $4$) for
  which $\Delta_1$ becomes a *non‑trivial* Alexander polynomial on **primitive** cycle shapes — i.e. a
  genuine obstruction the rank‑1 evaluation hides? (This is the honest door this pass leaves open.)
- [ ] **(R3 — Plücker)** Cores $=E_0=I_2$ and C8 $=$ the Grassmann–Plücker quadric. Is C8 the
  **complete** generating relation of the core ideal (the second syzygy module of $I_2$ of a generic
  $m\times2$ matrix), or does a *straightening law* over $\mathbb Z[X,Y]$ add relations the integer
  evaluation hides? (Hand to Huang et al. / bracket algebra.)
- [ ] **(R3/R4 — the difference ideal)** $E_0$(rotation family) $=D\cdot\langle S^{(j)}{-}S^{(i)}\rangle$:
  the core ideal **factors** as $\langle D\rangle$ times the **difference ideal**
  $J=\langle S^{(j)}{-}S^{(i)}\rangle$. Is $J$ a finer, $o$‑independent invariant of the cycle shape
  (its evaluated gcd a new ceiling sharper than the cores) — or does it too collapse?
- [ ] **(R4 — Squier)** The derived‑module free resolution (eq. 2) is a length‑1 (projective) resolution.
  Does the **monoid** (no‑inverse) defect force a longer resolution / a genuine $H_2$ (a 3‑cell) where
  Squier's homology would place the C8 relation — or is the rank‑2 Koszul/Plücker syzygy the whole story?

---

## 8. Verdict for the roadmap

R1 (Crowell derived / multivariable Alexander module) is the **named theory of $\ker(1-\chi)$** and it
**delivers the exact module presentation**: $\mathscr A_\psi=$ the 2‑variable character‑augmentation
module, Alexander matrix $=$ $\chi$‑Fox‑Jacobian, with the **new second cocycle $T$** and the **binary
fundamental formula $D=(X{-}1)T-(Y{-}1)S$**. It **places** $\langle D\rangle$ (the augmentation value),
the cores ($=E_0=I_2$), and C8 (the Plücker syzygy) inside the Fitting filtration, and **closes** the
carried open question: $\langle D\rangle$ is the *evaluated* order ideal, the higher $E_k$ **collapse**
(rank‑2 ceiling / rank‑1 evaluation), and the multivariable Alexander polynomial is trivial on primitive
shapes. **No new scalar exclusion handle** — but the presentation is now exact, the obstruction set
(cores/C8) is certified *complete at the determinantal level*, and the only finer route (rank‑$\ge2$
enrichment) is precisely identified for R2. Honest yield: **the exact module, a new cocycle/identity, and
a closed question — not a new lever.**
