# The algebraic structure of the word-cocycle

This note is the structural backbone of [`cocycle-combine`](../RATIONALE.md): what algebraic
object the rotation-sum cocycle *is*, what group acts, and where the generic
$\mathbb{Z}[X,Y]$-combinatorics ends and the exceptional arithmetic of $2$ and $3$ begins.

Every claim below (tagged **C1**–**C11**) is certified as a polynomial identity in
$\mathbb{Z}[X,Y]$ by [`verify_structure.py`](verify_structure.py) (run it; exits 0). Notation is
the kernel's ([`lib/cocycle.py`](../lib/cocycle.py)): for a gap word $w=(d_0,\dots,d_{o-1})$ of
positive integers,
$$S(w)=\sum_{k=0}^{o-1}X^{e_k}Y^{\,o-1-k},\quad e_k=\textstyle\sum_{i\lt k}d_i,\qquad
D(w)=X^{E}-Y^{o},\quad E=\textstyle\sum_i d_i,\ \ o=\operatorname{len}w.$$
Specializing $(X,Y)\mapsto(2,3)$ recovers the integer rotation sums and $D=2^E-3^o$; on a genuine
cycle $\gcd_j S^{(j)}=|D|$, and $|D|$ is odd.

---

## 1. The representation — a transfer-matrix monoid homomorphism

Give each letter $d$ a $2\times2$ matrix over $R:=\mathbb{Z}[X,Y]$. The word map is then a product:
$$M(d)=\begin{pmatrix}Y&0\\1&X^{d}\end{pmatrix},\qquad
M(w)=\prod_{k=0}^{o-1}M(d_k)=\begin{pmatrix}Y^{\,o(w)}&0\\[2pt]S(w)&X^{\,E(w)}\end{pmatrix}.
\tag{C1, C2}$$
So $M:W\to GL_2\!\big(R[Y^{-1}]\big)$ is a **monoid homomorphism** from the free monoid of gap words.
The off-diagonal entry *is* $S$; the diagonal carries the two characters $w\mapsto Y^{o}$ and
$w\mapsto X^{E}$. The image sits in the affine/Borel group $(R,+)\rtimes(\text{characters})$ — i.e.
$S$ is read off a **transfer-matrix product**, which is the same matrix the
[`circulant_matrix`](../../circulant_matrix/RATIONALE.md) approach diagonalizes (the link to chase).

**$S$ is a rank-2 rational series.** In the language of weighted automata
([[berstel-reutenauer-noncommutative-rational-series]]), $S$ is a *recognizable / rational*
noncommutative series with the linear representation $(\lambda,\mu,\gamma)$,
$\lambda=(0,1)$, $\mu(d)=M(d)$, $\gamma=(1,0)^{\top}$, so $S(w)=\lambda\,\mu(w)\,\gamma$. This
representation is **minimal**: its Hankel matrix has **rank exactly $2$ (C10)** — the dimension-$2$
representation gives $\operatorname{rank}\le2$, and the $2\times2$ Hankel minor on rows/cols
$\{\varepsilon,(1)\}$, $\det\!\big(\begin{smallmatrix}0&1\\1&X+Y\end{smallmatrix}\big)=-1$, gives
$\operatorname{rank}\ge2$. So C1 is not just *a* representation but the *smallest* one, and the whole
machinery (residuals, Hadamard products, the rank/recurrence theory) of rational series applies.

Conjugation-invariant data of $M(w)$:
$$\operatorname{tr}M=X^{E}+Y^{o},\qquad \det M=X^{E}Y^{o},\qquad D=X^{E}-Y^{o}=\lambda_1-\lambda_2,$$
the difference of the two eigenvalues $\lambda_1=Y^o,\ \lambda_2=X^E$. The vector $(D,-S)^{\top}$ is
the $Y^{o}$-eigenvector of $M(w)$ **(C4)**, and $(0,1)^\top$ the $X^E$-eigenvector. The full
characteristic polynomial is $\det(tI-M(w))=(t-X^{E})(t-Y^{o})$ **(C11)**: a cyclic word is intrinsically
a **fibered** class with monodromy $M(w)$, and this is its fibered Alexander polynomial — so
$D=\lambda_2-\lambda_1$ is the monodromy's eigenvalue gap (see [[thurston-alexander-norm]]).

## 2. The group actions

**Rotation = conjugation.** Writing a length-$o$ word as $\tau=uv$, its rotation is $\rho=vu$, and
$$M(vu)=M(u)^{-1}\,M(uv)\,M(u). \tag{C3}$$
So the cyclic group $\mathbb{Z}/o$ acting by shift *is* conjugation in the matrix monoid.
**Cyclic words $=$ conjugacy classes $=$ candidate cycles**, and the rotation sums $S^{(j)}$ are the
$(2,1)$-entries along one conjugacy orbit.

**The genuine cocycle.** Normalize $\sigma(w):=S(w)/Y^{o(w)}$ and let the character
$\chi(w):=X^{E}/Y^{o}$ act on $R[Y^{-1}]$ by multiplication. Then
$$\sigma(uv)=\sigma(u)+\chi(u)\,\sigma(v), \tag{C5}$$
a **crossed homomorphism**: $\sigma\in Z^1(W,R_\chi)$. This is why "cocycle" is literally the right
word — the concatenation identity is a 1-cocycle condition for the character action.

## 3. Cohomology pins down why $G$ ignores prefactors

The coboundary of a constant $c$ is, at the $S$-level,
$$\partial c:\ w\longmapsto c\cdot D(w). \tag{C6}$$
Therefore **$S$ is canonically defined modulo $\langle D\rangle$** — and $D$ is exactly the cycle
denominator. On a cycle every rotation shares one $D$, so the statement $\gcd_j S^{(j)}=|D|$ reads:
*restricted to the conjugacy orbit, the cocycle equals its own coboundary generator up to the gcd.*
The recurring trick "$G$ (odd) kills the $X^{a}$ prefactor in a compensation" is just the observation
that those prefactors live in the coboundary direction $\langle D\rangle$, which the gcd already owns.

## 4. The payoff — a Plücker/Jacobi structure on the cores

Assign each word the vector $\mathbf v(w):=\big(D(w),\,S(w)\big)\in R^{2}$. The antisymmetric core
of the prototype is then a literal $2\times2$ determinant:
$$C(u,v)=S(uv)-S(vu)=\det\!\begin{pmatrix}D(u)&D(v)\\ S(u)&S(v)\end{pmatrix}=\mathbf v(u)\wedge\mathbf v(v).
\tag{C7}$$
Because $R^{2}$ has rank $2$, **any three words are $R$-linearly dependent**, which is the
Plücker relation (verified):
$$D(u)\,C(v,w)+D(v)\,C(w,u)+D(w)\,C(u,v)=0. \tag{C8}$$

Why this is a tool, not just decoration:
- **Cores come in bundles.** Once a family has a spanning pair of cores, every other core is an
  $R$-combination of them (via C8) — free leverage for the combinator search.
- **A simultaneity obstruction.** If two of $C(u,v),C(v,w),C(w,u)$ are small while the $D$'s are
  large, the third is *forced* large. Small cores cannot proliferate freely.
- **The $C=0$ locus is a rank-drop locus.** $C(u,v)=0\iff \mathbf v(u)\parallel\mathbf v(v)\iff
  D(u)S(v)=D(v)S(u)$ — a clean algebraic handle on the degenerate (shared-fixed-point / Steiner)
  stratum the ceiling cannot cover.

## 5. Generic vs. exceptional — the separation principle

Everything in §1–§4 is an **identity in $\mathbb{Z}[X,Y]$**: the *generic* cocycle layer, blind to
what $X,Y$ are. Arithmetic enters only at $X\mapsto2,\,Y\mapsto3$, in three escalating flavors:

| layer | what it uses | where it bites |
|---|---|---|
| **generic** | $\mathbb{Z}[X,Y]$ identities (C1–C8) | the representation, Plücker, all telescoping prefactors |
| **cheap arithmetic** | $G=\lvert D\rvert$ is **odd** ($X=2$) | dropping $X^{a}$ prefactors; the odd part $2^{\lvert e-d\rvert}-1$ of $X^{e-d}-1$ in P2 |
| **exceptional** | $S$-unit relations: $2^{a}-3^{b}$ unusually small ($4{-}3$, $9{-}8$, $3{-}2$, …) | where a small core meets a small $D$ — non-vacuous ceilings, and the $C=0$ strata |

**Working principle for the search:** do all cocycle algebra generically in $R$, and quarantine every
appeal to "$2$ and $3$" into a final, *named* arithmetic step. A compensation is **cheap** if its
core is a pure $\mathbb{Z}[X,Y]$ identity (it can only re-express the size bound $|D|\approx 2^E$,
matching the honest barrier inherited from `cycle-gcd`). The barrier is explicit: Ellison's
$|2^{x}-3^{y}|>2^{x}e^{-x/10}$ for $x>27$ ([[ellison1971-pillai]]) forces $|D|\gtrsim2.56^{\,o}$ off a
finite exceptional set, so a generic core $C$ bounds $|D|\le|C|$ to finitely many words. A compensation
can **beat transcendence theory only by cashing in an exceptional $2$–$3$ relation** — so those are the
ones worth hunting.

## 6. The Baker-free edge obstruction (Knight)

The §5 principle has a clean, *published* exemplar: Knight's proof that no Collatz **high cycle**
of integers exists ([`notes/knight2023-high-cycles.md`](notes/knight2023-high-cycles.md)). In our
language it is exactly a compensation collapsing to a monomial core, with the arithmetic finish
being the *cheap* tier (not Baker's theorem). With $g(v)=\sum_i X^{d_i}Y^{x-1-i}$ the
parity-vector numerator — which **equals our $S$ of the cyclic gap word** and Trümper's link
function $L$ — the two edge-bit identities are

$$Y\,g(1u0)-g(0u1)+D = X^{E-1}(X-1),\qquad g(p01)-g(p10)=X^{E-2}(X-1). \tag{C9a, C9b}$$

The central block $u$ (resp. prefix $p$) cancels completely: these are pure
$\mathbb{Z}[X,Y]$ identities (the **generic** layer). Arithmetic enters only at $X\mapsto2$, where
both right sides become the **even monomials** $2^{E-1},2^{E-2}$. The high cycle is realized by the
**upper Christoffel word** $v_h=1u0$ (Halbeisen–Hungerbühler [[halbeisen-hungerbuhler1997-rational-collatz-bounds]]:
the balanced/Christoffel rotation is exactly the extremal-minimum class), whose reverse $v_h^{R}=0u1$ is
*another rotation of the same cyclic word* (Cohn [[cohn1972-markoff-forms]]: reverse $=$ conjugacy for
primitive/Christoffel words) — so on an integer cycle both $g$-values share the odd denominator $D$ and
$G=|D|$ divides the integer combination, hence divides a power of $2$, forcing $|D|=1$. **No lower
bound on $|2^E-3^o|$ is used** — the obstruction is purely the *parity* (even core vs. odd $G$).

This sharpens the §5 reading of "cheap arithmetic": a monomial core $X^{a}(X-1)$ is the strongest
*Baker-free* ceiling — it kills a whole rotation class (the high cycle, the lexicographic extreme)
without transcendence theory, but only that class. Beating the size barrier for *all* cycles still
needs the exceptional $2$–$3$ tier. The lever C9 supplies is **which** rotation pair to combine:
the two that straddle the Christoffel seam, where the core degenerates to a monomial.

**Literature corroboration of §1–§4.** Trümper's free-semigroup development
([`notes/trumper2014-free-semigroup.md`](notes/trumper2014-free-semigroup.md)) is an independent
rediscovery of the representation: his link function $L(w)=\sum_k X^{e_k}Y^{o-1-k}$ **is** $S$, his
$D(w)=X^E-Y^o$ is ours, and his composition laws
$L(w_aw_b)=Y^{o_b}L(w_a)+X^{E_a}L(w_b)$, $D(w_aw_b)=Y^{o_b}D(w_a)+X^{E_a}D(w_b)$ are exactly the
$(2,1)$- and eigenvalue-entries of the monoid hom **C1/C2/C5**. His commutator
$L_{ab}-L_{ba}=D_aL_b-D_bL_a$ is the wedge core **C7**; his one-step rotation law
$\Phi\mapsto(Y\Phi\pm1)/X^{d_0}$ on the cycle function $\Phi=L/D$ is **C3** acting on the cocycle;
and $L(w^n)/D(w^n)=L(w)/D(w)$ (repetition-invariance) is the **P1** circuit degeneracy.

---

## How the certified results read in this language

- **P0** $S(uv)-S(vu)=C(u,v)$: the defining wedge **(C7)**; the $w^qw'$ prefactor $X^{(q-1)|w|}$ is a
  coboundary multiple **(C6)**, hence $q$-free after $G$ absorbs it.
- **P1** circuit $d^o$: $\mathbf v$ rank-drops ($S=D/(X^d-Y)$, all rotations equal), so every core
  vanishes — the $C=0$ locus of §4.
- **P2** single-defect $d^aed^b$: the ceiling is the *odd part at $X=2$* of one wedge
  $S(\rho_{o-2})-S(\rho_{o-1})=X^{(o-1)d}(X^{e-d}-1)$ — generic wedge (C7) + one **cheap-arithmetic**
  step. Independent of $a,b$ because the coboundary prefactor $X^{(o-1)d}$ is gcd-invisible.

## Open structural threads

1. **Plücker-generate a family's cores** — fix a spanning pair, derive the rest, read off the
   minimal $|C|$ without a fresh search per word.
2. **Whole-orbit wedges from $M$** — express all $\binom{o}{2}$ rotation-pair cores as entries of
   $M(\tau)$ conjugates at once; does the matrix expose a smaller joint core than any single pair?
3. **Bridge to `circulant_matrix`** — $M(w)$ here is the $2\times2$ transfer matrix; relate its
   spectrum to the $o\times o$ circulant's eigenvalues $\hat c_\ell=D/(2^{E/o}\omega^\ell-3)$.
4. **Is $C$ a Lie 2-cocycle?** C8 is the Jacobi/Plücker identity; check whether $(R^2,\wedge)$ with
   the word-indexing carries a Lie-algebra / Poisson structure worth exploiting.
5. **Generalize C9 beyond the Christoffel seam** — C9 needs $1u0,0u1$ to be one rotation class.
   Which other rotation *pairs* of which words give a monomial (or monomial$\times(X-1)$) core?
   A monomial core is the Baker-free ceiling; map the full locus of word-pairs that achieve one.
6. **The cycle function $\Phi=S/D$ and its orbit** — Trümper's rotation law
   $\Phi\mapsto(Y\Phi\pm1)/X^{d_0}$ realizes the Collatz map *on the start number* as a Möbius/affine
   action along the conjugacy orbit (C3). Does the orbit of $\Phi$ expose cycle obstructions
   (integrality of $\Phi$) more directly than the rotation sums $S^{(j)}$ do?
7. **The $3m\!+\!1$ vs. $3m\!-\!1$ duality** — $S$ is shared by both rules; only $D=X^E-Y^o$ flips
   sign ($\bar D=Y^o-X^E$). Trümper reads each cyclic word as a cycle under *whichever* rule makes
   $D>0$. Is the sign of $D$ a clean generic/exceptional discriminant for the search?
8. **Cocycle complexity $\leftrightarrow$ controlled factorization (flagship).** Recast the whole
   search as a complexity statement. *Dictionary:* a $\mathbb{Z}[X,Y]$-combination of rotation sums is
   a move within the cocycle class $[\sigma]\in H^1$ modulo the coboundary $\langle D\rangle$
   (**C5/C6**); the shift-gcd $G=\gcd_j S^{(j)}=|D|$ is the **minimal integral representative** (the
   "content") of that class. *Candidate complexity measures* (smallest-first): (i) the **rank** of $S$
   as a rational series — but that is fixed at $2$ (**C10**), so the discriminating quantity must live
   in the **core** $C$ or in a parametrized family, not in $S$; (ii) the **Mahler measure** of the
   reduced core $\mathrm{M}_X\!\big(C(\rho^iw,\rho^jw)\big|_{Y=1}\big)$ — which by **Lind–Schmidt–Ward**
   *is* the topological entropy of the core's algebraic $\mathbb{Z}$-action, giving "low complexity" a
   rigorous dynamical meaning ($M=1\iff h=0$); (iii) the subword complexity of
   $w$ (Sturmian/Christoffel $=$ minimal). There is a *second, complementary* complexity
   axis — the **span** (Newton-polytope width $=$ Alexander/Thurston norm), distinct from the **height**
   (Mahler/entropy) above; they are different invariants of the same core, meeting only on fibered faces
   (Fried/McMullen). Our words are intrinsically fibered (monodromy $M(w)$, Alexander polynomial
   $(t-X^E)(t-Y^o)$, **C11**), and $\operatorname{width}_{(\log2,\log3)}N(D)=|E\log2-o\log3|$ recasts the
   size barrier as a polytope width. Full treatment: [[thurston-alexander-norm]]. *The load-bearing
   link is Kronecker's theorem:* an integer
   polynomial nonzero at $0$ has Mahler measure $1$ **iff** it is a monomial times a product of
   cyclotomics. **Observed across the bench** (not yet certified): the structured cores are exactly the
   Mahler-$1$ ones — circuit P1 ($C=0$), single-defect P2 ($X^{(o-1)d}(X^{e-d}-1)$), Christoffel/edge
   C9 ($X^{E-1}(X-1)$) all factor as $X^{a}\prod\Phi_{k}(X)$, while generic $C(u,v)$ carries a
   non-cyclotomic factor (Mahler $>1$). So the conjecture sharpens to: *a family admits a controlled
   (monomial$\times$cyclotomic, Mahler-$1$) core $\iff$ it lies in a low-complexity stratum*, with
   **Lehmer's problem** governing how small a *nontrivial* complexity can be. *The §5 payoff (now sharp):*
   a Mahler-$1$ core gives the ceiling $G\mid 2^{a}\prod_k\Phi_{n_k}(2)$; by **Bang–Zsygmondy** every
   factor $\Phi_{n_k}(2)$ with $n_k\notin\{1,2,6\}$ contributes a *new* primitive prime $\ge n_k+1$ that
   then divides $G=|D|$. So $G$ can stay small enough to beat the Ellison barrier
   ([[ellison1971-pillai]]) **only if the core's cyclotomic indices collapse into $\{1,2,6\}$** (forcing
   $G=2^a3^c$, where Baker/Bilu–Hanrot–Voutier take over) — a concrete **search-pruning gate** on which
   structured words could possibly host an exceptional cycle. *Next steps:* (a) fix one complexity $\kappa$ and
   certify the easy direction (structured $\Rightarrow$ Mahler $1$); (b) survey the literature for an
   existing notion of cocycle/coboundary complexity (quasimorphism **defect**, bounded cohomology) and
   for cyclotomic-factorization criteria; (c) test whether $\kappa$ is rotation-invariant and
   sub-additive under concatenation (it should descend from the **C1** monoid hom). Full literature
   chain (entropy/Mahler, Thurston/Alexander, $S$-unit endpoint) and references: [[cocycle-complexity]].
