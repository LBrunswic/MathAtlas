# Report — Thurston norm vs. Alexander norm, and their translation into the cohomology of words

- **Source file:** _topic/report note_ (rigorous parts certified in `verify_structure.py` as **C11**, and
  computed here; the 3-manifold statements are cited to McMullen/Thurston/Turaev/Fried, not re-proved).
- **Feeds:** thread §8; the cohomological half of [[cocycle-complexity]]; uses **C1, C4, C5, C6, C7, C11**.
- **Formal companion:** [[thurston-alexander-formal]] gives the Bourbaki definition–theorem–proof version,
  including the proved inequality $\lVert\phi\rVert_A\le\lVert\phi\rVert_T$.

This report does three things: (1) recall the two norms in 3-manifold topology and McMullen's inequality
between them; (2) extract the *purely algebraic* skeleton (group ring + Newton polytope + Fox calculus)
that needs no 3-manifold; (3) show our word-cocycle is a literal instance of that skeleton, translate
both norms into it, and say precisely what is rigorous, what is analogy, and how it relates to the Mahler
(entropy) complexity of [[cocycle-complexity]].

---

## 1. The two norms in their home (3-manifold topology)

Let $M$ be a compact orientable $3$-manifold, $H=H_1(M;\mathbb Z)/\mathrm{tors}$ (free abelian of rank
$b_1$), so $H^1(M;\mathbb Z)=\operatorname{Hom}(H,\mathbb Z)$ are the integral cohomology classes $\phi$.

**Thurston norm (geometric).** For $\phi\in H^1(M;\mathbb Z)$, dual to properly embedded surfaces $S$,
$$\|\phi\|_T=\min_{S\,\text{dual to }\phi}\chi_-(S),\qquad \chi_-(S)=\sum_{\text{components }S_i}\max\!\big(0,-\chi(S_i)\big).$$
It is a seminorm; its unit ball is a rational polytope. Top-dimensional faces whose open cone consists of
classes represented by *fibrations* $M\to S^1$ are **fibered faces** (Thurston; Fried).

**Alexander norm (algebraic).** Let $\Delta_M\in\mathbb Z[H]$ be the Alexander polynomial — the order of
the Alexander module $H_1(\widetilde M;\mathbb Z)$ over $\mathbb Z[H]$, $\widetilde M\to M$ the maximal
free-abelian cover. Write $\Delta_M=\sum_{g\in H}a_g\,g$ with Newton polytope
$N(\Delta_M)=\operatorname{conv}\{g:a_g\ne0\}\subset H\otimes\mathbb R$. Then
$$\|\phi\|_A=\max_{g,h\in N(\Delta_M)}\phi(g-h)=\operatorname{width}_\phi N(\Delta_M).$$

**McMullen's theorem** (*Ann. Sci. ENS* 35 (2002), 153–171). If $b_1(M)\ge2$ then
$$\|\phi\|_A\le\|\phi\|_T\qquad\text{for all }\phi\in H^1(M;\mathbb Z),$$
with the correction $\|\phi\|_A\le\|\phi\|_T+\big(1+b_3(M)\big)\|\phi\|_1$ when $b_1=1$ (for a knot
complement this is $\deg\Delta_K\le 2g(K)$, since $\|\phi\|_T=2g-1$). **On a fibered face the inequality is
an equality** and (Fried) $\Delta_M$ restricted there is the **characteristic polynomial of the
monodromy**; its Mahler measure is the monodromy's dilatation/entropy.

So the two norms are two readings of *one* polynomial $\Delta_M$: the Alexander/Thurston norm is its
**Newton-polytope width** (a degree/span), while the Mahler measure of the same $\Delta_M$ (on a fibered
cone) is the **dynamical dilatation** (a height). They are independent invariants that *coincide on
fibered faces in the sense of belonging to the same polynomial*.

---

## 2. The purely algebraic skeleton (no 3-manifold needed)

Three classical facts strip the topology away:

- **Newton-polytope seminorm.** For *any* $f\in\mathbb Z[H]$, $H$ free abelian, $\phi\mapsto
  \operatorname{width}_\phi N(f)$ is a seminorm on $\operatorname{Hom}(H,\mathbb R)$. The Alexander norm is
  this seminorm for $f=\Delta_M$.
- **Alexander polynomial from a presentation (Fox calculus).** For a group $G=\langle g_i\mid r_j\rangle$
  with $H=G^{ab}/\mathrm{tors}$, the Alexander matrix is $\big(\overline{\partial r_j/\partial g_i}\big)$
  (Fox derivatives, abelianised into $\mathbb Z[H]$); $\Delta$ is the gcd of its maximal minors. **Turaev**
  (*A norm for the cohomology of 2-complexes*, arXiv:math/0203042) defines a Thurston-type norm for any
  finite $2$-complex and proves the Alexander–Fox polynomial lower-bounds it — so "Alexander $\le$
  Thurston" is intrinsically combinatorial.
- **Magnus embedding.** The free group $F=\langle g_i\rangle$ embeds into the affine/Borel group by
  $g\mapsto\big(\begin{smallmatrix}\bar g&0\\ \partial g&1\end{smallmatrix}\big)$, where $\bar g\in H$ is
  the abelianisation and $\partial g$ the (column of) Fox derivatives. The off-diagonal is a **crossed
  homomorphism** (1-cocycle) for the $H$-action — it satisfies the cocycle/derivation product rule.

---

## 3. Our cohomology of words *is* this skeleton

Compare the Magnus matrix with our **C1** transfer matrix:
$$\text{Magnus }\begin{pmatrix}\bar g&0\\ \partial g&1\end{pmatrix}\qquad\longleftrightarrow\qquad
M(w)=\begin{pmatrix}Y^{o}&0\\ S(w)&X^{E}\end{pmatrix}.$$
The dictionary is exact:

| Magnus / Fox / Alexander | our word-cocycle |
|---|---|
| abelianisation $\bar w\in H$ | the grading $(E,o)$, characters $Y^o,\ X^E$ |
| Fox derivative $\partial w$ (off-diagonal) | $S(w)=\sum_kX^{e_k}Y^{o-1-k}$ — a **Fox-derivative-type prefix sum** |
| cocycle/derivation rule for $\partial$ | $S(uv)=Y^{o_v}S(u)+X^{E_u}S(v)$ (**C5**) |
| fundamental formula $w-1=\sum\partial w\,(g-1)$ | the augmentation $D=X^E-Y^o$ (the coboundary, **C6**) |
| group ring $\mathbb Z[H]$, $H$ free abelian | $\mathbb Z[X^{\pm},Y^{\pm}]$, here $H=\mathbb Z^2$ (the $X,Y$ lattice) |
| Alexander module / its order $\Delta$ | the shift-module of a cyclic word; **monodromy char poly** below |

**A cyclic word is intrinsically a fibered class.** A length-$o$ cyclic word *is* a loop, and its
rotation = conjugation by $M(u)$ (**C3**) makes $M(w)$ the **monodromy** of the corresponding mapping
torus. Its characteristic polynomial is, certified as **C11**,
$$\Delta_w(t)=\det\!\big(tI-M(w)\big)=(t-X^{E})(t-Y^{o})=t^2-(X^E+Y^o)\,t+X^EY^o,$$
with eigenvalues $\lambda_1=Y^o$ (eigenvector $(D,-S)^\top$, **C4**) and $\lambda_2=X^E$ (eigenvector
$(0,1)^\top$). Hence
$$\boxed{\,D=X^E-Y^o=\lambda_2-\lambda_1\,}$$
is the **eigenvalue gap** of the monodromy — the Alexander polynomial's "size" in the fiber direction.
Because words are always fibered, **McMullen's inequality is for us an equality**, and the content moves to
*which* polytope/height we read off $\Delta_w$ and the cores.

---

## 4. The two norms, translated and computed

There are two natural lattices of directions $\phi$:

**(a) The fiber/shift direction $t$.** Reading $\Delta_w(t)=(t-X^E)(t-Y^o)$ as a polynomial in $t$ over
$\mathbb Z[X,Y]$, its $t$-degree is $2$. So the "Alexander norm of the fibering class" is $\deg_t\Delta_w=2$
— the fiber has $b_1=2$ (the rank-2 module $S$ lives on), consistent with $S$ having **rank exactly 2**
(**C10**). This is the degenerate-but-honest statement that every cyclic word fibers with a rank-2 fiber.

**(b) The gap-grading directions $(X,Y)$ — where the geometry lives.** Here $H=\mathbb Z^2$ and we take
Newton polytopes in the exponent plane $(a_X,a_Y)$:

- $N(D)$ is the **segment** $(E,0)$–$(0,o)$. Its width in a direction $\phi=(\alpha,\beta)$ is
  $|\alpha E-\beta o|$. In the **Collatz direction** $\phi=(\log2,\log3)$,
  $$\operatorname{width}_\phi N(D)=|E\log2-o\log3|=\big|\log(2^E/3^o)\big|=\big|\log|\lambda_2/\lambda_1|\big|.$$
  *The Alexander/Newton norm of $D$ in the Collatz direction is exactly the log eigenvalue-ratio that
  controls $|D|=|2^E-3^o|$* — so the Alexander norm reframes the Ellison size barrier
  ([[ellison1971-pillai]]) as a polytope width. (Verified: $w=(3,1,1,2,4)$ gives $2.1316=|11\log2-5\log3|$.)
- $N(S)$ is the **staircase hull** of $\{(e_k,o-1-k)\}$ — e.g. $w=(3,1,1,2,4)$:
  $(0,4),(3,3),(4,2),(5,1),(7,0)$.
- $N\big(C(u,v)\big)$ is a $2$-dimensional polygon; its width is the "span complexity" of the core.

**The decisive clarification (span vs. height).** The Thurston/Alexander norm is the Newton-polytope
**width** — a *degree/span* invariant. It is **not** the Mahler measure (a *height*) of
[[cocycle-complexity]]. They are independent: a cyclotomic $\Phi_k(X)$ has Mahler measure $1$ but Newton
width $\varphi(k)$ (large); $2X-1$ has width $1$ but Mahler measure $2$. So the program has **two
complementary complexity axes** on the same core polynomial:

| axis | invariant of the core | what it measures | program |
|---|---|---|---|
| **span** | Newton-polytope width (Alexander/Thurston norm) | spread of the support; "degree" | this report |
| **height** | Mahler measure $=$ entropy (Lind–Schmidt–Ward) | root location; dilatation | [[cocycle-complexity]] |

By Fried/McMullen they **meet on the fibered cone**: there $\Delta=$ monodromy char poly, its width $=$ the
norm and its Mahler measure $=$ the dilatation. For us every word is fibered, so $\Delta_w=(t-X^E)(t-Y^o)$
carries *both* — width (in $t$) $=2$, and Mahler measure (the dilatation) governed by $|\lambda_2/\lambda_1|
=2^E/3^o$, i.e. the same $D$-size again.

---

## 5. What this buys, and the honest ledger

**Rigorous / certified.** C1 (Magnus/transfer matrix), C5 (Fox-derivative cocycle rule), C6 ($D$ = the
augmentation/coboundary), C4+C11 (monodromy char poly $(t-X^E)(t-Y^o)$, $D=\lambda_2-\lambda_1$). The
Newton polytopes of $S,D,C$ and their widths are explicitly computable; $\operatorname{width}_{(\log2,\log3)}N(D)=|E\log2-o\log3|$ is an identity.

**Cited, not re-proved.** McMullen's $\|\phi\|_A\le\|\phi\|_T$ and its equality on fibered faces;
Turaev's $2$-complex norm; Fried's monodromy/dilatation identification. These live in 3-manifold / 2-complex
topology; we *instantiate their algebraic side*, we do not import a specific 3-manifold.

**Analogy, flagged.** Calling $D$/$\Delta_w$ "the Alexander polynomial" of the cyclic word is exact in the
fibered (monodromy char poly) sense; identifying a full *Alexander module* of a cyclic word (the shift
module with relation $\Delta_w(t)$ and its order ideal over $\mathbb Z[X^\pm,Y^\pm,t^\pm]$) and proving a
McMullen-type inequality against a Turaev complexity of the word's presentation $2$-complex is **open**.

**Next steps.** (a) Define the multivariable Alexander module of a cyclic word and compute its order ideal
in $\mathbb Z[X,Y,t]$ — does its Newton polytope recover $N(S)\cup N(D)$? (b) Prove
$\operatorname{width}_{(\log2,\log3)}N(D)=|E\log2-o\log3|$ as the certified "Alexander form of the barrier"
(candidate C12). (c) Decide whether the *span* axis adds anything the *height* axis misses for beating the
barrier — likely not for $D$ (both reduce to $2^E/3^o$), but the **core** $C(u,v)$ may have small Mahler
measure (Mahler-1, cyclotomic) yet large Newton width, or vice versa, and that mismatch is exactly where to
look.
