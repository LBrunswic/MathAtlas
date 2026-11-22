# Leverage: Gröbner–Shirshov bases (Bokut–Chen, *Bull. Math. Sci.* 2014) — L1·3

**Promise:** medium–high — this is the **decision-procedure / normal-form** layer the roadmap asked
for, and it returns a sharp, honest verdict: **the balanced slot-swap $(\star)$ is *already* a
(reduced) Gröbner–Shirshov basis — vacuously, because the cocycle $S$ is INJECTIVE per length**, so
the $S$-preserving word congruence is *trivial*. No new length-reducing *move* falls out (the prize is
a clean null), but three concrete structures the drafts did **not** have do:
**(1)** the per-length **injectivity pin** ($\Phi$ faithful ⇒ "$S(w)=S(w')$" forces $w=w'$), which
*resolves* the L1·2 open question about normal forms;
**(2)** the explicit **overlap critical-pair $S$-polynomial** $\delta=X^{|A|}C(B,C)-Y^{\operatorname{len}C}C(A,B)$
— the exact 3-cell L1·4 (Squier) consumes;
**(3)** the correct **CDL setting** (Mikhalev–Zolotykh "double free algebra" over *commutative*
coefficients, three composition types $C_1/C_2/C_3$) and the coefficient-ring caveat
(binomial/monic relations need **no field** — they work over $\mathbb Z[1/6]$ and $R/\langle D\rangle$;
but $\langle D\rangle$ is an **integer**, not polynomial, ideal).
**Status:** read in depth (CDL for associative algebras §2.1; CDL over commutative algebras §2.5
= Mikhalev–Zolotykh Thm 2.24; semigroup congruence/normal-form machinery §3 intro); dictionary built;
**13/13 checks pass** (`checks/lit_groebner_shirshov.py`, exit 0). Verdict: **CONFLUENT (vacuously) —
no new move**, with the normal forms pinned and the two critical pairs handed to L1·4.
**Last iterated:** 2026-06-08

**Source:** L. A. Bokut & Yuqun Chen, *Gröbner–Shirshov bases and their calculation*, Bull. Math. Sci.
**4** (2014) 325–395 — [`sources/bokut-chen-groebner-shirshov-1303.5366.pdf`](../sources/bokut-chen-groebner-shirshov-1303.5366.pdf)
(arXiv:1303.5366v3, 92 pp., read in depth). Section/theorem numbers below are Bokut–Chen's own.

---

## 1. What Bokut–Chen give (the CDL machinery, with citations)

The **Composition–Diamond lemma (CDL)** is the noncommutative analogue of Buchberger's theorem: a
generating set $S$ of an ideal is a **Gröbner–Shirshov basis (GSB)** iff every *composition*
(critical pair / $S$-polynomial) is *trivial* (reduces to $0$); equivalently iff the
$S$-irreducible words $\operatorname{Irr}(S)$ form a linear basis of the quotient.

| B–C ref | object | content |
|---|---|---|
| §2.1, p. 18 | **monomial order** | well-order $\gt$ on $X^\ast$ with $u\gt v\Rightarrow w_1uw_2\gt w_1vw_2$; standard example **deg-lex** (degree first, then lex) |
| §2.1 (i) | **intersection composition** | $w=\bar f b=a\bar g$, $|\bar f|+|\bar g|\gt|w|$ (overlap): $(f,g)_w=fb-ag$ |
| §2.1 (ii) | **inclusion composition** | $w=\bar f=a\bar g b$ (one leading word inside the other): $(f,g)_w=f-agb$ |
| §2.1 | **GSB / triviality** | $S$ monic is a GSB iff every composition $\equiv0\bmod(S,w)$; $\operatorname{Irr}(S)=\{u: u\ne a\bar sb\}$ |
| Thm 2.3 | **CD-lemma (field $k$)** | (i) $S$ a GSB $\iff$ (ii) $f\in\mathrm{Id}(S)\Rightarrow \bar f=a\bar sb$ $\iff$ (iii) $\operatorname{Irr}(S)$ is a $k$-basis of $k\langle X\mid S\rangle$ |
| §2.1 "Shirshov algorithm" | **completion** | add all nontrivial compositions, make monic, iterate $\to$ GS completion $S^c$ with $\mathrm{Id}(S^c)=\mathrm{Id}(S)$; then minimize/reduce |
| Thm 2.5 | **uniqueness** | every ideal has a *unique reduced* GSB for a fixed order |
| §3 intro, p. 9 & p. 40 | **semigroup case** | for $P=\mathrm{sgp}\langle X\mid S\rangle$ via $kP=k\langle X\mid S\rangle$: **compositions of binomials $u_i-v_i$ are again binomials**; $\operatorname{Irr}(S^c)$ = **normal forms** of $P$ |
| **§2.5, Thm 2.24** | **CDL over a *commutative* algebra** (Mikhalev–Zolotykh) | the **"double free associative algebra"** $k[X]\otimes k\langle Y\rangle$: words $u=u^Xu^Y$, $u^X\in[X]$ (free *commutative* monoid), $u^Y\in Y^\ast$ (free *noncommutative* monoid); **three** composition types $C_1$ inclusion, $C_2$ overlap, $C_3$ **external** |

**The genuinely relevant theorem is §2.5 (Theorem 2.24), not the field case §2.1.** Reason
(dictionary §2 below): our coefficients $X,Y$ are *commutative* and the slot-swap frame
$X^{|P|}Y^{\operatorname{len}Q}$ is a commutative *monomial coefficient that depends on the slot
position*. B–C's $C_3$ "**External**" composition — which exists **only** over commutative
coefficients, when $\gcd$ of the commutative $X$-parts is non-empty (p. 35) — is precisely the
critical-pair type the frame prefactors force.

---

## 2. Dictionary — GSB/CDL $\leftrightarrow$ the Fox presentation of $\mathcal I_D$

Our words are positive words $w=(d_0,\dots,d_{n-1})$ in the **free monoid** $Y^\ast$ on the infinite
gap alphabet $\{x_d:d\in\mathbb N_{\gt0}\}$. The Magnus/Fox transfer matrix
$$\Phi(w)=\begin{pmatrix}X^{|w|}&S(w)\\0&Y^{\operatorname{len}w}\end{pmatrix}$$
is a monoid hom $Y^\ast\to\mathrm{UT}_2(R)$, $R=\mathbb Z[X,Y]$ (L1·2 F4). The production rule is the
**balanced slot-swap** $(\star)$: for $\chi(M)=\chi(M')$ (i.e. $|M|=|M'|$ **and** $\operatorname{len}M=\operatorname{len}M'$),
$$S(PMQ)-S(PM'Q)=X^{|P|}Y^{\operatorname{len}Q}\bigl(S(M)-S(M')\bigr).\tag{$\star$}$$

| B–C notion | our object | status |
|---|---|---|
| free monoid $X^\ast$ over a field | gap monoid $Y^\ast$, **coefficients $R=\mathbb Z[X,Y]$ commutative** | **mismatch → use §2.5, not §2.1** |
| double free algebra $k[X]\otimes k\langle Y\rangle$ | $R\langle x_1,x_2,\dots\rangle$: commutative part $[X]=\{X^aY^b\}$, noncommutative part = words | **the exact setting (Thm 2.24)** |
| commutative coefficient $u^X\in[X]$ | the **frame prefactor** $X^{|P|}Y^{\operatorname{len}Q}=\alpha_X(P)\varepsilon_Y(Q)$ | **correspond — slot position $\Rightarrow$ the $X$-part** |
| monomial order **deg-lex** | the bigraded weight $(|\cdot|,\operatorname{len})$ (letter-sum, then length) **refined by lex** | correspond; $X\!\leftrightarrow\!2,Y\!\leftrightarrow\!3$ is the grading |
| binomial semigroup relation $u-v$ | the swap as a relation $PMQ-PM'Q$ | **trivial — see §3 (injectivity)** |
| intersection/overlap composition $C_2$ | overlapping slots $AB\mid BC$ in $ABC$ | **the live critical pair → $\delta$, §4** |
| inclusion composition $C_1$ | nested slots (a swap inside a swapped block) | resolves by **chain rule / block-coarsening** (L1·2 F8) |
| **external composition $C_3$** | **disjoint** slots $PM_1QM_2R$ | resolves: **frame monomials commute in $R$** (verified C5) |
| GS completion $S^c$, $\operatorname{Irr}(S^c)$ = normal forms | the normal-form question of L1·2 | **answered — §3** |

**Coefficient-ring caveat (addressed).** CDL Thm 2.3 is stated over a **field** $k$ because reduction
must *clear leading coefficients*. We do **not** need a field: our relations are **binomial / monic**
(leading coefficient $1$, or a frame monomial that is a *unit* in $\mathbb Z[1/6][X^{\pm},Y^{\pm}]$),
and B–C's **semigroup case** (p. 9: "compositions of binomials are binomials") and the over-commutative
§2.5 both go through over any commutative coefficient ring — in particular over the **PID
$\mathbb Z[1/6]$** and over $R/\langle D\rangle$. The one place a field would matter — non-unit leading
coefficients producing zero-divisors mod $D$ — is avoided by keeping the graded order so that
$D=X^E-Y^o$ itself reads as the **monic binomial $X^E\to Y^o$** (§5, D1).

**Mismatches, stated honestly.**
1. **Commutative coefficients, not a free algebra over a field.** This is *why* it is §2.5 and not
   §2.1, and why it is **not** commutative Buchberger: the noncommutative word order is load-bearing
   because the frame coefficient depends on *where* the slot sits ($X^{|P|}$ vs $Y^{\operatorname{len}Q}$).
2. **Infinite alphabet.** $\{x_d\}$ is infinite — **no obstruction** (B–C/Shirshov allow any
   well-ordered $X$); the alphabet collapses onto the one-parameter grading $x_d\mapsto X^d$.
3. **$\langle D\rangle$ is an integer ideal, not a polynomial one** (§5, D2): the polynomial
   $X^E-Y^o$ can never divide a nonzero core, so the "ideal" $\mathcal I_D$ is an *evaluation*
   ($X,Y\to2,3$) phenomenon layered on top of the word-level GSB.

---

## 3. Is it a GSB? — the verdict, and the normal forms

### 3.1 The structural pin: $S$ is injective per length ⇒ $\Phi$ is faithful (NEW)

For a fixed length $n$, the coefficient of $Y^{n-1-k}$ in $S(w)=\sum_{k=0}^{n-1}X^{e_k}Y^{n-1-k}$ is
**exactly** $X^{e_k}$ (the $k$-th partial sum), because the $Y$-exponents $n-1-k$ are distinct for
distinct $k$. Hence
$$\boxed{\ \text{len}\,w=\text{len}\,w'\ \text{and}\ S(w)=S(w')\ \Longrightarrow\ w=w'\ }$$
(verified **A1/A2**, exhaustively for $n\le7,\ N\le15$). Since $\Phi(w)=\Phi(w')$ forces equal length
(the diagonal $Y^{\operatorname{len}}$) and then equal $S$, the transfer matrix $\Phi$ is an
**injective** monoid hom: *the cocycle $S$ together with the length faithfully encodes the word.*

**Consequence for the GSB.** The balanced slot-swap, read as a *relation* $PMQ=PM'Q$ (a binomial set
to $0$), is valid **only when $S(PMQ)=S(PM'Q)$**, i.e. when $S(M)=S(M')$; by injectivity (equal
length is forced by $\chi$-balance) this means $M=M'$. So **the $S$-preserving balanced-swap
congruence is the *trivial* congruence** — every nontrivial composition is vacuous, and $(\star)$ is
*already* a **reduced Gröbner–Shirshov basis** (the empty/identity one). This is the honest
**CONFLUENT** verdict: $(\star)$ is a GSB, *because there is nothing to complete*. The L1·2 open
question "are the normal forms the $\chi$-reduced short words?" is thereby answered: under the
$S$-preserving congruence the normal form of $w$ **is $w$ itself** (no two words share an $S$-class).

### 3.2 The $\chi$-blind word rule: normal forms $(1^{n-1},\,N-n+1)$

If one instead *drops* the $S$-tracking and applies $(\star)$ as a pure **word** rewriting — replace
any contiguous slot $M$ by any $\chi$-balanced $M'$ that is **lex-smaller** (the $(|\cdot|,\operatorname{len})$
grading does not orient, since $\chi$-balance fixes $(\text{sum},\text{len})$; only the lex refinement
does) — then because the whole word is itself an admissible slot, **every** non-minimal word reduces
in *one step* to the lex-minimum of its $(\text{sum},\text{len})$ class. The system is terminating and
**confluent**, with the closed-form normal form
$$\boxed{\ \mathrm{NF}(w)=(\underbrace{1,1,\dots,1}_{n-1},\ N-n+1)\ },\qquad N=|w|,\ n=\operatorname{len}w$$
(the maximally $1$-loaded "short" word; verified **B1** confluence over 8 random reduction orders on
all words $n\le6,N\le13$; **B2** the closed form). **But this rule is $S$-BLIND** (verified **B3**: it
changes $S$ on $4032/4095$ words) and **preserves length** — it computes only the $(\text{sum},\text{len})$
class. So **"shorter words $\Rightarrow$ smaller $S$" is NOT realisable as a confluent
length-reducing word system**: by §3.1 $S$ is injective per length, so one cannot shorten a word while
preserving $S$. *The length reduction in $\mathcal I_D$ does not live at the word level at all — it
lives in the module of differences (cores).*

---

## 4. The critical pairs — what completion throws off (for L1·4)

The reduction calculus is therefore a calculus of **$S$-differences** (wedges), and the genuine
critical pairs are between $(\star)$-moves on those differences. Taking the natural balanced swap to
be a **block rotation** $M=AB\to M'=BA$ (always $\chi$-balanced), the move's core is the
**antisymmetry** (verified **C2**)
$$S(AB)-S(BA)=C(A,B)=D(A)S(B)-D(B)S(A).$$

**The overlap composition $C_2$ (the live critical pair).** Reduce $ABC$ two ways by swapping the
*overlapping* slots $AB$ and $BC$ (both rotated): $ABC\to BAC$ and $ABC\to ACB$. Their $S$-discrepancy
has the **closed form** (verified **C3**, a $\mathbb Z[X,Y]$ identity over a 120-instance battery)
$$\boxed{\ \delta\ :=\ S(BAC)-S(ACB)\ =\ X^{|A|}\,C(B,C)\ -\ Y^{\operatorname{len}C}\,C(A,B)\ }$$
This is the **Shirshov $S$-polynomial of two block-rotation swaps** — a concrete object the drafts did
**not** have. It is a **two-frame combination of cores**: generically **NOT a single $(\star)$-move**
(verified **C3**: $107/120$ overlaps are not a monomial times one balanced difference). So **$(\star)$
alone is *not* confluent on differences** — closing the overlap requires the antisymmetry as an extra
relation. The discrepancy lies in $\operatorname{span}_R\{C(A,B),C(B,C)\}$ (verified **C3b**), whose
*quadratic closure* is the known **Plücker/Jacobi** identity (verified **C4**)
$$D(u)C(v,w)+D(v)C(w,u)+D(w)C(u,v)=0\qquad\text{(C8).}$$

**Disjoint / external composition $C_3$ resolves trivially** (verified **C5**): two disjoint slot-swaps
commute because the frame monomials commute in $R$ — B–C Lemma 2.1 Case 1 / the external-composition
triviality of §2.5. **Inclusion $C_1$ resolves** by the chain rule / block-coarsening (L1·2 F8: $\Phi$
is a hom on gap-*blocks*, so a swap inside a swapped block is consistent). **The single irreducible
obstruction is the overlap pair $\delta$, and it closes on the antisymmetry/Plücker module** — exactly
the two critical pairs L1·2 flagged ($\chi(u)=1$ inner-core and reversal $=$ transpose), now made
precise as: *the cores do not reduce among words; their syzygy is C8.*

---

## 5. The coefficient relation $D$ and the mod-$D$ layer

- **D1 (verified).** $D=X^E-Y^o$ is a **monic binomial** $X^E\to Y^o$; the two monomials are coprime,
  so it has **no self-overlap** — a *one-rule, trivially confluent* GSB on the commutative side.
  Under the bigraded order it orients as $X^E\to Y^o$ (on a near-cycle $2^E\approx3^o$ the $X$-degree
  dominates).
- **D2 (verified — the honest caveat).** The core $C(u,v)$ has $X$-degree $\lt E=|uv|$ ($D(u)S(v)$
  tops out below $X^E$), so the polynomial $X^E-Y^o$ can **never** divide a nonzero core (185 nonzero
  cores tested, every polynomial remainder $\ne0$). **The cycle ideal is an integer/evaluation
  phenomenon, not polynomial divisibility.**
- **D3/D4 (verified).** At $(X,Y)=(2,3)$, $G=\gcd_jS^{(j)}$ divides every rotation difference (778
  pairs), and each such difference *is* a core $C(u,v)$. On a genuine cycle $G=|D|$, so **the cores are
  the elements of $\mathcal I_D$** — the mod-$D$ relations are differences/cores, never $S$-preserving
  slot-swaps. This re-confirms from the GSB side the drafts' "small cores must be wedges
  $C(u,v)$" (inner-core-extraction Gen 2).

---

## 6. Verification — `checks/lit_groebner_shirshov.py` (exit 0, 13/13 PASS)

All identities checked as $\mathbb Z[X,Y]$ symbolic identities or by exhaustive enumeration; ranges
inline; robust kernel-path insertion (confirmed from `/tmp`).

| Check | Claim | Result |
|---|---|---|
| A1 | coeff of $Y^{n-1-k}$ in $S(w)$ is $X^{e_k}$ ($S$ pins the word) | PASS |
| A2 | $S$ injective on each fixed length ($n\le7,N\le15$, exhaustive) | PASS |
| A3 | ⇒ $S$-preserving swap forces $M=M'$ (exact $(\star)$ congruence trivial) | PASS |
| B1 | confluence battery: 8 random reduction orders → same NF ($n\le6,N\le13$) | PASS |
| B2 | $\mathrm{NF}(w)=(1^{n-1},N-n+1)$ (lex-min short word) | PASS |
| B3 | word rule is length-preserving & **$S$-blind** ($S$ changed $4032/4095$) | PASS |
| C1 | $(\star)$ frame extraction identity | PASS |
| C2 | antisymmetry $S(AB)-S(BA)=C(A,B)$ | PASS |
| C3 | **overlap $S$-polynomial** $\delta=X^{|A|}C(B,C)-Y^{\operatorname{len}C}C(A,B)$; not a single move ($107/120$) | PASS |
| C3b | $\delta\in\operatorname{span}_R\{C(A,B),C(B,C)\}$ (closure = antisymmetry/Plücker) | PASS |
| C4 | Plücker/Jacobi **C8** (quadratic closure; KNOWN) | PASS |
| C5 | external/disjoint swaps commute (no new move) | PASS |
| D1 | $D$ a monic binomial $X^E\to Y^o$, no self-overlap (confluent one-rule GSB) | PASS |
| D2 | poly $D$ never divides a nonzero core ⇒ $\langle D\rangle$ is integer/eval | PASS |
| D3/D4 | $G\mid$ rotation differences at $(2,3)$; each difference $=C(u,v)$ | PASS |

---

## 7. Proposed structure (what to build; how L1·4 consumes it)

**The GSB picture of the Fox presentation, in three layers.**
1. **Word layer (faithful).** $\Phi$ injective ⇒ the $S$-preserving congruence is trivial; $(\star)$
   is a reduced GSB with normal forms = the words themselves. The $\chi$-blind reduct collapses each
   $(\text{sum},\text{len})$ class to $(1^{n-1},N-n+1)$ — confluent, but $S$-blind and
   length-preserving. **Theorem to record:** *no confluent length-reducing $S$-preserving word system
   exists* (the directing bet "shorter ⇒ smaller $S$" fails at the word level by injectivity).
2. **Difference (core) layer — where the reduction really is.** The objects are wedges
   $C(u,v)=S(uv)-S(vu)$. The single production rule is the block-rotation swap with core $C$; the
   **unique critical pair** is the overlap $S$-polynomial $\delta=X^{|A|}C(B,C)-Y^{\operatorname{len}C}C(A,B)$,
   which closes **iff** the antisymmetry/Plücker relations hold. **Build:** the rewriting system on
   cores whose relation module is generated by $C8$; its GSB is the Plücker/Jacobi ideal.
3. **Coefficient layer.** $D=X^E\to Y^o$, a trivially-confluent monic binomial; the mod-$D$
   reduction is the *integer* specialization $G\mid C$.

**Hand-off to L1·4 (Squier).** The critical pair to feed Squier's homological-finiteness machine is
the **single 3-block overlap** generating $\delta$; the question "is the move set confluent?" is
answered **no** at the difference level, with the *one* obstruction being the C8 syzygy. Squier should
test whether **C8 (Plücker) is the complete set of $2$-cells** (i.e. the cores need no relation beyond
Jacobi), or whether a third homology class hides (the holonomy quadratic, L1·5). The reversal $=$
transpose obstruction reappears here as the asymmetry of left vs. right frame ($X^{|A|}$ vs.
$Y^{\operatorname{len}C}$) in $\delta$.

**Does it deliver "short normal forms ⇒ small cores"?** **No, and now we know precisely why:** $S$ is
injective per length, so short normal forms do **not** carry small $S$; the smallness must come from
the *cores'* own structure (the bounded-defect lever's $\operatorname{sixfree}$ ceiling), not from a
word-shortening GSB. This is a useful negative: it redirects effort from "find a length-reducing GSB"
(impossible) to "bound the core module via C8" (the live route, L1·5/L1·6).

---

## 8. Open questions / probes (feeding L1·4 / the lever)

- [ ] **(L1·4)** Is the **C8/Plücker** relation the *complete* set of $2$-cells for the core rewriting
      system (overlap $\delta$ the only critical pair), so that Squier certifies the core module is
      *finitely presented with C8 the sole relator* — or is there a 3-cell (a relation among the C8
      relations) signalling the holonomy/cup-product layer (L1·5)?
- [ ] **(cores)** The overlap $S$-polynomial $\delta=X^{|A|}C(B,C)-Y^{\operatorname{len}C}C(A,B)$ is a
      *two-frame* combination. Does iterating overlaps ($ABCD,\dots$) generate **only** $\mathbb Z[X,Y]$-
      combinations of pairwise cores closed under C8, or a genuinely *new* multi-core invariant — the
      thing the bounded-defect no-go ($\ge2$ growing gaps) is really fighting?
- [ ] **(coefficient ring)** Over $R/\langle D\rangle$ with $D$ taken **polynomially** (not at $(2,3)$),
      $D$ is a zero-divisor-free monic binomial, but $X^E-Y^o$ factors (cyclotomically). Does a
      *polynomial* GSB modulo the **factors** of $D$ (the $\Phi_k(X)\,$/$\,$Bang–Zsygmondy primitive
      parts) sharpen the integer ceiling — i.e. is there a per-cyclotomic-factor normal form?
- [ ] **(infinite alphabet)** Block-coarsening (chain rule) makes $(\star)$ scale-free; does the
      *induced* GSB on gap-**blocks** stay finite per bounded block-type, giving a finite confluent
      system on each bounded-defect family (the constructive form of the bounded-defect lever)?

---

## 9. Verdict for the roadmap

L1·3 returns a **clean, honest verdict**: the Fox presentation of $\mathcal I_D$ is a **finite confluent
GSB — vacuously**, because $S$ is injective per length ($\Phi$ faithful), so the $S$-preserving
balanced-swap congruence is trivial and there is *nothing to complete*. **No new length-reducing
move** (the prize is a null — but a sharp one: it *proves* "shorter words ⇒ smaller $S$" cannot be a
word-level GSB). The yield is three structures the drafts lacked: the **injectivity pin** (resolving
the L1·2 normal-form question), the explicit **overlap critical-pair $S$-polynomial**
$\delta=X^{|A|}C(B,C)-Y^{\operatorname{len}C}C(A,B)$ (the exact 3-cell for Squier), and the correct
**CDL setting** (Mikhalev–Zolotykh double free algebra over commutative coefficients, three
composition types, no field needed) with the caveat that $\langle D\rangle$ is an *integer* ideal. The
reduction calculus is hereby relocated from words to the **core module**, whose sole relator is the
known **C8/Plücker** — which is exactly what L1·4 (Squier) is to certify.
