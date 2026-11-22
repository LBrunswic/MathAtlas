# Topic — cocycle complexity ↔ controlled factorization (the §8 program)

- **Source file:** _synthesis note; sources not yet acquired_ (open-access pointers below; this note
  feeds thread §8 of [`structure.md`](../structure.md)). Built from three literature scouts (cohomology /
  Mahler / rational-series).
- **Feeds:** thread §8; refines the §5 generic/exceptional separation.

## The translation (the user's table, made precise)

| informal | precise |
|---|---|
| $\mathbb Z[X,Y]$-combination $\Leftrightarrow$ cocycle equivalence | move within $[\sigma]\in H^1(W,R_\chi)$ mod the coboundary $\langle D\rangle$ (**C5/C6**) |
| GCD $=$ minimal representative | $G=\gcd_jS^{(j)}=\lvert D\rvert$ is the *content* of the class |
| monomial $X^aY^b\cdot$(low-degree) $\Leftrightarrow$ low complexity | **Kronecker**: integer poly, nonzero at $0$, has **Mahler measure $1$** $\iff$ monomial $\times\prod\Phi_k$ |

## Three rigorous complexity notions (and the theorem behind each)

1. **Entropy / Mahler measure (sharpest).** **Lind–Schmidt–Ward** (*Invent. Math.* 101, 1990):
   $\log M(f)=h(\alpha_{1/f})$, the topological entropy of $f$'s algebraic $\mathbb Z$-action. So
   $M(\text{core})=1\iff$ cyclotomic$\times$monomial $\iff h=0$ — "low complexity" *is* zero entropy.
   **Lehmer's problem** (smallest $M>1$, $=1.17628\ldots$; Dobrowolski's lower bound) is the spectral
   gap above it. **Baake–Coons–Manibo** (arXiv:1711.02492): for substitution words the Mahler measure of
   the Borwein polynomial $=$ the Lyapunov exponent of the substitution **matrix cocycle** — a literal
   "word cocycle $\to$ Mahler measure" bridge, kin to our **C1**.
2. **Thurston/Alexander norm (cohomological).** **McMullen** (*Ann. Sci. ENS* 35, 2002):
   $\lVert\phi\rVert_A\le\lVert\phi\rVert_T$ — the Alexander-polynomial degree lower-bounds the Thurston
   norm on $H^1$, with equality on **fibered faces**. Dictionary: $\gcd_jS^{(j)}\leftrightarrow$ Alexander
   polynomial; "controlled cyclotomic factorization" $\leftrightarrow$ the fibered/equality case.
   **Silver–Williams** (arXiv:math/0105234): $M(\Delta_K)=$ homology-growth rate in covers; Lehmer
   $\Leftrightarrow$ the Alexander-norm gap. (Quasimorphism **defect** — Calegari *scl*, Frigerio — is
   the closest "complexity of a 1-cocycle", but our $\sigma$ is a *twisted* cocycle, not a real
   quasimorphism, so the defect framework needs a $\chi$-twisted extension that **does not yet exist**.)
3. **Rank / Cohn factorization (algebraic).** $S$ has Hankel rank exactly $2$ (**C10**); the
   discriminating complexity therefore lives in the **core** $C$ / parametrized families. Cohn's free-
   field factorization (Cohn FIR; Schrempf, arXiv:1803.10627) stratifies $C$ by factorization length;
   a rank-2 series admits at most one non-trivial "cut", sharply constraining factored forms of $C$.

## The chain to the exceptional $2$–$3$ locus (the §5 payoff, now end-to-end)

rank-2 minimality (**C10**) → Cohn factorization of $C$ in the free field → degenerate vs.
non-degenerate sub-families (**Skolem–Mahler–Lech**; eigenvalue ratio $\chi=X^E/Y^o$, never a root of
unity at $(2,3)$ since $2^E\ne3^o$ — so the canonical series is *non-degenerate*) → the smallness/zero
set of $C\big|_{X=2,Y=3}$ is a **sum-of-$S$-units** problem over $S=\{2,3\}$ (**Evertse–Schlickewei–
Schmidt**, *Ann. of Math.* 155, 2002; finiteness with explicit bound) → **Baker** lower bound on
$\lvert2^a-3^b\rvert$ → the only "doubly-representable" small values of $3^x-2^y$ are a finite set
(**Stroeker–Tijdeman 1982**; **Bennett 2003**: $\lvert c\rvert>13\Rightarrow$ at most one solution; e.g.
$3-2=9-8=1$). **Bell–Smertnig** (*Selecta* 27, 2021): rational **Pólya** series are unambiguous, proved
*via* $S$-unit equations — series complexity $\leftrightarrow$ $S$-unit arithmetic, directly.

**The Zsygmondy gate (concrete pruning).** A Mahler-$1$ core gives $G\mid 2^a\prod_k\Phi_{n_k}(2)$;
**Bang–Zsygmondy** forces each $\Phi_{n_k}(2)$ with $n_k\notin\{1,2,6\}$ to contribute a *new* primitive
prime $\ge n_k+1$ dividing $G$. So $G=\lvert D\rvert$ can stay small (beat the Ellison barrier) **only if
the core's cyclotomic indices collapse into $\{1,2,6\}$** — then $G=2^a3^c$ and Baker/**Bilu–Hanrot–
Voutier** take over. This is a usable filter on which structured words could host an exceptional cycle.

## Status / next steps

No new $\mathbb Z[X,Y]$ claim is certified this round — this is the program, not a theorem. (a) Fix one
$\kappa$ (Mahler measure of the reduced core looks best) and certify the easy direction *structured
$\Rightarrow$ $M=1$* on the P1/P2/C9 families; (b) test $\kappa$'s rotation-invariance and behaviour
under concatenation (should descend from the **C1** monoid hom); (c) implement the Zsygmondy gate as a
search filter. **Acquire next (open access):** Smyth survey (arXiv:math/0701397); Lind–Schmidt–Ward
(author PDF); McMullen (NUMDAM); Calegari *scl* (uchicago); Evertse–Schlickewei–Schmidt (Annals);
Bennett *Pillai revisited* (UBC); Bell–Smertnig (arXiv:1906.07271); Hartnick–Talambutsa
(arXiv:1508.03166). See the references-wanted table in [`KNOWLEDGE_MAP.md`](../KNOWLEDGE_MAP.md).
