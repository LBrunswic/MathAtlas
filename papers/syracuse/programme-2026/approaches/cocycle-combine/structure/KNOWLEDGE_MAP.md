# Knowledge map — cocycle-structure

**Read this file at the start of every `cocycle-structure` session.** It is the table of contents
for the structural-theory knowledge base: the owned synthesis, the reading notes, and the source
library. One line per item; detail lives in the linked file.

## The owned synthesis

- [`structure.md`](structure.md) — the algebraic structure of the word-cocycle, certified by
  [`verify_structure.py`](verify_structure.py) (run it; exits 0). Headline facts:
  - **C1/C2** $M(w)=\prod_k\!\big(\begin{smallmatrix}Y&0\\1&X^{d_k}\end{smallmatrix}\big)
    =\big(\begin{smallmatrix}Y^o&0\\S&X^E\end{smallmatrix}\big)$ — transfer-matrix monoid hom.
  - **C3** rotation $=$ conjugation by $M(u)$; cyclic words $=$ conjugacy classes.
  - **C5** $\sigma=S/Y^o$ is a crossed homomorphism for the character $\chi=X^E/Y^o$.
  - **C6** coboundary of a constant is $w\mapsto c\,D(w)$ ⇒ $S$ defined mod $\langle D\rangle$.
  - **C7** core $=$ wedge: $C(u,v)=\det\!\big(\begin{smallmatrix}D(u)&D(v)\\S(u)&S(v)\end{smallmatrix}\big)$.
  - **C8** Plücker/Jacobi: $D(u)C(v,w)+D(v)C(w,u)+D(w)C(u,v)=0$.
  - **C9** Knight edge core: $Y\,g(1u0)-g(0u1)+D=X^{E-1}(X-1)$, $g(p01)-g(p10)=X^{E-2}(X-1)$ —
    a monomial core at $X{=}2$, the **Baker-free** high-cycle (Christoffel) obstruction.
  - **C10** $S$ is a rank-**exactly-2** rational/recognizable series; the C1 matrices are its
    *minimal* linear representation (Hankel rank $=2$).
  - **C11** monodromy char poly $\det(tI-M(w))=(t-X^E)(t-Y^o)$ — a cyclic word is a **fibered** class,
    $(t-X^E)(t-Y^o)$ its Alexander polynomial, $D=\lambda_2-\lambda_1$ the eigenvalue gap.
  - **§5** generic ($\mathbb{Z}[X,Y]$) vs. exceptional ($2$–$3$ arithmetic) separation principle.
  - **§6** literature corroboration: Trümper's link function $L\equiv S$, his composition laws $=$
    C1/C2/C5, his commutator $=$ C7, his rotation law on $\Phi=L/D$ $=$ C3.

## Reading notes (`notes/`)

One file per source or focused topic. Each cites its source, distills the relevant result, and says
**how it connects** to a tagged claim in `structure.md`. Format: [`notes/_TEMPLATE.md`](notes/_TEMPLATE.md).

| note | topic | feeds |
|------|-------|-------|
| [knight2023-high-cycles](notes/knight2023-high-cycles.md) | high cycle = Christoffel word; Baker-free monomial-core obstruction | C9; §5–§6 |
| [trumper2014-free-semigroup](notes/trumper2014-free-semigroup.md) | free semigroup of T-words; link function $L\equiv S$; cycle function $\Phi$ | C1/C2/C3/C5/C7, P1; §6–§7 |
| [bohm-sontacchi1978-cycle-formula](notes/bohm-sontacchi1978-cycle-formula.md) | closed form: cycle member $=S/D$ (necessary & sufficient) | foundation; C5/C6/C7 |
| [terras1976-stopping-time](notes/terras1976-stopping-time.md) | the encoding/parity vector — origin of the word coding | C1 |
| [cohn1972-markoff-forms](notes/cohn1972-markoff-forms.md) | primitive/Christoffel words; reverse=conjugacy; Markoff $\to SL_2$ trace | C9, C1; §3–§4 |
| [halbeisen-hungerbuhler1997-rational-collatz-bounds](notes/halbeisen-hungerbuhler1997-rational-collatz-bounds.md) | Christoffel rotation = high cycle; optimal length/range bounds | C9; search range |
| [ellison1971-pillai](notes/ellison1971-pillai.md) | explicit $\lvert2^x-3^y\rvert>2^xe^{-x/10}$ (Baker) | §5 size barrier |
| [lagarias-annotated-bibliography](notes/lagarias-annotated-bibliography.md) | the annotated $3x+1$ bibliography (I & II) — reference map | all threads |
| [eliahou1993-cycle-lengths](notes/eliahou1993-cycle-lengths.md) | CF-of-$\log_23$ cycle-length bound; admissible lengths | §5; search targets (PDF not yet acquired) |
| [berstel-reutenauer-noncommutative-rational-series](notes/berstel-reutenauer-noncommutative-rational-series.md) | rational series; rank = Hankel rank = min representation; minimality | C10/C1; §8 (rank-as-complexity), §3 |
| [cocycle-complexity](notes/cocycle-complexity.md) | the §8 program: complexity (entropy/Mahler, Thurston/Alexander, rank) ↔ controlled factorization; chain to the $2$–$3$ locus | §8; refines §5 |
| [thurston-alexander-norm](notes/thurston-alexander-norm.md) | Thurston vs Alexander norm; Magnus/Fox translation; monodromy $=(t-X^E)(t-Y^o)$; span (Newton width) vs height (Mahler) | C11, C1/C4/C5/C6; §8 |
| [thurston-alexander-formal](notes/thurston-alexander-formal.md) | Bourbaki form: defs + **Thm $\lVert\phi\rVert_A\le\lVert\phi\rVert_T$** ($\lvert\alpha E-\beta o\rvert\le\sum_k\lvert\alpha d_k-\beta\rvert$, eq. iff $\phi$-monotone) | C1–C11; checked by `thurston_alexander_check.py` |

## Source library (`sources/`)

PDF/DJVU of papers and books, catalogued in [`sources/README.md`](sources/README.md). Binaries are
git-ignored (local-only); the catalogue (citation + filename + why-it-matters) is tracked.

- **Knight 2023** (`knoght.pdf`) — high cycles don't exist; the C9 exemplar.
- **Trümper 2014** (Chinese J. Math.) — free semigroup of T-words; independent C1–C7 rediscovery.
- **Böhm–Sontacchi 1978** (BDIM) — closed form cycle member $=S/D$, the foundation.
- **Terras 1976** (EuDML) — the encoding/parity vector; origin of the word coding.
- **Cohn 1972** (GDZ) — Markoff/primitive words; reverse=rotation; $SL_2$ trace bridge to C1.
- **Halbeisen–Hungerbühler 1997** — Christoffel = high cycle; optimal cycle bounds.
- **Ellison 1971** (NUMDAM) — explicit $|2^x-3^y|$ lower bound (the §5 barrier).
- **Lagarias bibliography I & II** (arXiv) — the reference map.
- **Berstel–Reutenauer**, *Noncommutative Rational Series* (CUP) — $S$ is a rank-2 rational series; rank-as-complexity.

## Reading list — references wanted

Bibliographic targets that should back the structural claims, grouped by which thread they serve.
Move a row into `sources/` + a reading note once acquired and read.

_Acquired this round (now in `sources/` with notes): Böhm–Sontacchi 1978, Terras 1976, Cohn 1972,
Halbeisen–Hungerbühler 1997, Ellison 1971, Lagarias bibliography I & II._

| topic | why it matters here | candidate references |
|-------|--------------------|----------------------|
| **$S$ as a rational series** | formalises C1 ($S$ = weighted-automaton/transfer-matrix output) | **Berstel–Reutenauer**, *Noncommutative Rational Series* (acquired, **unread** — read next) |
| **Sturmian / conjugacy-to-shift** | is C3 the finite shadow of $\Phi^{-1}T\Phi=$ shift? Christoffel via Sturmian | **López–Stoll 2009** (*Integers* 9, A13); **Bernstein–Lagarias 1996** (Canad. J. Math. 48, 1154) |
| **Free semigroup of $x/2,(3x+1)/2$** | independent backing for Trümper/§6 | **Misiurewicz–Rodriguez 2005**; Bergelson–Misiurewicz–Senti 2006 |
| Christoffel words (combinatorics) | C9 rotation class; Lyndon/balance order | Berstel–Lauve–Reutenauer–Saliola 2009 (*Christoffel words*); Berstel–de Luca 1997; **Series 1985** (geometry of Markoff numbers) |
| Cycle lower bounds / state of the art | the honest barrier; admissible cycle lengths | **Eliahou 1993** (PDF not yet acquired); **Simons–de Weger 2005** (free PDF, deweger.net); **Martiny 2015** (free PDF, pitt.edu); Steiner 1978 |
| Sharp linear-forms-in-logs | quantitative $|2^E-3^o|$ from below | **Rhin 1987** (*Progr. Math.* 71, 155–164); Baker 1975; Matveev 2000 |
| $S$-unit / recurrence / $2^a3^b$ (§8 endpoint) | smallness of $C|_{2,3}$ as a sum-of-$S$-units; the exceptional locus | **Evertse–Schlickewei–Schmidt** (Annals 155, 2002); **Evertse–Győry**, *Unit Equations*; **Bennett 2003** (Pillai, UBC) / Stroeker–Tijdeman; **Bell–Smertnig** (Pólya series, arXiv:1906.07271); Everest–vdPoorten–Shparlinski–Ward, *Recurrence Sequences*; Skolem–Mahler–Lech (Ouaknine–Worrell survey) |
| Cohn factorization of rational series (§8) | stratifies the core $C$ by factorization length | Cohn, *Free Ideal Rings*; Schrempf (arXiv:1803.10627) |
| **Mahler measure / Kronecker / Lehmer** (§8) | complexity $\leftrightarrow$ monomial$\times$cyclotomic factorization of cores | Kronecker 1857; **Smyth**, *Mahler measure: a survey*; **Everest–Ward**, *Heights of Polynomials & Entropy in Algebraic Dynamics*; Boyd |
| **Quasimorphism defect / bounded cohomology** (§8) | a "cocycle complexity": core $=$ coboundary defect | **Calegari**, *scl* (free PDF, uchicago); **Frigerio**, *Bounded Cohomology of Discrete Groups* (arXiv:1610.08339) |
| **Thurston/McMullen norm on $H^1$** (§8) | leading model: $\gcd_jS^{(j)}\leftrightarrow$ Alexander polynomial, $\|\phi\|_A\le\|\phi\|_T$, fibered face $=$ controlled factorization | **McMullen 2002** (NUMDAM, ASENS); **Turaev** (arXiv:math/0203042); Friedl survey (arXiv:2108.08645) |
| **Counting-function $H^1$ equivalence** (§8) | cochain-level coboundary test; $O(n)$ algorithm (needs $\chi$-twist) | **Hartnick–Talambutsa** (arXiv:1508.03166, 2407.10569) |
| **Cyclotomic values $\Phi_n(2)$ / primitive divisors** (§8) | turns Mahler-$1$ cores into the $2$–$3$ ceiling $G\mid\prod\Phi_k(2)$ | Bang–Zsygmondy; **Bilu–Hanrot–Voutier** (primitive divisors of Lucas/Lehmer sequences) |
| Group cohomology $H^1$ / crossed homs | makes "cocycle / coboundary $=D$" rigorous | Brown, *Cohomology of Groups*; Serre, *Local Fields* |
| Word coding (background) | the original parity vector = our word | Everett 1977; Wirsching, *Dynamical System Gen. by 3n+1* (LNM 1681) |

## Conventions

- A claim only enters `structure.md` after `verify_structure.py` certifies it (new claims get a new
  `Cn` tag + a `check(...)` block in the script).
- A reading note must name its source file in `sources/` (or mark it "not yet acquired") and link the
  `structure.md` claim it supports.
- Keep this map's bullet/table lines to one line each; depth goes in the linked file.
