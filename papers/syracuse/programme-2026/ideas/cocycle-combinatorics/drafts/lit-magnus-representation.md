# Leverage: the functorial Magnus representation (Florens–Massuyeau–Serrano de Rodrigo, arXiv:1604.06905)

**Promise:** medium. The paper is the canonical home of "the Magnus representation is a crossed
homomorphism whose determinant is an Alexander/Reidemeister normalization," which is exactly the
algebraic skeleton of our cocycle $S$. The honest yield is a **negative-but-decisive** answer to the
L1·7 normalization question plus a **structural identification** of two of our facts (the $\mathbb{Z}[1/6]$-coset
and the reversal=transpose dead end) with named topological invariants — not a new reduction law.
**Status:** read in full (36 pp.); rank‑1 dictionary built; all transfers verified on the kernel
(`checks/lit_magnus_representation.py`, exit 0).
**Source:** [`sources/magnus-representation-1604.06905.pdf`](../sources/magnus-representation-1604.06905.pdf)
(text dump `sources/magnus.txt`).

> Notation: this is the **rank‑1 / $2\times2$** shadow of the paper. Their objects are rank‑$2g$
> modules over $R=\mathbb{Z}[G]$; ours is the single cocycle $S$ realized as the off‑diagonal of a
> $2\times2$ transfer matrix. Mismatches are flagged explicitly.

## 1. What the paper actually proves (with locations)

- **§1, §5.1 — the Magnus representation is a *crossed* homomorphism.** Classically (Birman [Bir74],
  recalled in the Introduction, l.35–42) the Magnus "representation" of $\mathrm{MCG}(\Sigma)$ assigns
  to $f$ the matrix of **Fox free derivatives** $\big(\partial f_*(x_i)/\partial x_j\big)$ over
  $\mathbb{Z}[\pi]$; it is **not** a group homomorphism (the Introduction stresses "how far they are
  from being group homomorphisms"). The paper's whole point is to **repair** this into an honest
  functor `Mag` by passing from maps to **graphs / Lagrangian relations**.
- **§5.1, Lemma 5.4 + the "Jacobian matrix" (l.2251).** On a mapping cylinder $c(f)$,
  $\mathrm{Mag}(c(f),\phi)$ is the **graph of the unitary isomorphism** $f_*$, whose matrix is the
  Fox Jacobian. So: *crossed hom $\rightsquigarrow$ genuine homomorphism by taking the graph.*
- **§3.1–3.2 — antipode + skew‑Hermitian form.** The antipode $a\mapsto\bar a$ of $\mathbb{Z}[\pi]$ is
  the anti‑homomorphism with $\bar x=x^{-1}$ (l.678). On the abelianization $G$ this is
  $g\mapsto g^{-1}$. The $\phi$‑twisted intersection form $\langle\cdot,\cdot\rangle_s$ (eq. (3.7),
  (3.8); Lemma 3.1) is **skew‑Hermitian** w.r.t. this antipode, and the Magnus rep is **unitary**
  for it (Sakasai's "symplecticity," [Sak08]/[Sak12]).
- **Theorem 6.3 + Remark 6.4 — the determinant is the Alexander/torsion normalization.** With
  $\Delta(M,\partial_\pm M):=\mathrm{ord}\,H_1^\phi(M,\partial_\pm M)\in(R\setminus\{0\})/\!\pm G$ a
  *relative Alexander polynomial*, the Alexander functor factors
  $$A(M,\phi)=\Delta(M,\partial_+M)\cdot\Lambda r_\phi(M)=\Delta(M,\partial_-M)\cdot\det\!\big(r_\phi(M)\big)^{-1}\cdot\Lambda r_\phi(M),$$
  hence $\boxed{\det\big(r_\phi(M)\big)=\Delta(M,\partial_-M)\big/\Delta(M,\partial_+M)}$ **in $R/\!\pm G$.**
  The invariant lives **intrinsically modulo the unit group $\pm G$**; the determinant merely converts
  the "from‑below" normalization into the "from‑above" one (proved via Reidemeister torsions, [FM15]).

## 2. Dictionary (their Magnus rep $\leftrightarrow$ our rank‑1 $M(w),S,C$)

Put $E=|w|$ (letter‑sum, $\to 2$, $\to X$), $o=\operatorname{len}w$ (length, $\to 3$, $\to Y$).

| Paper (rank‑$2g$, $R=\mathbb{Z}[G]$) | Ours (rank‑1, $\mathbb{Z}[X,Y]$) | Status |
|---|---|---|
| Fox‑Jacobian Magnus matrix $r_\phi(M)$ | the cocycle $S(w)$ (rank‑1 Fox derivative; one generator) | correspond |
| crossed‑hom failure of $r_\phi$ | $S(uv)=Y^{o_v}S(u)+X^{E_u}S(v)$ ($\chi$‑twist) | correspond |
| functorial repair = **graph** of $f_*$ (Lemma 5.4) | $M(w)=\left(\begin{smallmatrix}Y^{o}&0\\ S(w)&X^{E}\end{smallmatrix}\right)$, the transfer matrix (graph of the crossed hom; an honest monoid hom) | **correspond — this is the key match** |
| antipode $\bar x=x^{-1}$ (§3.1) | $X\mapsto X^{-1},\,Y\mapsto Y^{-1}$ | correspond |
| unit group $\pm G\subset R^\times$ | $\pm X^aY^b\,(=\pm2^a3^b)$, the 6‑units | correspond |
| invariant defined in $R/\!\pm G$ | core/ceiling defined up to a 6‑unit; $\operatorname{sixfree}(\cdot)$ = canonical rep | correspond |
| $\det r_\phi=\Delta(M,\partial_-)/\Delta(M,\partial_+)\in R/\!\pm G$ | $\det M(w)=X^{E}Y^{o}$ — a **pure 6‑unit** | correspond, **degenerate** (see §3) |
| relative Alexander poly $\Delta(M,\partial_\pm)$ | $D(w)=X^{E}-Y^{o}$ (so $G=\lvert D\rvert$); eigen‑gap of $M(w)$ | correspond (Reidemeister‑torsion role) |
| skew‑Hermitian form $\langle\cdot,\cdot\rangle_s$; $r_\phi$ **unitary** | **no constant form** makes $M(w)$ unitary (V5b) | **MISMATCH (rank)** |
| composition = Lagrangian‑relation composition (graph $\cap$, project) | concatenation $M(uv)=M(u)M(v)$ | correspond on cylinders; paper's gluing has a torsion/closure correction with no rank‑1 analogue |

**Principal mismatches.**
1. **rank‑1 vs rank‑$2g$.** Their determinant $\det r_\phi$ is a *non‑trivial* unit (ratio of two
   Alexander polynomials). Ours collapses to $\det M(w)=X^EY^o$ — *literally the unit we already
   quotient by*. So the "determinant normalization" carries **no extra information** in rank 1.
2. **unitarity is a rank‑$2g$ phenomenon.** Sakasai symplecticity needs the genuine genus‑$g$
   Magnus matrix; our $2\times2$ transfer matrix (= graph of a crossed hom, *not* the genus‑$g$ rep)
   admits **no constant skew‑Hermitian form** (V5b solves $\bar M^{\!\top}HM=H$ $\Rightarrow H=0$).
3. **cobordism gluing vs free‑monoid concatenation.** The functor's composition is a Lagrangian
   *relation* composition whose "correction term" is a closure/torsion submodule — genuinely
   topological, with no shadow in our $M(uv)=M(u)M(v)$. The crossed‑hom correction we *do* have is the
   $\chi$‑twist, already in `cocycle.py`.

## 3. Relation extracted (in OUR notation)

**RE‑1 (the L1·7 normalization, resolved — `NEW?: no(finer)/yes(certification)`, `TRANSLATABLE?: yes`).**
The transfer matrix obeys
$$\det M(w)=X^{|w|}\,Y^{\operatorname{len}w}\qquad(=2^{E}3^{o}\text{ at }(2,3)),$$
a **pure 6‑unit**. This is the rank‑1 image of Theorem 6.3 / Remark 6.4's $\det r_\phi\in R/\!\pm G$.
Consequence for the lever ceiling: the L1·7 hope — *promote the $\mathbb{Z}[1/6]$‑coset
$S(\beta d)-S(d\beta)$ to a canonical integer via a determinant/torsion normalization* — resolves as
follows. Because $\det M(w)$ **is** the unit group $\pm G$, every rotation‑pair extraction of the same
arc differs by exactly a 6‑unit:
$$S(d^{k}\beta d^{L-k})-S(d^{k+1}\beta d^{L-k-1})=X^{kd}Y^{\,L-k-1}\big(S(\beta d)-S(d\beta)\big),$$
so $\operatorname{sixfree}$ of the wedge is **independent of $k$ and $L$** and equals
$\operatorname{sixfree}(S(\beta d)-S(d\beta))$. **Therefore the ceiling already *is* a well‑defined
integer** — the canonical 6‑free representative of a full $\pm G$‑coset — and **no determinant can
sharpen it**, because the only normalizing unit available is $\pm G$ itself. The L1·7 worry ("coset,
not integer") is answered: it is a *full* $\pm G$‑coset, $\operatorname{sixfree}$ is its canonical
section, and that is the finest normalization the Magnus/torsion theory permits. *(This is the
honest determinant finding: a certification, not a new bound.)*

**RE‑2 (discriminant identity — `NEW?: minor`, `TRANSLATABLE?: yes`).** Since $M(w)$ is triangular
with diagonal $X^{E},Y^{o}$, its eigenvalues are $X^{E},Y^{o}$ and
$$D(w)^2=\operatorname{tr}M(w)^2-4\det M(w),\qquad G=\lvert D\rvert=\lvert X^{E}-Y^{o}\rvert\ \text{(on a cycle)}.$$
So **$G$ is the eigenvalue gap = discriminant root of the transfer matrix**, and $D=X^E-Y^o$ plays the
role of the relative Alexander polynomial $\Delta(M,\partial_\pm M)$ — both are "$\det$ of a
presentation, mod $\pm G$." This pins our $G$ to a Reidemeister/Alexander invariant, matching the
paper's torsion picture, but adds no new inequality.

**RE‑3 (reversal=transpose, identified — `NEW?: no`, `TRANSLATABLE?: yes`).** The paper's duality is
**not** plain transpose but the **antipode‑transpose** $\bar M^{\!\top}$ (conjugate‑transpose for the
skew‑Hermitian form, $X\mapsto X^{-1}$). Two facts (V5) show this **does not rescue** our reversal
route:
- (a) $S(w^{R})$ is **not** a 6‑unit multiple of the antipode $S(w)\!\mid_{X\to1/X,Y\to1/Y}$ (an
  index‑shift in the partial sums survives), so reversal is a genuine transpose, not a unit twist.
- (b) the antipode‑transpose duality needs the rank‑$2g$ unitary structure; our $2\times2$ transfer
  matrix admits **no constant unitary form**.

This *confirms and explains* draft **[P4] Gen‑8**: "reversal = matrix transpose is not a fixed
conjugation." The structural reason in topological terms: the genuine Magnus rep is **unitary**
(needs the antipode $X\mapsto X^{-1}$, i.e. Laurent coefficients), whereas our $S$ lives in the
**graph/transfer** picture, which has no such form. So passing to the antipode forces the
$\mathbb{Z}[X,Y]\hookrightarrow\mathbb{Z}[X^{\pm},Y^{\pm}]$ extension — exactly the "escapes the
valid rotation lattice (scalar **and** Laurent‑monomial)" obstruction P4 already proved. *The paper
hands us the name of the obstruction, not a way around it.*

## 4. Verification (`checks/lit_magnus_representation.py`, exit 0 — all PASS)

| Check | Claim | Result |
|---|---|---|
| V1 | $M$ is a monoid hom; $\det M(w)=X^{E}Y^{o}$ (pure 6‑unit) | PASS (symbolic, 9 words / 4 concatenations) |
| V2 | rotation $=$ conjugation by $M(\text{prefix})$; $\det,\operatorname{tr}$ rotation‑invariant | PASS |
| V3 | $D^2=\operatorname{tr}^2-4\det$; eigenvalues $=X^{E},Y^{o}$ | PASS |
| V4 | $\operatorname{sixfree}(\text{wedge})$ indep. of $k,L$ $=\operatorname{sixfree}(\text{core})$ | PASS ($\beta\in\{(3),(3,4),(4,3,4),(2,3),(4,1,1,3)\}$, $d\in\{1,2,5\}$, $L=2..8$, all $k$) |
| V5a | $S(w^{R})$ not a 6‑unit multiple of antipode $S(w)$ | PASS |
| V5b | no constant form $H$ with $\bar M^{\!\top}HM=H$ (only $H=0$) | PASS |

V4 is the load‑bearing one: it *realizes* the "det $=$ unit $\Rightarrow$ invariant mod $\pm G$"
prediction on the lever's actual ceiling, certifying the ceiling is a well‑defined integer
(sample values $\operatorname{sixfree}=1,65,25,1103,17,209,5,\dots$ are run‑length‑invariant).

## 5. Proposed structure / rationale

- **Keep the transfer matrix $M(w)$ as the canonical object**, *named*: it is the rank‑1 functorial
  repair (graph of the crossed hom $S$), the exact analogue of `Mag(c(f)) = graph of f` (Lemma 5.4).
  Its determinant is the unit, its eigen‑gap is $D=\pm G$, rotation is conjugation. This is a clean
  packaging of facts the drafts already use piecemeal, with a literature anchor.
- **Record L1·7 as resolved (negatively for sharpening, positively for well‑definedness):**
  $\operatorname{sixfree}(S(\beta d)-S(d\beta))$ **is** the canonical integer; the Magnus/torsion
  determinant cannot improve it because the determinant *is* $\pm G$. The promoted
  `bounded-defect-lever` approach can cite this to stop hunting for a finer normalization.
- **Reversal route stays closed**, now with a topological *reason* (unitarity needs the antipode =
  Laurent extension), not just a computational witness. Do **not** reopen it.
- **What would actually move the needle is rank $\ge 2$**, where $\det r_\phi$ is a *non‑trivial*
  Alexander ratio. Our setting is rank‑1 by construction (one prime pair $2,3$), so the informative
  part of the paper structurally cannot fire here. This is the ceiling of this leverage.

## 6. Open questions / probes

- [ ] **Is there a rank‑2 enrichment that is *honest* for us?** E.g. tracking two coprime moduli at
      once (a $2$‑generator $G$) so that $\det r_\phi$ becomes a non‑trivial Alexander ratio with
      real content — or is any such enrichment a fiction for a single Diophantine equation $2^E=3^o\pm G$?
- [ ] **Does the factorization $A=\Delta\cdot\mathrm{Mag}$ suggest a *second* invariant** beyond $G$?
      $\Delta(M,\partial_-)$ vs $\Delta(M,\partial_+)$ are two normalizations differing by $\det$; in
      rank 1 they coincide up to $\pm G$, but is there a refined pair (e.g. $\operatorname{sixfree}$
      from the prefix‑frame vs the suffix‑frame) that the lever does not yet exploit?
- [ ] **Cup‑product / Reidemeister‑torsion reading of $C(u,v)$.** The wedge core is $H^1\wedge H^1\to H^2$;
      the paper's torsion factorization is the natural home for a "torsion of the cup product."
      Does it give a *multiplicativity* law for $\operatorname{sixfree}(C)$ under arc concatenation
      (a telescoping the current P0/P1 moves miss)?
- [ ] **Confirm V4's run‑length invariance is *exactly* the $\pm G$ quotient**, not a coincidence of
      small $L$: prove $\operatorname{sixfree}$ is constant for all $L$ from the unit‑prefactor identity
      (it follows from V1+V4 symbolic factorisation, already PASS — worth stating as a lemma in the
      approach).

## 7. Verdict for the roadmap

The Magnus anchor (L1·1) **confirms the algebraic skeleton** ($S$ = rank‑1 Fox crossed hom; $M(w)$ =
its functorial graph; $\det$ = the $\pm G$ unit; $G$ = eigen‑gap/Alexander torsion) and **decisively
resolves L1·7**: the lever ceiling is already a well‑defined integer and the determinant cannot
sharpen it. It does **not** yield a new reduction/gluing law (the cobordism functoriality is
genuinely topological; rank‑1 kills the informative determinant) and does **not** reopen reversal.
Net: a certification + two named obstructions, no new lever.
