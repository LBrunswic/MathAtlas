# Leverage roadmap — Layer-1 (the Magnus cocycle & its expansion-reduction calculus)

An ordered series of `--leverage` calls (one paper each, depth) to deepen the **Layer-1**
structure: the **Magnus 1-cocycle** and the **word expansion-reduction calculus** it powers — i.e. the
algebraic skeleton that captures the *word combinatorics* (which words/combinations land in the
cycle-ideal, and the **expansion-reduction** moves between them, starting from the cyclic roll). This is
**not** the Layer-2 arithmetic (primitive divisors / $\operatorname{sixfree}\to\infty$) — that is the
terminal size-check, tracked separately.

**Target object (reframed 2026-06-09 — the integer cyclic quotient, expansion-reduction).** Start from the
**cyclic roll** (rotation orbit) $\{w_0,\dots,w_{o-1}\}$ of a word $w$ inside the monoid-algebra quotient
$$A=\mathbb{Z}[W]\big/\ker(\pi\circ S),\qquad
  \pi:\ \mathbb{Z}[1/6]\twoheadrightarrow \mathbb{Z}[1/6]\big/(\chi(w)-1)\ \cong\ \mathbb{Z}/G\mathbb{Z},$$
with $\ker(\pi\circ S)=\mathcal{I}_D$ and $(\chi(w)-1)=\langle D\rangle=\langle G\rangle$ — so $\pi$ is the
**integer / eval** reduction mod $G=|2^E-3^o|$, *not* the polynomial reduction mod $\langle D\rangle\subset\mathbb{Z}[X,Y]$.
Rotation preserves $(E,o)$, so $\pi$ is simultaneously defined on the whole orbit, and on a genuine cycle
$G=\gcd_jS^{(j)}\Rightarrow$ **every rotation is $\equiv0\pmod G$**: the cyclic roll generates the *zero*
submodule of $\mathbb{Z}/G$.
- **The strategy class is EXPANSION-REDUCTION**, not length-monotone reduction. *Expand* (powers $w^k$,
  insertion of rolled sub-blocks, concatenation with orbit elements) to a longer combination, then *reduce*
  it to a **small nonzero residue** $C$, forcing $G\le|C|$ against Matveev/Ellison. The one working lever
  [P3] **is** exactly this — expand the background run $d^L$, reduce the adjacent-rotation wedge to the fixed
  weight-2 core $C(\beta,d)$ (Suciu–Wang L1·5: that target is weight-invariant under the expansion).
- **Why the old framing is retired:** the original premise "shorter words ⇒ smaller $S$ ⇒ a confluent
  *length-reducing* system" was **falsified by L1·3** ($S$ injective per length; word NF is $S$-blind). Pure
  length-monotone reduction is dead. The live object is the **integer cyclic quotient** $A$ (L1·3's
  "integer/eval, not polynomial" caveat), where expansion-reduction can realize a small residue that no
  length order reaches.

**Run each as:** `/incubate --leverage cocycle-combinatorics <paper>`. Status legend:
`queued` · `mining` · `done → drafts/lit-<slug>.md` · `dropped`.

> **Reframed (2026-06-08) onto the binary/$\chi$-augmentation picture — see [`STRUCTURE.md`](STRUCTURE.md).**
> L1·1–L1·3 (done) are folded into STRUCTURE §1–§3. The deepened, sustained continuation is the
> **reading program STRUCTURE §4 (R1–R5)**: each pass reads ONE paper *against the living note* and
> updates it (note → read → update → iterate). **R1 ✅ done** (Crowell character-augmentation module —
> `drafts/lit-alexander-module.md`): $\mathcal I_D$ pinned, new cocycle $T$, $D=(X{-}1)T-(Y{-}1)S$, Fitting
> filtration terminates at the cores (no finer scalar handle). **R3 ✅ done** (Huang et al. —
> `drafts/lit-plucker-bracket.md`): generic generator $=$ Plücker **pair** ($D$+$S$ rows), **C8 alone
> incomplete**; cycle stratum adds a non-minimal **telescoping** syzygy; the difference ideal $J=$ the
> zero-sum ideal **collapses** to $G$ (no new lever, but unifies floor/lever/zero-sum). **R4 ✅ done**
> (Guiraud–Malbos arXiv:**1011.0558** — `drafts/lit-squier-rewriting.md`): over $\mathbb{Q}[X,Y]$
> $\operatorname{pd}E_0\le1$ (Hilbert–Burch) ⇒ **NO 3-cell** — Plücker pair + telescoping are the **complete**
> 2-cells. **The *polynomial* core-relation module is bounded** (Fitting R1 / 1st syz R3 / higher syz R4 all
> closed over $\mathbb{Q}[X,Y]$): the **polynomial** layer holds no relation beyond C8. **⚠️ Corrected scope
> (2026-06-09): this does NOT close the goal.** R3/R4 answered a *polynomial-ring* syzygy question; the
> expansion-reduction lever lives in the **integer cyclic quotient** $A=\mathbb{Z}[W]/\ker(\pi\circ S)$ (mod
> $G$ — L1·3's "integer/eval, not polynomial" caveat), which Hilbert–Burch does **not** touch. So the earlier
> "Layer-1 COMPLETE / no new lever" was an over-reach (polynomial layer ≠ integer quotient). Live doors:
> **R2** (rank-$\ge2$ enrichment → a genuine 3-cell) and — newly the spine — **Movement IV: expansion-reduction
> in $A$** (non-length-monotone completion; the circulant $\mathbb{Z}[\mathbb{Z}/o]$ arithmetic of the orbit mod $G$). **L1·5 ✅ done (2026-06-09, read *constructively*)** — `drafts/lit-suciu-wang.md`: cup product $=\partial_X$-linearization
> of the core (rank-1 shadow), **no new lever**; the **weight / Chen-rank grading** is the named source of the [P3]
> ceiling's $o$-independence, and the $\ge2$-gap no-go $=$ **weight-growth $\omega\to\infty$**. (Only the *3-cell/holonomy*
> reading of L1·5 was superseded by R4 — the *constructive* weight reading was live and is now mined.) **Next: L1·6**
> (arXiv:2512.05512, "finitely many invariants per fixed combinatorial degree") — is exclusion a *finite-weight*
> phenomenon? — and/or **R5 find-thread** for the twisted (rank-$\ge2$) cup product (door R2).

---

## Movement I — anchor the cocycle as a Magnus representation

### L1·1 — Magnus representation / Gassner as a Magnus cocycle  ✅
- **Paper:** functorial Magnus representation, [arXiv:1604.06905](https://arxiv.org/pdf/1604.06905) · readable · **done → [drafts/lit-magnus-representation.md](drafts/lit-magnus-representation.md)** (2026-06-08)
- **Extract (our terms):** $S(w)=$ off-diagonal Magnus-matrix entry built from Fox derivatives; the cocycle identity in matrix form; **reduced vs. unreduced** Magnus rep; determinant = Alexander invariant.
- **Outcome (certification + 2 named obstructions; NO new reduction law):** RE-1 $\det M(w)=X^{|w|}Y^{\operatorname{len}w}$ is a pure 6-unit ⇒ **resolves L1·7** (the $\operatorname{sixfree}$ ceiling is already a well-defined, *unimprovable* integer); RE-2 $G=|D|=$ eigen-gap ($D^2=\operatorname{tr}^2-4\det$); RE-3 reversal=transpose is a **unitary** (not orthogonal) obstruction. The informative Magnus determinant (Alexander ratio) is **rank $\ge2$** and degenerates in our single-prime-pair setting — Alexander/torsion side **exhausted for rank-1**. Verified `checks/lit_magnus_representation.py` (exit 0). **Propagate** RE-1 + V4 to `approaches/bounded-defect-lever`.

## Movement II — the reduction engine (the word combinatorics)

### L1·2 — Fox free differential calculus  ✅
- **Paper:** R. H. Fox, *Free differential calculus I*, Annals 57 (1953) 547–560 · obtained · **done → [drafts/lit-fox-calculus.md](drafts/lit-fox-calculus.md)** (2026-06-08)
- **Extract:** the fundamental formula as the **canonical reduction primitive**; recast P0–P3 as Fox-derivative identities.
- **Outcome (engine, high value; no new move):** $S=$ total Fox derivative under the rank-1 abelianization, **per-gap split** $S=\sum_d S_d$; **P0–P3 unify into one production rule $(\star)$** (balanced slot-swap; chain rule ⇒ block-coarsening); **NEW canonical $\mathcal{I}_D$-membership identity** $D(w)=\sum_d S_d(w)(X^d-Y)$ over atoms $a_d=X^d-Y$. Verified `checks/lit_fox_calculus.py` (14/14, exit 0). **Hand-off:** the *Fox presentation of $\mathcal{I}_D$* — atoms $a_d$, generator $(\star)$, admissible order $(|\cdot|,\operatorname{len})$, two critical pairs ($\chi(u)=1$ + missing inverse rule) — is now ready for L1·3 and L1·4.

### L1·3 — Gröbner–Shirshov bases for monoid algebras  ✅
- **Paper:** Bokut–Chen, *Gröbner–Shirshov bases and their calculation*, [arXiv:1303.5366](https://arxiv.org/abs/1303.5366) · readable · **done → [drafts/lit-groebner-shirshov.md](drafts/lit-groebner-shirshov.md)** (2026-06-08)
- **Extract:** is the Fox presentation a finite confluent GSB? normal forms? a new completion rule?
- **Outcome (sharp, REDIRECTS the program; no new move):** **$S$ is injective per length** (coeff of $Y^{n-1-k}$ is $X^{e_k}$) ⇒ the word-level $(\star)$-congruence is **trivial** and its normal form is **$S$-blind / length-preserving** — so **"shorter words ⇒ smaller $S$" is provably NOT a word-level GSB** (the exact reason P0–P4 never shrank words). **Reduction lives at the core layer:** unique overlap critical-pair $\delta=S(BAC)-S(ACB)=X^{|A|}C(B,C)-Y^{\operatorname{len}C}C(A,B)$, closing **only via C8/Plücker** ($\delta\in\operatorname{span}_R\{C(A,B),C(B,C)\}$). Three layers: word ($\Phi$ injective, trivial) / core (where reduction is, C8 the sole relator) / coefficient ($D$ monic binomial; cycle ideal **integer/eval, not polynomial**; cores *are* the mod-$D$ relations). Verified `checks/lit_groebner_shirshov.py` (13/13, exit 0). **Hand-off to L1·4:** the single 3-block overlap generating $\delta$, and the question "is C8 the *complete* 2-cell set or is there a 3-cell (holonomy)?". **Program redirect: abandon word-shortening; bound the core module via C8.**

### L1·4 — Squier homological finiteness / rewriting cohomology
- **Paper:** Squier, *Word problems and a homological finiteness condition for monoids*, JPAA 49 (1987); + Guiraud–Malbos, [arXiv:1009.0381](https://arxiv.org/abs/1009.0381) · mixed (Guiraud–Malbos readable) · **queued (NEW ref)**
- **Extract:** **critical pairs = obstructions to reduction = homology classes**.
- **Goal:** test whether our move set is *confluent*, and whether **C8/Plücker and reversal=transpose are the complete obstruction set** — the most likely source of a *new* family-enlarging relation (or a clean "no further reduction" theorem).

## Movement III — the cores and the bridge to the ceiling

### L1·5 — Suciu–Wang holonomy Lie algebra / cup products  ✅
- **Paper:** Suciu–Wang, *Cup products, lower central series, and holonomy Lie algebras*, [arXiv:1701.07768](https://arxiv.org/pdf/1701.07768) · readable · **done → [drafts/lit-suciu-wang.md](drafts/lit-suciu-wang.md)** (2026-06-09)
- **Extract:** the cup-product formula as a core-*generating* identity for $C(u,v)$; the holonomy quadratic relations as the **full relation module** among cores (Plücker = Jacobi as its ideal). Read **constructively** (STRUCTURE §0), not as a 3-cell hunt (R4 already closed that).
- **Outcome (NEW relation + weight bridge; NO new lever):** the cup product is the **$\partial_X$-linearization of our core** at the trivial character — $\partial_X C(u,v)\rvert_{X=Y=1}=E_u o_v-o_u E_v=\langle u\rangle\cup\langle v\rangle$ (with $C\rvert_{1,1}=\partial_Y C\rvert_{1,1}=0$), plus a single-word crossing primitive $A$ with $\delta A=$ linearized core. The rank-1 wall made exact ⇒ cup product is the **shadow** of $C$; **prizes #1/#3 are nulls** (no core *generated*; holonomy quadratic $=$ Jacobi $=$ weight-2 shadow of C8). **The gain is prize #2 (the Movement-III bridge):** the **weight / Chen-rank grading** (Labute) is the named structural source of [P3]'s $o$-independence — $C(\beta,d)$ a *fixed weight-2* cup product, unique bracket ($\dim\operatorname{lie}_2=1$) — and the $\ge2$-growing-gap no-go restates as **weight-growth $\omega\to\infty$**. Verified `checks/lit_suciu_wang.py` (13/13, exit 0). **Build suggested:** the $\chi$-deformation **weight tower** $\partial_X^k C\rvert_{1,1}/k!$ — is exclusion a *finite-weight* phenomenon? (→ L1·6.) **Propagate** the weight-framing to `approaches/bounded-defect-lever`.

### L1·6 — Modular-knot Burau cocycle (boundedness mechanism)
- **Paper:** *Alexander polynomials of modular knots*, [arXiv:2512.05512](https://arxiv.org/pdf/2512.05512) · readable · **queued**
- **Extract:** the proven "**finitely many invariants per fixed combinatorial degree**, any coefficient in long runs" — a ceiling bounded by *combinatorial type, not word length*.
- **Goal:** the bridge from the L1 reduction calculus to the $o$-independent ceiling — the structural form of the bounded-defect lever.

### L1·7 (normalization of the cocycle / determinant) — ✅ resolved by L1·1, not needed
- **Paper:** Kitayama, [arXiv:0705.2371](https://arxiv.org/abs/0705.2371); Conway–Estier, [arXiv:1709.03479](https://arxiv.org/abs/1709.03479) · readable · **dropped — answered by L1·1 RE-1**
- **Resolution:** $\det M(w)$ is a pure 6-unit, so $\operatorname{sixfree}(S(\beta d)-S(d\beta))$ is already the canonical 6-free representative of a full $\pm G$-coset — **well-defined and unimprovable**; no external normalization can sharpen it (the only normalizing unit available *is* $\pm G$). Re-open only if a rank-$\ge2$ enrichment makes $\det$ non-trivial.

---

## Movement IV — expansion-reduction in the integer cyclic quotient $A=\mathbb{Z}[W]/\ker(\pi\circ S)$  *(the reframed spine, 2026-06-09)*

The genuinely live direction for the **Target object** above. L1·3 killed *length-monotone* reduction and
R3/R4 closed the *polynomial* relation module — neither touches the **integer cyclic quotient** $A$ (mod $G$),
where an **expansion-reduction** strategy on the rotation orbit can realize a small nonzero residue. These
leverages mine the algebra of that quotient and of non-length-monotone completion.

### L1·8 — non-length-monotone rewriting / completion-with-expansion  ✅  *(read CONSTRUCTIVELY)*
- **Paper:** Guiraud–Malbos–Mimram, *A Homotopical Completion Procedure with Applications to Coherence of
  Monoids* (RTA 2013, LIPIcs 21, 223–238) · readable · **done → [drafts/lit-homotopical-completion.md](drafts/lit-homotopical-completion.md)** (2026-06-09)
- **Extract:** completion adds rules/cells from critical pairs (expansions) that generate the congruence
  *without* a length-reducing order — does it give an expansion-reduction path to a small residue in $A$
  (mod $G$) beyond the C8 overlap $\delta$?
- **Outcome (honest NULL — and it KILLS the word-level expansion door too):** **(A)** Tietze generator-adding
  / block-coarsening to a super-letter is **$S$-invisible** ($\Phi$ a faithful monoid hom — the rewriting
  form of L1·3 per-stratum injectivity), so non-length-monotone completion adds **no new arithmetic at the
  word/monoid level**. **(B)** the C8 overlap $\delta$ is **coarsening-invariant** ⇒ completion re-derives
  C8/Plücker, adds no cell; the run-sliding infinite family completes to **one fixed weight-2 cell**
  $C(\beta,d)$ (Kapur–Narendran ↔ [P3]). No smaller residue mod $G$. **Gains:** the **quasicenter heuristic
  (§3.4) is the constructive criterion for when [P3] exists** (one growing run $=$ quasicenter); and the null
  **redirects Movement IV to L1·9** — since word/monoid-level expansion is dead, the lever (if any) is the
  **integer circulant residue of the orbit mod $G$**, not a rewriting move. Verified `checks/lit_homotopical_completion.py` (14/14, exit 0). **Propagate** the quasicenter criterion to `approaches/bounded-defect-lever`.

### L1·9 — circulant / $\mathbb{Z}[\mathbb{Z}/o]$ arithmetic of the orbit mod $G$  ✅
- **Paper:** Silver–Williams, ***Mahler measure, links and homology growth*** (Topology 41, 2002,
  **math/0003127**) — the companion that actually carries the resultant identity (the queued
  *Mahler measure of Alexander polynomials* math/0105234 has only Dehn-surgery limits; agent read both,
  used 0003127) · readable · **done → [drafts/lit-silver-williams.md](drafts/lit-silver-williams.md)** (2026-06-09)
- **Extract:** the orbit is a cyclic $\mathbb{Z}[\mathbb{Z}/o]$-module; its circulant determinant is the
  resultant $\operatorname{Res}(t^o-1,\widehat S)=\prod_\zeta\widehat S(\zeta)$ (R-SW2). Does it construct a
  small orbit residue mod $G$?
- **Outcome (constructive NULL — the circulant AMPLIFIES the floor to $G^o$; + 3 new identities):** since
  $G\mid$ every $S^{(j)}$, $G$ survives in **every** DFT component ⇒ $\det\operatorname{circ}(S)=G^o\det\operatorname{circ}(m)$,
  every cyclotomic block $\ge G^{\varphi(d)}$ (R-SW4) — the **sharp integer avatar of R3's $J$-collapse**, no
  smaller residue. The obstruction is exact: $\Delta=X^E-Y^o t$ is **degree-1 & never cyclotomic** ⇒ Mahler $\gt1$
  ⇒ Gordon growth $=$ Layer-2. **New, verified identities:** transfer law $X^{d_j}S(w_{j+1})=Y S(w_j)+D$ (R-SW1);
  circulant$=$resultant (R-SW2); **period Fox formula** $G(w^r)=\prod_{d\mid r}\Phi_d^{*}(2^E,3^o)$ (R-SW3,
  identifies $\Delta_1$ as the cyclic-cover cofactor → feeds Layer-2 Bang–Zsygmondy). Verified
  `checks/lit_silver_williams.py` (49/49, exit 0). **Propagate** R-SW3 blocks + R-SW4 floor to `approaches/bounded-defect-lever`.

---

## Movement IV verdict (2026-06-09) — both spine probes are NULL on construction; the live doors are off the single rank-1 orbit

The reframed spine asked whether an **expansion-reduction** strategy on the cyclic roll, in the **integer cyclic
quotient $A$ (mod $G$)**, can construct a small representative the polynomial closures (L1·3/R3/R4) can't see. Two
leverages settled it for a **single rank-1 orbit**:
- **L1·8** — word/monoid-level *expansion* (Tietze completion) is **$S$-invisible** (rewriting form of L1·3 injectivity); no move.
- **L1·9** — the integer *circulant* of the orbit **amplifies** $G$ to $G^o$; no smaller residue. The crux is exact:
  **the cycle Alexander polynomial $\Delta=X^E-Y^o t$ is degree-1 and never cyclotomic.**

So the expansion-reduction lever does **not** live in the algebra of one rank-1 orbit. The two doors that remain
(both genuinely outside the closed setting):
1. **R2 — rank-$\ge2$ enrichment:** a *higher-degree* cycle polynomial $\Delta$ that **could be cyclotomic** for a
   structured family — the only route to a constructively small orbit residue. **This is now the top live probe.**
2. **Layer-2 $(2,3)$-arithmetic:** Bang–Zsygmondy / BHV on the $\Phi_d^{*}(2^E,3^o)$ blocks (R-SW3) — the existing
   `bounded-defect-lever` no-go, now fed by the period Fox formula.

---

## Movement V — R2: rank-$\ge2$ enrichment (a higher-degree, possibly-cyclotomic $\Delta$)  *(opened 2026-06-09)*

The only door that could turn the algebra **constructive** (a small orbit residue). Seeded by `--find-thread R2`
(THREADS group G — 4 angles converging on "need an enriched $\Delta$ that is generalized-cyclotomic, $M=1$").

### R2·1 — McMullen Alexander–Thurston norm (the GO/NO-GO pivot)  ✅
- **Paper:** McMullen 2002 (Ann. ÉNS 35) · **done → [drafts/lit-mcmullen-norm.md](drafts/lit-mcmullen-norm.md)** (2026-06-09)
- **Outcome (decision + unifying law):** Alexander norm $=$ Newton-polytope width; our $\Delta_G$ is **binomial in
  every guise** ⇒ **segment polytope** ⇒ **no unit ($M{=}1$) slice** (binomial dichotomy: non-unit $s^a-s^b$, or
  vanishing $b_1{=}\infty$). **This unifies + retires the R1 and L1·9 nulls as one geometric fact.** A small slice
  **requires a 2-dim Newton polytope** ($\ge3$ non-collinear monomials); **every rank-1-derived enrichment**
  ($D,T,(\Delta_S,\Delta_T)$, circulant) **stays $\dim N\le1$** — so **refined NO-GO** there. McM-5: cores
  $\in\mathfrak m^1\setminus\mathfrak m^2$, lead term $=$ cup product, $p{=}1$. Verified `checks/lit_mcmullen_norm.py`
  (18/18). **The single live door inside $(2,3)$: a non-abelian twisted $\Delta_\rho$ (multi-term in $t^n$).**

### R2·2 — Boden–Friedl IV: non-abelian twisted Alexander polynomial  ✅  *(the decisive test — CLOSED)*
- **Paper:** Boden–Friedl 2012, *Metabelian SL$(n,\mathbb C)$ reps IV* (arXiv:1209.4244) · **done → [drafts/lit-boden-friedl.md](drafts/lit-boden-friedl.md)** (2026-06-09)
- **Outcome (decisive NO-GO + unifying lemma):** we admit metabelian reps (from the **period module** $H/(t^n-1)=\mathbb Z/G(w^n)$,
  non-degenerate since $2^E/3^o$ is never a root of unity), but the metabelian monodromy is a **single weighted $n$-cycle**
  whose **char poly is forced binomial** $\lambda^n-(\prod g_i)\mu^n$ ⇒ $\Delta_\rho=X^{En}-c_\chi Y^{on}t^n$ (segment, no
  $M=1$ slice); every escape (Wada mult./tensor/within-orbit) stays binomial. **No $(2,3)$-twist gives a 2-dim Newton
  polytope.** Verified `checks/lit_boden_friedl.py` (18/18). **Unifying lemma: "one weighted cycle ⇒ binomial char poly"**
  $=$ the common mechanism of the abelian-DFT (L1·9), metabelian (R2·2), and orbit-circulant collapses. Suciu/Teichmüller
  follow-ups now superfluous (Suciu only confirms: a binomial's char variety is one translated subtorus, no 2-dim jump).

---

## ==> LAYER-1 CLOSED (2026-06-09). The algebraic incubation has reached its terminus.

The Layer-1 algebra is closed in **all three** directions, all collapsing to the **same wall**: the cocycle's Alexander
polynomial is the **binomial** $\Delta=X^E-Y^o t$, and a binomial has **no unit ($M=1$) slice** (segment Newton polytope).
- (i) **polynomial syzygies** (R1/R3/R4): cores are the complete handle, $\operatorname{pd}\le1$, no 3-cell.
- (ii) **integer-quotient expansion-reduction** (Movement IV): word/monoid completion is $S$-invisible (L1·8); the integer circulant amplifies the floor to $G^o$ (L1·9).
- (iii) **representation-theoretic enrichment** (Movement V / R2): every rank-1-derived enrichment (McMullen R2·1) and every metabelian twist (Boden–Friedl R2·2) stays binomial ⇒ segment ⇒ no $M=1$ slice.

**No constructive lever lives in the algebra.** Exclusion lives **entirely in the Layer-2 $(2,3)$-arithmetic** —
Bang–Zsygmondy / BHV on the $\Phi_d^{*}(2^E,3^o)$ blocks (R-SW3) — the home of the `approaches/bounded-defect-lever`
no-go. **Next: pivot to Layer-2 (an approach, not an incubation thread).** The reframed expansion-reduction objective is
answered: it cannot beat the floor within the algebra; the binomial $\Delta$ is the obstruction, and breaking it needs
arithmetic the $(2,3)$-dynamics does not provide.

---

## Throughline

L1·1 anchors the cocycle. **The original throughline (L1·2–4 "build a length-reducing calculus") is
RETIRED** — L1·3 proved length-monotone word reduction is dead, and R3/R4 closed only the *polynomial*
relation module. **The reframed spine is Movement IV: expansion-reduction on the cyclic roll in the
integer quotient $A$ (mod $G$)** — non-length-monotone completion (L1·8) and the circulant arithmetic of
the orbit (L1·9), with L1·5–6 / the [P3] weight tower supplying the bounded reduction target. R3/R4 are
retained as a **bounding lemma** (the polynomial layer adds nothing beyond C8), not the terminus. After each
leverage, fold its `lit-<slug>.md` and update the status above; re-run `--find-thread` if a step opens a new
sub-question.
