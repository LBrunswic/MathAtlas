# Covering reductions (the existential / non-systematic meta-layer)

**Promise:** medium — Part 1's *core primitive* (multi-anchor shared-frame extraction) is **verified
airtight** and yields one genuinely **new excludable family** (periodic backgrounds $u^p\beta$,
enlarging P3 from single-letter to period-$u$ runs). But the same verification **localizes the
strategy's make-or-break exactly on the P4 trapped-run obstruction**: a variable block survives with a
*bounded* 6-free prefactor only when there is a **single** growing background; $\ge 2$ growing runs —
even perfectly aligned — make the unit *prefactors* diverge. So the meta-strategy can only ever cover a
positive-density family if pigeonhole forces a single-background structure, which the Part-2 probe
finds generic words do **not** have. The genuinely open part is whether a **chain of many local moves**
(not a single combination) can cover — the unavoidable-patterns / Zimin-word `--find-thread` target.
**Status:** exploratory — **Part 1 foundation verified** (`checks/covering_reductions.py`, exit 0);
Parts 2/3 framed with one probe each. The meta-strategy's make-or-break (Part-2 extractability +
strength) is the **open crux**, sharpened but not closed.
**Last iterated:** 2026-06-09 (Gen 1 of this draft)

## The strategy (3 parts) — systematic-vs-special, why the closures don't block it

Recent leverages **CLOSED *systematic* word reduction**: there is no single confluent length-reducing
rule / Gröbner–Shirshov basis (L1·3 — $S$ is injective per stratum), and no representation-theoretic
twist inside $(2,3)$ gives a 2-dim Newton polytope / $M=1$ slice / small core (R2 — Boden–Friedl,
McMullen). Those are **systematic** statements: "there is no *uniform rule* that reduces *every* word."

**This strategy is *special / existential*, not systematic, so the closures do not apply.** Build a
**covering family** of reduction *patterns* $\{\pi_1,\dots,\pi_m\}$ such that **every word in a
positive-density family contains at least one** $\pi_i$ (we don't know *which* — hence non-systematic,
but existence is guaranteed by an unavoidability/pigeonhole argument). If each $\pi_i$ triggers a
reduction to a small core, then every such word reduces $\Rightarrow$ small core $\Rightarrow$
$G=|2^E-3^o|\le\operatorname{sixfree}(\text{core})$ bounded $\Rightarrow$ violates Matveev/Ellison
$G\gtrsim 2.56^{\,o}\Rightarrow$ excluded. The closures forbid *one rule for all words*; they say
nothing about *a finite menu of patterns, one of which each word must contain*.

### Core primitive — multi-anchor shared-frame extraction (generalizes the proven P3)

Cut a word into blocks $W=b_1b_2\cdots b_m$. The cocycle $S(uv)=Y^{\operatorname{len}v}S(u)+X^{|u|}S(v)$
telescopes to
$$S(W)=\sum_{i=1}^m X^{\operatorname{Pre}_i}\,Y^{\operatorname{Suf}_i}\,S(b_i),\qquad
\operatorname{Pre}_i=\!\!\sum_{j\lt i}\!|b_j|,\quad \operatorname{Suf}_i=\!\!\sum_{j\gt i}\!\operatorname{len}(b_j).$$
If $W'=b_1'\cdots b_m'$ has $\chi(b_i')=\chi(b_i)$ for **every** $i$ (equal letter-sum **and** length —
e.g. $b_i'$ a permutation of $b_i$), the prefactors $X^{\operatorname{Pre}_i}Y^{\operatorname{Suf}_i}$
are **identical** for $W$ and $W'$, so
$$\boxed{\,S(W)-S(W')=\sum_{i=1}^m X^{\operatorname{Pre}_i}Y^{\operatorname{Suf}_i}\bigl(S(b_i)-S(b_i')\bigr)\,}$$
The **anchor** blocks (the matched/shared sub-patterns $x,y,z$, with $b_i=b_i'$) **cancel**; only the
**variable** blocks survive, each as a **unit** $\operatorname{unit}_K=X^{\operatorname{Pre}_K}Y^{\operatorname{Suf}_K}$
times a shorter block-difference. *More aligned anchors $\Rightarrow$ more cancellation.* Special cases:
- **P3** (one variable block) $=$ $[P,M,Q]$ with $P,Q$ anchors, $M\to M'$: recovers
  $S(PMQ)-S(PM'Q)=X^{|P|}Y^{\operatorname{len}Q}(S(M)-S(M'))$ **exactly** (verified, PART A pin).
- **P1** (one anchor block $u$): with $\chi(x)=\chi(x'),\chi(y)=\chi(y')$ the plain difference
  $S(xuy)-S(x'uy')=\operatorname{unit}_x(S(x)-S(x'))+\operatorname{unit}_y(S(y)-S(y'))$, the inner core
  $u$ as the anchor (verified, PART A). P1's $\chi$-reweighting is the device for the $\chi(x)\ne\chi(x')$
  case. **$u^p v$** is the $p\sim o/\operatorname{len}u$-aligned-anchor case (Family 1).

### Part 1 — the verifiable foundation (DONE this generation)

**(1) The multi-anchor identity is verified** over $\mathbb{Z}[X,Y]$ on the real kernel for 1, 2, 3
anchors (PARTS A; 60 random instances each + explicit pins). The exact unit prefactors are
$\operatorname{unit}_K=X^{\operatorname{Pre}_K}Y^{\operatorname{Suf}_K}$ (e.g. the pinned 3-anchor
$AxByCzD$ gives $\operatorname{unit}_{A,B,C,D}=Y^{7},X^{4}Y^{6},X^{8}Y^{5},X^{10}Y^{4}$ off a sample
signature). It generalizes P3 (single frame) and P1 (single inner core), both reproduced exactly.

**(2) Reduction-strength bookkeeping — *which families reduce strongly enough to exclude?*** The
winning condition (à la P3, **not** "core $\lt G$") is: the **6-free part of the residual core bounded
independent of $o$**. A residual is bounded iff it is **one** $\operatorname{unit}\times(\text{bounded
block-difference})$; that needs **all but one** block to be an anchor.

| Family | shape | residual | 6-free vs $o$ | verdict |
|---|---|---|---|---|
| **F1 periodic bg** | $u^p\beta$ | $\operatorname{unit}\cdot(S(\beta u)-S(u\beta))$ | **bounded** (o-indep) | **EXCLUDES** (NEW) |
| **F2 two growing runs** | $e_1d^ae_2d^{2a}$ | best valid combo | grows $23,23,1537,26857$ | weak (open no-go) |
| **F3 symmetric two-anchor** | $\beta_1u^k\beta_2u^k$ | $(\operatorname{unit}_{\beta_1}\!-\!\operatorname{unit}_{\beta_2})(S\beta_1\!-\!S\beta_2)$ | grows $1319,\dots,24{,}062{,}143$ | weak |

- **F1 is a genuine *new* excludable family.** $u^p\beta$ = a bounded defect arc $\beta$ sliding through
  a **period-$u$** run (not a single-letter run $d^L$). Both $u^k\beta u^{p-k}$ and
  $u^{k+1}\beta u^{p-k-1}$ are rotations of cyclic $u^p\beta$, so the wedge is a **valid** $G$-multiple;
  by the identity it equals $\operatorname{unit}\cdot(S(\beta u)-S(u\beta))$, $o$-independent. Verified
  ceilings $13,23,53,5$ for $u=(1{,}2),(2{,}1),(1{,}1{,}2),(2{,}3)$; $G\mid\text{ceiling}$ and
  $G\le\text{ceiling}$ over $p=2..9$. **This is the one promotion-grade output of Part 1** — it
  **enlarges P3 from single-letter to periodic backgrounds.**
- **F3 is the decisive structural finding.** Even when two anchors $u^k$ are *perfectly aligned* (matched
  positions, identical content) and the defects $\beta_1,\beta_2$ are $\chi$-matched so the rotation
  cleanly swaps them, the residual is $(\operatorname{unit}_{\beta_1}-\operatorname{unit}_{\beta_2})(S(\beta_1)-S(\beta_2))$:
  a **difference of two units sitting $O(o)$ apart** times a bounded factor. The bounded factor is
  irrelevant — the *unit prefactor difference* diverges (6-free $1319,9823,72023,\dots$, Bang–Zsygmondy).
  **So "more aligned anchors" does *not* rescue exclusion once there are $\ge2$ growing runs** — it
  recovers the P4 trapped-run obstruction at the level of the prefactors. A variable block contributes a
  *bounded* 6-free part only with a **single** $\operatorname{unit}$, i.e. a **single growing
  background**.

**Part-1 verdict.** The core primitive is exact; its exclusion reach is precisely *single growing
background + bounded defect arc*, now extended to **periodic backgrounds** (F1, new). It does **not**
break the $\ge2$-growing-run barrier; the meta-strategy inherits P4's obstruction.

### Part 2 — the make-or-break (the pigeonhole/unavoidability step) — FRAMED, not closed

Among the $n$ length-$L$ windows of a length-$n$ word over the gap alphabet, if the number of distinct
patterns is $o(n)$ then some short pattern repeats $\gtrsim n/(\#\text{patterns})$ times $\to$ many
anchors. **This is exactly unavoidable-patterns / Zimin-word theory** (combinatorics on words) married
to our arithmetic — flag for `--find-thread`. The two **hard sub-questions**, now sharp:

- **(a) Extractability.** Are the pigeonhole-forced repeats in *aligned / $\chi$-matched*
  (rotation-lattice-composing) configuration, or just raw occurrences? Part 1 (F1 vs F3) says a forced
  repeat is *extractable to a bounded residual* **only if it forms a single growing background**
  (the run goes entirely into the anchor frame). Scattered repeats with growing material between them
  hit F3 (diverging prefactor difference).
- **(b) Strength.** Does the cumulative reduction bound the 6-free part **independent of $o$**, or only
  shave a constant? F1 bounds it; F2/F3 do not.

**The probe (PART C, honest).** For random words ($n=8,16,32,64$, gaps $1..3$) measure the maximal
**shared-frame length** over rotation pairs (common prefix $+$ common suffix); the *residual block* is
$n-\text{maxframe}$. A bounded single-frame extraction needs $\text{residual}=O(1)$. Result: mean
residual length $5.6\to12.4\to26.6\to57.9$ — it **drifts up linearly with $n$**. Generic words have
**no long shared frame**, so the bounded single-frame extraction is **unavailable**, confirming that
pigeonhole-forced repeats are *not* in single-background configuration. **Honest caveat:** this does
**not** prove no clever *multi-move* covering exists — chaining many local reductions is exactly the
open question.

### Part 3 — the dichotomy (balanced ⇒ pigeonhole, heavy ⇒ P3) — SKETCH + one check

The circuit word $0^a1^b$ (single huge run) is the **low-subword-complexity extreme**: pigeonhole-as-
repeats is weakest, but the single run is **P3** territory. Decompose $w=uv$ via the **cocycle
partial-sum walk** $e_k=\sum_{j\lt k} d_j$ and its **discrepancy** $\max_k|e_k-\rho k|$, $\rho=|w|/\operatorname{len}w$:

- $v$ **heavy** $=$ a long single-letter run $d^L$ (the walk has a long straight segment, slope $d$) —
  **P3 regime**. Verified (PART D): a junction defect $e$ against $d^L$ gives the P3 bounded wedge,
  $\operatorname{sixfree}(S(ed)-S(de))=7$, $o$-independent over $L=2..8$.
- $u$ **balanced** $=$ low discrepancy (the walk hugs the line) $\Rightarrow$ no long run
  $\Rightarrow$ high subword complexity $\Rightarrow$ **pigeonhole forces a repeated short factor** —
  **Part-2 regime**. Verified (PART D): a Sturmian-like $u$ (discrepancy $0.80$, alphabet $\{1,2\}$,
  length 15) is forced to contain a repeated length-4 factor (e.g. $(1,2,1,1)$).

The decomposition covers the word space (balanced $\cup$ heavy), but the two regimes are handled by
**different** moves and the **unsolved coupling is the $u$–$v$ junction**: one combination cannot bound
both the balanced anchors and the heavy run at once (F3's two-growing-region obstruction). This is the
same wall as P4, restated at the dichotomy level.

## Thread

This is the **meta-layer** that deploys the proven extractions P1 (inner core, $\chi(u)$) and P3 (outer
frame, $X^{|P|}Y^{\operatorname{len}Q}$) via an *existential/unavoidability* mechanism, dodging the
*systematic* closures L1·3/R2. Part 1 verifies the core primitive and finds its exact reach (single
growing background, now periodic — F1 new). Parts 2/3 are the open crux: the same Part-1 bookkeeping
shows the meta-strategy faces the **P4 trapped-run obstruction** whenever pigeonhole produces $\ge2$
growing runs, which the probe finds is the generic case. The live hope is multi-move covering, an
unavoidable-patterns question.

## Working notes

- **The exact mechanism of failure (F3, the cleanest new exhibit).** With anchors aligned, the residual
  is $(\operatorname{unit}_{\beta_1}-\operatorname{unit}_{\beta_2})(S(\beta_1)-S(\beta_2))$. At $(2,3)$
  the prefactor difference is $\sim 3^{\Theta(k)}-2^{\Theta(k)}3^{\Theta(k)}$ — two monomials whose
  exponents grow as the anchors recede $O(o)$ apart. Bang–Zsygmondy on that binomial-of-monomials
  forces a primitive prime, so $\operatorname{sixfree}$ diverges. **The anchors cancel, but the
  *positions* of the surviving variable blocks do not — and the position monomials are the obstruction.**
  This is the prefactor-level statement of P4's "at most one run can be a shared frame per combination."
- **Why F1 works and F2/F3 don't, in one line.** F1 has **one** variable block (the residual is one
  $\operatorname{unit}\times$bounded) because the *entire* growing structure is the periodic background,
  which sits in the anchor frame. F2/F3 have a *second* growing run trapped between defects, forcing a
  **second** $\operatorname{unit}$ (or a unit *difference*) that diverges.
- **F1 vs P3, precisely.** P3 = uniform run $d^L$ (a single repeated **letter**). F1 = a run $u^p$ of a
  fixed **period** $u$ (a repeated **block**). The sliding move slides $\beta$ by one full period $u$;
  both endpoints are rotations because the cut at period boundaries of $u^p\beta$ gives $u^{p-j}\beta u^j$.
  The ceiling is $\operatorname{sixfree}(S(\beta u)-S(u\beta))$ — the period-$u$ analogue of $S(\beta d)-S(d\beta)$.
- The probe's residual-length growth is a *necessary-condition* test (no long shared frame $\Rightarrow$
  no single-frame extraction). It cannot see multi-move chains, which is why Part 2 stays open.

## Open questions

- [ ] **(Part-2 crux — the make-or-break)** Can a **chain of local reductions** (not one combination)
      cover a positive-density family? The probe kills the *single-frame* route for generic words; the
      multi-move route is untested. This is the unavoidable-patterns / Zimin-word `--find-thread` target
      — does combinatorics-on-words give a covering set of patterns each forcing a *single-background*
      sub-configuration?
- [ ] **(Part 1 — promote F1?)** The periodic-background family $u^p\beta$ has an $o$-independent
      ceiling $\operatorname{sixfree}(S(\beta u)-S(u\beta))$. Tabulate which periods $u$ and arcs $\beta$
      give the **smallest** ceilings (the F1 analogue of the bounded-defect atlas); does the
      cyclotomic-collapse gate generalize from $X^{|e-d|}-1$ to the period-$u$ core? Confirm $u^p\beta$
      is not already subsumed by P3 under a change of background (it is not for non-constant $u$).
- [ ] **(Part 1 — multi-period backgrounds)** Does $u^p w^q\beta$ (two *different* periodic
      backgrounds, both growing) reduce, or is it the F2/F3 trapped case? Predict: trapped (two growing
      runs of different periods cannot both be a single frame). Verify.
- [ ] **(Part 3 — quantify the junction)** Make the $u$–$v$ coupling precise: for $w=uv$ with $u$
      balanced and $v=d^L$ heavy, is there *any* rotation combination bounding $G(w)$ $o$-independently,
      or does the balanced part's scattered anchors always trap a run? (Expected: trapped, = F3.)
- [ ] **(Part 2 — strength even if extractable)** Suppose a forced repeat *is* a single background of
      period $u$ covering a $(1-\epsilon)$-fraction of the word; is the residual defect arc *bounded*,
      or does the $\epsilon$-fraction of "other" letters form a second growing run? Density alone may
      not give a *bounded* arc.

## Iteration log
- 2026-06-09 (Gen 1, this draft): created for the user's covering-reductions strategy. **Part 1 done
  and verified** (`checks/covering_reductions.py`, exit 0): the multi-anchor shared-frame identity
  proven over $\mathbb{Z}[X,Y]$ for 1/2/3 anchors with pinned unit prefactors (PART A); reduction-strength
  bookkeeping of three families (PART B) — **F1 periodic background $u^p\beta$ is a NEW excludable
  family** ($o$-independent ceiling, enlarges P3 from single-letter to period-$u$ runs), while **F2**
  (two growing runs) and **F3** (symmetric two-anchor) **diverge** — F3 the cleanest exhibit that
  aligning anchors does not help (the unit *prefactor difference* diverges). **Part 2 framed** as the
  open make-or-break with sub-questions (a) extractability and (b) strength; **probe (PART C)** shows
  generic random words have residual block growing linearly with $n$ (no long shared frame $\Rightarrow$
  single-frame extraction unavailable) — honest, does not rule out multi-move covering. **Part 3
  sketched** with the discrepancy decomposition $w=uv$ (balanced $\Rightarrow$ pigeonhole, heavy
  $\Rightarrow$ P3) and one check (PART D): heavy $d^L$ is P3 ($o$-indep ceiling $7$), balanced
  Sturmian-like $u$ forced to repeat; the $u$–$v$ junction is the unsolved coupling. Flagged
  unavoidable-patterns / Zimin words as the `--find-thread` target for Part 2.
