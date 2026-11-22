# Inner-core extraction (the corrected "balanced swap")

**Promise:** medium — the identity is **certified airtight** (a fully proven $\mathbb{Z}[X,Y]$
identity): a fixed inner subword extracts up to the unit $\chi(u)$. The Gen-2 "no-go" (bridge object
never $\lt G$) is **true but was not the right test**: exclusion needs a bounded *6-free part*, not a
sub-$G$ core (Gen 3). The lever that bounds a defect is the **dual** of P1 — share the outer runs,
vary the inner block — distilled into [bounded-defect-lever](bounded-defect-lever.md).
**Status:** principle — **proven** (identity); program-route **re-opened** via the dual extraction
(Gen 3): feeds the program for bounded contiguous defect arcs. **Gen 5:** the user's normalized
re-expression is certified — P1 $=$ a reversal-symmetric pair of dual-P1 extractions; **no** new
$u$-free reduction (obstruction $\chi(u)=1$); real signal but a unification, not a lever.
**Last iterated:** 2026-06-08 (Gen 5)

## The principle (one crisp claim)

For any blocks $x,x',y,y'$ and any inner core $u$, the cocycle rule gives the **exact** identity
$$\chi(x')\,S(xuy)-\chi(x)\,S(x'uy')\;=\;\underbrace{\bigl[\chi(x')S(x)-\chi(x)S(x')\bigr]}_{\text{outer boundary term, $u$-free}}\;+\;\chi(x)\chi(x')\chi(u)\,\bigl[S(y)-S(y')\bigr].$$
So **a fixed inner subword $u$ contributes only through the unit $\chi(u)$** — it can be extracted
up to a $\mathbb{Z}[1/6]$ unit, leaving a boundary term plus a (unit-scaled) short difference.

**Corollary (the literal Move 2 is false).** $\chi(x')S(xuy)-\chi(x)S(x'uy')\sim S(yx)-S(y'x')$
does **not** hold in general: matching the $S(x)$-coefficient of any combination
$\alpha S(xuy)-\beta S(x'uy')$ against $S(yx)-S(y'x')$ forces $\chi(x)\chi(u)\chi(y)=\chi(xuy)=1$,
impossible for a nonempty word.

**Corrected characterization of the unit cases** (the old claim "$x=x'$ or $y=y'$" was *false* —
it captures only 96 of the 210). The **structural** unit family is exactly $S(y)=S(y')$ (in the
$\chi$-normalized $S$; verified in [`../checks/unit_cases.py`](../checks/unit_cases.py), 152 cases,
zero exceptions): there the core term vanishes and, with balance $\chi(x)\chi(y)=\chi(x')\chi(y')$,
putting $\lambda:=\chi(x')/\chi(x)=\chi(y)/\chi(y')$,
$$\text{LHS}=\chi(x)\,[\lambda S(x)-S(x')],\qquad S(yx)-S(y'x')=\chi(y')\,[\lambda S(x)-S(x')],$$
so the ratio is the unit $\chi(x)/\chi(y')$ **exactly** (proven, not just numeric). The remaining 58
unit cases have $S(y)\ne S(y')$ and are $u$-dependent numerical coincidences with no closed form.

## The normalized form (Gen 5 — chasing the user's hint)

Introduce the **suffix-weighted ("reversed") sum** $\hat S(w):=S(w)/\chi(w)$, whose cocycle reads
$\hat S(ab)=\hat S(b)+\hat S(a)/\chi(b)$ — the prefix cocycle read right-to-left (it is the
transpose direction of the transfer matrix; see *Reversal* below). Dividing the proven P1 identity by
the unit $\chi(x)\chi(x')\chi(u)$ (legitimate, $\chi$ is a $\sim$-unit, $G\perp6$) and reassembling
with the cocycle gives **two exact $\mathbb{Z}[X,Y]$ closed forms** (no balance needed):
$$\frac{\chi(x')S(xuy)-\chi(x)S(x'uy')}{\chi(x)\chi(x')}
   \;=\;\underbrace{\bigl[\hat S(x)-\hat S(x')\bigr]}_{\text{suffix / right read}}
   \;+\;\underbrace{\bigl[S(uy)-S(uy')\bigr]}_{\text{prefix-shared core }u},$$
$$\frac{\chi(x')S(xuy)-\chi(x)S(x'uy')}{\chi(x)\chi(x')\chi(u)}
   \;=\;\bigl[\hat S(xu)-\hat S(x'u)\bigr]\;+\;\bigl[S(y)-S(y')\bigr].$$
Here $S(uy)-S(uy')=\chi(u)\,[S(y)-S(y')]$ (the shared **prefix** $u$ extracts as the unit $\chi(u)$,
$S(u)$ cancelling) and $\hat S(xu)-\hat S(x'u)=[\hat S(x)-\hat S(x')]/\chi(u)$ (the shared **suffix**
$u$ extracts as the unit $1/\chi(u)$). The inner-core $\hat S(u)$ cancels in both. Certified in
[`../checks/p1_hint_reduction.py`](../checks/p1_hint_reduction.py) (PART A free-symbol + PART B real
kernel, $549$ suffix-cocycle instances and $128$ closed-form instances over 8 length signatures, all
$\mathbb{Z}[X,Y]$, zero failures).

**What this *is*:** P1 normalized $=$ **a prefix (left) extraction $+$ a suffix (right) extraction** —
i.e. P1 is literally **the dual shared-frame lever applied twice** (once on each end), and is
**reversal-symmetric**. The two Gen-3 "P1 vs its dual" objects are one identity in two normalizations.
The residual boundary term is itself a clean suffix-difference:
$\chi(x')S(x)-\chi(x)S(x')=\chi(x)\chi(x')\,[\hat S(x)-\hat S(x')]$.

**What it is *not*: no new $u$-free reduction.** Writing $Q:=\dfrac{\chi(x')S(xuy)-\chi(x)S(x'uy')}{\chi(x)\chi(x')\chi(u)}
=[S(y)-S(y')]+\dfrac{\hat S(x)-\hat S(x')}{\chi(u)}$, the core $u$ **survives** as the unit $\chi(u)$
weighting the two boundary differences against each other. $Q$ genuinely depends on $u$
([`p1_hint_reduction.py`](../checks/p1_hint_reduction.py) PART C: fixing $x,x',y,y'$ and varying $u$
over distinct $\chi$-signatures gives **5 distinct** $Q$ values). So $Q$ is **not** a unit times any
$u$-free difference of shorter/rearranged words built from $x,x',y,y'$ — *except* in the degenerate
**unit family $S(y)=S(y')$**, where the $y$-term vanishes and $Q=[\hat S(x)-\hat S(x')]/\chi(u)\sim
\hat S(x)-\hat S(x')$ (a genuine suffix-shared extraction shortening $xuy\!\mapsto\!x$). PART C2b
confirms this split: for $S(y)=S(y')$ quads, $u$-free targets work for **all** $u$; for generic
$S(y)\ne S(y')$ quads, **0** targets work for all $u$. The precise obstruction:
$Q-Q|_{\chi(u)=1}=(\hat S(x)-\hat S(x'))\,(1/\chi(u)-1)$, nonzero unless $\chi(u)=1$ — which is exactly
the old Move-2 obstruction $\chi(xuy)=1$, recovered cleanly in the normalized frame.

**Verdict.** The user's manipulation is **real signal but a re-expression, not a new lever**: it
exposes P1 as a reversal-symmetric pair of dual-P1 (shared-frame) extractions and normalizes the
boundary term to $\hat S(x)-\hat S(x')$ — sharpening the *bridge* to [bounded-defect-lever](bounded-defect-lever.md),
not opening a new exclusion route. The inner core cannot be deleted; it can only be *rolled to a
boundary* (becoming a shared prefix/suffix frame) and there extracted as a unit.

## Thread

This is the salvage of the original "extract sub-patterns / roll the subword" hope. The user's
instinct (a fixed core $u$ should be removable) is correct; the precise output is the boundary term
$\chi(x')S(x)-\chi(x)S(x')$, not $S(yx)-S(y'x')$. **Gen 5 sharpens this:** normalized, that boundary
term is the suffix-difference $\hat S(x)-\hat S(x')$, and the whole P1 combination is a prefix
extraction plus a suffix extraction — the inner core can be *rolled to either boundary* but never
deleted (obstruction $\chi(u)=1$).

## Working notes

**[Gen 1] First evidence** (in [`../checks/move_checks.py`](../checks/move_checks.py)): over 392
$\chi$-balanced instances the literal swap ratio is a unit in 210, non-unit in 182; the free-symbol
expansion gives $\text{LHS}=\chi_{x'}S_x-\chi_x S_{x'}+\chi_x\chi_{x'}\chi_u(S_y-S_{y'})$, and the
literal-Move-2 obstruction is $\chi(xuy)=1$ (impossible).

**[Gen 2] P1 certified airtight** ([`../checks/p1_certificate.py`](../checks/p1_certificate.py), exit 0):
- **Part A** free-symbol cocycle proof — two applications of $S(ab)=S(a)+\chi(a)S(b)$ with $\chi$
  multiplicative give the boxed identity, $S(u)$ cancelling exactly.
- **Part B** the *real kernel* identity (homogenized $S$ from `lib/cocycle.py`, $X,Y$ symbolic) is
  verified $=0$ as a $\mathbb{Z}[X,Y]$ identity over **216 concrete instances spanning 9 block-length
  signatures** (core lengths 0–3, asymmetric/empty blocks). Each pass certifies the identity at that
  block-length signature, not merely at $(2,3)$.
- **Part C** a fully symbolic-letter instance (lengths fixed, letters free) simplifies to $0$ over
  $\mathbb{Q}(X,Y)$. So the identity is **proven for all blocks**, not just sampled.

**[Gen 2] The $G$-divisibility bridge — real but vacuous**
([`../checks/g_divisibility_bridge.py`](../checks/g_divisibility_bridge.py), exit 0, 17952 instances):
- *The right family:* let $W=uR$ (cyclic) with $u$ occurring **once**; two splits $R=R_1R_2=R_1'R_2'$
  give $xuy=R_2\,u\,R_1$ and $x'uy'=R_2'\,u\,R_1'$, **both rotations of $W$**, with $x,x',y,y'$
  partitioning $R$ — none containing $u$. (My first attempt $W=sutu$ was wrong: it buried a second
  copy of $u$ inside $y$. With one $u$, the core is genuinely eliminated.)
- Since $G\mid S(\text{any rotation of }W)$ and $\chi(\cdot)$ is a unit ($G\perp6$), $G\mid\text{LHS}$
  **automatically**. Verified on all 17952; the **control** (non-rotation pairs) gives $G\mid\text{LHS}$
  in only 6/87, so the rotation hypothesis is doing the work.
- **$u$-elimination is striking:** for fixed $(R,\text{splits})$ and fixed $(\lvert u\rvert,\operatorname{len}u)$,
  the integer LHS is **identical** across different cores $u$ (e.g. cores $(1,3),(2,2),(3,1)$ all give
  $-6248/729$). The arbitrarily long middle $u$ is invisible to the constraint beyond its $\chi$-signature.
- **But the ceiling is vacuous:** $0/17952$ instances have $0\lt\lvert\text{num(LHS)}\rvert\lt G$.

**[Gen 2] Why it is vacuous — a rigorous no-go**
([`../checks/small_core_search.py`](../checks/small_core_search.py), exit 0):
- *Tension (Part A, proven):* $u$ drops out of the **plain** difference $S(xuy)-S(x'uy')$ iff
  $\chi(x)=\chi(x')$ (the $S(u)$-coefficient is exactly $\chi(x)-\chi(x')$); and then
  $\text{LHS}=\chi(x)\,[S(xuy)-S(x'uy')]$ — a unit times the genuine antisymmetric core.
- *Search (Part B):* over cyclic words len 4–7, every equinumerous middle-$u$ rotation pair with
  $\chi(x)=\chi(x')$ gives $\lvert\text{num}\rvert\ge G$ (smallest ratio $=2$); **no** small core.
- *No-go (Part C, certified):* **any** $\mathbb{Z}[1/6]$-unit combination of *full* rotation sums of
  $W$ is a multiple of $G$ (since $G$ divides each rotation sum); as $G$ is **odd**, its odd part is
  still a multiple of $G$, so a nonzero such combination has $\lvert\text{odd part}\rvert\ge G$. A
  Matveev ceiling needs a core $\lt G$ — impossible unless the core is $0$ (the classical Steiner/
  bounded-circuit locus). **Conclusion: the P1 bridge can never beat the size barrier.** Small cores
  must be wedges $C(u,v)=D(u)S(v)-D(v)S(u)$ of *proper* sub-blocks (whose own $D$ can be small), where
  P1's $u$-elimination does not apply. See [rotation-combo-floor](rotation-combo-floor.md).

**[Gen 5] Reversal / transpose connection** ([`p1_hint_reduction.py`](../checks/p1_hint_reduction.py)
PART D, exit 0): $\hat S(w)=\sum_{j=1}^{o}X^{-e^R_j}Y^{j}$ where $e^R_j$ are the prefix sums of the
**reversed** word $w^R$ — verified over all $120$ words of length $\le4$. So $\hat S$ reads $w$
right-to-left. In structure.md's transfer matrix $M(w)=\bigl(\begin{smallmatrix}Y^o&0\\ S&X^E\end{smallmatrix}\bigr)$,
this is the **transpose** direction: $M(w)^\top$ is the reversed product of $M(d)^\top=\bigl(\begin{smallmatrix}Y&1\\0&X^d\end{smallmatrix}\bigr)$,
with the same off-diagonal $S$. The prefix-extraction term $S(uy)-S(uy')$ lives in $M$; the
suffix-extraction term $\hat S(x)-\hat S(x')$ lives in $M^\top$. P1's reversal symmetry is the
statement that the combination is invariant (up to a unit) under this transpose — which is *why* it
unifies with the dual shared-frame lever (`bounded-defect-lever`), whose engine
$S(PMQ)-S(PM'Q)=X^{|P|}Y^{\operatorname{len}Q}(S(M)-S(M'))$ is the prefix-extraction term read on
both ends.

## Open questions

- [x] **General proof.** *Done* — `p1_certificate.py` proves it three ways (free-symbol, real-kernel
      $\mathbb{Z}[X,Y]$ over 9 block-length signatures, symbolic letters). Airtight.
- [x] **Characterize the 210 unit cases.** *Done & corrected* — the old $\{x=x'\}\cup\{y=y'\}$ is
      **false** (96/210). Structural family is $S(y)=S(y')$ (152 cases, ratio $=\chi(x)/\chi(y')$
      proven); 58 sporadic $u$-dependent units remain. (`unit_cases.py`.)
- [x] **Does it feed the program?** *Resolved as a no-go.* The bridge ($W=uR$, two splits) makes the
      LHS $G$-divisible and eliminates $u$, **but** the LHS is a unit-combination of full rotation
      sums $\Rightarrow$ multiple of $G$ $\Rightarrow$ never $\lt G$ (Part C of `small_core_search.py`).
      No Matveev exclusion from this route.
- [x] **Wedges of proper sub-blocks (the redirect).** *Resolved (Gen 3).* The extraction that works
      is the **dual** of P1 — share the *outer* frame (the long runs) instead of the *inner* core —
      giving $S(PMQ)-S(PM'Q)=X^{|P|}Y^{\operatorname{len}Q}(S(M)-S(M'))$ for $\chi(M)=\chi(M')$. The
      surviving object is the run-independent local defect core, not a full-rotation combo. See
      [bounded-defect-lever](bounded-defect-lever.md) (`defect_compose.py` PART A/B).
- [x] **The odd-part lever (how P2/C9 actually win), composed with extraction.** *Resolved (Gen 3).*
      **Yes** — the shared-frame (dual-P1) extraction *does* bound a defect parameter, and it
      **enlarges** the excludable family from a single-letter defect (P2) to any bounded contiguous
      defect *arc* $\beta$, ceiling $\operatorname{sixfree}(S(\beta d)-S(d\beta))$, $o$-independent.
      The 6-free part (not "odd part" — $G\perp 6$ kills $2$- **and** $3$-powers) is the bounded
      quantity. **Correction to this draft's no-go:** the Gen-2 bridge object was declared vacuous for
      never being $\lt G$, but its *6-free part* was never checked — for a bounded-arc word it is
      bounded, so the inner-core/rotation-combo route **does** feed the program after all. The genuine
      limit is the no-go boundary: $\ge 2$ simultaneously growing gaps (`defect_compose.py` PART C).
      Distilled into [bounded-defect-lever](bounded-defect-lever.md).
- [~] **Iterate the extraction.** Can the residual boundary term $\chi(x')S(x)-\chi(x)S(x')$ be
      telescoped to peel a word to a length-bounded core? *Gen 5 partial:* normalized it is
      $\hat S(x)-\hat S(x')$, and each peeled letter $a$ off the front of $x$ contributes a **pure
      unit** $\hat S(x)-\hat S(\text{tail})=\hat S(a)/\chi(\text{tail})=Y/(X^a\chi(\text{tail}))$
      (single letters have $S=1$). So $\hat S(x)=\sum$ of $\operatorname{len}x$ unit terms — peeling
      collapses to a bounded core **iff** $x,x'$ agree outside a bounded arc, which is exactly the
      [bounded-defect-lever](bounded-defect-lever.md) hypothesis. No *new* peeling power here.
- [~] **(Gen 5) Hint settled — does the normalized form sharpen the dual lever's derivation?** The
      reversal-symmetric reading $Q=[\hat S(x)-\hat S(x')]/\chi(u)+[S(y)-S(y')]$ shows the
      bounded-defect wedge is the $S(y)=S(y')$ (or $x=x'$) face of P1. *Gen 6 settled the no-go half:*
      pairing the two-ended move with reversal/transpose ($\hat S$) buys **nothing** for the
      $\ge2$-growing-gap no-go — for the reversal-symmetric $e_1=e_2$ family the reversal is itself a
      rotation and the two-ended core vanishes ([`two_ended_lever.py`](../checks/two_ended_lever.py)
      PART E). The cleaner notation question ($\operatorname{sixfree}(\hat S(\beta d)-\hat S(d\beta))$)
      remains cosmetic. The two-ended generalization is now its own draft,
      [two-ended-extraction](two-ended-extraction.md).

## Iteration log
- 2026-06-08: extracted from `seed.md`. Stated the exact inner-core identity, recorded numeric +
  symbolic evidence, and the corollary that the literal Move 2 is false. General-block proof and
  program-relevance remain open.
- 2026-06-08 (Gen 2): **certified P1 airtight** (`p1_certificate.py`: free-symbol + real-kernel
  $\mathbb{Z}[X,Y]$ over 9 block-length signatures + symbolic letters). Built the **$G$-divisibility
  bridge** ($W=uR$, two splits; `g_divisibility_bridge.py`, 17952 instances): $G\mid\text{LHS}$ and
  $u$ eliminated beyond its $\chi$-signature — *real*. **Corrected** the 210-unit-case claim
  (`unit_cases.py`): structural family is $S(y)=S(y')$, ratio $\chi(x)/\chi(y')$, not
  $\{x=x'\}\cup\{y=y'\}$. **Found the make-or-break no-go** (`small_core_search.py`): the bridge
  object is a multiple of $G$, never sub-$G$, so no Matveev ceiling — distilled into
  `rotation-combo-floor.md`. Re-rated promise high→medium.
- 2026-06-08 (Gen 3): **the no-go was over-stated.** "Never $\lt G$" is true but is *not* the
  exclusion criterion (exclusion = 6-free part bounded independent of $o$). The extraction that bounds
  a defect is the **dual** of P1 (share the outer runs, vary the inner block); it *does* feed the
  program and **enlarges** the family to bounded contiguous defect arcs. Resolved the two live
  redirect questions; spun the result into [bounded-defect-lever](bounded-defect-lever.md)
  (`odd_part_lever.py`, `defect_compose.py`, both exit 0).
- 2026-06-08 (Gen 5): **chased the user's hint** — divide P1 by $\chi(x)\chi(x')\chi(u)$ and reassemble
  in the suffix-weighted sum $\hat S=S/\chi$. *Checked* ([`p1_hint_reduction.py`](../checks/p1_hint_reduction.py),
  exit 0): two exact $\mathbb{Z}[X,Y]$ closed forms (A: $[\hat S(xu)-\hat S(x'u)]+[S(y)-S(y')]$; B:
  $[\hat S(x)-\hat S(x')]+[S(uy)-S(uy')]$); the suffix cocycle (549 inst.); the reversal formula
  $\hat S(w)=\sum X^{-e^R_j}Y^j$ (120 words); and the $u$-dependence/candidate search. **Findings:**
  (1) the manipulation is a **clean re-expression** that exposes P1 as a **reversal-symmetric pair of
  dual-P1 (shared-frame) extractions** — prefix-share $u$ on the $y$-side, suffix-share on the
  $x$-side — and normalizes the boundary term to $\hat S(x)-\hat S(x')$. (2) It is **not** a new
  $u$-free reduction: $Q$ depends on $u$ via $\chi(u)$; generically (PART C2b: $S(y)\ne S(y')$) **no**
  $u$-free target is a unit-ratio for all $u$; the obstruction is exactly $\chi(u)=1$ (= old $\chi(xuy)=1$).
  A genuine $u$-free shortening $xuy\mapsto x$ exists **only** in the known degenerate $S(y)=S(y')$ unit
  family. Promise unchanged (medium) — sharpens the bridge/unification, opens no new lever.
- 2026-06-08 (Gen 6): **generalized the two-ended (reversal-symmetric) move** and ran the headline
  make-or-break against the $\ge2$-growing-gap no-go; spun the result into
  [two-ended-extraction](two-ended-extraction.md). Settled the Gen-5 transpose/no-go sub-question here
  (reversal/$\hat S$ pairing is nil for the no-go — `two_ended_lever.py` PART E). No change to P1 itself.
