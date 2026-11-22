# The bounded-defect lever (shared-frame extraction + the 6-free part)

**Promise:** high — this is the *positive* counterpart to the two Gen-2 no-goes. It is the precise
mechanism by which structure.md's P2/C9 beat the size barrier, recast as a move on words, and it
**enlarges** the excludable family from a single-letter defect to any bounded contiguous defect
*arc*. It also **corrects** the framing of the [P2] rotation-combination floor: exclusion needs a
*6-free part bounded independent of $o$*, **not** a core $\lt G$.
**Status:** principle — engine + reach **proven**; the **positive lever is promotion-ready** (a clean,
verified arc-enlargement of structure.md P2). The **no-go boundary is NOT proven** — Gen 4 sharpened it
to a clean reduction (uniform $a$-independent / cyclotomic-collapsed reduced polynomial) and **corrected**
Gen 3's "clean divergence" (low-$a$ coincidences exist; even 3-term unit combos hit 6-free part $1,11,5$);
it reduces to an open cyclotomic-collapse / Lehmer question.
**Last iterated:** 2026-06-08 (Gen 4)

> **L1·8 pointer (2026-06-09, `drafts/lit-homotopical-completion.md`):** this lever is the *rewriting form*
> of Guiraud–Malbos–Mimram completion-with-expansion. The run-sliding move telescopes to
> $S(\beta d^L)-S(d^L\beta)=S(d^L)\,C(\beta,d)$ with completion coefficient $S(d^L)=(X^{Ld}-Y^L)/(X^d-Y)$;
> the infinite step-family is generated mod 6-units by the **single fixed weight-2 core** $C(\beta,d)$ —
> the analog of Kapur–Narendran's $stsst^k=ts^{k+1}ts$ collapsing onto the quasicenter generator $a=st$.
> The lever's existence criterion is the paper's **quasicenter heuristic** (one growing run $=$ the
> quasicenter; bounded defect $\beta$); the $\ge2$-gap no-go $=$ "no single quasicenter run encloses the
> defects" $=$ weight-growth $\omega\to\infty$. **No new lever — but the criterion + the
> completion-terminates-in-one-cell packaging are the gain.** Verified `checks/lit_homotopical_completion.py` (14/14).

## The principle (one crisp claim)

Let $W$ be a cyclic gap word over a uniform background letter $d$, whose **non-background letters all
fit inside a single contiguous arc $\beta$** of bounded length, the complementary arc being a uniform
run $d^{L}$ (so $o$ grows only by enlarging $L$). Then the two adjacent rotations that slide $\beta$
by one step through the run differ by
$$S(d^{k}\beta d^{L-k}) - S(d^{k+1}\beta d^{L-k-1}) \;=\; X^{kd}\,Y^{\,L-k-1}\,\bigl(S(\beta d)-S(d\beta)\bigr),$$
a **rotation-pair wedge** of $W$. Both terms are rotations of $W$, so $G\mid$ wedge; and since
$G\perp 6$, the unit prefactor $X^{kd}Y^{L-k-1}$ drops, leaving
$$\boxed{\,G \;\le\; \operatorname{sixfree}\!\bigl(S(\beta d)-S(d\beta)\bigr)\,}$$
where $\operatorname{sixfree}(n)$ strips every factor of $2$ and $3$. **The right-hand side depends
only on the bounded arc $\beta$ and the background $d$ — it is independent of the run length $L$,
hence of $o$.** With Ellison's $|2^E-3^o|\gtrsim 2.56^{\,o}$ this caps $o$: only finitely many words
in the family can be genuine cycles.

- $\beta$ a single letter $e$ recovers structure.md **P2** exactly: $S(ed)-S(de)=X^e-X^d$, ceiling
  $\operatorname{sixfree}(2^{e}-2^{d})=\operatorname{sixfree}(2^{|e-d|}-1)$.
- $\beta$ a multi-letter block (e.g. two **adjacent** defects $e_1e_2$, or $e_1d^ge_2$ with $g$
  *fixed*) is the **enlargement**: still a fixed ceiling, $o$-independent.

## The engine — shared-frame extraction (the dual of P1)

For $\chi(M)=\chi(M')$ (equal letter-sum **and** length, e.g. $M'$ a permutation of $M$ — the
rationale's balance condition), the cocycle gives the **exact** identity
$$S(P\,M\,Q)-S(P\,M'\,Q)\;=\;X^{|P|}Y^{\operatorname{len}Q}\,\bigl(S(M)-S(M')\bigr).$$
The shared **outer frame** $P,Q$ (here the long uniform runs) extracts as the **unit**
$X^{|P|}Y^{\operatorname{len}Q}$, leaving the run-independent local core $S(M)-S(M')$. Taking
$M=\beta d$, $M'=d\beta$ (a permutation, so $\chi$-balanced) gives the lever's wedge.

This is **dual to [P1]**: P1 shares the *inner* core $u$ (extracted via $\chi(u)$) and varies the
outer blocks; the shared-frame extraction shares the *outer* frame and varies the inner block. To
**bound a defect** you must extract the long runs and keep the defect as the residual — that is the
shared-frame (dual) direction. (When $|M|\ne|M'|$ the identity carries an extra term
$X^{|P|}(X^{|M|}-X^{|M'|})S(Q)$; it vanishes precisely under the balance condition.)

## The correction to the [P2] floor (important)

The [rotation-combo-floor](rotation-combo-floor.md) draft proved any unit-combination of full
rotation sums is $\ge G$ and concluded "never a sub-$G$ core, only $C=0$." That divisibility is
**true**, but the conclusion "hence no exclusion" is **wrong**: the lever's wedge *is* exactly such a
rotation combination, so $|\text{wedge}|\ge G$ — yet it still excludes, because its **6-free part is
bounded independent of $o$**. Exclusion never needed a core $\lt G$; it needs
$\operatorname{sixfree}(\text{core})$ capped by a constant. The floor describes the *size* axis; the
lever lives on the *6-free* axis. (This also reopens the Gen-2 inner-core "no-go": that bridge object
was declared vacuous for never being $\lt G$, but its 6-free part was never examined — for a
bounded-arc word it is bounded, and it *does* feed the program.)

## The reach, and the no-go boundary

**Reach (enlargement).** Excludable iff the defect support fits one **bounded** contiguous arc with a
single growing background run. Verified: `defect_compose.py` PART B — for $\beta\in\{(3,4),(4,3,4),
(4,1,1,3)\}$ the $\beta$-wedge 6-free part is **constant** (65, 1103, 127) over run lengths 2..8. In
particular $d\,e_1d^{B}e_2\,d$ with $B\to\infty$ **is** excludable: take $\beta=e_2 d^{2}e_1$ (the
short-gap side, length 4), run $=d^{B}$.

**No-go boundary (Gen 4: sharpened to a clean reduction + corrected; still open).** If $\ge 2$ cyclic
gaps between defects grow simultaneously (e.g. the symmetric $d^ae_1d^ae_2d^a$), no bounded arc encloses
all defects. Gen 4 (`multigap_nogo.py`) establishes:

- **Framing correction (PART A).** For the symmetric family $\gcd_j S^{(j)}(W_a)=1$ for **every** $a$ (the
  words are not cycles). Since $\mathbb{Z}[1/6]$ is a PID, by Bézout some $\mathbb{Z}[1/6]$-**linear**
  combination of the rotations equals a $6$-unit (6-free part $1$). So the no-go is **false** if read as
  "no $\mathbb{Z}[1/6]$-linear combo has bounded 6-free part." The exclusion lever uses **unit (monomial)**
  coefficients $\pm X^aY^b$ and — to exclude an *infinite* family — a **uniform** scheme: a *fixed* reduced
  polynomial $f$ with $\text{combo}_a=(\text{monomial}_a)\cdot f$ for all $a$, so
  $\operatorname{sixfree}(\text{combo}_a)=\operatorname{sixfree}(f(2,3))=$ const. That is what the no-go
  must deny.
- **Corrected evidence (PART B).** Gen 3's "clean divergence" was an artifact of a small coefficient box.
  With box $\pm2^c3^d$ ($c,d\le2$): 2-term min 6-free part grows ($23,23,1537,3979,10145,26851,73385$ for
  $a=2..8$), but **3-term unit combos hit low-$a$ coincidences** — 6-free part $1,23,11,5$ at $a=2..5$ —
  that **vanish by $a=6$** ($3841,11651,19577$) and use **non-uniform** recipes (different rotation
  indices/coeffs per $a$). So the finite search finds **no uniform bounded scheme** but also **does not
  prove** the no-go.
- **The clean reduction (PART C — the win).** Every nonzero rotation-pair difference factors as
  $X^p(X-1)\,P_a(X,Y)$ with $P_a$ **non-cyclotomic** (Mahler$(P_a|_{Y=1})\approx1.5$, bounded away from $1$)
  of total degree $2a+2$ **growing**; the *minimum* non-cyclotomic degree over all differences also grows.
  Contrast the bounded-arc wedge, whose reduced core $S(\beta d)-S(d\beta)$ is **$a$-independent**. Hence
  the no-go **reduces** to: *no unit-combo of the $\ge2$-growing family has an $a$-independent
  (Mahler-$1$ / cyclotomic-collapsed) reduced polynomial.* This is a cyclotomic-collapse / Lehmer-flavored
  statement (structure.md thread 8) — **open**, not closed here.
- **Plücker backbone (PART D).** C8 $D(u)C(v,w)+D(v)C(w,u)+D(w)C(u,v)=0$ verified on arc triples of the
  family: the three arc-cores are $R$-linearly tied, so small cores cannot proliferate — the structural
  reason $\ge2$ growing gaps resist simultaneous taming. (The $Y=1$ Mahler screen is too coarse to read
  "tameable" cleanly off C8 — recorded honestly.)

## Working notes

- The win is precisely the structure.md flagship reading: bounded-arc cores factor as (monomial in
  $X,Y$)$\times$(fixed polynomial), so the value at $(2,3)$ is (unit)$\times$(constant) and the
  6-free part is bounded. Multi-gap words have a non-cyclotomic factor of growing degree (Mahler
  $\gt 1$), so the 6-free part is $\approx 2^{\Theta(\text{2nd run})}$.
- A single difference of rotation sums can extract exactly **one** shared frame (one prefix + one
  suffix = one outer run). With $\ge 2$ growing runs, the second run is trapped *inside* the wedge
  and contributes the non-cyclotomic factor. This is the structural heart of the no-go.
- **(Gen 4) The precise notion of exclusion = a UNIFORM reduced polynomial.** Because $\gcd_jS^{(j)}=1$
  for non-cycle family members, "bounded 6-free part of *some* combo" is achievable trivially (Bézout) and
  is **not** the exclusion criterion. The lever works because the wedge's reduced polynomial is literally
  *$a$-independent*; the no-go is the assertion that no unit-combo of the $\ge2$-growing family admits an
  $a$-independent reduced polynomial. Equivalently (Kronecker + Bang–Zsygmondy): the combo's reduced
  polynomial must be a monomial times cyclotomics whose indices collapse to $\{1,2,6\}$.
- **(Gen 4) Strongest exclusions — the cyclotomic-collapse atlas** (`ceiling_atlas.py`). Single-defect
  $d^aed^b$: ceiling $=\operatorname{sixfree}(2^{|e-d|}-1)=\operatorname{sixfree}\bigl(\prod_{k\mid|e-d|}\Phi_k(2)\bigr)$,
  which **collapses to $1$ iff $|e-d|\in\{1,2\}$** (the only $n$ whose divisors lie in $\{1,2,6\}$, where
  $\Phi_k(2)\in\{1,3\}$ is 6-smooth) — the **strongest possible** exclusion ($G\le1$: only the trivial
  circuit). For $|e-d|\notin\{1,2\}$ Bang–Zsygmondy drops a primitive prime ($n{=}3\to7$, $4\to5$, $5\to31$,
  $6\to7$, …). Genuine **2-defect** bounded arcs $e_1d^ge_2$ ($g$ fixed) never collapse to $1$: their local
  core carries a *fixed* irreducible non-cyclotomic factor, smallest ceiling $5$ ($\beta=(2,3),d=1$), then
  $7,11,13,17,23,\dots$ — still $o$-independent (verified run-length-invariant), hence valid but weaker.

## Open questions

> **Structural source of the $o$-independence (L1·5, Suciu–Wang — see
> [`lit-suciu-wang.md`](lit-suciu-wang.md)).** The reduced core $C(\beta,d)=S(\beta d)-S(d\beta)$ is a
> **fixed weight-2 cup product** $[\beta]\cup[d]$ in the holonomy/Magnus grading (combinatorial degree,
> *not* word length: Labute Thm 7.2; Suciu–Wang Cor 8.2/Thm 8.3). Sliding $\beta$ through the run $d^L$
> keeps the weight fixed (verified $L$-independent), which is *why* the ceiling is $o$-independent; the
> $\ge2$-growing-gap no-go is the statement that the trapped configuration's **weight grows** with $o$.
> The cup product itself is only the linearization $\partial_XC\rvert_{X=Y=1}=E_\beta-d\,o_\beta$ — the
> exclusion-carrying part is the $\chi$-twist (off-ring). No new lever was constructed; the gain is the
> named weight bridge.

- [ ] **Close the no-go rigorously (now a clean reduction — OPEN).** Gen 4 reduced it to: *no unit-combo
      of the $\ge2$-growing family has an $a$-independent (Mahler-$1$ / cyclotomic-collapsed) reduced
      polynomial.* Two concrete sub-attacks: **(i)** prove every nonzero unit-combo polynomial of $W_a$ has
      reduced degree $\to\infty$ in $a$ (the rotation sums all have degree $\Theta(a)$ and the family
      structure should forbid cancelling to a fixed remainder); **(ii)** make C8 telescoping precise —
      show that cancelling the run-1 non-cyclotomic factor via Plücker forces the run-2 factor to appear,
      so the two growing runs cannot be cyclotomic-ized at once. *Caveat established by Gen 4:* a pure
      "min-6-free-grows" finite search will **not** close it — low-$a$ coincidences (3-term combos at
      $6$-free part $1,11,5$) are real; the statement is genuinely about uniform/asymptotic structure.
- [ ] **Is the reduction's Lehmer-flavored statement even true, or is there a uniform counterexample?**
      Search for an $a$-independent reduced polynomial among unit-combos using $\ge4$ terms or larger
      monomial prefactors (the dangerous direction Gen 4 did not exhaust). A genuine uniform bounded
      scheme would **reopen the multi-defect case** — the single most important thing to settle.
- [x] **Which arcs give a *small* ceiling?** *Done (Gen 4, `ceiling_atlas.py`).* Single-defect collapses
      to ceiling $1$ iff $|e-d|\in\{1,2\}$ (strongest exclusion); genuine 2-defect arcs give fixed
      $o$-independent ceilings $\ge5$ ($\beta=(2,3),d=1\to5$; then $7,11,13,17,23$). Cyclotomic-collapse
      gate confirmed: ceiling $=\operatorname{sixfree}(\prod_{k\mid|e-d|}\Phi_k(2))$ for single defects.
- [ ] **Exact ceiling and tightness for multi-letter arcs.** Single-letter ceiling is attained
      (`odd_part_lever.py` PART B). Is the genuine 2-defect ceiling also attained, and what is its growth
      in $|\beta|$ and in the internal gap $g$?
- [ ] **Two short gaps, both bounded.** $e_1 d^{g_1} e_2 d^{g_2} e_3 \dots$ with all $g_i$ fixed is a
      single bounded arc — covered. Confirm the ceiling is computable as $\operatorname{sixfree}$ of
      one local core and tabulate for a few multi-defect bounded arcs.

## Iteration log
- 2026-06-08 (Gen 3): distilled from `odd_part_lever.py` + `defect_compose.py`. Proved the
  shared-frame extraction identity (dual of P1), reconstructed the P2/C9 6-free lever, **corrected**
  the [P2]-floor framing (exclusion = bounded 6-free part, not sub-$G$), established the reach
  (bounded contiguous arc + one long run $\Rightarrow$ $o$-independent ceiling) and the no-go
  boundary ($\ge 2$ growing gaps $\Rightarrow$ 6-free part diverges, non-cyclotomic cofactor).
- 2026-06-08 (Gen 4): **no-go sharpened + corrected; secondary atlas done.** Checked: `multigap_nogo.py`
  — (A) framing correction ($\gcd_jS^{(j)}=1$, so a *linear*-combo no-go is false; exclusion needs a
  unit/**uniform** scheme); (B) extended search (k=2,3 unit combos, $a=2..8$) **corrects** Gen 3's "clean
  divergence" — 3-term combos hit low-$a$ 6-free coincidences $1,11,5$ that vanish by $a=6$, via
  non-uniform recipes; (C) the **clean reduction** — every rotation difference $=X^p(X-1)P_a$, $P_a$
  non-cyclotomic (Mahler $\approx1.5$), $\deg=2a+2$ growing, while the bounded-arc reduced core is
  $a$-independent; so the no-go reduces to "no unit-combo has an $a$-independent reduced polynomial"
  (cyclotomic-collapse / Lehmer, **open**); (D) Plücker C8 verified on arc triples. `ceiling_atlas.py` —
  strongest exclusion is single-defect $|e-d|\in\{1,2\}$ (ceiling $1$, full); genuine 2-defect arcs give
  fixed $o$-independent ceilings $\ge5$. **Verdict:** positive lever promotion-ready; no-go boundary
  reduced-but-open (Gen 3's "established by strong evidence" was over-stated — low-$a$ coincidences exist).
