# bounded-defect-lever

Promoted from the incubator idea [`ideas/cocycle-combinatorics`](../../ideas/cocycle-combinatorics/RATIONALE.md)
(principle **[P3]**, draft [`bounded-defect-lever.md`](../../ideas/cocycle-combinatorics/drafts/bounded-defect-lever.md)).
Sibling of [`cocycle-combine`](../cocycle-combine/RATIONALE.md); same kernel
([`lib/cocycle.py`](../cocycle-combine/lib/cocycle.py)) and structural theory
([`structure/structure.md`](../cocycle-combine/structure/structure.md), esp. P2/C9, C8 Plücker, thread 8).

## Idea

On a genuine Syracuse cycle with gap word $W$ (length $o$, gap-sum $E$), the shift-gcd
$G:=\gcd_{0\le j\lt o}S^{(j)}(W)=|2^E-3^o|=|D|$ is **odd** ($G\perp 6$). Take a cyclic word over a
uniform background letter $d$ whose **non-background letters all fit inside a single bounded
contiguous arc $\beta$**, the complementary arc being one long run $d^{L}$ (so $o$ grows only by
enlarging $L$). The two adjacent rotations that slide $\beta$ by one step through the run differ by a
**rotation-pair wedge** of $W$:
$$S(d^{k}\beta d^{L-k}) - S(d^{k+1}\beta d^{L-k-1}) \;=\; X^{kd}\,Y^{\,L-k-1}\,\bigl(S(\beta d)-S(d\beta)\bigr).$$
Both terms are rotations of $W$, so $G\mid$ wedge; and since $G\perp 6$ the unit prefactor
$X^{kd}Y^{L-k-1}$ drops, leaving
$$\boxed{\,G \;\le\; \operatorname{sixfree}\!\bigl(S(\beta d)-S(d\beta)\bigr)\,}$$
where $\operatorname{sixfree}(n)$ strips every factor of $2$ and $3$. **The right-hand side depends
only on the bounded arc $\beta$ and the background $d$ — it is independent of the run length $L$,
hence of $o$.** With the transcendence lower bound $|2^E-3^o|\gtrsim 2.56^{\,o}$ (Ellison/Matveev,
via `cycle-literature`) this caps $o$: only finitely many words in the family can be genuine cycles.

The engine is **shared-frame extraction** — for $\chi(M)=\chi(M')$ (equal letter-sum **and** length)
the cocycle gives the exact $\mathbb{Z}[X,Y]$ identity
$$S(P\,M\,Q)-S(P\,M'\,Q)\;=\;X^{|P|}Y^{\operatorname{len}Q}\,\bigl(S(M)-S(M')\bigr),$$
so the shared outer frame $P,Q$ (the long runs) extracts as the **unit** $X^{|P|}Y^{\operatorname{len}Q}$,
leaving the run-independent local core $S(M)-S(M')$. Taking $M=\beta d$, $M'=d\beta$ (a permutation,
hence $\chi$-balanced) gives the lever's wedge. This is **dual to** the inner-core extraction [P1]:
P1 shares the *inner* core and varies the outer blocks; here we share the *outer* frame and vary the
*inner* defect block — which is exactly the direction that bounds a defect.

## Why it might work

- **It is the right axis.** Exclusion never needed a core $\lt G$ (the rotation-combination floor [P2]
  shows any unit-combination of full rotation sums is $\ge G$). It needs the **6-free part** of a
  rotation-sum wedge bounded by a constant independent of $o$ — which this lever delivers exactly.
- **It is a clean, certified enlargement of a known win.** $\beta$ a single letter recovers
  structure.md **P2/C9** exactly (single-defect circuit $d^aed^b$, ceiling
  $\operatorname{sixfree}(2^{|e-d|}-1)$). A multi-letter arc $\beta$ (e.g. two adjacent defects, or
  $e_1d^ge_2$ with $g$ *fixed*) is a genuine extension still giving a fixed, $o$-independent ceiling.
- **The extraction identity is a proven $\mathbb{Z}[X,Y]$ identity** (not a heuristic), and the
  strongest exclusions are mapped: single-defect $|e-d|\in\{1,2\}$ collapses the ceiling to $1$;
  genuine 2-defect arcs give fixed ceilings $\ge 5$.

## Known prior art / why it isn't obviously dead

- **structure.md P2/C9** (the single-defect circuit ceiling $2^{|e-d|}-1$, independent of run
  multiplicities) is the $|\beta|=1$ special case — this approach generalizes it to bounded arcs.
- **Steiner 1977 / Simons–de Weger** (circuits, bounded $m$-cycles) and the `cycle-literature`
  transcendence lower bound supply the exclusion lever the ceiling feeds into.
- It is **not** subsumed by `cocycle-combine`'s size route: that route was shown (in the incubator)
  to bottom out at the floor $\ge G$; the novelty here is reframing exclusion onto the 6-free axis.
- **Not yet a theorem in general:** the boundary case — $\ge 2$ cyclic gaps growing
  *simultaneously* — is **open** (reduced to a cyclotomic-collapse / Lehmer-flavored question; see
  STATUS). The approach is alive precisely on closing or breaking that reduction.
