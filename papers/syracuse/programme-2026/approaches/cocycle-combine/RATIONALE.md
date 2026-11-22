# Cocycle-Combine

## Idea

A child of [`cycle-gcd`](../cycle-gcd/RATIONALE.md), turning its one successful trick into a
systematic, agentic search.

On a genuine Syracuse cycle with gap word $\tau$ (length $o$, gap-sum $E$), the gcd of the
cyclic rotation sums is *exactly* the cycle denominator,
$$G \;:=\; \gcd_{0\le j\lt o} S^{(j)}(\tau) \;=\; |2^{E}-3^{o}| \;=\; |D|,$$
and $G$ is **odd**. Therefore **any** $\mathbb{Z}[X,Y]$-linear combination of the rotation
sums is divisible by $G$:
$$\Big(\textstyle\sum_j c_j\,S^{(j)}\Big)\Big|_{(2,3)} \;\equiv\; 0 \pmod{G},
\qquad c_j \in \mathbb{Z}[X,Y].$$
If for a structured family of words we can choose the $c_j$ so that the combination
*compensates* — collapses to a **small / parameter-free / explicitly bounded** core integer
$C$ — then $G \mid C$, i.e.
$$|2^{E}-3^{o}| \;\le\; |C| \quad\text{(unless } C=0\text{)},$$
an **a-priori upper bound** on the gcd of exactly the kind `cycle-gcd` needs. Since $|2^E-3^o|$
grows with the word length, each compensation kills all but finitely many words in its family,
*except* on the degenerate locus $C=0$ (shared rational fixed point — the known bounded-circuit
core handled by Steiner / Simons–de Weger).

The prototype is already proved: for $\tau=w^qw'$, the single difference
$S^{0}-S^{|w|} = X^{(q-1)|w|}\,C(w,w')$ telescopes to the $q$-free core
$C(w,w')=D(w)S(w')-D(w')S(w)$ (see [`cycle-gcd/periodic-words.md`](../cycle-gcd/periodic-words.md)).
**Cocycle-combine asks: which other word-patterns admit such a compensating combination, and
how small is the resulting $C$?** Different word structures should permit different
combinations; the prize is either many small ceilings (collectively covering all words) or one
pattern whose ceiling grows slower than $\min_E|2^E-3^o|$.

## Why it might work

1. **The engine is a cocycle.** $S(uv)=Y^{\operatorname{len}v}S(u)+X^{|u|}S(v)$ makes
   rotation-by-a-block a clean shift operator; differences and finite differences of rotations
   telescope, and the telescoped prefactors are *pure powers of $X$* — which $G$ (odd) ignores.
   This is exactly why the $w^qw'$ core is $q$-free.
2. **It is search-shaped.** "Find integer/monomial coefficients $c_j$ killing the high-degree
   terms of $\sum_j c_j S^{(j)}$" is a concrete linear-algebra / Gröbner / lattice problem over
   $\mathbb{Z}[X,Y]$ that a focused agent can attack pattern-by-pattern, and every candidate is
   cheaply falsifiable: expand the polynomial identity, then test $G\mid C$ over a numeric
   battery at $(2,3)$.
3. **The payoff layer already exists.** `cycle-gcd` has shown the gcd phrasing is equivalent to
   a lower bound on $|2^E-3^o|$ (Baker/Matveev territory); a rich catalogue of cheap
   compensations is precisely the elementary substitute we are testing for.

## Known prior art / why it isn't obviously dead

- The single-difference (periodic) case is done and verified ([`periodic-words.md`](../cycle-gcd/periodic-words.md));
  this approach is its generalization to arbitrary combinations and word shapes.
- The $C=0$ stratum is the classical bounded-circuit case (Steiner 1977; Simons–de Weger ≤68) —
  known finite. So the approach only needs to *bound* the complement $C\ne0$, which is where the
  cheap ceiling bites.
- Honest barrier (inherited from `cycle-gcd`): because $G=|D|$ exactly on cycles, no combination
  can do better than re-express a lower bound on $|2^E-3^o|$. The bet is that *structured*
  combinations expose such a bound combinatorially, family by family, more cheaply than
  transcendence theory — and that the catalogue is finite/coverable.

## How the search is run (the agentic loop)

- [`PATTERNS.md`](PATTERNS.md) — the **sheet**: catalogue of candidate word-patterns, each with
  the rationale for *why* a compensating combination should exist and how small its core might be.
- [`LEDGER.md`](LEDGER.md) — the orchestrator's two living tables: the **TODO** table
  (pattern ⇄ rationale ⇄ priority ⇄ status) and the **RESULTS** table
  (pattern ⇄ Z-linear combination ⇄ core $C$ ⇄ gcd bound ⇄ verified? ⇄ success?).
- The [`combinator`](../../.claude/agents/combinator.md) agent — given one pattern, searches for
  the combination, writes + runs a sympy verification script, and files a report.
- The [`/cocycle-combine`](../../.claude/skills/cocycle-combine/SKILL.md) orchestrator skill —
  maintains the tables and dispatches combinators across pending patterns.
- [`lib/cocycle.py`](lib/cocycle.py) — the trusted sympy kernel ($S$, $D$, rotations, the
  cocycle identities, and the symbolic+numeric certifiers every combinator must call).
- `reports/<pattern>.md` + `reports/<pattern>.py` — one combinator drop per pattern.
