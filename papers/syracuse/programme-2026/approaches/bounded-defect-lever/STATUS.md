# Status — bounded-defect-lever

## Current state
active — promoted from `ideas/cocycle-combinatorics` [P3] (2026-06-08); the **positive lever is
proven and certified** (engine + reach + strongest-exclusion atlas); the **$\ge 2$-growing-gap no-go
boundary is reduced-but-open** (a cyclotomic-collapse / Lehmer question). Certificate scripts
currently live in the idea folder — migrating them here is the first housekeeping step.

## Results
- **Shared-frame extraction identity (proven, $\mathbb{Z}[X,Y]$).** For $\chi(M)=\chi(M')$,
  $S(PMQ)-S(PM'Q)=X^{|P|}Y^{\operatorname{len}Q}\,(S(M)-S(M'))$ — the outer frame extracts as a unit.
  The dual of the inner-core extraction [P1]. Certified in
  [`p1_certificate.py`](../../ideas/cocycle-combinatorics/checks/p1_certificate.py) (P1, three ways)
  and [`odd_part_lever.py`](../../ideas/cocycle-combinatorics/checks/odd_part_lever.py) (the dual).
- **The bounded-defect ceiling (proven for one growing run).** A cyclic word over background $d$ with
  all defects in one bounded contiguous arc $\beta$ and a single growing run $d^{L}$ has the
  **$o$-independent** ceiling $G\le\operatorname{sixfree}(S(\beta d)-S(d\beta))$. Verified in
  [`odd_part_lever.py`](../../ideas/cocycle-combinatorics/checks/odd_part_lever.py): the wedge is
  $\ge G$ (a rotation combo) yet its 6-free part is bounded and constant over run lengths; the
  single-defect ceiling is tight ($\max_a G$ hits it).
- **Reach = enlargement of structure.md P2 (proven).** $\beta$ a single letter recovers P2 exactly;
  multi-letter arcs (e.g. $d\,e_1 d^{B} e_2\,d$ via $\beta=e_2 d^2 e_1$) keep a fixed ceiling over
  growing $B$. Verified in
  [`defect_compose.py`](../../ideas/cocycle-combinatorics/checks/defect_compose.py) PART B
  (6-free part constant over runs 2..8).
- **Strongest-exclusion atlas (proven).** Single-defect collapse gate:
  $\operatorname{ceiling}=\operatorname{sixfree}\prod_{k\mid|e-d|}\Phi_k(2)$, collapsing to $1$ iff
  $|e-d|\in\{1,2\}$; genuine 2-defect arcs give fixed $o$-independent ceilings $\ge 5$ (smallest
  $\beta=(2,3),d{=}1\to 5$). Verified in
  [`ceiling_atlas.py`](../../ideas/cocycle-combinatorics/checks/ceiling_atlas.py).
- **The "$\ge G$ is not the test" correction (proven).** Any $\mathbb{Z}[1/6]$-unit combination of
  full rotation sums is divisible by $G$, hence $\ge G$ — but exclusion lives on the **6-free axis**,
  not the size axis ([P2] floor, re-scoped). Certified in
  [`small_core_search.py`](../../ideas/cocycle-combinatorics/checks/small_core_search.py).

## Dead ends
- **Driving the core $\lt G$ directly (closed).** The rotation-combination floor [P2]: a nonzero
  unit-combination of full rotation sums is always $\ge G$; the only sub-$G$ object is $C=0$ (the
  classical Steiner / bounded-circuit locus). So the exclusion *must* come from a bounded 6-free part,
  not from a small core. (`small_core_search.py`.)
- **The literal "balanced swap" Move 2 (false).** $\chi(x')S(xuy)-\chi(x)S(x'uy')\sim S(yx)-S(y'x')$
  fails (obstruction $\chi(xuy)=1$, impossible); the correct output is the inner-core identity [P1].
  (`move_checks.py`.)

## Open questions
- **Close the $\ge 2$-growing-gap no-go.** For a symmetric family $d^a e_1 d^a e_2 d^a$ ($a\to\infty$),
  every nonzero rotation-pair difference carries a **non-cyclotomic** factor (Mahler $\approx 1.5$) of
  degree $2a{+}2$ — verified in
  [`multigap_nogo.py`](../../ideas/cocycle-combinatorics/checks/multigap_nogo.py) (PART C), with
  Plücker C8 the simultaneity backbone (PART D). This **reduces** the no-go to: *no
  $\mathbb{Z}[1/6]$-unit combination of the rotations has an $a$-independent (cyclotomic-collapsed,
  Mahler-1) reduced polynomial.* That reduction is **open** (Lehmer-flavored; structure.md thread 8).
  ⚠ A finite search cannot settle it — Gen-4 found low-$a$ coincidences (3-term combos hit 6-free
  parts $1,11,5$ at $a=2..5$) that vanish by $a=6$, refuting any naive "min diverges" claim.
- **Attack the reduction directly.** (i) Prove every nonzero unit-combo polynomial of $W_a$ has
  reduced degree $\to\infty$ (rotation sums all have degree $\Theta(a)$ — show the family forbids
  cancelling to a fixed remainder); or (ii) make the C8 telescoping precise (cancelling run-1's
  non-cyclotomic factor forces run-2's).
- **Counter-attack (stay honest).** Hunt for a uniform $a$-independent reduced polynomial among
  $\ge 4$-term unit combos / larger monomial prefactors (not exhausted by Gen 4) — a hit would
  **reopen** the multi-defect case and break the lever's generality.
- **Tightness of the multi-letter ceiling** and its growth in $|\beta|$; map all arcs $\beta$ with
  ceiling $\le 7$ (the Bang–Zsygmondy / cyclotomic-collapse gate).

## Next step under consideration
Migrate the five load-bearing certificate scripts (`odd_part_lever.py`, `defect_compose.py`,
`multigap_nogo.py`, `ceiling_atlas.py`, plus the [P1] `p1_certificate.py`) into this folder so the
approach is self-contained, then attack the reduction: prove reduced-degree-$\to\infty$ for unit
combinations of the symmetric $\ge 2$-growing-gap family (option (i) above), the cleanest route to
closing the no-go boundary.
