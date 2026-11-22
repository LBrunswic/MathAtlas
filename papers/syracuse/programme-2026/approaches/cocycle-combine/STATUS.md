# Status — cocycle-combine

## Current state

Active — infrastructure scaffolded, sympy kernel green, and the agentic loop (patterns sheet →
orchestrator → combinator → ledger) **validated end-to-end** on P1 (pipeline check) and P2 (first
new ceiling). Inherits the proved prototype P0 (eventually-periodic $w^qw'$) from
[`cycle-gcd/periodic-words.md`](../cycle-gcd/periodic-words.md). Tier-1 P2,P3,P4,P9,P10,P11 all run
(P2 the lone ✔; P3/P4/P9/P10 ✗ via the geometric/imprimitivity obstruction; P11 ✗ via the new
mod-$D$ reduction barrier). Two sharpened lessons now bound the search: a ✔ must (i) avoid a
geometric mode that grows with a family parameter, and (ii) bound the **integer** core by its
$X$-exponent without ever reducing mod $D$ — exactly what P2 does. Next: Tier-2 patterns (P8
closed-form, P5 palindromic, …) via `/cocycle-combine --next`.

The live tables are in [`LEDGER.md`](LEDGER.md); the trusted machinery in
[`lib/cocycle.py`](lib/cocycle.py).

## Results

- **Structural theory written + certified.** [`structure/structure.md`](structure/structure.md)
  (owned by the [`cocycle-structure`](../../.claude/skills/cocycle-structure/SKILL.md) skill;
  certified by [`verify_structure.py`](structure/verify_structure.py), exits 0). The word-cocycle is
  a **transfer-matrix monoid homomorphism** $M(w)=\prod_k\!\big(\begin{smallmatrix}Y&0\\1&X^{d_k}\end{smallmatrix}\big)=\big(\begin{smallmatrix}Y^o&0\\S&X^E\end{smallmatrix}\big)$;
  **rotation = conjugation** (cyclic words = conjugacy classes); $\sigma=S/Y^o$ is a genuine crossed
  homomorphism and the **coboundary of a constant is $w\mapsto c\,D(w)$** — so $S$ is defined mod
  $\langle D\rangle$, which is *why* odd $G$ ignores prefactors. The core is a **wedge**
  $C(u,v)=\det\!\big(\begin{smallmatrix}D(u)&D(v)\\S(u)&S(v)\end{smallmatrix}\big)$ obeying a
  **Plücker/Jacobi relation** $D(u)C(v,w)+D(v)C(w,u)+D(w)C(u,v)=0$ — a free linear relation among
  cores. Organizing axis: **generic $\mathbb{Z}[X,Y]$ algebra vs. exceptional $2$–$3$ arithmetic**
  (only the latter can beat the size barrier). Knowledge base + reading notes + source library under
  [`structure/`](structure/) ([`KNOWLEDGE_MAP.md`](structure/KNOWLEDGE_MAP.md)).
- **Kernel built + verified.** [`lib/cocycle.py`](lib/cocycle.py): $S$, $D$, rotations, the
  concatenation cocycle and antisymmetry checks, prototype core $C(w,w')$, and the two certifiers
  `verify_symbolic_identity` (polynomial identity in $\mathbb{Z}[X,Y]$) and
  `verify_divisibility_battery` ($G\mid C$ over a numeric battery at $(2,3)$). Self-test reproduces
  the $1\to1$ and $-5\to-7$ cycle data and $C((1,2),(3))=-26$.
- **Word algebra $\mathbb{Z}[W]$ + guaranteed-gain simplifier ([`lib/wordalg.py`](lib/wordalg.py), self-test exits 0).**
  Clean three-layer module on the kernel: (1) the monoid algebra `Comb` with the structure maps
  packaged by the transfer rep $M(w)=\big(\begin{smallmatrix}Y^{\mathrm{len}}&0\\S&X^{|w|}\end{smallmatrix}\big)$
  (diagonal = character $\chi$, off-diagonal = $S$, $D=M_{11}-M_{00}$) and the quotient map
  $\pi_w:\mathbb{Z}[W]\to\mathbb{Z}_{2,3}/(1-\chi(w))$; (2) three guaranteed-gain moves on word-differences —
  prefix/suffix strip (exact) and **shared-interior cancel + roll** $S(PBQ)-S(P'BQ')\equiv Y^{\mathrm{len}B+\mathrm{len}Q}X^{-|Q|}(S(QP)-S(Q'P'))\pmod D$
  (residue $=D\,(S(Q)-S(Q'))$), the one genuinely-mod-$D$ move, **guarded to fire only in the seed
  stratum** so its residue stays a multiple of $G$ (P11 discipline: never collapse to a $\mathbb{Z}/D$
  residue — the output is always an honest shorter difference sized by $\mathrm{sixfree}(S)$);
  (3) `greedy_simplify(w)` descends over rotation-pair differences and reports $\mathrm{sixfree}$, $|D|$,
  and the **$\mathrm{sixfree}\lt 3^o$** verdict. Self-test certifies every chain (exact $\mathbb{Z}[X,Y]$ / mod-$D_0$,
  and $G\mid$ core), reproduces the **P2** single-defect ceiling, and exhibits words where the
  interior-cancel is decisive (e.g. $(2,2,2,1,2,1,1)\to$ sixfree $29$).
- **P0 prototype (inherited, proved).** $S^{0}-S^{|w|}=X^{(q-1)|w|}C(w,w')$, $G\mid C(w,w')$,
  $q$-free ceiling. Logged as the seed RESULTS row.
- **P1 circuit $d^o$ (∅, certified).** $(X^d-Y)S(d^o)=D$; all rotations equal so $G=S(d^o)=D/(2^d-3)$
  exactly — core $=G$, ceiling vacuous (the single-circuit/Steiner stratum). Validated the
  pipeline end-to-end. [`reports/P1.md`](reports/P1.md).
- **P2 single-defect circuit $d^aed^b$ (✔, certified — first new ceiling).** The $o$ rotations are
  $\rho_i=d^ied^{o-1-i}$ (defect sliding through all positions); the *last adjacent pair*
  difference kills the $Y$-power, giving
  $$S(\rho_{o-2})-S(\rho_{o-1})=X^{(o-1)d}\bigl(X^{e-d}-1\bigr).$$
  $G$ odd ⇒ $G\mid 2^{|e-d|}-1$, so any single-defect-circuit cycle forces
  $$|2^E-3^o|\le 2^{|e-d|}-1,$$
  a ceiling **independent of the run multiplicities $a,b$** — hence finitely many such cycles per
  defect $(d,e)$. Certified: $\mathbb{Z}[X,Y]$ identity + 1512-instance battery + 864 independent
  checks, all clean; non-vacuous (e.g. word $(1,1,1,4,1,1,1)$: $|D|=1163$ vs bound $7$).
  Degenerate locus $C\equiv0\iff e=d$ (= P1). [`reports/P2.md`](reports/P2.md).
- **P9 balanced blocks $u_1\cdots u_q$ (✗, certified — obstruction + $q{=}2$ collapse).** Blocks of
  equal length $o$ and equal gap-sum $E$, internal arrangement free (generalizes P0's $w^q$). The
  common diagonal $a{=}Y^o,b{=}X^E$ makes $S(R^kw)=\sum_i a^{q-i}b^{i-1}s_i$ ($s_i{=}S(u_i)$), so the
  rotation-sum vector is **circulant** with geometric generator $c_m=a^{q-1-m}b^m$. In
  $\mathbb{Z}[X,Y][t]/(t^q-1)$, $c(t)(bt-a)=b^q-a^q$ makes $c$ a unit whose top term $b^{q-1}$ forces
  **every nonzero combination to $X$-degree $\ge E(q-1)$** — grows with $q$, so no $q$-uniform core
  (the P3 geometric obstruction, in circulant form). At $q{=}2$ it collapses to the P0 antisymmetry
  core $(a-b)(s_1-s_2)$: $|D(u)|{=}|a-b|$ cancels into $G{=}|D(u)|(2^E+3^o)$, giving the ceiling
  $(2^E+3^o)\mid(s_2-s_1)$; an escape search up to $(o,E){=}(5,9)$ found **no** distinct balanced
  pair evading it, so $q{=}2$ always forces $s_1=s_2$ (collapse to P0). Certified (circulant
  obstruction, $c(t)(bt-a)$ identity $q\le7$, min $X$-deg $=q-1$, $q{=}2$ core abstract + 82 real
  pairs); script exit 0. [`reports/P9.md`](reports/P9.md).
- **P10 double-run with defect $x^qy\,z^p$ (✗, certified — obstruction; ✔ only on the $x{=}z$ merge).**
  Run of $x$ ($q\times$), single defect $y$, run of $z$ ($p\times$); generalizes P0 ($p{=}0$, tail
  $w'{=}y$) and P2 ($x{=}z{=}(d)$, $y{=}(e)$ — the only ✔). The user's **two-stage** plan works as
  posed: $\Delta_x$ (one-$x$-block rotation difference) telescopes the $x$-run to the $q$-free core
  $C_x(p)=C(x,yz^p)$; $\Delta_z$ telescopes the $z$-run to the $p$-free $C_z(q)$. The decisive
  finding is that each core **splits exactly into its two geometric growth modes** with $q,p$-free
  block coefficients:
  $$C_x(p)=\tfrac1{D(z)}\bigl(X^{E_y}\,C(x,z)\,X^{pE_z}-N\,Y^{po_z}\bigr),\quad C(x,z)=D(x)S(z)-D(z)S(x).$$
  A $q,p$-free *nonzero* combination would need $C(x,z)=0$ **and** $N=0$ at once; certified that
  $C(x,z)=0\Rightarrow N=D(x)D(z)(D(y)r-s_y)$, so $N=0$ then drives all three blocks onto **one
  shared rational fixed point** (the imprimitive/single-circuit stratum, $C\equiv0$, vacuous). Off
  it, $C_x(p)$ carries an unremovable $Y^{po_z}$ (3-power) factor odd $G$ can't strip; the
  kill-the-$Y$-mode trick only closes by mixing two *different* words ($z^p$ vs $z^{p-1}$), so it is
  not a single-word rotation combination. **P2 succeeds precisely because $x=z$ merges the runs
  into one defect-circuit ($C(x,z)=0$).** Certified ($S$ formula, both stages, mode decomposition,
  obstruction, P2 reduction; $G\mid\Delta_x$ over 80 instances), script exit 0.
  [`reports/P10.md`](reports/P10.md).
- **P11 stratum twist / topological cover (✗, certified — but the increment is real and = P2).** A
  *propagation* idea, not a word-family: reuse one word's certificate $(a,b)$ (with
  $C(w)=aD+bS(w)$, $0\lt|C|\lt|D|$) across the whole fixed-$(E,o)$ stratum (all share one $D$) by
  twisting with adjacent transpositions, since $D(w')=D(w)\Rightarrow C(w')=C(w)+b(S(w')-S(w))$. The
  two increment identities are certified in $\mathbb{Z}[X,Y]$:
  $\Delta S=Y^{o-2-i}X^{P_i}(X^{d_{i+1}}-X^{d_i})$ (transposition; only $P_i$ moves) and
  $Y^{o-2-i}X^{P_{i+1}}(X-1)$ (unit-transfer). Since $\gcd(2^E-3^o,6)=1$ the monomial prefactor is a
  **unit mod $D$**, so the unit-stripped increment size is $2^{|d_i-d_{i+1}|}-1$ — **exactly the P2
  ceiling** (recovered via the defect swap of $d^o$). **But the covering claim fails:** with $b{=}1$
  ($C\equiv S(w)\bmod D$) one certificate makes $C\ne0$ for every word *except* those with
  $D\mid S(w)$ — the tautology, not a theorem; and the uncovered words are *precisely* the genuine
  cycle candidates (e.g. $(11,7)$, $D{=}{-}139$: orbit of $(1,1,1,2,1,1,4)$, all 7 rotations
  $\equiv0$, $\gcd_j S^{(j)}{=}|D|$). The least-residue $|C|$ fills $(0,|D|/2]$ (vacuous), and one
  twist scatters the residue by $\sim|D|/3$–$|D|/2$. Certified, script exit 0.
  [`reports/P11.md`](reports/P11.md).

## Dead ends

- **The geometric/imprimitivity obstruction (P3, P4, P9, P10).** When a family's rotations share a
  common geometric factor that grows with the family parameter, odd $G$ cannot strip it, so no
  single-word combination reaches a parameter-uniform core below the P0 value. P3: $(uv)^q$ carries
  $\mathrm{geo}_q$; P9: the circulant unit $c(t)$, top term $b^{q-1}$ (even non-periodic equal-block
  words inherit it — the "$s_i$ in a fixed finite set" leverage is real but the diagonal weights
  dominate); **P10: a *two-run* word can't telescope both runs at once — killing one leaves the
  other's 3-power ($Y^{po_z}$) growth, and the only escape ($C(x,z)=0$) merges the runs back to P2's
  single defect-circuit.** The parameter-free content lives in *cross-length* extractions (P0/P4) or
  in genuinely *single-defect* words (P2), not in single-word combinations of any family with a
  growing geometric mode.
- **The mod-$D$ reduction barrier (P11).** A small *polynomial* increment is no protection once you
  reduce mod $D$: a unit (any monomial, since $\gcd(D,6){=}1$) times a small bracket is a *generic*
  residue, filling $(0,|D|/2]$. Any "deform a covered word to a neighbour" or local scheme that lives
  **mod $D$** inherits this — the cheap structure is destroyed by reduction, collapsing to the
  tautology "$D\mid S(w)$ iff $w$ is a cycle candidate." The lesson cuts the other way too: P2 (and
  every ✔-hope) must bound the **integer** core via its $X$-exponent and *never* reduce mod $D$.
- _(Honest barrier, inherited from the parent: $G=|D|$ exactly on cycles, so every compensation can
  only re-express a lower bound on $|2^E-3^o|$; the bet is that structured combinations expose it
  cheaply, family by family.)_

## Open questions

- **Which patterns compensate at all?** Run combinators on P1–P8; populate the RESULTS table.
- **Does any core's $X$-exponent stay $<E$ as the family grows?** Only then is the ceiling
  non-vacuous against $|2^E-3^o|\approx2^E$.
- **Can the patterns be made to cover all words?** Every word is some $w^qw'$; is there a
  decomposition rule giving $|C|<f(o)$ with $f$ sub-exponential for *every* word?
- **Map each family's $C=0$ locus** and confirm it sits inside the known bounded-circuit cases.

## Next step under consideration

Validate the pipeline end-to-end on a Tier-0/1 pattern (P1 closed form, then P2 single-defect),
confirm the combinator → ledger flow, then fan out across Tier-1 (P2,P3,P4).
