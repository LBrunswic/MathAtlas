# Ledger

The orchestrator's living state for [`cocycle-combine`](RATIONALE.md). Two tables:
**TODO** (patterns awaiting a combinator) and **RESULTS** (what combinators found). The
[`/cocycle-combine`](../../.claude/skills/cocycle-combine/SKILL.md) skill is the sole writer here;
combinators write only their `reports/<pattern>.{md,py}` drops and report back.

Pattern IDs (P0…) and definitions live in [`PATTERNS.md`](PATTERNS.md). Keep both files in sync.

Legend — **Status**: `todo` · `running` · `done` · `blocked`. **Success**: `✔` (non-trivial
ceiling, symbolic identity certified, numeric battery clean) · `✗` (no useful compensation
found / core too large) · `∅` (degenerate: $C\equiv0$, the known-hard stratum) · `—` (not run).

---

## TODO table — pattern ⇄ rationale ⇄ priority ⇄ status

| Pattern | One-line rationale (why compensation is expected) | Priority | Status | Assigned |
|---------|----------------------------------------------------|----------|--------|----------|
| P1 single circuit $d^o$ | constant word ⇒ geometric sum ⇒ $S=D/(X^d-Y)$; clean closed form, validates the pipeline | warm-up | done | combinator |
| P2 single-defect circuit $d^aed^b$ | rank-1 perturbation of P1; core should depend on the defect $(e-d)$ only, not on $a,b$ | high | done | combinator |
| P3 two-block periodic $(uv)^q$ | P0 plus an inner-boundary telescoping; two compensations may pin a smaller joint core | high | done | combinator |
| P4 finite-difference in $q$ | $(\sigma_q-X^{|w|})$ annihilates the $q$-recurrence, exposing the exact minimal core | high | done | combinator |
| P9 balanced blocks $u_1\cdots u_q$ ($\operatorname{len},\lvert\cdot\rvert$ fixed) | common diagonal ⇒ $S=\sum_i a^{q-i}b^{i-1}s_i$ with $s_i$ in a $q$-independent finite set; $q{=}2$ already forces $(2^E+3^o)\mid(s_2-s_1)$. Find the block-rotation combination giving a $q$-uniform core | high | done | combinator |
| P10 double-run with defect $x^qy\,z^p$ | generalizes P0 ($p{=}0$) and P2 ($x{=}z{=}(d)$, the only ✔). **Two-stage**: $\Delta_x$ telescopes the $x$-run ($q$-free core, $p$-dependent), $\Delta_z$ telescopes the $z$-run ($p$-free, $q$-dependent); then **combine the two** ($\Delta_x\Delta_z$) to kill both run parameters | high | done | combinator |
| P11 stratum twist / topological cover | reuse one word's certificate $(a,b)$ across the fixed-$(E,o)$ stratum via adjacent transpositions; $\Delta S=Y^{o-i-1}X^{P_{i-1}}(X^{d_{i+1}}-X^{d_i})$, monomial is a unit mod $D$, essential size $2^{\lvert d_i-d_{i+1}\rvert}-1$ (= P2 ceiling). Propagation radius = how far the mod-$D$ residue stays in $(0,\lvert D\rvert)$ | high | done | combinator |
| P8 coprime circuits $d_1^{o_1}d_2^{o_2}$ | both blocks closed-form ⇒ $C$ fully explicit; charts the $C=0$ locus exactly | medium | todo | — |
| P5 palindromic $w=\tilde w$ | reversal functional equation ⇒ candidate extra divisibility on $G$ | medium | todo | — |
| P6 Sturmian/balanced | structured rotation orbit; nested CF telescoping | medium | todo | — |
| P7 arithmetic-progression gaps | quadratic $e_k$; twisted second difference may kill Gaussian growth | low | todo | — |

## RESULTS table — pattern ⇄ Z-linear combination ⇄ core ⇄ bound ⇄ verified ⇄ success

| Pattern | Z-linear combination $\sum_j c_j S^{(j)}$ | Core $C$ | gcd bound $G\le$ | Symbolic id | Numeric battery | Report | Success |
|---------|-------------------------------------------|----------|------------------|-------------|-----------------|--------|---------|
| P0 (prior) | $S^{0}-S^{|w|}=X^{(q-1)|w|}C$ | $C(w,w')=D(w)S(w')-D(w')S(w)$ | $|C(w,w')|$, $q$-free | ✓ (periodic-words.md) | ✓ ($q\le6$) | [periodic-words.md](../cycle-gcd/periodic-words.md) | ✔ |
| P1 circuit $d^o$ | (none) all rotations equal; $(X^d-Y)S=D$ | $C=S(d^o)=D/(X^d-Y)$ | $=G$ (equality) | ✓ ($d{\le}5,o{\le}6$) | ✓ (48) | [P1.md](reports/P1.md) | ∅ |
| P2 single-defect $d^aed^b$ | $S^{(o-2)}-S^{(o-1)}$ (last adjacent rotation pair) | $X^{(o-1)d}(X^{e-d}-1)$; odd part $2^{\lvert e-d\rvert}-1$ | $2^{\lvert e-d\rvert}-1$, **indep. of $a,b$** | ✓ | ✓ (1512) + 864 indep. | [P2.md](reports/P2.md) | ✔ |
| P3 two-block $(uv)^q$ | every rotation factors $S^{(j)}=S(A_i)\cdot\mathrm{geo}_q$, $A=uv$; common $\mathrm{geo}_q=D(A^q)/D(A)$ blocks any $q$-free single-word combo. Best is $q{=}1$: $S(uv)-S(vu)$ | $C(u,v)=D(u)S(v)-D(v)S(u)$ = P0 core (no smaller joint core pinned) | $\lvert C(u,v)\rvert$ at $q{=}1$ only; $(uv)^q$ imprimitive (not a cycle) for $q\ge2$ | ✓ (obstruction) | ✓ ($q{=}1$ clean; 24 documented $q\ge2$ non-divisions, expected) | [P3.md](reports/P3.md) | ✗ |
| P4 finite-diff in $q$ ($w^qw'$) | $(\sigma_q-X^{\lvert w\rvert})$ gives $Y^{(q-1)n+n'}S(w)$ — **invalid** (mixed-length, $Y$-power, not $G$-divisible). Only $G$-valid extraction is P0's within-word $S^0-S^n$ | $C(w,w')=D(w)S(w')-D(w')S(w)$ = P0 core exactly (no sharpening) | $\lvert C(w,w')\rvert$ (reproduces P0; P4 adds no bound of its own) | ✓ (recurrence, $\sigma$-collapse, 2nd-order annihilator, exact closed form) | ✓ ($\sigma$-combo $G$-divisible 1/24 of $G{>}1$; P0 core clean all instances, $q{=}2..6$) | [P4.md](reports/P4.md) | ✗ |

| P9 balanced blocks $u_1\cdots u_q$ | $q{=}2$: $S(u_1u_2)-S(u_2u_1)$; general $q$: any $\sum_k g_k S(R^kw)$, core $=g\circledast c$ (circulant, generator $c_m=a^{q-1-m}b^m$) | $q{=}2$: $(a-b)(s_1-s_2)$, $q$-free, $X$-deg $\le 2E-1$; $q\ge3$: $X$-deg $\ge E(q-1)$, grows with $q$ | $q{=}2$ only: $(2^E+3^o)\mid(s_2-s_1)$ ($\lvert D(u)\rvert{=}\lvert a-b\rvert$ cancels from $G{=}\lvert D(u)\rvert(2^E+3^o)$) | ✓ (circulant obstruction; $c(t)(bt-a)=b^q-a^q$ $q{\le}7$; min $X$-deg $=q-1$ $q{=}2,3,4$; $q{=}2$ core abstract) | ✓ ($q{=}2$: 82 pairs; gen-$q$: 12 words $q{=}2..5$; escape search 0 escapes up to $(5,9)$) | [P9.md](reports/P9.md) | ✗ |

| P10 double-run defect $x^qy\,z^p$ | (i) $\Delta_x{=}S(w){-}S(R^{|x|}w){=}X^{(q-1)E_x}C_x(p)$, $C_x(p){=}C(x,yz^p)$; (ii) $\Delta_z{=}X^{(p-1)E_z}C_z(q)$; the two cores split into geometric modes but no single-word combo kills both | $C_x(p)=\frac1{D(z)}\!\big(X^{E_y}C(x,z)X^{pE_z}-N\,Y^{po_z}\big)$, $C(x,z){=}D(x)S(z){-}D(z)S(x)$; $X$-exp $E_y{+}pE_z$ (strippable) but $Y$-exp $p\,o_z$ (3-power, **not** strippable) | none for $x\ne z$ off the degenerate locus; on $x{=}z$ reduces to P2 $2^{\lvert e-d\rvert}-1$ | ✓ ($S$, both stages, mode decomposition, obstruction $C(x,z){=}0\Rightarrow N{=}D(x)D(z)(D(y)r{-}s_y)$, P2 reduction) | ✓ ($G\mid\Delta_x$ over 80 instances: 5 triples $\times$ $q,p\in1..4$) | [P10.md](reports/P10.md) | ✗ |

| P11 stratum twist / topological cover | certificate $C(w){=}aD{+}bS(w)$; twist $w{\to}w'$ (adj. transposition), $D(w'){=}D(w)$ ⇒ $C(w'){=}C(w){+}b(S(w'){-}S(w))$, $\Delta S{=}Y^{o-2-i}X^{P_i}(X^{d_{i+1}}{-}X^{d_i})$ | $C(w')\equiv C(w){+}(bu)(X^{d_{i+1}}{-}X^{d_i})\pmod D$, $u$ unit; least-residue $\lvert C\rvert$ spreads $\sim$uniformly over $(0,\lvert D\rvert/2]$; increment odd part $2^{\lvert d_i-d_{i+1}\rvert}-1$ (P2 size) **not** preserved mod $D$ | only vacuous $\lvert D\rvert\le\lvert C\rvert\lt\lvert D\rvert$; the genuine small bound it contains is P2's $2^{\lvert e-d\rvert}-1$ (defect-swap special case). No stratum-wide cover | ✓ (both increment ids; $\gcd(D,6){=}1$; P2 recovery) | ✓ ($\gcd(D,6)$ $E\in[2,17]$; P2 over 36 words; stratum exp. $(5,3),(8,5),(7,4),(10,6),(11,7),(12,7)$) | [P11.md](reports/P11.md) | ✗ |

_(combinator drops append rows here)_

---

## Run log

One line per dispatch: date · pattern · combinator outcome.

- 2026-05-21 · P1 · ∅ — geometric closed form $(X^d-Y)S(d^o)=D$ certified; core $=G$, vacuous ceiling (single-circuit/Steiner stratum). Pipeline validated end-to-end.
- 2026-05-21 · P2 · ✔ — last-adjacent-rotation difference compensates to core $2^{|e-d|}-1$ **independent of $a,b$**; ceiling $|2^E-3^o|\le 2^{|e-d|}-1$. Symbolic id + 1512-instance battery + 864 independent checks all clean.
- 2026-05-21 · P3 · ✗ — certified obstruction: $(uv)^q$ is imprimitive, every rotation carries a common factor $\mathrm{geo}_q=D(A^q)/D(A)$ ($X$-deg $(q-1)|uv|$) that odd $G$ can't strip, so no single-word combination reaches a $q$-free core below the P0 value $C(u,v)$. Verified (script exit 0). The cross-length $q$-free lead it surfaced was handed to P4.
- 2026-05-22 · P11 · ✗ — stratum twist / topological cover. The increment identities are real and certified ($\mathbb{Z}[X,Y]$): adjacent transposition gives $\Delta S=Y^{o-2-i}X^{P_i}(X^{d_{i+1}}-X^{d_i})$, unit-transfer $Y^{o-2-i}X^{P_{i+1}}(X-1)$; $\gcd(2^E-3^o,6)=1$ so the monomial is a unit mod $D$ and the unit-stripped size is $2^{|d_i-d_{i+1}|}-1$ = **the P2 ceiling exactly** (recovered via the defect swap of $d^o$). But the covering claim **fails**: reusing one certificate $b{=}1$ ($C\equiv S(w)\bmod D$) makes $C\ne0$ for every word *except* those with $D\mid S(w)$ — the tautology, not a covering theorem. The uncovered words are precisely the genuine cycle candidates (e.g. at $(E,o){=}(11,7)$, $D{=}{-}139$, the orbit of $(1,1,1,2,1,1,4)$ has all 7 rotations $\equiv0$, $\gcd_j S^{(j)}{=}|D|$). Covered $|C|$ fills $(0,|D|/2]$ (reaches $\ge|D|/4$ every stratum) so $|C|\lt|D|$ is vacuous; a single twist moves the residue by $\sim|D|/3$–$|D|/2$. **Reduction mod $D$ destroys the small polynomial increment** — a unit times a small bracket is a generic residue. P2 wins precisely because it bounds the *integer* $C$ by its $X$-exponent and never reduces mod $D$. Script exit 0.
- 2026-05-22 · P10 · ✗ — double-run with defect $x^qy\,z^p$ (generalizes P0 at $p{=}0$ and P2 at $x{=}z$). The two-stage telescoping works: $\Delta_x$ gives $q$-free core $C_x(p)=C(x,yz^p)$, $\Delta_z$ gives $p$-free $C_z(q)$. Both cores split exactly into geometric modes with $q,p$-free block coefficients: $C_x(p)=\frac1{D(z)}(X^{E_y}C(x,z)X^{pE_z}-N\,Y^{po_z})$ where $C(x,z)=D(x)S(z)-D(z)S(x)$. A $q,p$-free nonzero combination requires $C(x,z)=0$ AND $N=0$ simultaneously — certified that this forces all three blocks onto one shared rational fixed point (imprimitive/single-circuit stratum, $C\equiv0$, vacuous). Off it, $C_x(p)$ carries unremovable $Y^{po_z}$ (3-power) growth odd $G$ can't strip; the kill-the-$Y$-mode trick needs two *different* words ($z^p$ vs $z^{p-1}$), so it isn't a single-word rotation combination. **P2 wins only because $x=z$ merges the two runs ($C(x,z)=0$).** Script exit 0.
- 2026-05-22 · P9 · ✗ — balanced blocks (equal len & gap-sum, free arrangement). Common diagonal ⇒ $S(R^kw)$ is circulant with geometric generator $c_m=a^{q-1-m}b^m$; in $\mathbb{Z}[X,Y][t]/(t^q-1)$, $c(t)(bt-a)=b^q-a^q$ makes $c$ a unit, and its top term $b^{q-1}$ forces every nonzero combination to $X$-deg $\ge E(q-1)$ — grows with $q$ (P3 obstruction in circulant form). Certified. At $q{=}2$ it collapses to the P0 antisymmetry core $(a-b)(s_1-s_2)$: $\lvert D(u)\rvert$ cancels into $G=\lvert D(u)\rvert(2^E+3^o)$ giving $(2^E+3^o)\mid(s_2-s_1)$; escape search up to $(o,E){=}(5,9)$ found 0 distinct pairs evading it, so $q{=}2$ always forces $s_1=s_2$ (collapse to P0). Script exit 0.
- 2026-05-21 · P4 · ✗ — confirms P0, does not sharpen. The proposed $(\sigma_q-X^{|w|})$ annihilator yields $Y^{(q-1)n+n'}S(w)$, which is **not** a valid gcd core (mixes word-lengths, is a growing $Y$-power; $G$-divisible in only 1/24 of $G{>}1$ instances). Exact closed form for $S(w^qw')$ derived but it's a formula, not a ceiling; the sole $G$-valid extraction is P0's within-word difference. Verified (script exit 0).
