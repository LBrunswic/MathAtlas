# Survey — what is known about cycles of the 3x+1 map

A citation-backed reference shelf. **Statements + provenance, not our own proofs.** Honest
labelling throughout: every cycle result below is *proven*, but most quantitative bounds are
*conditional on the numerically verified range* $N_0$ (currently $\approx 2^{71}$), and the
full "no nontrivial cycle" claim remains **open**.

Notation is the project-standard one ([`CHEATSHEET.md`](../../CHEATSHEET.md)): accelerated
odd-to-odd Syracuse map, $o$ odd steps per period, $E$ total halvings per period,
$D := 2^E - 3^o$, weighted sum $S := \sum_{k=0}^{o-1} 2^{e_k} 3^{\,o-1-k}$, smallest cycle
element $N_0$. The literature's $(K, L, m)$ map to ours as $K = o$ (odd steps),
$K + L = E$ (total halvings), $m$ = number of local minima ("circuits") of the cycle.

---

## 0. The closed-form cycle equation (Böhm–Sontacchi)

Setting $a_o = a_0$ in the Diophantine closed form gives the **cycle equation**
$$ (2^E - 3^o)\,a_0 \;=\; S \;=\; \sum_{k=0}^{o-1} 2^{e_k} 3^{\,o-1-k}, \qquad a_0 = \frac{S}{D},\ \ D = 2^E - 3^o. $$
So a cycle exists **iff** $D \mid S$ with the quotient a positive integer $\gt 1$. This is the
representation of **C. Böhm & G. Sontacchi, "On the existence of cycles of given length in
integer sequences like $x_{n+1}=x_n/2$ if $x_n$ even, and $x_{n+1}=3x_n+1$ otherwise,"** Atti
Accad. Naz. Lincei Rend. (8) **64** (1978) 260–264. Tao's "Conjecture 3" (blog, 2011) restates
it: no $k\ge1$ and $0=a_1\lt a_2\lt\cdots\lt a_{k+1}$ with $n\gt1$ and
$(2^{a_{k+1}}-3^k)n = \sum_i 3^{k-i}2^{a_i}$, $2^{a_{k+1}}-3^k$ a *proper* divisor of the RHS.
The **equivalence** "weak Collatz $\iff$ no such divisibility witness" is elementary algebra
(proven); only nonexistence of a witness is conjectural. — This is exactly the equation the
[`cycle-gcd`](../cycle-gcd/STATUS.md) and [`diophantine-distribution`](../diophantine-distribution/STATUS.md)
approaches build on.

---

## 1. The "critical band": is every cycle at $E = \lceil o\log_2 3\rceil$?

**No — $E$ is not forced to the minimal band value $\lceil o\log_2 3\rceil$.** What *is* proven
is stronger: the **ratio** $E/o$ is trapped in a razor-thin sliver immediately above
$\log_2 3 = 1.5849625\ldots$, whose width is set by $1/N_0$.

**The sandwich (Crandall 1978; Eliahou 1993; Sinisalo 2003; Hercher 2023).** From the exact
loop product $2^{E} = \prod_{n\in\text{cycle}}(3 + 1/n)$, the RHS exceeds $3^o$ (lower bound)
and, by AM–GM, is at most $(3+\mu)^o$ with $\mu = \tfrac1o\sum 1/n_i$. Hence
$$ \log_2 3 \;\lt\; \frac{E}{o} \;\le\; \log_2\!\Big(3 + \tfrac{1}{N_0}\Big) \;\approx\; \log_2 3 + \frac{1}{N_0\cdot 3\ln 2}, $$
equivalently $0 \lt E - o\log_2 3 \lt \dfrac{o}{N_0\cdot 3\ln 2}$. This is **Sinisalo (2003)
Lemma 1** verbatim ($\ln3/\ln2 \lt n/k \le \ln(3+1/R)/\ln2$ for smallest element $\ge R$) and
**Hercher (2023) Thm. 16**. So $\lceil o\log_2 3\rceil$ is the **left edge** of the proven
admissible interval; $E$ may sit above it, but only as far as $1/N_0$ permits — and with
$N_0 \gtrsim 2^{71}$ the band is $\sim 10^{-21}$ wide per odd step.

**Continued fractions pin the admissible $(E,o)$.** Because $E/o$ is a reduced fraction in an
interval of width $\sim 1/N_0$ above $\log_2 3$, and the smallest-denominator fraction in any
interval is governed by the continued-fraction / Stern–Brocot structure (Hercher Lemma 22;
Sinisalo via Farey sequences), admissible $o$ are forced toward the **convergent
denominators** of $\log_2 3 = [1;1,1,2,2,3,1,5,2,23,\ldots]$:
$$ \tfrac{8}{5},\ \tfrac{19}{12},\ \tfrac{65}{41},\ \tfrac{84}{53},\ \tfrac{485}{306},\ \tfrac{1054}{665},\ \tfrac{24727}{15601},\ \ldots $$
(denominators $5,12,41,53,306,665,15601,\ldots$). **Crandall (1978)** first used these
convergents to bound cycles ($k \gt \tfrac32\min(q_j,\,2N_0/(q_j+q_{j+1}))$); **Eliahou (1993)**
sharpened the approximation argument; Steiner / Simons / Simons–de Weger run the same engine.

**Terminology caveat.** "Critical band" / "level" is **not** standard nomenclature in the
canonical literature (Crandall, Lagarias, Eliahou, Simons–de Weger, Steiner all just speak of
"the ratio" $E/o$ vs. $\log_2 3$). Eric Roosendaal's *3x+1 cycles* web page discusses
informal "critical values"; treat **our** $E(o)=\lceil o\log_2 3\rceil$ framing as the rigorous
*left endpoint* of the admissible interval, not a theorem that $E$ equals it.

---

## 2. Cycle shapes proven impossible (parity-word / gap-word patterns)

> **Exhaustive paper-by-paper backing:** [`EXCLUDED_PATTERNS.md`](EXCLUDED_PATTERNS.md)
> (Author · Paper · excluded/characterized pattern · URL · verification status), maintained and
> grown by the [`/excluded-patterns`](../../.claude/skills/excluded-patterns/SKILL.md) skill.
> The table below is the headline summary.

A cycle is encoded by a periodic parity word; the structural quantity is $m$ = number of
maximal odd-step runs = number of local minima = number of concatenated "circuits".

| pattern | result | who / when |
|---|---|---|
| **circuit** ($m=1$): one run of odd steps then one run of halvings (climb-once, fall-once; all gaps $1$ except the last) | only the trivial cycle | **Steiner 1977** |
| **2-cycle** ($m=2$) | none nontrivial | **Simons 2005** |
| **$m$-cycle, $m\le 68$** | none nontrivial | **Simons–de Weger 2005** |
| **$m$-cycle, $m\le 75$** ($m\ge76$) | none nontrivial | Simons–de Weger, updated (larger $N_0$) |
| **$m$-cycle, $m\le 91$** ($m\ge92$) | none nontrivial — **current record** | **Hercher 2023** |

- **R. P. Steiner, "A theorem on the Syracuse problem,"** Proc. 7th Manitoba Conf. on
  Numerical Math. (1977) 553–559. A *circuit* of params $(a,b)$ needs
  $(2^a-1)\,3^{\cdots}/(2^{a+b}-3^b)\in\mathbb Z_{\gt0}$; via the CF of $\log_2 3$ + Baker's
  linear-forms-in-logarithms + finite computation, only $(a,b)=(1,1)$ works.
- **J. L. Simons, "On the nonexistence of 2-cycles for the 3x+1 problem,"** Math. Comp. **74**
  (2005) 1565–1572 (Steiner-style, Laurent–Mignotte–Nesterenko bound).
- **J. L. Simons & B. M. M. de Weger, "Theoretical and computational bounds for $m$-cycles of
  the $3n+1$ problem,"** Acta Arith. **117** (2005) 51–70. *Definition:* $m$-cycle = exactly $m$
  local minima. Proved $m\ge76$ (original $m\ge69$, i.e. ruled out $m\le68$; strengthened to
  $m\le75$ with later verification). Mechanism: an $m$-cycle would force $E/o$ to approximate
  $\log_2 3$ better than the convergents allow unless $o$ is astronomical, while $N_0$ caps $o$
  from above — the two collide for small $m$.
- **C. Hercher, "There are no Collatz-$m$-Cycles with $m\le 91$,"** J. Integer Seq. **26**
  (2023) Art. 23.3.5 (arXiv:2201.00406). Main theorem: $m\ge92$. Iterated CF sharpening of the
  lower bound on $o$ until it exceeds Simons–de Weger's upper bound. Notes the next threshold
  needs only $N_0\ge 3\cdot2^{69}$ (already met by Barina).

**Discrepancy resolved (for our notes):** the "68 vs 75" question — Simons–de Weger's *original*
2005 paper ruled out $m\le68$; the $m\le75$ figure is the later version using a larger verified
range. Current unambiguous record is **Hercher: $m\le91$**. A "circuit" $=$ an $m$-cycle with
$m=1$. **No unconditional, $N_0$-independent shape exclusion is known**, and nothing rules out
$m\ge92$ — that gap *is* the cycle part of Collatz. (Our [`cycle-gcd`](../cycle-gcd/STATUS.md)
P1/Steiner-stratum and [`cocycle-combine`](../cocycle-combine/LEDGER.md) P2 single-defect
results live inside this landscape: P2's "$|D|\le 2^{|e-d|}-1$ per defect" is a *new* a-priori
ceiling for its specific word family, complementary to the $m$-indexed exclusions.)

---

## 3. Divisibility / number-theoretic conditions

1. **$D \mid S$ (closed form, §0).** $D = 2^E - 3^o$ divides the weighted sum $S$; $a_0=S/D$.
2. **$D$ is odd**, and $\gcd(D,6)=1$ (difference of a power of 2 and a power of 3). So cycle
   elements have an odd denominator, giving congruence restrictions on $S$ mod small primes.
   *(This oddness/coprimality is exactly what powers the [`circulant_matrix`](../circulant_matrix/STATUS.md)
   per-prime "keep/shed" gcd law and the [`cocycle-combine`](../cocycle-combine/structure/structure.md)
   "$S$ defined mod $\langle D\rangle$" picture.)*
3. **How small can $|D|$ be? — linear forms in logarithms.** A cycle forces $2^E,3^o$
   extremely close. **Baker's method** gives $|2^E - 3^o| \gg 2^E / E^{C}$ (absolute $C$).
   The effective constant used in cycle work is **G. Rhin's** irrationality measure
   ("Approximants de Padé et mesures effectives d'irrationalité," Séminaire de Théorie des
   Nombres Paris 1985–86, Progr. Math. **71**, Birkhäuser 1988, 155–164):
   $|x\log2 - y\log3| \gt C\max(x,y)^{-13.3}$ (exponent $\approx13.3$, $C\approx0.46$). De
   Weger's consequence: $0\lt(o\!+\!L)\log2 - o\log3\lt 2^{-0.158\,o}$ has **no** solutions for
   $o\ge32$ — the clash that yields the $m$-cycle nonexistence ranges. *(This is the precise
   provenance of the "Matveev exclusion zone" used informally in
   [`cycle-gcd/eventually-periodic.tex`](../cycle-gcd/eventually-periodic.tex); Matveev's
   theorem is the modern general-purpose successor to Baker/Rhin for this bound.)*
4. **2-adic admissibility (Terras 1976; Lagarias 1985).** Each admissible parity vector of
   length $k$ is realized by exactly one residue class mod $2^k$ (Terras, "A stopping time
   problem on the positive integers," Acta Arith. **30** (1976) 241–252 — the encoding is a
   2-adic isometry). **Lagarias, "The 3x+1 problem and its generalizations,"** Amer. Math.
   Monthly **92** (1985) 3–23, formalizes the continuous extension of $T$ to $\mathbb Z_2$,
   defines *admissible vectors*, and ties the exponent vector $(e_0,\dots,e_{o-1})$ to the
   cycle's admissibility congruence. Integrality of $a_0=S/D$ is the arithmetic shadow of this.
5. **Period structure (Eliahou 1993).** Any nontrivial period $p$ has the form
   $p = 301994\,a + 17087915\,b + 85137581\,c$ with $a,b,c\ge0$, $b\ge1$, $ac=0$ (under the
   $\sim2^{40}$ verification of the day) — see §4.

---

## 4. Quantitative bounds (current records)

**Verification bound $N_0$ (smallest possible cycle element).** Any nontrivial cycle has every
element $\gt N_0$.
- Oliveira e Silva: to $20\cdot2^{58}\approx5.76\times10^{18}$, later $\sim10^{20}$; Hercher
  (2023) uses $N_0 = 704\cdot2^{60}\approx8.12\times10^{20}\approx2^{69.5}$.
- **D. Barina (2021)**, "Convergence verification of the Collatz problem," J. Supercomputing
  **77** 2681–2688: $\mathbf{1.5\times2^{70}\approx1.77\times10^{21}}$.
- **D. Barina (2025)**, "Improved verification limit…," J. Supercomputing **81**:
  $\mathbf{2^{71}\approx2.36\times10^{21}}$ — **current**. ⇒ smallest cycle element $\gt 2^{71}$.

**Cycle length / number of odd steps $o$.**
- **S. Eliahou (1993)**, "The 3x+1 problem: new lower bounds on nontrivial cycle lengths,"
  Discrete Math. **118** 45–56: at $N_0\approx2^{40}$, any nontrivial cycle has **$\ge
  17{,}087{,}915$ terms** (period form in §3.5).
- Scaling with the modern $N_0$: number of odd steps **$o \gtrsim 1.375\times10^{11}$**
  (Hercher 2023; an earlier figure $o\gt7.2\times10^{10}$ also appears), and total length
  $\approx \mathbf{2.18\times10^{11}}$ terms (shortcut map) / $\approx3.56\times10^{11}$
  (unshortcut map) per current verified-range summaries.

**Number of cycles.** For each fixed $(E,o)$ there are only **finitely many** cycles (the
closed form §0 bounds the witnesses), so finitely many of each length — *proven*. Whether the
**total** number of nontrivial cycles is finite is **open** for $3x+1$ (the $3x+d$-cycle
conjecture posits finitely many positive cycles per $d$).

**Density companion (not a cycle bound).** **Krasikov–Lagarias (2003)**, "Bounds for the 3x+1
problem using difference inequalities," Acta Arith. **109** 237–258 (arXiv:math/0205002): at
least $x^{0.84}$ integers below $x$ reach $1$. Constrains how thin any exceptional (cyclic or
divergent) set can be; does not forbid cycles.

**Context — cycles of related maps.** $3x+1$ on positive integers: only the trivial
$1\!\to\!2\!\to\!1$. The $3x-1$ map (equivalently $3x+1$ on negatives) has **three** genuine
nontrivial cycles — the $-1$, $-5$, and $-17$ orbits (periods 2, 5, 18). These reproduce in
our framework: our [`diophantine-distribution`](../diophantine-distribution/STATUS.md) fixed-
point computation already recovers $-1$ and $-7$. **Moral:** any $3x+1$ no-cycle proof must use
more than the cycle equation alone, since closely related maps *do* have cycles.

---

## 5. Honest proven / conjectural ledger

**Proven:** Böhm–Sontacchi closed form & divisibility equivalence · $D$ odd, $\gcd(D,6)=1$ ·
ratio sandwich $\log_2 3 \lt E/o \le \log_2(3+1/N_0)$ · Steiner no-circuit · Simons no-2-cycle ·
Simons–de Weger $m\ge76$ · Hercher $m\ge92$ · Eliahou period $\ge1.7\times10^7$ (now
$\gtrsim10^{11}$ odd steps) · Terras/Lagarias 2-adic bijection & admissibility · Baker/Rhin
linear-form lower bounds · finitely many cycles per length · smallest element $\gt2^{71}$.

**Conjectural / open:** that *no* admissible $(E,o,(e_k))$ yields integer $a_0\gt1$ — i.e. no
nontrivial cycle at all; finiteness of the *total* number of cycles; any $N_0$-independent
exclusion; exclusion of $m\ge92$.

---

## References

- Böhm & Sontacchi 1978, Atti Accad. Naz. Lincei Rend. (8) **64** 260–264. *(page nos. per
  Lagarias bibliography — cross-check before print.)*
- Steiner 1977, "A theorem on the Syracuse problem," Proc. 7th Manitoba Conf. 553–559.
- Crandall 1978, "On the '3x+1' problem," Math. Comp. **32** 1281–1292 — https://www.ams.org/journals/mcom/1978-32-144/S0025-5718-1978-0480321-3/
- Terras 1976, "A stopping time problem on the positive integers," Acta Arith. **30** 241–252.
- Lagarias 1985, "The 3x+1 problem and its generalizations," Amer. Math. Monthly **92** 3–23.
- Eliahou 1993, Discrete Math. **118** 45–56 — https://www.sciencedirect.com/science/article/pii/0012365X9390052U
- Rhin 1988, Progr. Math. **71** 155–164 — https://link.springer.com/chapter/10.1007/978-1-4757-4267-1_11
- Belaga & Mignotte 1998, "Embedding the 3x+1 conjecture in a 3x+d context," Exp. Math. **7** 145–151.
- Sinisalo 2003, "On the minimal cycle lengths of the Collatz sequences" — https://www.probleme-syracuse.fr/cargo/Sinisalo_collatz.pdf
- Krasikov & Lagarias 2003, Acta Arith. **109** 237–258 — https://arxiv.org/abs/math/0205002
- Simons 2005, Math. Comp. **74** 1565–1572 — https://www.ams.org/journals/mcom/2005-74-251/S0025-5718-04-01728-4/
- Simons & de Weger 2005, Acta Arith. **117** 51–70 — https://eudml.org/doc/278746
- Tao 2011, "The Collatz conjecture, Littlewood–Offord theory, and powers of 2 and 3" — https://terrytao.wordpress.com/2011/08/25/
- Barina 2021, J. Supercomputing **77** 2681–2688 — https://link.springer.com/article/10.1007/s11227-020-03368-x
- Barina 2025, J. Supercomputing **81** — https://link.springer.com/article/10.1007/s11227-025-07337-0
- Hercher 2023, J. Integer Seq. **26** Art. 23.3.5 — https://arxiv.org/abs/2201.00406 · https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.html
- Lagarias annotated bibliography — https://arxiv.org/abs/math/0309224 (1963–1999) · https://arxiv.org/abs/math/0608208 (2000–2009)
- Eric Roosendaal, "The 3x+1 cycles page" — https://www.ericr.nl/wondrous/cycles.html

### To verify against primary sources before quoting in print
- Rhin exponent $13.3$ / constant $0.46$ and de Weger's $2^{-0.158\,o}$ (from secondary
  summaries / SdW PDF).
- Böhm–Sontacchi exact volume/pages.
- The "$\approx2.18\times10^{11}$ total terms" figure (web summary, not a primary theorem).
- Whether Simons–de Weger's printed bound is $m\le68$ or $m\le75$ in the edition you cite.
