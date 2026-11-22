# The Patterns Sheet

Candidate word-patterns and the **rationale** for why each may admit a compensating
$\mathbb{Z}[X,Y]$-linear combination of rotation sums $S^{(j)}$. This is the menu the
orchestrator hands to [`combinator`](../../.claude/agents/combinator.md) agents; results land in
[`LEDGER.md`](LEDGER.md). See [`RATIONALE.md`](RATIONALE.md) for the governing principle: a
combination $\sum_j c_j S^{(j)}$ is divisible by $G=\gcd_j S^{(j)}=|D|$, so any compensation to a
small core $C$ gives the ceiling $|2^E-3^o|\le|C|$ (unless $C=0$).

**What "compensation" means concretely.** Pick coefficients $c_j(X,Y)$ (integers, or monomials
$X^aY^b$ that $G$ is coprime to) so that, after the cocycle identities cancel the leading terms,
$\sum_j c_j S^{(j)}$ equals a target $C$ of strictly lower complexity than a single $S^{(j)}$ —
ideally parameter-free, or with a gap-sum exponent that does not grow with the family parameter.

**Reading the table.** *Combination idea* is a starting hypothesis, not a guarantee — the
combinator's job is to find the actual coefficients (or report none exists). *Core size goal* is
the prize: how the exponent of $X$ in $|C|$ should behave.

---

## Tier 0 — proved / warm-up (validate the pipeline)

| # | Pattern | Definition | Combination idea | Why compensation is expected | Core size goal | Status |
|---|---------|-----------|------------------|------------------------------|----------------|--------|
| P0 | **Eventually-periodic** $w^qw'$ | block $w$ repeated $q\times$ then tail $w'$ | $S^{0}-S^{|w|}$ (one block-rotation difference) | block telescoping: cocycle splits off the lead block, the $Y^{L}S(w)$ terms cancel, leaving $X^{(q-1)|w|}C(w,w')$; $G$ odd kills the $X$ power | $C$ **$q$-free**; $X$-exp $=|w|+|w'|$ | **proved** (periodic-words.md) |
| P1 | **Single circuit / constant gap** $d^o$ | every gap equals $d$ | none needed: $S=\sum_k(X^d)^kY^{o-1-k}=D/(X^d-Y)$ | constant word ⇒ geometric sum ⇒ $S$ itself factors through $D$; all rotations equal | $G=|D|/|2^d-3|$ exactly | warm-up |

## Tier 1 — high priority (most likely to extend the prototype)

| # | Pattern | Definition | Combination idea | Why compensation is expected | Core size goal | Priority |
|---|---------|-----------|------------------|------------------------------|----------------|----------|
| P2 | **Single-defect circuit** $d^{a}e\,d^{b}$ | constant word $d^{o-1}$ with one altered gap $e$ (or one inserted letter) | $S(\tau)-($combination reconstructing the pure circuit $d^{o}$) | $\tau$ is a rank-1 perturbation of the closed-form circuit P1; subtracting the circuit's geometric sum should leave a core controlled only by the *defect* $(e-d)$, not by $a,b$ | $X$-exp independent of $a,b$ (only $d,e$) | **high** |
| P3 | **Two-block periodic** $(uv)^q$ | alternating blocks, period $u v$ | $S^{0}-S^{|uv|}$, then iterate $u\leftrightarrow v$ | direct P0 instance with $w=uv,\,w'=\varnothing$, *plus* a second difference exploiting the inner $u\mid v$ boundary; two telescopings may pin a smaller joint core | $q$-free; possibly smaller than naive $C(uv,\varnothing)$ | **high** |
| P4 | **Finite-difference in $q$** $w^qw'$ | same family as P0 | $\big(\sigma_q-X^{|w|}\big)S(w^qw')$ where $\sigma_q$ shifts $q\to q-1$ | the cocycle gives the first-order $q$-recurrence $S(w^qw')=Y^{n}S(w^{q-1}w')\cdot(\dots)+X^{|w|}S(\dots)$; the annihilator $(\sigma_q-X^{|w|})$ should collapse it to a closed form, exposing the minimal core directly | reveals the *exact* minimal $C$, not just a divisor | **high** |
| P11 | **Stratum twist / topological cover** | not one word-family but a *propagation rule* across the stratum $\mathcal{S}_{E,o}=\{$words with fixed gap-sum $E$, length $o\}$ (all share one $D$); the simple twist is the **adjacent transposition** $d_i\leftrightarrow d_{i+1}$ (and its cousin the unit-transfer $d_i{\to}d_i{+}1,d_{i+1}{\to}d_{i+1}{-}1$) | reuse one word's certificate $(a,b)$ on a twisted neighbour: since $D(w'){=}D(w)$, $D\mid C(w'){=}aD{+}bS(w'){=}C(w){+}b(S(w'){-}S(w))$ holds for free — coverage propagates along the stratum graph, the increment is the radius | $S(w'){-}S(w)=Y^{o-i-1}X^{P_{i-1}}(X^{d_{i+1}}{-}X^{d_i})$ (only $P_i$ moves) — a **monomial $\times$ local binomial**; $G{=}\lvert2^E{-}3^o\rvert$ is coprime to $6$ so the monomial is a **unit mod $D$**, and the essential size is the odd part $2^{\lvert d_i-d_{i+1}\rvert}-1$ — *literally the P2 ceiling*, now for a swap inside **any** background word. Transpositions+unit-transfers connect the whole stratum, so one covered base word may tile $\mathcal{S}_{E,o}$ | core lives **mod $D$** (absorb $D$-multiples into $a$); propagation rule $C(w')\equiv C(w)+(bu)(X^{d_{i+1}}{-}X^{d_i})\pmod D$, $u$ unit. Radius small when adjacent gaps are *close* — complementary to where P2 bites | **high** |
| P10 | **Double-run with defect** $x^{q}y\,z^{p}$ | run of block $x$ ($q\times$), single defect block $y$, run of block $z$ ($p\times$); blocks general and possibly distinct. Generalizes **P0** ($p{=}0$, tail $w'{=}y$) and **P2** ($x{=}z{=}(d)$, $y{=}(e)$, the only ✔) | **two-stage**: (i) a block-rotation difference $\Delta_x$ telescoping the $x$-run gives a $q$-free combination with core $C_x(p)=C(x,\,yz^p)$ (still $p$-dependent); (ii) a block-rotation difference $\Delta_z$ telescoping the $z$-run gives a $p$-free core $C_z(q)$ (still $q$-dependent). **Then combine the two** — a double telescoping $\Delta_x\Delta_z$ (or a $\mathbb{Z}[X,Y]$-combination of $C_x,C_z$) to kill *both* run parameters at once | closed form $S(w)=c^pb\,s_xG_x(q)+c^pA^qs_y+A^qB\,s_zG_z(p)$ ($a{=}Y^{o_x},A{=}X^{E_x}$, etc.; $G_x(q)=\frac{A^q-a^q}{A-a}$): all $q,p$-growth sits in $A^q,C^p$ and the two geometric sums, so a rotation difference telescopes each run. A *single* defect should keep the word primitive (unlike P3's $(uv)^q$), so P2's "defect controls the core, runs don't" has a real shot; the risk is that telescoping one run leaves an $A^q$- or $C^p$-growing tail from the other — hence the **need to combine two combinations**, not one | $X$-exp independent of **both** $q$ and $p$ (only the block data $x,y,z$ and the run-ratio mismatch $E_x$ vs $E_z$); reduces to P2's $2^{|e-d|}-1$ when $x{=}z{=}(d)$ | **high** |
| P9 | **Balanced blocks** $u_1u_2\cdots u_q$ | $q$ blocks all of **equal length** $\operatorname{len}(u_i)=o$ and **equal gap-sum** $|u_i|=E$; internal arrangements free (generalizes P0's $w^q$, which forces $u_i$ identical) | block-rotations $R^kw$ (cyclic permutations of the blocks); seek $\sum_k c_k(X,Y)\,S(R^kw)$ killing the geometric weights | **common diagonal**: $M(u_i)=\big(\begin{smallmatrix}Y^o&0\\ s_i&X^E\end{smallmatrix}\big)$ all share $(a,b)=(Y^o,X^E)$, so $S(w)=\sum_i a^{q-i}b^{i-1}s_i$ with $s_i:=S(u_i)$ in a **fixed finite set** (compositions of $E$ into $o$ parts) independent of $q$ — the P2-style setup for a $q$-uniform core. At $q{=}2$: $S(u_1u_2)-S(u_2u_1)=(a-b)(s_1-s_2)$, and $G=\lvert D(u)\rvert(2^E+3^o)$ cancels $\lvert D(u)\rvert$ to give $(2^E+3^o)\mid(s_2-s_1)$ — forcing $s_1=s_2$ (collapse to P0) when the block range stays below $2^E+3^o$. General $q$: adjacent $S(R^k)-S(R^{k+1})$ carries a wrap term $a^{q-1}-b^{q-1}$; find the combination that compensates it away | $X$-exp **independent of $q$** (only $o,E$ and the block differences $s_i-s_j$) | **high** |

## Tier 2 — exploratory (new structure, higher risk)

| # | Pattern | Definition | Combination idea | Why compensation is expected | Core size goal | Priority |
|---|---------|-----------|------------------|------------------------------|----------------|----------|
| P5 | **Palindromic** $w=\tilde w$ | gap word equal to its reversal | $X^{|w|}Y^{\,n-1}S(w)(1/X,1/Y)$ vs $S(\tilde w)$ | reversal functional equation: $S(\tilde w)$ relates to $S(w)$ evaluated at $(1/X,1/Y)$ times a monomial; for palindromes this is a self-relation, candidate extra divisibility on $G$ | extra factor of $G$, not a numeric ceiling | medium |
| P6 | **Sturmian / balanced** | gaps $\in\{d,d+1\}$, balanced (mechanical word) | rotation orbit is highly structured (continued-fraction layered); combine rotations along the CF expansion | balanced words have $o$ distinct rotations forming an arithmetic structure; nested telescoping along CF convergents may compensate | $X$-exp $\sim$ CF-partial-quotient bounded | medium |
| P7 | **Arithmetic-progression gaps** $d_k=\alpha+\beta k$ | linear gap profile | combine $S^{(j)}$ against $S^{(j+1)}$ with $X^{\beta}$-twisted coefficients to telescope the quadratic $e_k$ | $e_k$ quadratic in $k$ ⇒ a $q$-Gaussian / theta structure; a twisted second difference may kill the Gaussian growth | unclear; probe symbolically | low |
| P8 | **Concatenation of coprime circuits** $d_1^{o_1}d_2^{o_2}$ | two circuits glued | apply P0 with $w=d_1^{o_1}$, $w'=d_2^{o_2}$; core $=D(w)S(w')-D(w')S(w)$ with both $S$ closed-form (P1) | both blocks have closed-form $S=D/(X^{d_i}-Y)$, so $C$ has an explicit closed form — a fully computable family to map the $C=0$ locus exactly | closed-form $C$; charts the degenerate stratum | medium |

---

## Cross-cutting questions for every pattern

- **Where is $C=0$?** The degenerate locus is the known-hard bounded-circuit core; mapping it for
  each family tells us what the cheap ceiling does *not* cover.
- **Does the $X$-exponent of $C$ stay below $E$?** Only then is $|C|<2^E$ and the ceiling
  non-vacuous against the generic $|2^E-3^o|\approx 2^E$.
- **Can several patterns be combined to cover all words?** Every cyclic word is *some* $w^qw'$
  (P0 with $q=1$); the leverage is choosing the decomposition that minimizes $|C|$. A theorem of
  the form "every word lies in a pattern with $|C|<f(o)$, $f$ sub-exponential" would close
  `cycle-gcd`.

## Adding a pattern

Append a row here (with rationale) **and** a TODO row in [`LEDGER.md`](LEDGER.md). The orchestrator
`/cocycle-combine --add-pattern` does both. Keep the rationale honest about *why* cancellation is
expected — that hypothesis is what the combinator tests.
