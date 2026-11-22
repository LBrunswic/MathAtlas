# Chart of pattern intersections

*2026-10-30. Interactive chart: [`patterns/patterns_chart.html`](patterns/patterns_chart.html), which
works offline and has light and dark modes, a word-range selector, per-row tooltips and a table
view. Data and scripts: `patterns/pattern_chart.py` (classification), `patterns/gen_html.py`
(rendering), `patterns/data_*.json`. Math uses `\lt`/`\gt`.*

## 1. The classes

A **primitive cyclic gap word** belongs to a class when some rotation of it has the class's shape,
with every growing exponent $\ge2$ and at most **4 letters of fixed material**. The fixed material
is all base words and spacers together. That budget is what makes "pattern" mean "low complexity";
without it every word would fit every shape.

| class | shape | what covers it | status |
|---|---|---|---|
| **A** | $w^aw'$ (one growing block) | `R1/WPow`, `decideR1` | proved |
| **B** | skeleton: $\ge2$ blocks, one shared exponent, equal slopes | `R1/Skel`, R1 classification | proved |
| **C** | tower $(u^av)^by$ | `R1/Nested`, `R1/Tower` | proved |
| **D** | $u^ax\,v^by$, independent exponents, $u,v$ on the **same side** of $\log_23$ | `R1/TwoExp` (new) | proved |
| **X** | $u^ax\,v^by$, independent exponents, $u,v$ **straddling** $\log_23$ | `R1/Straddle` (new), `decide_twoexp.py` | proved, **conditional on Matveev** |
| **E** | few descents: at most 2 gaps $\ge2$ ($m$-cycles, $m\le2$) | Steiner, Simons–de Weger | literature |
| **F** | balanced (Christoffel-type) | Knight (`Christoffel.lean`) | proved |

## 2. Headline numbers

The three enumeration ranges:

| range | primitive cyclic words | in no class | nonempty regions |
|---|---|---|---|
| length $\le10$, gaps $\le3$ | 9,379 | 7,887 (84%) | 35 of 127 |
| length $\le8$, gaps $\le4$ | 11,460 | 9,069 (79%) | 31 |
| length $\le14$, gaps $\le2$ | 2,536 | 2,067 (82%) | 33 |

Across all three ranges, **41** regions are nonempty.

The largest regions in the first range are:

| region | words | coverage |
|---|---|---|
| X only | 394 | Matveev-conditional |
| D only | 294 | proved |
| A only | 239 | proved |
| C only | 155 | proved |
| A ∩ X | 81 | — |
| A ∩ D | 60 | — |

Three things stand out:
- **X was the largest open region, and is now closed conditional on Matveev.** Straddling
  two-exponent words form the largest single region, and 528 words carry an X decomposition.
  §6 classifies the whole class from Matveev's two-logarithm theorem, with an effective decider.
- **Most short words are in no class.** Their cycle question is untouched by every family-level
  method here; a structural method can only reach them through a different notion of pattern.
- **Known cycle words in range.** $(1,2)$, the −5 cycle, lies in $E\cap F$. The −17 cycle word
  $(1,1,1,2,1,1,4)$ lies in **E only**: at budget 4 it is in none of the machinery classes, since
  $1^3\,2\,1^2\,4$ would need unequal exponents on equal blocks, plus a spacer.

## 3. Words in exactly one class (exclusive witnesses)

These are the shortest witnesses over the three ranges, with the decomposition that was found.

| class | witnesses (in that class and no other) |
|---|---|
| A only | `2,2,4` = $2^2\,4$ · `2,4,4` = $4^2\,2$ · `1,2,2,3` = $2^2\,3\,1$ |
| B only | `1,2,2,3,2,2` = $1\,2^2\,3\,2^2$ · `1,2,2,4,2,2` = $1\,2^2\,4\,2^2$ · `1,3,3,2,3,3` = $1\,3^2\,2\,3^2$ |
| C only | `1,1,1,2,1,1,2,2` = $(1^2\,2)^2\,2\,1$ · `1,1,1,2,1,1,2,3` = $(1^2\,2)^2\,3\,1$ |
| D only | `1,2,2,1,3,3,3` = $2^2\,1\,3^3\,1$ · `1,2,2,2,1,3,3` = $2^3\,1\,3^2\,1$ |
| X only | `1,1,1,2,1,2,2` = $1^3\,2\,1\,2^2$ · `1,1,1,2,1,3,3` = $1^3\,2\,1\,3^2$ |
| E only | `1,3`, `1,4` ($m=1$, Steiner circuits) · `2,4` ($m=2$) · the −17 cycle `1,1,1,2,1,1,4` |
| F only | `1,1,1,2,1,1,1,2,1,1,2` · `1,2,2,1,2,2,2,1,2,2,2` (length 11; shorter balanced words also fall in A or E) |
| no class | `2,3,4` · `2,4,3` · `1,2,3,2` |

The chart's tooltips and table view give witnesses for every intersection region, e.g.
$A\cap C$: `1,1,2,1,1,2,2` = $(1,1,2)^2\,2$ = $(1^2\,2)^2\,2$.

## 4. What the chart does not show

- **Results depend on the budget and the ranges.** Raising the budget moves words out of "no
  class"; longer words populate more regions. The 41 regions found are a lower bound.
- **Some regions are structurally empty at this budget.** 86 of the 127 intersections are empty in all three ranges; many, e.g. $B\cap C$,
  need more than 4 letters of fixed material.
- **Membership is only a sufficient-shape test.** It records the first decomposition found, not all
  of them.
- **Literature classes are scaled down.** Simons–de Weger exclude $m$-cycles for all $m\le68$ (and
  later work extends this); class E uses $m\le2$ so that it is a pattern on short words.

## 5. New theorem behind class D (`R1/TwoExp.lean`)

> **Same-side two-exponent families.** Let $u,v\ne\varnothing$ lie on the same side of $\log_23$
> (both $2^{|\cdot|}>3^{\mathrm{len}\,\cdot}$, or both $\lt$), and let $x,y$ be arbitrary positive
> words. Then the cycle words $u^ax\,v^by$ are:
> - finitely many pairs $(a,b)$ with both cores $C(u,x\,v^b\,y)$ and $C(v,y\,u^a\,x)$ nonzero
>   (`twoExp_classification`);
> - pairs with $C(u,xv^by)=0$, which are cycle words iff $u$ is (`twoExp_degenerate_u`);
> - pairs with $C(v,yu^ax)=0$, which are cycle words iff $v$ is (`twoExp_degenerate_v`).

**Proof outline.**
- **Linear form.** $D(v)\,C(u,xv^by)$ is the linear form $\alpha\,2^{b|v|}-\beta\,3^{b\,\mathrm{len}v}$
  (`twoExp_linear`).
- **No cancellation.** On the same side, $|D(u^axv^by)|\gtrsim2^{a|u|}2^{b|v|}$ (or the 3-analogue),
  so $a$ is bounded independently of $b$ (`twoExp_a_bounded`).
- **Rotation.** For each such $a$, rotate to $v^b(yu^ax)$ (`isCycleWord_rotate`). This is a $w^aw'$
  family.
- **Why same side matters.** Straddling allows $2^E\approx3^o$, which is where Baker/Ellison enters.

**Check.** On 600 random families with $a,b\le8$ (38,400 members):
- the same-side families have 448 cycles, all on the degenerate loci;
- the straddling families have cycles with both cores nonzero, e.g. $1^a2^b$ at $a=b=1$ (the −5
  cycle).

## 6. Class X: two exponents on any sides (`R1/Straddle.lean`, `decide_twoexp.py`)

**Theorem (`twoExp_cycles_of_matveev`).** Assume `MatveevTwoThree c` with $c\ge0$ (the published
theorem for $c=c_0\approx5.86\cdot10^8$). Fix positive words $u,v\ne\varnothing$ and $x,y$. Then a
finite set $F$ of pairs $(a,b)$ exists such that a nonempty $W=u^axv^by$ is a cycle word iff one
of the following holds:
- $(a,b)\in F$;
- $C(u,xv^by)=0$ and $u$ is a cycle word;
- $C(v,yu^ax)=0$ and $v$ is a cycle word.

Each degenerate locus is a single value of one exponent, or everything (`twoExp_zero_u`). The
argument does not care which side of $\log_23$ the blocks lie on.

**Proof outline.**
- **Two ceilings, one per block.** Rotating $W$ so that $u$, resp. $v$, comes first, the $w^aw'$
  ceiling and the linear form give $|D(W)|\le k_uG_v^{\,b}$ and $|D(W)|\le k_vG_u^{\,a}$, where
  $G=\max(2^{|\cdot|},3^{\mathrm{len}\,\cdot})$ (`twoExp_ceiling_real`). Each ceiling is exponential
  in one exponent only.
- **The product.** Since $\min(2^{|u|},3^{\mathrm{len}\,u})\ge2$,
  $\max(2^E,3^O)^2\ge2^E3^O\ge2^{a+b}G_u^{\,a}G_v^{\,b}$.
- **Matveev.** It gives $\max(2^E,3^O)\le2e^c(B+1)^{\lceil c\rceil}|2^E-3^O|$ (`polyLB_of_matveev`).
- **Combine.** Multiplying the two ceilings leaves $2^{a+b}\le K(a+b+1)^{2\lceil c\rceil}$
  (`twoExp_pow_le_of_polyLB`, with an explicit $K$). So $a+b$ is bounded.
- **Beyond two blocks.** *Corrected 2026-10-30.* An earlier version said two is the limit of this
  method. That compared equal weights only. The right threshold is the tropical budget
  $\min(A,B)\lt1$ of [`SCHEME.md`](SCHEME.md) §2.4, and e.g. $1^a2^b1^c2^d$ is inside it.

**Effective decision (`decide_twoexp.py`).** Matveev's constant makes the bound on $a+b$ about
$10^{10}$, which is far too large to enumerate. The decider reduces it.
- **Regimes.** Off the loci, either $|\Lambda|\ge1$ and $a+b\le N_1=2+\log_2(k_uk_v)$, or
  $\|O\,\log_23\|\le C\,2^{-(O-\mu)/(2\lambda)}$, where $\lambda=\max(\mathrm{len}\,u,\mathrm{len}\,v)$
  and $\mu=\mathrm{len}\,x+\mathrm{len}\,y$.
- **Convergents.** By best approximation, a block $q_k\le O\lt q_{k+1}$ of convergent denominators
  of $\log_23$ is excluded as soon as $\|q_k\log_23\|\gt C\,2^{-(q_k-\mu)/(2\lambda)}$. About 24
  convergents reach Matveev's $O_{\max}$, which is $4\cdot10^{10}$ to $10^{11}$ here, and only $O\lt O_{\text{small}}$ (typically a
  few dozen) survives.
- **Enumeration.** What is left is a small box, enumerated exactly.

Examples:

| family | $N_1$ | $O_{\text{small}}$ | off-locus cycles |
|---|---|---|---|
| $1^a2^b$ | 6 | 41 | $(1,1)$, the −5 cycle |
| $(1,1)^a\,2\,(2,2)^b$ | 14 | 306 | none |
| $2^a\,1\,1^b\,3$ | 13 | 41 | none |

The loci of $1^a2^b$ are $b=0$ (the powers of $1$, the −1 cycle) and $a=0$ (the powers of $2$, the
cycle 1). So **$1^a2^b$ is decided completely, negative cycles included**. `TwoBackground` covered
positive cycles only, conditional on Ellison.

**Check.** `decide_twoexp.py --selftest 150` ran 150 random families (99 same side, 50 straddling;
one fully degenerate family was skipped). It compared the decider with brute force on $a,b\le14$:
23 off-locus cycles, **0 mismatches**. It also checks the linear-form identity numerically on every
family.

**Trust.** The Lean side (Matveev ⇒ finite, with the explicit inequality) is proved and
axiom-clean. The Python reduction (convergents at 80 digits, the sharpened $1/|D|$ ceiling) is not
formalized. It is the same inequality chain with tighter constants.
