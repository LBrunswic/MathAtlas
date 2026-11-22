# The rotation-combination floor (a proven no-go that prunes the calculus)

**Promise:** medium — a certified divisibility fact ($\ge G$) that is **real but was mis-framed as a
no-go**. The "$\ge G$" floor does **not** block exclusion: the actual exclusion lever (P2/C9, now
[bounded-defect-lever](bounded-defect-lever.md)) uses rotation-sum wedges that *are* $\ge G$ yet whose
**6-free part is bounded independent of $o$**. See the correction below.
**Status:** principle — **proven** (floor), but the *consequence* re-scoped (Gen 3): exclusion lives
on the 6-free axis, not the size axis.
**Last iterated:** 2026-06-08

## The principle (one crisp claim)

Let $W$ be a cyclic gap word and $G:=\gcd_{0\le j\lt o}S^{(j)}(W)$ its shift-gcd (on a genuine
Syracuse cycle $G=\lvert 2^E-3^o\rvert=\lvert D\rvert$, and $G$ is **odd**, $G\perp6$). Then **any
$\mathbb{Z}[1/6]$-unit combination of full rotation sums of $W$**,
$$L=\sum_j \varepsilon_j\,S^{(j)}(W),\qquad \varepsilon_j\in\{\pm2^a3^b\},$$
is divisible by $G$: writing $L=N/(2^a3^b)$ in lowest terms, $G\mid N$. Hence either $N=0$ or
$\lvert N\rvert\ge G$; and since $G$ is odd, $\operatorname{oddpart}(N)$ is **also** a multiple of
$G$, so $\lvert\operatorname{oddpart}(N)\rvert\ge G$ when $N\ne0$.

**Consequence (the floor).** The only **sub-$G$** object obtainable from a nonzero rotation-sum
combination is $C=0$ (the degenerate Steiner / bounded-circuit locus). True — but see the correction.

> **⚠ Correction (Gen 3): "$\ge G$" is NOT the exclusion criterion.** A Matveev/Ellison exclusion
> does **not** need a core $\lt G$. It needs a core whose **6-free part is bounded by a constant
> independent of $o$** — then $G\le\operatorname{sixfree}(C)=$ const, and the transcendence
> *lower* bound $G\gtrsim2.56^{\,o}$ caps $o$. The winning P2/C9 cores are *exactly* rotation-sum
> wedges (so $\ge G$, on this floor) whose 6-free part is the bounded defect ceiling. Verified:
> `odd_part_lever.py` PART C and `defect_compose.py` PART A — the lever-wedge is divisible by $G$ with
> $|\text{wedge}|\ge G$, **yet** $\operatorname{sixfree}(\text{wedge})\le$ a fixed constant for all
> run lengths. So this floor prunes only the sub-strategy "drive $|C|$ below $G$ directly"; it does
> **not** prune rotation-sum combinations as a route to exclusion. The live lever is
> [bounded-defect-lever](bounded-defect-lever.md).

## Why this matters

This is the precise reason the inner-core bridge ([inner-core-extraction](inner-core-extraction.md))
is *real but vacuous*: it produces a genuine $G$-divisible object that even **eliminates the inner
core $u$**, but that object is a combination of full rotation sums, so it sits on the floor
$\ge G$. The $u$-elimination buys nothing on the size axis.

**Where small cores actually live.** The certified small-core wins are **wedges of proper
sub-blocks**, $C(u,v)=D(u)S(v)-D(v)S(u)=S(uv)-S(vu)$, where $D(u)=2^{\lvert u\rvert}-3^{\operatorname{len}u}$
is itself small (the near-coincidences $2^a\approx3^b$: $4{-}3,9{-}8,\dots$), or the monomial cores
$X^a(X-1)$ of single-defect/Christoffel words (structure.md P2, C9). These are *not* combinations of
full-cycle rotation sums — they combine sub-words whose own $D$ is small. P1's $u$-extraction does
**not** apply to them (the eliminated $u$ would have to be a full-cycle factor). So the move calculus,
to beat the barrier, must operate on proper sub-block wedges and/or the **odd-part** lever ($G$ odd
kills $2$-powers, leaving a defect-bounded ceiling), not on whole-word rotation combinations.

## Working notes

Certified in [`../checks/small_core_search.py`](../checks/small_core_search.py) (exit 0):

- **Part C (the floor):** 158 random $\mathbb{Z}[1/6]$-unit combinations of up to 3 rotation sums,
  over words of length 3–7, letters 1–4. In every case the numerator is a multiple of $G$, has
  $\lvert N\rvert\ge G$ when nonzero, and $\operatorname{oddpart}(N)$ is a multiple of $G$ with
  $\lvert\operatorname{oddpart}(N)\rvert\ge G$. (The divisibility $G\mid N$ is in fact a tautology —
  $G$ divides each $S^{(j)}$ by definition — so the floor is forced, not merely sampled.)
- **Part B (search):** over cyclic words length 4–7 (letters 1–3), every equinumerous middle-$u$
  rotation pair with $\chi(x)=\chi(x')$ has $\lvert\text{num}\rvert\ge G$; smallest ratio
  $\lvert\text{num}\rvert/G=2$. No sub-$G$ core exists in range — consistent with the floor.

Cross-checked in [`../checks/g_divisibility_bridge.py`](../checks/g_divisibility_bridge.py): the
inner-core bridge gives $0/17952$ instances with $\lvert\text{num(LHS)}\rvert\lt G$.

## Open questions

- [ ] **Is the floor exactly $G$ attainable, and when?** $\lvert N\rvert=G$ (ratio 1) would mean two
      rotation sums are consecutive multiples of $G$. The search's minimum was $2$ under the
      equinumerous constraint; without it, does ratio $1$ occur? Characterize the ratio-1 pairs (on a
      genuine cycle $S^{(j)}=\pm x_j G$ with $x_j$ the cycle elements, so ratio $=\lvert x_a-x_b\rvert$
      — ratio 1 $\iff$ adjacent cycle values differ by 1).
- [ ] **Does the floor extend to $\mathbb{Z}[X,Y]$-polynomial coefficients?** Here we used unit
      (monomial) coefficients. If a move uses genuine polynomial coefficients $p_j(X,Y)$, the
      combination need not be a multiple of $G$ at $(2,3)$ — does that open any room, or do the
      polynomial coefficients just reintroduce $D=X^E-Y^o$ (a $G$-multiple) and stay on the floor?
- [ ] **Formal complement.** State precisely: small cores $\iff$ wedges $C(u,v)$ of proper sub-blocks
      with $\lvert D(u)\rvert$ small, OR odd-part-reducible monomial cores. Is this a clean dichotomy
      (every sub-$G$ core is one of these), or are there other sources?

## Iteration log
- 2026-06-08 (Gen 2): distilled from the inner-core bridge no-go. Certified the floor
  (`small_core_search.py` Part C) and recorded the redirect to proper-sub-block wedges / odd-part.
- 2026-06-08 (Gen 3): **re-scoped the consequence.** The floor ($\ge G$) is real but is *not* an
  exclusion obstruction: P2/C9 (the [bounded-defect-lever](bounded-defect-lever.md)) win with
  rotation-sum wedges that are $\ge G$ yet have a 6-free part bounded independent of $o$. Added the
  correction box; verified in `odd_part_lever.py` (PART C) and `defect_compose.py` (PART A). Exclusion
  lives on the 6-free axis, not the size axis.
