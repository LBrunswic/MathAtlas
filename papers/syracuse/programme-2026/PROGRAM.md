# A cocycle word‑simplification program for Collatz cycles

*Standalone overview. Self‑contained; written so it reads without the surrounding research notes.*
*Math is written with `\lt` / `\gt` (bare `<`/`>` in `$…$` break some Markdown previews).*

---

## 0. Goal in one sentence

Prove the non‑existence of non‑trivial cycles of the $3x+1$ map by **constructing, for every candidate
cycle, a small representative of its rotation ideal**, and squeezing the size of that representative
against a linear‑forms‑in‑logarithms lower bound on $\lvert 2^E-3^o\rvert$.

A non‑trivial Collatz cycle with $o$ odd steps and $E$ even (halving) steps is encoded by its **gap
word** $w=(d_0,\dots,d_{o-1})$, where $d_i\ge 1$ is the number of halvings after the $i$‑th odd step and
$E=\sum_i d_i$. The whole program works with this word and a cocycle attached to it; the dynamics of
the map never reappear.

---

## 1. The cocycle and the floor

For a gap word $w=(d_0,\dots,d_{n-1})$ put the prefix sums $e_k=\sum_{i\lt k} d_i$ (so $e_0=0$), and define
the **homogenised cocycle**
$$S(w)=\sum_{k=0}^{n-1} X^{\,e_k}\,Y^{\,n-1-k}\ \in\ \mathbb Z[X,Y],
\qquad D(w)=X^{E}-Y^{n},\quad E=\textstyle\sum_i d_i,\ n=\#\text{gaps}.$$
The **specialisation** $X\mapsto 2,\ Y\mapsto 3$ recovers the integer quantities of the cycle problem:
$S(w)\in\mathbb Z$ and $D(w)=2^E-3^o$ (with $n=o$). Two facts drive everything.

* **Cocycle / rotation structure.** $S(uv)=Y^{\operatorname{len}v}S(u)+X^{\lvert u\rvert}S(v)$, and the
  $o$ cyclic rotations $w_0,\dots,w_{o-1}$ of a length‑$o$ word have **rotation sums** $S^{(j)}=S(w_j)$
  all sharing the same $D$ (rotation is invariant on $(E,o)$).
* **The floor.** On a *genuine* cycle,
  $$\boxed{\,G(w):=\gcd_{0\le j\lt o} S^{(j)}(w) \;=\; \lvert 2^E-3^o\rvert \;=\;\lvert D\rvert\,}$$
  and $G$ is **odd and coprime to $3$** (each $S^{(j)}$ is: its $k{=}0$ term is $3^{o-1}$, its last term is a
  pure power of $2$). Every $\mathbb Z$‑linear combination of the rotations is divisible by $G$, so

  $$\textbf{any nonzero representative } C \text{ of the rotation ideal satisfies } \lvert C\rvert\ \ge\ G \;=\;\lvert 2^E-3^o\rvert .$$

This is the **floor**: representatives cannot be smaller than $\lvert 2^E-3^o\rvert$ on a cycle.

---

## 2. The exclusion squeeze

Two opposing bounds on the same quantity $\lvert 2^E-3^o\rvert$ trap the cycle.

* **Upper (constructive, our job).** Apply *simple word moves* (§4) to the rotations to build a small
  representative $C$. Because $C$ is divisible by $G$ and $G$ is $6$‑free, the **$6$‑free part** of $C$
  is again a multiple of $G$, so
  $$G\;=\;\lvert 2^E-3^o\rvert\ \le\ \operatorname{sixfree}(C).$$
  The aim is to make $\operatorname{sixfree}(C)$ **small and, ideally, $o$‑independent**.

* **Lower (transcendence, their job).** Baker/Rhin linear‑forms‑in‑logarithms give a growing lower bound
  $\lvert 2^E-3^o\rvert\ge B(o)$ (§3).

Combining, $B(o)\le \lvert 2^E-3^o\rvert\le \operatorname{sixfree}(C)$. **If a word family admits a
representative whose $6$‑free part is bounded (or grows slower than $B(o)$), then for all large $o$ the
family contains no cycle.** Exclusion therefore lives on the **$6$‑free axis**, not the size axis: a
representative may be enormous yet have a tiny $6$‑free part.

> **Why $6$‑free and not absolute size.** On a cycle $\operatorname{sixfree}(C)\ge G\approx 3^{o(1-\varepsilon)}$
> is itself huge; the leverage is that $\operatorname{sixfree}$ can stay *constant* across a family while
> $G$ grows, which is impossible for a cycle — hence the family is excluded.

---

## 3. The controlled lower bound $B(o)$

Write $\Lambda=\lvert E\ln 2-o\ln 3\rvert$; then $\lvert 2^E-3^o\rvert\approx 3^o\,\Lambda$ near a
coincidence. The best effective estimate for this specific two‑log form is **Rhin (1987)**, packaged for
the cycle problem by **Simons–de Weger (Math. Comp. 74, 2005), Lemma 12**:
$$\Lambda \;\gt\; e^{-13.3\,(0.46057+\ln o)} \;=\; 0.00219\,o^{-13.3}
\qquad\Longrightarrow\qquad
\boxed{\ \lvert 2^E-3^o\rvert \;\gt\; 0.00219\cdot \dfrac{3^o}{o^{13.3}}\ }.$$

* It is **polynomial** in the loss ($3^o/o^{13.3}$), with a tiny constant, hence **weak in the practical
  range**: it first exceeds a *constant* ceiling $c=5$ only near $o\approx 60$. That $o\approx 60$ is the
  current **rigorous exclusion threshold** for a bounded‑ceiling family.
* **Conjecturally** the irrationality measure of $\log_2 3$ is $2$, which would give
  $\lvert 2^E-3^o\rvert\ge 3^{o(1-\varepsilon)}\approx 3^o$ and push the threshold down dramatically — but
  this is unproven.
* **Trivial regime.** When $w$ is far from a coincidence ($2^E$ not near $3^o$), $\lvert 2^E-3^o\rvert$ is
  of order $\min(2^E,3^o)$ and no transcendence is needed.

*Reference trail:* Rhin 1987 ($\mu(1,\log2,\log3)\le 7.616$, best for this case); Laurent–Mignotte–
Nesterenko 1995, Laurent 2008, Gouillon 2006 (general two‑log constants); Mignotte–Voutier 2022 (three
logs); Salikhov 2007 ($\mu(\log 3)\le 5.125$ — a *different* number, not the one that governs $\lvert 2^E-3^o\rvert$).

---

## 4. The move calculus

The representatives are built by **simple, exact moves** on differences of rotations. Each move is a
verified $\mathbb Z[X,Y]$ identity; none uses the cycle hypothesis, so the construction is purely
combinatorial.

A **difference** $(u,v)$ stands for the ideal element $S(u)-S(v)$. The moves:

1. **Roll (seed).** The cyclic rotations $w_0,\dots,w_{o-1}$ are the starting word set; differences are
   drawn from it. The roll is only a *seeding* step — the engine then acts on arbitrary word sets.
2. **Frame strip** (boundary). For equal‑length $u,v$: a shared **prefix** $x$ peels as a unit,
   $S(xu')-S(xv')=X^{\lvert x\rvert}\,(S(u')-S(v'))$; a shared **suffix** $z$ peels as $Y^{\lvert z\rvert}$ when
   the remaining prefixes have equal gap‑sum.
3. **Anchor split** (interior, multi‑step). At any position $k$ where the prefix gap‑sums agree
   ($\sum u[{:}k]=\sum v[{:}k]$) the cocycle splits the difference exactly,
   $$S(u)-S(v)=Y^{\,n-k}\bigl(S(u_{\lt k})-S(v_{\lt k})\bigr)+X^{\,e_k}\bigl(S(u_{\ge k})-S(v_{\ge k})\bigr),$$
   and one recurses — peeling one atomic segment per step down to irreducible leaves (and **null**
   segments where the two coincide).

**Anchored free basis $+$ combination round.** The all‑pairs differences are *redundant*: among
$\binom{o}{2}$ of them only $o-1$ are independent ($\,(w_i{-}w_j)+(w_j{-}w_k)+(w_k{-}w_i)=0\,$). One instead
takes an **anchored** generating set — group the rotations by a shared feature (e.g. first gap), fix an
anchor per group, and use $w_j-w_{\text{anchor}}$ — which is *free*. Any other difference is a
$\mathbb Z$‑combination, e.g. $w_a-w_b=(w_a-w_{\text{anchor}})-(w_b-w_{\text{anchor}})$, and **combining the
already‑reduced generators lets shared structure cancel to a smaller core**. This second (combination)
round is where genuinely smaller representatives appear.

The output is the **simplest representative**: the irreducible core of smallest $6$‑free part reachable.

---

## 5. First objective: below $3^o$, hence critical

Empirically the simple moves produce a representative with $\lvert C\rvert\lt 3^o$ **exactly in the
cycle‑relevant regime** $2^E\lesssim 2\cdot 3^o$ (critical and below), and fail to when $2^E\gg 3^o$.

The implication is exact: a nonzero representative with $\lvert C\rvert\lt 3^o$, divisible by $G=\lvert D\rvert$,
forces
$$\lvert 2^E-3^o\rvert\lt 3^o\ \Longrightarrow\ 3^o\lt 2^E\lt 2\cdot 3^o\ \Longrightarrow\ E=\lceil o\log_2 3\rceil
\quad(\textbf{critical}).$$

**Honest status.** Because every representative obeys $\lvert C\rvert\ge\lvert D\rvert$, a hypothetical
super‑critical cycle ($2^E\gg 3^o$, so $\lvert D\rvert\gg 3^o$) has *no* representative below $3^o$ at all.
Hence "moves yield a rep $\lt 3^o$" is **equivalent to criticality** — a *characterisation*, not an
independent proof. Indeed "all cycles are critical" is genuinely non‑trivial: the cycle equation alone
gives $2^E/3^o=\prod_i\bigl(1+\tfrac1{3x_i}\bigr)\le(4/3)^o$, allowing $E$ up to $\sim 2o$; criticality is
forced only because the cycle elements are huge ($x_{\min}\ge 5.76\times 10^{18}$, Oliveira e Silva),
which is exactly **de Weger's Lemma 8** ($\delta o\lt E\lt 1.000001\,\delta o$, $\delta=\log_2 3$).

**The provable, non‑circular milestone:** find an *explicit* upper bound $f(w)$ on the move‑representative's
$6$‑free part (from the cancellation structure of $S^{(i)}-S^{(j)}$) and prove $f(w)\lt 3^o$ for critical
words. The value is not "$\lt 3^o$" itself but **how far below** $f(w)$ goes as a function of word
structure — the road from the trivial $3^o$ down toward the Rhin bound $\sim 3^o/o^{13.3}$, which *is* the
exclusion.

---

## 6. Structural context: why the route is *word moves*, not algebra

A parallel effort tried to find the small representative purely algebraically (syzygies of the cocycle
"cores", the integer cyclic quotient, twisted/higher representations). The verdict was a clean closure:

* The cores form a rank‑$2$ Plücker module; over $\mathbb Q[X,Y]$ the syzygy resolution **terminates** (no
  higher cells), and the integer circulant of the orbit **amplifies** the floor rather than beating it.
* The decisive obstruction (McMullen's Alexander–Thurston norm $+$ Boden–Friedl twisted Alexander) is that
  the cocycle's Alexander polynomial $\Delta=X^E-Y^o t$ is a **binomial**, so its Newton polytope is a
  *segment*, so it has **no Mahler‑measure‑$1$ slice** — and every representation‑theoretic twist inside
  the $(2,3)$ dynamics stays binomial. *No constructive lever lives in the polynomial algebra.*

The conclusion is a **two‑layer thesis**: the algebra (Layer 1) is closed; the exclusion content is the
**Layer‑2 $(2,3)$‑arithmetic** — primitive divisors and $\operatorname{sixfree}\to\infty$ of
$\lvert 2^E-3^o\rvert$. The move calculus is the surviving constructive handle on Layer 1, and the
**bounded‑defect lever** is its one working instance:

> a cyclic word that is a bounded arc $\beta$ over one long background run $d^L$ has the adjacent‑rotation
> wedge $S(d^k\beta d^{L-k})-S(d^{k+1}\beta d^{L-k-1})=X^{kd}Y^{L-k-1}\,(S(\beta d)-S(d\beta))$, giving an
> **$o$‑independent ceiling** $G\le\operatorname{sixfree}(S(\beta d)-S(d\beta))$. This excludes that family
> down to a residual cyclotomic‑collapse (Bang–Zsygmondy) question on $\ge 2$ simultaneously growing runs.

---

## 7. An abelian estimator (AM–GM)

Writing $S(w)=3^{n-1}\sum_k \chi(w_{\lt k})$ with the **partial characters** $\chi(w_{\lt k})=2^{e_k}/3^{k}$,
the arithmetic mean of the $\chi_k$ is $A(w)=S(w)/(n\,3^{n-1})$ and the geometric mean is
$G_{\!*}(w)=\bigl(\prod_k\chi_k\bigr)^{1/n}=2^{\bar e}/3^{(n-1)/2}$, which depends only on $\sum_k e_k$ and
$n$ — it is **almost abelian** (nearly order‑independent), a candidate estimator for the size of the
abelian $6$‑free projection. With the **stark ratio** $C(w)=\max_k\chi_k/\min_k\chi_k$, AM–GM gives
$$G_{\!*}(w)\ \le\ A(w)\ \le\ C(w)\,G_{\!*}(w),$$
and the **AM/GM gap** $\log(A/G_{\!*})\ge 0$ measures the non‑abelian spread of the word. (This is a
structural estimator of the word, normalised; turning it into a numeric estimate of the integer $6$‑free
part is open — see §9.)

---

## 8. The tool

A reproducible engine and web UI live under `ideas/cocycle-combinatorics/tools/`:

* **`word_simplifier.py`** — the move engine. `roll(w)` seeds a word set; `simplify_set(words, pairs)`
  reduces the differences it spans (`pairs="anchored"` builds the free basis + combination round);
  `decompose(u,v)` is the multi‑step anchor split; `compare_to_floor`, `critical_bounds`,
  `character_bracket`, `family_scan`, `discover` expose the squeeze quantities; every reduction is verified
  as an exact $\mathbb Z[X,Y]$ identity.
* **`serve_simplifier.py`** — a stdlib web server (`python3 serve_simplifier.py`, then
  `http://localhost:8765`). Input a word (or generate a random **critical** word of a given length); it
  shows the **simplifying graph** (rotations → cores), the **multi‑step decomposition**, the **anchored
  lattice**, and a floor card with: $\lvert D\rvert$, $\log_{10}(6\text{-free}/\lvert D\rvert)$, the
  **controlled lower bound** (Rhin/de Weger) and **conjectural $\approx 3^o$ target**, the
  $\text{rep}/\text{bound}$ ratios, and the **abelian estimator** ($G_{\!*}\le A\le C\,G_{\!*}$). Graphs are
  skipped for $\lvert w\rvert\gt 30$ (kept fast); the rep$/{\approx}3^o$ ratio $\lt 1$ is precisely the
  §5 "rep $\lt 3^o$" test.

---

## 9. Status and open problems

**In hand.**
* The squeeze is set up correctly: floor $\lvert C\rvert\ge\lvert 2^E-3^o\rvert$, exclusion on the $6$‑free
  axis, against the verified Rhin/de Weger lower bound.
* One working family — the **bounded‑defect lever** — with an $o$‑independent ceiling.
* A reproducible move engine + UI; empirically, simple moves drop below $3^o$ on the critical regime.

**Open, in rough priority.**
1. **Explicit $f(w)$ (first objective, §5).** A closed‑form upper bound on the move‑representative's
   $6$‑free part; prove $f(w)\lt 3^o$ for critical words, then quantify how far below.
2. **Covering / pigeonhole.** A single move never shortens a generic word much; the live hypothesis is a
   *covering family* of moves such that every word in a positive‑density family admits one (unavoidable
   patterns / Zimin words). Make this precise or refute it.
3. **The $\ge 2$‑growing‑run no‑go.** Close (or bound) the residual cyclotomic‑collapse question that the
   bounded‑defect lever reduces to — a Layer‑2 Bang–Zsygmondy / primitive‑divisor statement on
   $\Phi_d^{*}(2^E,3^o)$.
4. **Normalise the abelian estimator (§7)** into an actual size estimate of the integer $6$‑free part.

---

## References

* J. Simons, B. de Weger, *Theoretical and computational bounds for $m$‑cycles of the $3n+1$ problem*,
  Math. Comp. **74** (2005), 1565–1572 (Acta Arith. 117). — Lemma 8 (criticality), Lemma 12 (Rhin bound).
* G. Rhin, *Approximants de Padé et mesures effectives d'irrationalité* (1987). — best two‑log estimate for $\log 2,\log 3$.
* M. Laurent, M. Mignotte, Yu. Nesterenko, *Formes linéaires en deux logarithmes…*, J. Number Theory **55** (1995).
* M. Laurent (2008); N. Gouillon, *Explicit lower bounds for linear forms in two logarithms*, JTNB (2006).
* J. Steiner (1977, 1‑cycles); J. Simons (2004, 2‑cycles); R. Crandall (1978); J. Lagarias (overviews).
* C. T. McMullen, *The Alexander polynomial of a 3‑manifold and the Thurston norm on cohomology*, Ann. ÉNS **35** (2002).
* H. Boden, S. Friedl, *Metabelian $SL(n,\mathbb C)$ representations of knot groups IV*, arXiv:1209.4244.
* H. Huang, M. Perlman, C. Polini, C. Raicu, A. Sammartano, *Relations between the $2\times2$ minors of a generic matrix*, arXiv:1909.11705.
* D. Silver, S. Williams, *Mahler measure, links and homology growth*, Topology **41** (2002).

*Living research notes: `ideas/cocycle-combinatorics/` (RATIONALE, STRUCTURE, LOG, drafts); approaches under `approaches/`.*
