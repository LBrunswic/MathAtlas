# Classification of r = 1 families, and a verified decision procedure

*2026-10-30. Lean: `lean/Syracuse/Approaches/R1/{LPoly,Family,Decide,Examples}.lean`. Every result
is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); the instances are evaluated in the
kernel with `decide +kernel`, not `native_decide`. Math uses `\lt`/`\gt`.*

## 1. Setting

An **r = 1 family** has one parameter $a\ge0$ and words
$$W(a)=s_0\,\beta_1^{m_1a+c_1}\,s_1\cdots\beta_k^{m_ka+c_k}\,s_k,$$
where the $s_i$ are fixed words and every block with $m_i\ge1$ has the same slope
$|\beta_i|/\mathrm{len}\,\beta_i=p/q$. This is the one-parameter, equal-slope case of the criterion
in [`RATIONALE.md`](RATIONALE.md) §3. In Lean the family is a `Family` (`p`, `q`, and a list of
`Seg.fixed w` / `Seg.grow β k m c` with $|\beta|=kp$, $\mathrm{len}\,\beta=kq$), checked by
`Family.okB`.

A member is a **cycle word** (`IsCycleWord`) when $W(a)\ne\varnothing$ and $D\mid S$. This includes
negative cycles; `isSyrCycle_of_dvd` turns it into an `IsSyrCycle`.

## 2. Closed form (`Family.closed`, `Family.D_closed`)

Put $s=(3^q)^a$, $t=(2^p/3^q)^a$, $N=\sum_i k_im_i$ and $\mu=\prod_i(2^{|\beta_i|}-3^{\mathrm{len}\beta_i})\ne0$.
There are computable $\gamma\in\mathbb Q[t]$ with $\deg\gamma\le N$, and integers $x_c,y_c\ge1$, such
that for every $a$:
$$\mu\,S(W(a))=s^N\gamma(t),\qquad D(W(a))=s^N\delta(t),\qquad \delta=x_ct^N-y_c .$$
The proof is by induction over segments, from $S(uv)=3^{\mathrm{len}v}S(u)+2^{|u|}S(v)$ and
$D(\beta)\,S(\beta^n)=S(\beta)\,D(\beta^n)$ (`S_wpow`, `D_wpow`).

## 3. The theorem

Let $h=\gcd(\delta,\gamma)$ in $\mathbb Q[t]$ and $\delta=h\delta'$.

> **Classification (`classification`, `decideR1_correct`).** Let $W$ be a valid r = 1 family with $N\ge1$.
> 1. **Finite case, $\deg\delta'\ge1$.** The cycle set is a finite, explicitly computed list. Every
>    cycle member has $a\lt a_0$, where $a_0$ is the first parameter that passes an explicit
>    growth test (`Family.finite_bound`).
> 2. **Constant case, $\deg\delta'=0$.** The fixed point $x^\ast=S(W(a))/D(W(a))$ is the **same
>    rational number for every $a$** (`const_ratio`). So either every member with $a\ge1$ is a cycle
>    or none is (`const_case`), and $a=0$ is checked on its own.
> 3. **Powers of one cycle (`const_one_orbit`).** In case 2, if some member is a cycle then one
>    integer $x$ starts all of them: $W(b)=\mathrm{gapWord}(x,\mathrm{len}\,W(b))$ for every
>    $b\ge1$. Every $W(b)$ is a power of the primitive cycle word of $x$.
>
> When $N=0$ the family is constant (`Family.word_const`).

**Corollary.** An r = 1 family has infinitely many cycle members iff it is, from $a=1$ on,
(a reparametrisation of) the powers of a single cycle word. Every other r = 1 family has finitely
many cycle members. The bound is effective and elementary: no linear-forms-in-logarithms input is
needed, because the slope $p/q$ is rational and $2^p\ne3^q$.

### Proof of case 1: the product formula

- **Integrality.** Clear denominators with $L$, and evaluate $L h$, $L\delta'$, $L\gamma'$ and the
  Bézout cofactors $Lu$, $Lv$ homogeneously at $(z,s)=(2^{pa},3^{qa})$. This gives integers
  $\hat H,\Delta,\Gamma,\hat U,\hat V$ (`homZ`), with
  $$L^2D=\hat H\Delta,\qquad L^2\mu S=\hat H\Gamma,\qquad L^2s^K=\hat U\Delta s^{e_1}+\hat V\Gamma s^{e_2}.$$
- **Divisibility.** On a cycle, $D\mid S$ gives $\Delta\mid\Gamma$, hence $\Delta\mid L^2s^K$.
- **Coprimality.** $\Delta\mid L^2D$, and $D$ is coprime to $s=3^{qa}$. So $\Delta\mid L^2$, i.e.
  $|\Delta|\le L^2$, i.e. $|D|\le|\hat H|$.
- **The places.** This is the product formula: units at 2 and 3, the Bézout constant at $p\mid D$.
- **Growth at ∞.** $|D|\ge A\alpha^a-B_0\beta_0^a$, while
  $|\hat H|\le\sum_i|c_i|\beta_i^a$ with every $\beta\le\alpha-1$, because $\deg h\lt N$.
  - The test $g(a)=A\alpha^a-B_0\beta_0^a-\sum|c_i|\beta_i^a\gt0$ forces $|D|\gt|\hat H|$.
  - Once true it stays true, since $g(a+1)\ge\alpha g(a)$ (`gval_succ`).
  - It is true at the explicit Bernoulli bound $a_{\max}=(\alpha-1)\lceil B\rceil+1$ (`gval_amax`).

### Proof of case 2

- If $\delta'=c$ is constant then $\deg h=N$.
- Since $\deg\gamma\le N$, $\gamma'$ is constant too, so $\gamma=\kappa\delta$.
- Hence $S=\kappa\mu^{-1}D$ for all $a$.

## 4. The algorithm (`decideR1`)

Everything is computable by structural recursion and runs in the kernel.
1. Compute the closed-form data, $\delta$ and $\gamma$ (`Family.data`).
2. Run extended Euclid over $\mathbb Q$ (`egcd`, with fuel; `xgcd_spec` proves $h=u\delta+v\gamma$,
   $h\mid\delta$, $h\mid\gamma$). Then do exact division $\delta'=\delta/h$, $\gamma'=\gamma/h$
   (`ldiv_spec`), which gives $u\delta'+v\gamma'=1$.
3. If $N=0$: decide $a=0$, and the answer is constant.
4. If $\deg\delta'=0$: decide $a=0$ and $a=1$; the verdict is `allFrom 1 _` or `finite _`.
5. Otherwise, search for the first $a_0\le a_{\max}$ passing the growth test (`firstPos`, which is
   proved to stop), enumerate $a\lt a_0$ exactly, and return `finite l`.

- **Correctness and totality (`decideR1_correct`):** for every valid family and every $a$,
  `IsCycleWord (F.word a) ↔ (decideR1 F).mem a`.
- **Use:** `decideR1_iff (F := F) (v := v) (by decide) (by decide +kernel)`.
- **Test:** a tampered verdict is rejected by the kernel.

## 5. Decided families (`Examples.lean`)

| family | verdict |
|---|---|
| $1^a\,2\,1^a\,3\,1^a$ (`twoRunWord 1 2 3`) | none |
| $3^a\,1\,3^a\,2\,3^a$ | $a=0$ only ($[1,2]$, the −5 cycle) |
| $(1,2)^a\,1\,(1,2)^{2a}\,4$ | none |
| $2^a\,1\,2^{a+1}\,3$ | none |
| $(1,3)^a\,2^a$ (degenerate: $h=z-s$) | none |
| $(1,2)^a$ | every $a\ge1$ (constant $x^\ast=-5$) |
| $2^a$, $1^a$ | every $a\ge1$ (the cycles 1 and −1) |
| $1^a\,2\,1\,1\,4$ | $a=3$ only (the −17 cycle) |

A randomized suite (`r1_lean.py suite 60 7`, 70 families including these) compares Lean's `#eval
decideR1` with brute force on $a\le30$: **0 mismatches**, and 9 of the 70 families have cycles.

## 6. The families $w^aw'$, uniformly (`WPow.lean`)

With one growing block, the forms are *linear* in $[z:s]$. The resultant is
$3^{\mathrm{len}w'}C(w,w')$, where $C(w,w')=D(w)S(w')-D(w')S(w)$ is the $q$-free core of
`cycle-gcd/periodic-words.md`. The whole classification follows from one ring identity
(`wpow_append_identity`):
$$D(w)\,S(w^aw')-S(w)\,D(w^aw')=X^{a|w|}\,C(w,w').$$
- **$C\ne0$:** every cycle word $w^aw'$ has $D(w^aw')\mid C(w,w')$ (`wpow_append_dvd`), so
  $|D|\le|C|$, and only finitely many $a$ give cycles (`wpow_append_finite`).
- **$C=0$:** $w$ and $w'$ share the fixed point $S(w)/D(w)$, and $w^aw'$ is a cycle word iff $w$ is
  (`wpow_append_const`).

`wpow_append_classification` states both cases, uniformly in $(w,w')$. For the exact cycle set of a
concrete pair, use `decideR1 (wpowFamily w w')` (`wpowFamily_word`).

Example: $(1,2)^a\,4$ has $C=-66=-2\cdot3\cdot11$ and no cycles, decided by the kernel.

## 7. Beyond one growing exponent

- **Nested families and towers** (multiplicative exponents): see [`NESTED.md`](NESTED.md). A tower
  meets only finitely many cycles (`R1.tower_cycleStarts_finite`).
- **Skeleton families** (several blocks sharing one exponent): uniform ceilings in the cocycle data of
  the words. See [`SKELETONS.md`](SKELETONS.md).
- **Two independent exponents on the same side** (`u^a x v^b y`, r = 2 but no Baker input): the
  linear form `D(v)·C(u, x v^b y) = α 2^{b|v|} − β 3^{b len v}` bounds `a`; each fixed `a` is a
  `w^a w'` family in `b` after rotation. Finitely many cycles off the two degenerate loci
  (`R1.twoExp_classification`).
  Any sides, including straddling, conditional on Matveev: `R1.twoExp_cycles_of_matveev`, with the
  effective decider `decide_twoexp.py` ([`PATTERNS.md`](PATTERNS.md) §6).
- **Which families cover which words**: the pattern-intersection chart and its exclusive witnesses,
  [`PATTERNS.md`](PATTERNS.md).

## 8. Scope and what is not claimed

- **r ≥ 2 is out of scope.** That means two slopes, or two independent lengths. There the
  elimination ideal is zero, and `Vojta.lean` gives only a conditional statement.
- **Lean covers only the integer case of "constant $x^\ast$ ⇒ powers of one word".** For a
  non-integer $x^\ast\in\mathbb Z_2$ the same conclusion holds 2-adically, because a periodic
  2-adic point has a unique parity word. That is not formalized.
- **Speed of the kernel run.** It depends on $a_0$ and on the word lengths below $a_0$. All the
  families above check in a few seconds.
