# Nested families and towers

*2026-10-30. Lean: `lean/Syracuse/Approaches/R1/Nested.lean` (the level-2 family, with explicit
structure) and `lean/Syracuse/Approaches/R1/Tower.lean` (towers of any depth). Both are axiom-clean.
Math uses `\lt`/`\gt`.*

A **tower** has a base word $u_0$ and suffixes $u_1,\dots,u_k$. Its members are
$$T(a_1,\dots,a_k)=\big(\cdots\big((u_0^{a_1}u_1)^{a_2}u_2\big)^{a_3}\cdots\big)^{a_k}u_k .$$
- Exponents enter **multiplicatively**: the length is a polynomial in $(a_1,\dots,a_k)$, not an
  affine function.
- So a tower is not an r = 1 family, nor a run-torus family of any rank. The elimination picture of
  [`RATIONALE.md`](RATIONALE.md) §3 does not apply as stated.
- Depth 1 is $w^aw'$ ([`CLASSIFICATION.md`](CLASSIFICATION.md) §6). Depth 2 is $(w^aw')^bw''$.

## 1. Depth 2: $(w^aw')^bw''$, explicitly (`Nested.lean`)

Write $v_a=w^aw'$, $Z=2^{a|w|}$ and $T=3^{a\,\mathrm{len}w}$.

- **Plücker step** (`nested_identity`, valid in any commutative ring):
  $$D(w)\,C(v_a,w'')=D(v_a)\,C(w,w'')-2^{a|w|}D(w'')\,C(w,w').$$
  So $D(w)\,C(v_a,w'')=\alpha Z-\beta T$, where $\alpha=2^{|w'|}C(w,w'')-D(w'')C(w,w')$ and
  $\beta=3^{\mathrm{len}w'}C(w,w'')$ (`nested_linear`).
- **Zero set.**
  - Generically, $C(v_a,w'')=0$ for at most one $a$ (`nested_zero_subsingleton`).
  - If $\alpha=\beta=0$, then $C(v_a,w'')=0$ for every $a$ (`nested_zero_all`). This happens iff
    $C(w,w'')=0$ and ($C(w,w')=0$ or $w''=\varnothing$).
- **Joint bound** (`nested_exceptional_finite`): only finitely many $a$ admit a cycle with $b\ge2$
  and $C(v_a,w'')\ne0$.
  - The ceiling gives $|D(v_a^bw'')|\le|C(v_a,w'')|\le K(Z+T)$.
  - The dominant side of $2^{|w|}$ versus $3^{\mathrm{len}w}$ gives $|D(v_a^bw'')|\ge(Z+T)^2/8$ for
    large $a$ and every $b\ge2$.
  - So $Z+T\le8K$.
- **Classification** (`nested_classification`). The cycle members are:
  - $b=0$: the word $w''$;
  - $b=1$: the family $w^a(w'w'')$, classified by `WPow`;
  - $b\ge2$, $C\ne0$: **finitely many** pairs $(a,b)$;
  - $b\ge2$, $C=0$: here $v_a^bw''$ is a cycle word iff $v_a$ is. The set of such $a$ is empty, one
    point, or everything.

No hypothesis on the slopes of $w'$ or $w''$ is needed. Since $2^{|w|}\ne3^{\mathrm{len}w}$, one side
dominates as $a\to\infty$.

## 2. Towers of any depth (`Tower.lean`)

> **Tower theorem (`tower_cycleStarts_finite`).** For a nonempty positive base $u_0$ and positive
> suffixes $u_1,\dots,u_k$, the integers $x$ that start a cycle whose gap word lies in the tower
> (all exponents $\ge1$) form a **finite** set. A tower therefore meets only finitely many cycles; a
> cycle may still occur as infinitely many powers.

The proof is elementary, uses no linear forms in logarithms, and works by induction on the depth.
The invariant is **tameness** (`Tame`). A set $V$ of positive words is tame when:
1. **its fixed points are bounded:** $S(v)\le c\,|D(v)|$ for all $v\in V$;
2. **it is band-finite:** for every $R$, only finitely many $v\in V$ have $R^{-1}\le2^{|v|}/3^{\mathrm{len}v}\le R$.

The steps:
- **Base case** (`tame_finite`): finite sets are tame.
- **The step $V\mapsto\{v^bu:v\in V,b\ge1\}$ preserves tameness** (`tame_step`).
  - *Band-finiteness:* $2^{|v^bu|}/3^{\mathrm{len}\,v^bu}=\rho(v)^b\rho(u)$, so a member in a band forces
    $v$ into a band. Then $b$ is bounded, because $\rho(v)\ne1$ (`step_band`, `finite_exponents`).
  - *Fixed points:* outside the band $[1/3,3]$, $|D|\ge\frac23\max(2^{|W|},3^{\mathrm{len}W})$. Also
    $S(v^bu)=3^{\mathrm{len}u}S(v^b)+2^{b|v|}S(u)$ with $S(v^b)=x^\ast(v)D(v^b)$.
- **Cycles at one step** (`tame_cycles`). On a tame $V$, a cycle $v^bu$ with $b\ge2$ and $C(v,u)\ne0$
  has
  $$\tfrac23\max(v)^2\le|D(v^bu)|\le|C(v,u)|\le K\max(v),$$
  outside a finite exceptional set, where $\max(v)=\max(2^{|v|},3^{\mathrm{len}v})$. So $\max(v)$ is
  bounded and only finitely many $v$ remain.
- **Degenerate step** (`start_const`). If $C(v,u)=0$ then $v^bu$ and $v$ have the same fixed point,
  so the start point is counted one level down.
- **Decomposition** (`cycleStarts_step`). The start points of a step lie in three pieces:
  - the starts of the $b=1$ part. That part is again a tower of the same depth, with the last two
    suffixes merged (`appendSet_step`);
  - a finite set;
  - the starts of the previous level.

### What this covers, and what it says

- **It covers a lot.** Every finite nesting of powers with fixed base words is covered. This includes
  $(w^aw')^bw''$, $((w^aw')^bw'')^cw'''$, and so on. Families with some exponents $0$ are finite
  unions of towers with fewer levels, so the theorem extends to them.
- **It is a finiteness statement about cycles, not words.** A tower can contain infinitely many cycle
  words (e.g. $(1,2)^a$: the −5 cycle repeated). It cannot contain infinitely many *cycles*.
- **Sanity check.** Brute force on twelve towers (exponents up to 5–7) finds only start points from
  the known cycles:
  - −5 in $1^a2$;
  - −17 in $1^a(1,1,2,1,1,4)$;
  - −25 (on the −17 cycle) in $(1^a\,2114)^b1$;
  - −7 (on the −5 cycle) in $2^a1$.
- **Contrast with the skeleton route** ([`SKELETONS.md`](SKELETONS.md)). Skeleton families have
  linear exponents and get explicit polynomial ceilings. Towers have multiplicative exponents and get
  a qualitative finiteness theorem. They are finite in the same sense, with a different engine.

## 3. Not covered

- **Explicit bounds for towers.** The Lean proof gives finiteness. The constants exist but are not
  extracted, and depth 2 alone is explicit (`nested_exceptional_finite`).
- **Words with several independently growing blocks at the same level**, such as $u^av^b$. That is
  r = 2, where Levin/Vojta is the relevant tool ([`RATIONALE.md`](RATIONALE.md) §5).
