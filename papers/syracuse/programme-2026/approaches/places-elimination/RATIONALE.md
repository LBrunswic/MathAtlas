# places-elimination — the cocycle over Spec ℤ[1/6], the elimination criterion, and Vojta

*Written 2026-10-29. This records the conclusion of a design discussion about which algebro-geometric
structure captures the Syracuse cocycle, and what it buys. Math uses `\lt`/`\gt`. Lean:
`lean/Syracuse/Approaches/TwoRun.lean` and `lean/Syracuse/Approaches/Vojta.lean`. Decider:
[`decide_family.py`](decide_family.py).*

---

## 0. Summary

1. **The base is Spec ℤ[1/6], and the cocycle carries no global information.**
   - For S = {2, 3, ∞}, the Syracuse character is an isomorphism
     $\chi: H_1(F_2)\to\mathcal O_S^\times/\pm1$.
   - The cocycle class generates $H^1(F_2;\mathbb Z[1/6]_\chi)\cong\mathbb Z[1/6]$.
   - All the content is in the restrictions $H^1(\langle w\rangle)=\mathbb Z/D(w)$.
2. **The pattern exclusions are a product-formula argument.**
   - At 2 and 3, the run coordinates are units.
   - At $p\mid D$, there is divisibility.
   - At ∞, Matveev (or an elementary growth bound) applies.
   - The element the product formula is applied to is an equation of the image of an *incidence
     variety*. It exists **iff a projection is not dominant**, and a dimension count decides that.
3. **Criterion.**
   - **r = 1** (one growing parameter, all growing blocks of equal slope $|\beta|/\mathrm{len}\,\beta$):
     a resultant is an $o$-independent core. Elementary.
   - **r ≥ 2** (two slopes, or two independent lengths): no polynomial core exists at all. This is
     the regime of Vojta's conjecture for blow-ups, whose $S$-unit case is Levin's theorem.
   - *Refined 2026-10-30, see [`SCHEME.md`](SCHEME.md).* This is about **full** cores. Partial
     (rotation) cores settle every $r\ge2$ family inside the tropical budget $\min(A,B)\lt1$, with
     Matveev alone. Vojta is needed only outside that budget.
4. **The open `TwoRunNoGo` family $d^a e_1 d^a e_2 d^a$ is r = 1**, and has a uniform ceiling:
   $$|D|\ \Big|\ \operatorname{sixfree}\Big(4^{e_1}(2^d-2^{e_2})^3+3\cdot2^{e_2}(2^d-2^{e_1})^3\Big),$$
   which is nonzero unless $e_1=e_2=d$. Full exclusion follows from finitely many checks, all proved in
   Lean. `TwoRunNoGo` asks only for *unit* combinations of rotations, which is the wrong question for
   exclusion.

---

## 1. The places dictionary

The two branches $a(z)=(3z+1)/2$ and $b(z)=z/2$ define
$\rho:F_2\to\mathrm{Aff}_1(\mathbb Z[1/6])=(\mathbb G_a\rtimes\mathbb G_m)(\mathbb Z[1/6])$, the Borel of
$\mathrm{PGL}_2$.

- **Why ℤ[1/6] is forced.**
  - $\mathcal O_S^\times=\pm2^{\mathbb Z}3^{\mathbb Z}$ has rank $2=\operatorname{rk}H_1(F_2)$, and $\chi$ is an
    isomorphism onto it modulo ±1.
  - $\chi(x)-1$ is a unit for both generators (it is $2$ and $-\tfrac12$). So the coboundaries are a
    direct summand, $H^1(F_2;\mathbb Z[1/6]_\chi)\cong\mathbb Z[1/6]$, and $[S]$ is a generator.
- **One word.** $H^1(\langle w\rangle)=\mathbb Z[1/6]/(\chi(w)-1)=\mathbb Z/D$. The following are
  equivalent:
  - $w$ is a cycle;
  - $\operatorname{res}_w[S]=0$;
  - $M(w)\equiv$ scalar in $\mathrm{PGL}_2(\mathbb Z/D)$;
  - $\rho(w)$ is diagonalisable over $\mathbb Z[1/6]$;
  - the fixed-point sections $\infty$ and $[S:D]$ of $\mathbb P^1_{\mathbb Z[1/6]}$ are disjoint.
  
  Their finite intersection number is $\log|D/\gcd(D,S)|$.
- **Universal family.** Take the character torus $\mathbb T=\mathbb G_m^2=\operatorname{Spec}\mathbb Z[X^\pm,Y^\pm]$
  with the Syracuse section $\sigma=(2,3):\operatorname{Spec}\mathbb Z[1/6]\to\mathbb T$.
  - $K_w=V(D_w)$ is a subtorus; its components are the period factors.
  - $\mathrm{Triv}_w=V(D_w,S_w)$ is the locus where $w$ acts trivially. It depends only on the
    conjugacy class, because rotations differ by units mod $D$.
  - Cycle $\iff\sigma^{-1}(\mathrm{Triv}_w)=\sigma^{-1}(K_w)$, as schemes.
  - $\gcd(D,S)$ is the generalised gcd, i.e. the height relative to the blow-up of $\mathrm{Triv}_w$
    (Silverman).
- **Cores.** $C(u,v)$ is the translation part of the commutator $[\rho(u),\rho(v)]$, and $V(C)$ is where
  $u,v$ share a fixed point.

## 2. Two barriers for any uniform method

- **The 3x+k barrier.**
  - Conjugating by $z\mapsto kz$ turns $(3z+1)/2$ into $(3z+k)/2$. This is the same representation
    over $\mathbb Z[1/6k]$: a cycle of $3x+k$ is exactly a word with $D\mid kS$.
  - Every positive word is a cycle of $3x+k$ for $k=|D|/\gcd(D,S)$.
  - Lagarias (1990): infinitely many $k$ have $\ge k^{1-\varepsilon}$ cycles.
  - **So a method that is insensitive to inverting more primes cannot exclude a single word.** This
    covers everything over $\mathbb Z[X,Y]$, $\mathbb Q[X,Y]$ or the character torus over ℤ. It is the
    structural reason the Layer-1 programme
    ([`ideas/cocycle-combinatorics/STRUCTURE.md`](../../ideas/cocycle-combinatorics/STRUCTURE.md)
    R1–R4, McMullen, Boden–Friedl) closed.
- **The counting barrier.**
  - A critical stratum has $\binom{E-1}{o-1}\approx2^{0.950E}$ words, since the binary entropy at
    $o/E=1/\log_23$ is 0.950.
  - Against that, $|D|\ge3^{o(1-\varepsilon)}\approx2^{E(1-\varepsilon)}$.
  - So the expected number of hits per stratum is $\approx2^{-0.05E}$. Equidistribution, point
    counting and exponential sums give "expected ± error" and cannot certify zero.

## 3. The elimination criterion

Take a family with fixed spacer words and growing blocks $\beta_i^{m_ia+c_i}$.

- **Run coordinates.** If all growing blocks have slope $p/q$, put $z=X^{pa}$ and $s=Y^{qa}$. Then
  $D$ and $G=S\cdot\prod(X^{|\beta|}-Y^{\mathrm{len}\beta})$ are **homogeneous forms in $[z:s]$**, and
  $z,s$ are $6$-units at $(2,3)$.
- **Incidence variety.** $\mathcal V_F=V(D,G)\subset\mathbb T\times T_F$, over $\mathbb Z[1/6]$.
- **The criterion.** An $o$-independent core exists iff $\mathcal V_F\to\mathbb T$ is not dominant. It
  is an equation of the image, here the resultant $\operatorname{Res}_{[z:s]}(D,G)$.
- **The dimension count.** $\dim\mathcal V_F=r$, where $r$ is the dimension of the projectivised run
  space. So $r=1\Rightarrow$ core, and $r\ge2\Rightarrow$ generically no core.

Verified by Gröbner elimination done inside the torus (with saturation; [`elim.py`](elim.py)):

| family | r | elimination ideal ∩ ℚ[X,Y] |
|---|---|---|
| $1^a\,2\,1^a\,3\,1^a$ (`twoRunWord 1 2 3`) | 1 | $(X-1)(X^4+3X^3+3X^2+X+Y)$, up to a monomial |
| $1^a\,3\,2^a$ (two slopes) | 2 | 0 |
| $1^a\,2\,1^b\,3$ (two lengths) | 2 | 0 |

## 4. The two-run family $d^a e_1 d^a e_2 d^a$

Write $P=X^d$, $Q_i=X^{e_i}$, $u=Y^a$, $v=X^{da}$.

- **Closed forms.**
  - $D=Q_1Q_2v^3-Y^2u^3$.
  - $(X^d-Y)S=PQ_1uv^2+PYu^2v-Q_1Q_2uv^2+Q_1Q_2v^3-Q_1Yu^2v-Y^2u^3$.
- **Certificate.** $v^5\,Q_1Q_2\,R^*=A\,D+B\,G$, with
  $R^*=Q_1^2(P-Q_2)^3+YQ_2(P-Q_1)^3$; $R^*$ is the resultant up to the monomial $-Q_1Y^4$.
- **Ceiling.** At $(2,3)$ the units drop out, so every cycle has $D\mid R^*(2^d,2^{e_1},2^{e_2},3)$.
- **Nonvanishing.** $R^*(2^d,2^{e_1},2^{e_2},3)=4^{e_1}x^3+3\cdot2^{e_2}y^3$, where $x=2^d-2^{e_2}$ and
  $y=2^d-2^{e_1}$. The two terms have 3-adic valuations $3v(x)$ and $1+3v(y)$, so the sum vanishes
  only when $x=y=0$, i.e. $e_1=e_2=d$.
- **Growth.** The slope $d$ is an integer, so the family is never critical. $|D_a|$ grows
  geometrically, and no Baker bound is needed.

| $(d,e_1,e_2)$ | $R^*(2,3)$ | ceiling | cycles |
|---|---|---|---|
| (1,2,3) | −3648 | 19 | none |
| (2,1,3) | −64 | 1 | none |
| (1,3,2) | −3104 | 97 | none |
| (3,1,2) | 2848 | 89 | $a=0$ only: $[1,2]$ is the −5 cycle |
| (1,1,2) | −32 | 1 | $a=0$ only |

**Update 2026-10-30.** The r = 1 case is now fully classified, with a verified decision procedure.
See [`CLASSIFICATION.md`](CLASSIFICATION.md).

## 5. r ≥ 2: Vojta for blow-ups, Levin's theorem

For $r\ge2$ the product formula has to be applied at the **point**.

- **The setting.** The run coordinates $t(L)$ (e.g. $(3^a,2^{da},3^b,2^{db})$) form a 6-smooth point of
  $\mathbb G_m^n$. On a cycle, $\operatorname{gcd}_{6'}(F(t),G(t))=|D|$.
- **The theorem that applies.** Vojta's conjecture for the blow-up of $\mathbb G_m^n$ along $V(F,G)$,
  restricted to $S$-unit points, is **Levin's theorem** (Invent. Math. 215, 2019; Subspace Theorem).
  - Outside finitely many translates of proper subtori,
    $\log\gcd_{6'}(F(t),G(t))\le\varepsilon\,h(t)+C$.
  - With $h(t)\le\kappa\,o$ and $|D|\ge B(o)$ (Rhin/Matveev), this bounds $o$.
- **What Lean proves (conditional).** `Vojta.cycles_of_levin`: cycles of the family lie in finitely many
  exceptional character level sets, or have length $\le O$. `Vojta.twoLen_cycles_of_levin` instantiates
  it for $d^a e\,d^b f$.
- **What is not covered.**
  - The result is **ineffective**: the exceptional set is not computable from the Subspace Theorem.
  - The constants depend on the number of runs, so uniformity over arbitrary words is out of reach.
    That would need a conjectural uniform version beyond Vojta, and the counting barrier of §2
    suggests no such statement reaches high-complexity words.
- **The exceptional sets are decidable when slopes are equal.** For $u^av^b$ with equal slopes, each
  rational line $(a,b)=(pt+a_0,qt+b_0)$ is an $r=1$ family and is decided by §4's method
  (`decide_family.py twoword`). With different slopes, even lines are $r=2$.

## 6. Caveats and open points

- **Levin's exceptional set.** Its exact form should be re-checked against the PDF (not yet in
  `sources/`). `Vojta.lean` states a deliberately weaker form: character level sets, sum of heights,
  integer 6-smooth points.
- **A claim in `PROGRAM.md` §3.** It says $|2^E-3^o|\ge3^{o(1-\varepsilon)}$ is conjectural. I believe
  it is known *ineffectively*, from Ridout's theorem; what is open is the polynomial-loss version.
  This needs verifying before PROGRAM.md is changed.
- **Degenerate r = 1 families.** Here $D$ and $G$ share a factor $h$ (e.g. $(1,3)^a2^a$, $h=z-s$).
  The decider gives a ceiling for $D/h$, but the growth of $D/h$ is checked numerically only.
- **Lean coverage.** Lean instances are emitted for the `twoRunWord` family, which is uniform in
  $(d,e_1,e_2)$. Other $r=1$ families are decided by the script with a sympy-checked certificate, not
  in Lean.

## References

- A. Levin, *Greatest common divisors and Vojta's conjecture for blowups of algebraic tori*,
  Invent. Math. 215 (2019) 493–533.
- J. H. Silverman, *Generalized greatest common divisors, divisibility sequences, and Vojta's
  conjecture for blowups*, Monatsh. Math. 145 (2005); arXiv:math/0407415.
- Y. Bugeaud, P. Corvaja, U. Zannier, *An upper bound for the G.C.D. of aⁿ − 1 and bⁿ − 1*,
  Math. Z. 243 (2003).
- J. C. Lagarias, *The set of rational cycles for the 3x+1 problem*, Acta Arith. 56 (1990).
