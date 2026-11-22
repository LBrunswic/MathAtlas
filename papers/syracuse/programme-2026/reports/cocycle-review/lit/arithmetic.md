# Literature review — theme `arithmetic` (gcd of S-unit expressions, |2^E − 3^o|, primitive divisors)

*Agent: arithmetic. Date: 2026-10-30. 70 entries: 62 verified (quote from a fetched page) and 8 with verified metadata only (statement not fetched, or quoted from a secondary). Bibliography lines: `bib-arithmetic.jsonl`.*
*Math is written with `\lt` / `\gt` where needed. Everything marked **(derived here)** is my own algebra, checked by hand but not machine-checked. Rules forbade running experiments, so each such item comes with a cheapest first test for the engine.*

---

## 1. Executive summary

The literature confirms F1 and sharpens it. G = gcd(S, D) is a gcd of S-unit expressions in exactly the sense of Bugeaud–Corvaja–Zannier, Corvaja–Zannier and Levin. Cut a word into m runs and put t_i = (2^{d_i}/3)^{L_i}. Then (∏(2^{d_i}−3))·S and D become two fixed polynomials in the m S-units t_i (§3). That gives a hierarchy:

* **1 growing run.** The gcd divides a resultant: effective, o-independent, and exactly the bounded-defect lever.
* **2 growing runs.** G | (2^{|d₁−d₂|}−1)·gcd(2^{d₁L₁}−3^{L₁}, 2^{d₂L₂}−3^{L₂}), a Corvaja–Zannier gcd(u−1, v−1). With Ellison this excludes two-run {1,2} cycles elementarily.
* **m runs, m fixed.** Levin gives G ≤ e^{εo} outside finitely many subtorus families, ineffectively. The cyclotomic families are computable (Laurent; Aliev–Smyth).
* **Unboundedly many runs (balanced words).** Nothing applies: every theorem is for a fixed polynomial.

Two further limits:
1. **The 6-free axis gains only ε.** Evertse 1984 and Bugeaud–Evertse 2017: a bounded-term ceiling with growing exponents has sixfree(C) ≥ |C|^{1−ε} (effectively ≥ |C|^{c₁}).
2. **The record measure.** Bondareva–Luchin–Salikhov 2018 give μ(log₂3) ≤ 5.116201. This governs Λ asymptotically and beats Rhin's 13.3, but only beyond an unstated H₀.

Primitive-divisor theory (Zsigmondy, BHV, Stewart) reaches D only through gcd(E, o) and periodic words.

**Strongest hooks** (labels as in §2): H1 run-telescoping plus Corvaja–Zannier (closes m = 2); H2 lever = resultant; H5 6-free part ≈ size; H6 an explicit H₀ for BLS 2018; H3 and H4 Levin plus Laurent for fixed m.

---

## 2. Idea → hook map

| # | idea | source(s) | touches | what it would give | verdict | cheapest first test |
|---|---|---|---|---|---|---|
| H1 | **Run-telescoping**: (∏c_i)S ≡ C_m (mod D), with C_m an m-term S-unit sum (§3.1). For m=2, G divides (2^{|Δd|}−1)·gcd(A₁,A₂). | Corvaja–Zannier 2005; Hernández–Luca 2003; BCZ 2003; Ellison 1971 | F1, F2, OP3, OP1 | m=2 closed elementarily (Ellison: no {1,2} two-run positive cycle with E>27). Qualitatively G ≤ e^{εo} for both runs long, i.e. k(w) ≥ \|D\|^{1−ε}. | **keep** | Engine: check G \| (2^{\|Δd\|}−1)gcd(A₁,A₂) for d∈{1..6}², L ≤ 80; check (∏c)S − C_m = c'_m·D symbolically. |
| H2 | **Lever = resultant**: for βd^L, S/3^L and D/3^L are linear in t=(2^d/3)^L, and their resultant is ±(S(βd) − S(dβ)) times 2^{\|β\|} (§3.2) | (elementary; Levin's hierarchy n=1) | OP3, F2 | Explains *why* the lever is o-independent. Gives the general rule "one growing run ⇒ resultant ceiling", which carries over to *any* rank-1 sub-family. | **keep** | Symbolic check of Res identity in ℤ[X,Y]. |
| H3 | **Levin's gcd theorem for fixed m**: N_gcd,S(F(t), ∏t−1) < ε·max h(t_i) off a finite union Z of subtorus translates | Levin 2019; Corvaja–Zannier 2005; Huang–Levin 2022; Grieve–Wang | OP3, F2, F4 | For each fixed m and letter tuple: G ≤ e^{εo} except on families with affine relations among the (L_i) (§3.3). Ineffective. | **open** (qualitative only) | List the subtori Z for m=3 by hand; check whether F and ∏t−1 share a factor on each. |
| H4 | **Torsion-coset computation** of the exceptional families (the cyclotomic-collapse locus) | Laurent 1984; Aliev–Smyth 2007; Lam–Leung; Conway–Jones | OP3 | A *finite effective* list of the sub-families where gcd can stay large (periodic and other collapses). The ineffective part is then confined to Levin's ε-bound. | **keep** | Run Aliev–Smyth-style search on F\|_H for m=3, letters {1,2,3}. |
| H5 | **The 6-free part of bounded-term ceilings ≈ size**: sixfree(C) ≥ c·\|C\|^{1−ε} (ineffective), ≥ \|C\|^{c₁} (effective, dominant root) | Evertse 1984; Bugeaud–Evertse 2017; Gross–Vincent 2013; Bugeaud–Evertse–Győry 2018 | §2 of PROGRAM ("exclusion lives on the 6-free axis"), OP1, OP4 | The 6-free axis beats the size axis by at most \|C\|^ε, unless C is constant (lever) or the number of terms is unbounded. So f(w) must come from *size* cancellation or from many-term structure. | **keep** (as a limit) | Engine: plot log sixfree(C)/log\|C\| for one-parameter ceilings C_L; expect → 1. |
| H6 | **Record measure μ(log₂3) ≤ 5.116201** (ν(1,ln2,ln3) ≤ 4.116201) | Bondareva–Luchin–Salikhov 2018; Wu–Wang 2014; Zudilin 2004; Draper–Saad 2026 | F3, PROGRAM §3 | Λ > E^{−4.1163} for E ≥ H₀, against Rhin's E^{−13.3}. It would pull the bounded-ceiling threshold o≈60 down a lot, *if* H₀ were explicit. | **open** | Read BLS 2018 §§2–4 for an explicit H₀. If none is given, estimate H₀ from their asymptotic constants. |
| H7 | **Explicit size floors** for \|2^x − 3^y\| | Ellison 1971; Rhin 1987/SdW Lemma 12; Tijdeman 1973; Rozier–Terracol 2026; Gouillon; LMN; Laurent 2008; Matveev; Baker–Wüstholz | F3 | Confirms F3's crossover (o≈570). Rozier–Terracol's packaging \|2^j−3^q\| > 2.56^q/2 for q>12 is directly citable. | **keep** | — (already in use) |
| H8 | **Pillai / small \|2^a−3^b\|**: the complete list of c with ≥2 representations | Bennett 2003; Stroeker–Tijdeman 1982; Scott–Styer 2004; Pillai 1931/36/45 | F3, "exceptional tier" | \|(N+1)^x − N^y\| = c has ≤1 solution except (N,c) ∈ {(2,1),(2,5),(2,7),(2,13),(2,23),(3,13)}, so the near-miss words are finite and listed. | **keep** | Enumerate words with \|D\| ∈ {1,5,7,13,23}. |
| H9 | **Primitive divisors of Φ_d(2^E, 3^o)** for periodic words and for g = gcd(E,o) ≥ 2 | Zsigmondy 1892; Bang 1886; BHV 2001; Stewart 1977/2013; Schinzel 1962; GLNP 2017 | OP3, F4 | For A=2^E, B=3^o, every Φ_d(A,B) with d≥2 has a primitive prime ≡ 1 mod d (no exceptions). So G(w^r)/G(w) gains a new prime at each d \| r. Says *nothing* about D when gcd(E,o)=1. | **kill** (for D itself); keep for periodicity bookkeeping | — |
| H10 | **Largest prime factor P(2^a − 3^b)** with independent exponents | Bugeaud 2000; Bugeaud 2026; Győry–Yu 2006; Tijdeman 1973 | OP3 ("sixfree→∞") | Only (iterated-)log growth (effective). Useless next to \|D\| ≥ 2.56^o. D is coprime to 6, so sixfree(D) = \|D\| trivially. | **kill** | — |
| H11 | **gcd can be sub-exponentially large infinitely often** | Adleman–Pomerance–Rumely via Cohen–Sonn 2015 | F1, H1 | gcd(a^n−1, b^n−1) ≥ exp(exp(c log n/log log n)) for infinitely many n. On the diagonal L₁=L₂ the 2-run gcd can be large, but stays e^{o(o)}. | **keep** (calibration) | Engine: G on 1^n 2^n-type diagonals for smooth n. |
| H12 | **Large gcd ⇒ common division-sequence factor** | Granville 2022 | OP3 | Along any line in (L₁,L₂), "G large infinitely often" forces a shared cyclotomic (division-sequence) factor. Cyclotomic collapse is the *only* mechanism. | **keep** | — |
| H13 | **Function-field analogues** (Ailon–Rudnick, Silverman 2004, CZ 2008/2013, Ostafe, Levin–Wang, Brownawell–Masser, Mason–Stothers) | — | Layer 1 | These are the ℤ[X,Y]/ℂ[T] shadows. They are bounded and effective, but Layer 1 is already closed, and in char p they *fail* (Silverman 2004). | **kill** | — |
| H14 | **Unlikely intersections (BMZ) / new arithmetic conjecture (Campagna–Dill–Wilms 2026)** | BMZ 1999/2008; Campagna–Dill–Wilms 2026 | OP3 | Framework only. Our points live in a rank-2 S-unit group, not on a curve. CDW's dimension-1 case is exactly CZ. | **open/low** | — |
| H15 | **Uniformity in the number of terms** | Evertse–Schlickewei–Schmidt 2002; Erdős–Stewart–Tijdeman (not added) | F2 ((b) words) | Counts of non-degenerate solutions are explicit but super-exponential in n. No gcd theorem is uniform in n. | **kill** for (b) | — |

---

## 3. Quantitative analysis: what the gcd theorems give for (a) m-run words and (b) balanced words

### 3.1 The run-telescoped representative (derived here)

Let w = d₁^{L₁} d₂^{L₂} ⋯ d_m^{L_m} (cyclic, adjacent letters distinct), o = ΣL_i, E = Σd_iL_i. Put

* c_i = 2^{d_i} − 3 (odd, nonzero: −1, 1, 5, 13, 29, …),
* c'_i = ∏_{j≠i} c_j,
* t_i = 2^{d_iL_i}/3^{L_i},
* T_k = t₁⋯t_k (T₀ = 1, T_m = 2^E/3^o).

The geometric-series identity (X^d − Y)·S(d^L) = X^{dL} − Y^L and the cocycle S(uv) = Y^{len v}S(u) + X^{|u|}S(v) give

$$(\textstyle\prod_i c_i)\,S(w)=3^{o}\sum_{i=1}^{m} c'_i\,(T_i-T_{i-1}),\qquad D=3^{o}(T_m-1).$$

Replace T_m by 1, i.e. subtract c'_m·D:

$$C_m:=(\textstyle\prod c_i)S-c'_mD=3^{o}\Big[(c'_m-c'_1)+\sum_{k=1}^{m-1}(c'_k-c'_{k+1})\,T_k\Big],\qquad c'_k-c'_{k+1}=(2^{d_{k+1}}-2^{d_k})\!\!\prod_{j\ne k,k+1}\!\!c_j .$$

C_m is an integer: an **m-term sum of S-units** 2^{e(k)}·3^{o−ℓ(k)} (e, ℓ = run-boundary prefix sums) with bounded coefficients summing to 0. Since G | S and G | D, **G | gcd(C_m, D)**. It is the program's representative, written in closed form for run-structured words. Its size is

$$|C_m|\approx 3^{o}\max_{k\lt m}T_k = 3^{o}\cdot(\text{max partial character at run boundaries}).$$

The size relative to |D| ≈ 3^o·Λ is governed by the run-boundary walk of the partial characters χ = 2^{e_k}/3^k. That is §7's stark ratio, sampled at run boundaries. After removing the common monomial 3^{L_m}, exclusion holds for a rotation r whenever 3^{L_r} > 457·o^{13.3}·Σ|γ|·max_k T_k^{(r)}.

**m = 2, exactly.** C₂ = ±(2^{d₁} − 2^{d₂})·3^{L₂}·A₁ with A_i = 2^{d_iL_i} − 3^{L_i}. Since D = 2^{d₁L₁}A₂ + 3^{L₂}A₁ and G is prime to 6,

$$\boxed{\,G(d_1^{L_1}d_2^{L_2})\ \big|\ (2^{|d_1-d_2|}-1)\cdot\gcd\!\big(2^{d_1L_1}-3^{L_1},\ 2^{d_2L_2}-3^{L_2}\big)\,}$$

This is literally a Corvaja–Zannier gcd(u−1, v−1) with u = t₁, v = t₂, up to S-unit factors. u and v are multiplicatively independent iff d₁ ≠ d₂.

* **Elementary consequence (3x+1, G = |D|).** A cycle-relevant two-run word has d₁ = 1 < log₂3 < d₂ = d, so |A₁| < 3^{L₁}. A cycle needs |D| ≤ (2^{d−1}−1)·3^{L₁}.
  * *d = 2.* With Ellison (|D| > 2^E e^{−E/10} = e^{0.5931E} for E ∉ {1,…,11,13,14,16,19,27}) this needs 1.186·L₂ < 0.506·L₁. That forces E/o < 1.30 < log₂3, so D < 0. **No positive two-run {1,2} cycle with E > 27.**
  * *General d.* The same computation gives L₂ < (0.506·L₁ + (d−1)·ln 2)/(0.593·d), against the slope requirement L₂ ≈ 0.585·o/(d−1). With Ellison alone this excludes d ≤ 4 (d = 5 is borderline). With Rhin, each fixed d is excluded once 3^{0.585o/(d−1)} > 457·2^{d−1}·o^{13.3}. Large d is Simons–de Weger 1-cycle territory.
  * *3x+q.* G = |D|/q costs a factor q, so the exclusion holds once o ≫ ln q.
* **Literature consequence (ineffective).** Corvaja–Zannier 2005 (Hernández–Luca 2003 over ℚ) give log gcd(A₁,A₂) < ε·max(h(t₁),h(t₂)) ≤ ε·d·o, outside a proper Zariski-closed set. That set is a finite union of translates of subtori t₁^a t₂^b = c. On our points such a relation forces aL₁(d₁−d₂) = const, so **either L₁ or L₂ is bounded**. The exceptional set is precisely the one-growing-run families, the lever's domain. So for both runs long: k(w) = |D|/G ≥ |D|·e^{−εo}. Two-run words support 3x+k cycles only for exponentially large k. This holds for every k, which is consistent with F4: the theorem is blind to k, but it bounds k from below.

### 3.2 One growing run: the gcd is a resultant, and that is the lever (derived here)

For βd^L, write t = (2^d/3)^L and c = 2^d − 3. Then S/3^L = S(β) + 2^{|β|}(t−1)/c and D/3^L = 2^{|β|}t − 3^{len β}. These are two linear polynomials in t, so their gcd divides the resultant:

$$\operatorname{Res}_t\big(cS/3^L,\ D/3^L\big)=-2^{|\beta|}\big(cS(\beta)+3^{\mathrm{len}\,\beta}-2^{|\beta|}\big)=2^{|\beta|}\big(S(\beta d)-S(d\beta)\big).$$

That is exactly the bounded-defect ceiling sixfree(S(βd) − S(dβ)). **The lever is the rank-1 (n = 1) case of the Levin hierarchy.** It is effective and o-independent because a one-variable gcd is bounded by a resultant. Every exceptional sub-family that the 2-run and m-run theorems leave over is again rank 1 or lower, so this rule closes them the same way, unless the restricted polynomials *share a factor*. That shared factor is exactly the cyclotomic collapse.

### 3.3 m runs, m fixed: Levin (application derived here)

Take n = m variables t ∈ G_m^m(ℤ[1/6]), F = C_m/3^o (degree < m in each monomial chain) and G = t₁⋯t_m − 1, which is irreducible. F is not divisible by G because γ_k ≠ 0 for adjacent distinct letters. Levin 2019, Theorem 1.12(a) (counting only primes outside S, so the origin condition is not needed):

$$\log G(w)\ \le\ N_{\gcd,S}\big(F(t),G(t)\big)\ \lt\ \varepsilon\max_i h(t_i)\ \le\ \varepsilon\, d_{\max}\, o\,\log 2\qquad (t\notin Z).$$

* **Exceptional set Z.** Translates of proper subtori ∏t_i^{a_i} = c, i.e. pairs of affine relations Σa_id_iL_i = κ₂ and Σa_iL_i = κ₃ on the run-length vector. Examples: "L_i bounded"; "L_i − L_j bounded" when d_i = d_j (near-repetition, the source of periodicity); codimension-2 relations mixing letters.
* **Recursion.** On each translate, restrict and re-apply Levin (or the resultant in rank 1). It ends in finitely many words, or in sub-tori where F|_H and G|_H share a factor. G|_H is a binomial in the sub-torus coordinates, so the shared factor is cyclotomic in a monomial μ. Its locus is a set of torsion cosets, finite and computable by Laurent 1984 and Aliev–Smyth 2007. These are the "cyclotomic collapse" families of OP3. Periodic words u^p are the obvious ones, with G(u^p) ≥ |D(u^p)|/|D(u)|.
* **Effectivity.** The bound "ε·o" holds only outside Z and only beyond an *uncomputable* threshold (Subspace theorem). Bugeaud–Evertse say of the same mechanism: "we cannot compute the set of n for which (1.5) does not hold". So Levin gives a *qualitative* no-go for each fixed m and letter tuple, and no o₀ that a computer search could reach.
* **Letters may grow too.** Add s_i = 2^{d_i} as further S-unit variables (2m variables). That covers Simons–de Weger m-cycles: m blocks 1^{k_i−1}(l_i+1), i.e. ≤ 2m runs with the non-1 runs of length 1 and growing *value*.

**Comparison with Simons–de Weger.** The task brief equated "bounded number m of runs" with SdW m-cycles. That is inaccurate. An SdW m-cycle has m letters ≥ 2 (m local minima), so 1^{L₁}2^{L₂} has 2 runs but is an L₂-cycle in SdW's sense. SdW (and Hercher, m ≤ 91) is **effective and complete for 3x+1** on its family, using x_min, Rhin and continued fractions. Levin is **ineffective but stronger in kind**: k(w) ≥ |D|^{1−ε} for all large members, so it applies to every 3x+k with k below that. It needs no x_min, works for any fixed m, and covers fixed-letter run families that SdW does not. For 3x+1 with m = 2, §3.1 shows elementary size suffices. For m ≥ 3 the same size test (3^{L_r} vs the run-boundary character excursion) excludes every word with a run of 1s much longer than 13.3·log₂o whose character walk is unimodal. The remaining m-run words are the ones only Levin covers.

### 3.4 (b) Balanced / Sturmian words: why nothing applies

* **Variable count grows.** A balanced word of slope ≈ log₂3 has runs of length 1–2, so m ≈ 0.8·o runs. Even using the Sturmian block hierarchy (standard words s_{n+1} = s_n^{a_n}s_{n−1}, blocks as letters), S is a polynomial in about 2·(CF depth) ≈ 2·log o S-unit variables, and that number still grows. Levin, CZ, Evertse and Bugeaud–Evertse are statements about a *fixed* pair of polynomials in a *fixed* number of variables. Z, the ε-threshold and the constants all depend on that pair. The Subspace theorem is applied in a dimension that grows with the number of monomials. The quantitative Subspace / unit-equation counts (Evertse–Schlickewei–Schmidt 2002: explicit in n and r but super-exponential in n) bound how many exceptional subspaces there are, not where they lie. **No published gcd theorem is uniform in the number of terms.**
* **The statement itself must change.** Powers u^p of a Christoffel word are balanced and have G ≥ |D|^{1−1/p}. Primitive cycles of 3x+k with small k (F4) are many-run words with G = |D|/k. So "G ≤ |D|^{ε}" is false for (b) in general. The most one can hope for is "k(w) ≥ f(o) for all primitive w beyond o₀(k)". That is a statement about the *specific* value k = 1 and needs input beyond identities (F4).
* **What *does* carry over.** Fixed-depth block families U^{a₁}V^{b₁}⋯ (bounded block-run complexity, exponents growing) are in Levin's scope, with c_U = 2^{|U|} − 3^{len U}. Only words whose block structure refines at every scale (CF depth → ∞) escape all known theorems. This is a precise formulation of "the hard words" for OP2.

### 3.5 What the 6-free axis can and cannot buy (H5)

Evertse 1984 (Theorem 2 and its corollaries) shows the following. If C = x₀ + ⋯ + x_n is a sum of S-integers with gcd 1, bounded non-S parts and no vanishing subsum, then the S-free part of C is ≥ c(ε,n)·max|x_i|^{1−ε}. Bugeaud–Evertse 2017 Theorem 1.1 restates this for linear recurrences: [u_n]_S ≤ |u_n|^{δ+ε}, with δ = 0 when gcd(q₁⋯q_s, a₁,…,a_k) = 1. That condition holds for our ceilings, whose characteristic roots are 2^d, 3 and 1, with coefficients 2^d + 3 and 3·2^d prime to 6. Their Theorem 1.2 gives an *effective* [u_n]_S ≤ |u_n|^{1−c₁} under a dominant root (2^d ≠ 3 in modulus).

**Consequence.** For a family of ceilings with a bounded number of S-unit terms and growing exponents, sixfree(C) is |C|^{1−ε} (ineffectively) and at least |C|^{c₁} (effectively). PROGRAM §2's slogan "a representative may be enormous yet have a tiny 6-free part" can only hold when (i) the ceiling is constant up to an S-unit factor, as for the lever, or (ii) the ceiling has unboundedly many terms. For two-term ceilings it is elementary: v₂(3^b ∓ 1) ≤ v₂(b) + 2 and v₃(2^a ± 1) ≤ v₃(a) + 1 (lifting-the-exponent).

**For OP1 (explicit f(w)).** Look for *size* cancellation in C (small |C|), or for structures with many terms. Do not look for small 6-free parts of a few large terms.

### 3.6 Linear forms in two logarithms: what the records give

* **Rhin 1987 (via SdW Lemma 12).** Λ > e^{−13.3(0.46057 + ln o)}, valid for all H ≥ 2. This remains the best fully explicit all-range bound (Simons–de Weger, Acta Arith. 117 (2005) — the venue is Acta Arith., not Math. Comp. as PROGRAM.md's references say).
* **Bondareva–Luchin–Salikhov 2018.** |h₁ln2 + h₂ln3 + h| > H^{−4.116201} for H ≥ H₀. With h = 0 this is Λ > E^{−4.1163}, so μ(log₂3) ≤ 5.116201. It follows Wu–Wang 2014 (4.117) and Salikhov 2007 (μ(ln 3) ≤ 5.125/5.126). Draper–Saad 2026 still cite it as the record. **This is the measure that governs |2^E − 3^o| asymptotically.** PROGRAM §3's remark that the Salikhov line is "a different number, not the one that governs |2^E − 3^o|" is wrong for the linear-independence version: Theorem 1 of BLS bounds exactly the form E ln 2 − o ln 3. What is missing is only an explicit H₀.
* **Ellison 1971.** |2^x − 3^y| > 2^x e^{−x/10} for x ∉ {1,…,11,13,14,16,19,27}. Rozier–Terracol 2026 package it as |2^j − 3^q| > 2.56^q/2 for q > 12. It beats Rhin until o ≈ 570 (checked: 0.1586·o = 6.12 + 13.3·ln o at o ≈ 570). **F3 is confirmed.**
* **General two-log constants** (LMN 1995: 24.34; Laurent 2008: 25.2 with m=10; Gouillon 2006: about 5·10⁴ with h ≥ 1000; Matveev: about 5.7·10⁸; Baker–Wüstholz: about 1.1·10¹²) are all weaker for this pair than Rhin's specialised Padé bound.
* **Continued fraction** (A028507): log₂3 = [1;1,1,2,2,3,1,5,2,23,2,2,1,1,55,1,4,3,1,1,15,1,9,2,5,…]. Large quotients a₉=23, a₁₄=55, a₂₀=15, a₂₂=9, then a₄₄=37, a₄₆=55, a₄₉=49. The best near-misses come before them: 1054/665, 301994/190537, 630138897/397573379 (A005663/A005664). These o-values are where Λ is smallest and every ceiling test is hardest.
* **Caution.** A 2026 GitHub/Zenodo preprint (Jha) claims μ(log₂3) ≤ 3. It is unrefereed, AI-assisted per its README, and unchecked. Do not use it.

### 3.7 Effectivity ledger (item 7)

| effective, explicit | effective in principle, constant not stated | ineffective (Subspace / Roth–Ridout) |
|---|---|---|
| Rhin/SdW 13.3; Ellison; Tijdeman 1973; LMN; Laurent 2008; Gouillon; Matveev; Baker–Wüstholz; Stewart–Yu 2001; Zsigmondy/Bang; BHV; Stewart 1977/2013; Bennett 2001/2003; Stroeker–Tijdeman; Gross–Vincent; Bugeaud–Evertse Thms 1.2–1.3; Bugeaud 2000/2026; resultant bound (rank 1); Aliev–Smyth torsion cosets; all function-field gcd bounds | BLS 2018 / Wu–Wang (H ≥ H₀); Tijdeman's C₁ = c₁^{r⁴}(log p)^{14r²} | BCZ 2003; CZ 2005; Hernández–Luca; Levin 2019; Grieve–Wang; Wang–Yasufuku; Huang–Levin; Evertse 1984; Bugeaud–Evertse Thm 1.1; BEG 2018 (d > 1/n); Granville 2022; Pillai 1931/1936 |

**For a computer-assisted exclusion.** Only the left column can be chained with a finite search, because it produces an explicit o₀. Anything routed through the right column produces "finitely many exceptions" with no list and, per Bugeaud–Evertse, often no bound on their number. The rank-1 step (resultant) and the torsion-coset step are effective, so a *rigorous* m-run exclusion would need an effective replacement for Levin's step. None is known for n ≥ 2. Even BCZ's gcd(a^n−1, b^n−1) ≤ e^{εn} has no effective proof.

---

## 4. Annotated bibliography

Format: citation — URL/DOI — **quote** (verbatim from the fetched page; TeX rendered as plain text; when the quote comes from a secondary page, the note says which) — note — **verdict**.

### A. gcd of S-unit expressions

1. **Y. Bugeaud, P. Corvaja, U. Zannier**, *An upper bound for the G.C.D. of a^n − 1 and b^n − 1*, Math. Z. 243 (2003) 79–84. — (statement fetched from the restatement in Huang–Levin, arXiv:2207.14432; metadata from Bilu's and Levin–Wang's reference lists).
   **Quote:** "Let a,b ∈ Z be multiplicatively independent integers. Then for every ε>0, log gcd(a^n−1, b^n−1) ≤ εn for all but finitely many positive integers n."
   **Note:** The founding result. For the program it is the template of §3.1: D = 3^o(T−1) is an "a^n − 1". Ineffective (Subspace). **keep**
2. **P. Corvaja, U. Zannier**, *A lower bound for the height of a rational function at S-unit points*, Monatsh. Math. 144 (2005) 203–224. — https://arxiv.org/abs/math/0311030
   **Quote:** "We prove that, for all (u,v) ∈ Γ outside a proper Zariski closed subset of G_m^2, the height of p(u,v)/q(u,v) verifies h(p(u,v)/q(u,v)) > h(1:p(u,v):q(u,v)) − ε max(h(u),h(v)). As a consequence, we deduce upper bounds for (a generalized notion of) the g.c.d. of u−1, v−1 for u,v running over Γ."
   **Note:** This is exactly the two-run case (H1): G(d₁^{L₁}d₂^{L₂}) divides (2^{|Δd|}−1)·gcd(u−1, v−1) after S-unit normalisation. The exceptional set is the one-growing-run families. **keep**
3. **S. Hernández, F. Luca**, *On the largest prime factor of (ab+1)(ac+1)(bc+1)*, Bol. Soc. Mat. Mexicana (3) 9 (2003) 235–244. — via Bilu's Bourbaki survey, https://arxiv.org/abs/0907.2098
   **Quote:** "Corvaja and Zannier [24] and, independently, Hernández and Luca [39] proved that (ab + 1)(ac + 1)(bc + 1) cannot have only small prime divisors"
   **Note:** Levin's abstract credits it with the S-unit (over ℚ) form of the BCZ gcd bound. The primary was not fetched. **open (low)**
4. **A. Levin**, *Greatest common divisors and Vojta's conjecture for blowups of algebraic tori*, Invent. Math. 215 (2019) 493–533. — DOI 10.1007/s00222-018-0831-z (theorem fetched from Levin–Wang, arXiv:1903.03876, Thm 1.12).
   **Quote:** "(a) There exists a finite union Z of translates of proper algebraic subgroups of G_m^n such that N_{gcd,S}(F(u_1,…,u_n),G(u_1,…,u_n)) < ε max{h(u_1),h(u_2),…,h(u_n)} for all (u_1,…,u_n) ∈ G_m^n(O_{k,S}) \ Z."
   **Note:** The central theorem for fixed m (§3.3). Part (a) counts primes outside S, which is exactly G since G is prime to 6, so no origin hypothesis is needed. Ineffective. **keep** (open as a route to exclusion)
5. **J. H. Silverman**, *Generalized greatest common divisors, divisibility sequences, and Vojta's conjecture for blowups*, Monatsh. Math. 145 (2005) 333–350. — https://arxiv.org/abs/math/0407415
   **Quote:** "We apply Vojta's conjecture to blowups and deduce a number of deep statements regarding (generalized) greatest common divisors on varieties, in particular on projective space and on abelian varieties."
   **Note:** The conceptual frame: G = a height relative to the codimension-2 subscheme {S = D = 0}. Conditional (Vojta). **open (framework)**
6. **N. Ailon, Z. Rudnick**, *Torsion points on curves and common divisors of a^k−1 and b^k−1*, Acta Arith. 113 (2004) 31–38. — https://arxiv.org/abs/math/0202102 · DOI 10.4064/aa113-1-3
   **Quote:** "In the integer case, we conjecture that when a and b are multiplicatively independent and in addition a-1 and b-1 are coprime, then a^k-1 and b^k-1 are coprime infinitely often. In the polynomial case, we prove a strong version of this conjecture."
   **Note:** ℂ[T] analogue: gcd bounded, via Lang's torsion theorem. It is a Layer-1 shadow. Its conjecture says the *typical* 2-run G is tiny. **kill** (Layer 1)
7. **J. H. Silverman**, *Common divisors of a^n−1 and b^n−1 over function fields*, New York J. Math. 10 (2004) 37–43. — https://arxiv.org/abs/math/0401356
   **Quote:** "We show that if instead a,b ∈ F[T] for a finite field F of characteristic p, then deg(gcd(a^n−1,b^n−1)) is larger than Cn for a constant C=C(a,b)>0 and for infinitely many n"
   **Note:** In char p the ε-bound fails. A warning that the gcd bound is genuinely arithmetic (characteristic 0). **kill**
8. **P. Corvaja, U. Zannier**, *Greatest common divisors of u−1, v−1 in positive characteristic and rational points on curves over finite fields*, J. Eur. Math. Soc. 15 (2013) 1927–1942. — DOI 10.4171/JEMS/409
   **Quote:** "In our previous work we proved a bound for the g cd ( u − 1 , v − 1 ) , for S -units u , v of a function field in characteristic zero. … As pointed out by Silverman, the exact analogue does not work for function fields in positive characteristic."
   **Note:** Function-field versions, which are effective and uniform. These are Layer-1 analogues. **kill**
9. **A. Ostafe**, *On some extensions of the Ailon–Rudnick theorem*, Monatsh. Math. 181 (2016) 451–471. — https://arxiv.org/abs/1505.03957 · DOI 10.1007/s00605-016-0911-3
   **Quote:** "the Ailon-Rudnick Theorem, which says that if f,g ∈ C[T], then gcd(f^n−1,g^m−1) is bounded for all n,m ≥ 1."
   **Note:** A two-exponent version (n ≠ m) over ℂ[T], the shape of our 2-run gcd. Layer 1. **kill**
10. **A. Levin, J. T.-Y. Wang**, *Greatest common divisors of analytic functions and Nevanlinna theory on algebraic tori*, J. reine angew. Math. 2020 (2020) 77–107. — https://arxiv.org/abs/1903.03876 · DOI 10.1515/crelle-2019-0033
    **Quote:** "We study upper bounds for the counting function of common zeros of two meromorphic functions in various contexts."
    **Note:** Analytic analogue. Used here only as the verified restatement of Levin 2019 and BCZ. **kill** (as a lever)
11. **N. Grieve, J. T.-Y. Wang**, *Greatest common divisors with moving targets and consequences for linear recurrence sequences*, Trans. Amer. Math. Soc. (DOI 10.1090/tran/8220); arXiv 2019. — https://arxiv.org/abs/1902.09109
    **Quote:** "we obtain inequalities that bound the logarithmic greatest common divisor of moving multivariable polynomials evaluated at moving S-unit arguments."
    **Note:** "Moving" coefficients may absorb slowly growing letters (c_i = 2^{d_i} − 3 varying). It is the only gcd result with any non-fixed polynomial, but the growth allowed is small. Ineffective. **open**
12. **J. T.-Y. Wang, Y. Yasufuku**, *Greatest common divisors of integral points of numerically equivalent divisors*, Algebra Number Theory 15 (2021) 287–305. — https://arxiv.org/abs/1907.09324
    **Quote:** "We generalize the G.C.D. results of Corvaja--Zannier and Levin on G_m^n to more general settings."
    **Note:** A geometric generalisation. Nothing new for G_m^n. **kill**
13. **N. Grieve**, *Generalized GCD for toric Fano varieties*, Acta Arith. 195 (2020) 415–428. — https://arxiv.org/abs/1904.13188 · DOI 10.4064/aa190430-5-12
    **Quote:** "As a special case of our results, we deduce a bound for the generalized greatest common divisor of pairs of nonzero algebraic numbers."
    **Note:** Toric generalisation. **kill**
14. **K. Huang, A. Levin**, *Greatest common divisors on the complement of numerically parallel divisors*, arXiv:2207.14432 (2022). — https://arxiv.org/abs/2207.14432
    **Quote:** "In addition to proving results in a broader context than previously considered, we also study the exceptional set in this setting, for both the counting function and the proximity function."
    **Note:** The only paper found that *studies the exceptional set Z*. This is the place to look for which subtori must be excluded (H3/H4). **open**
15. **A. Granville**, *Classifying linear division sequences*, arXiv:2206.11823 (2022). — https://arxiv.org/abs/2206.11823
    **Quote:** "We also show that if two linear division sequences have a large common factor infinitely often then they are each divisible by a common linear division sequence on some arithmetic progression."
    **Note:** Along any line (L₁, L₂) = (αn+β, γn+δ), the 2-run gcd is a gcd of two recurrences in n. So "G large infinitely often" ⇒ shared cyclotomic factor. This supports "cyclotomic collapse is the only mechanism" (OP3). Ineffective. **keep**
16. **J. Cohen, J. Sonn**, *A cyclotomic generalization of the sequence gcd(a^n−1, b^n−1)*, J. Théor. Nombres Bordeaux 27 (2015) 53–65. — https://arxiv.org/abs/1103.2207 · DOI 10.5802/jtnb.893
    **Quote:** "Bugeaud, Corvaja and Zannier have obtained an upper bound exp(εn) for any given ε>0 and all large n, and demonstrate its approximate sharpness by extracting from a paper of Adleman, Pomerance, and Rumely a lower bound exp(exp(c log n/loglog n)) for infinitely many n"
    **Note:** A calibration: the 2-run gcd can be sub-exponentially large on special diagonals, but e^{o(o)}. It never reaches |D|. **keep** (calibration)
17. **F. Campagna, G. A. Dill, R. Wilms**, *Arithmetic unlikely intersections in powers of the multiplicative group*, arXiv:2607.15741 (2026). — https://arxiv.org/abs/2607.15741
    **Quote:** "We then show that our conjecture in dimension 1 follows from work of Corvaja-Zannier, we obtain some partial result in dimension 2, and we present some open problems that are special cases of the conjecture."
    **Note:** The current frontier. A conjectural "size vs complexity" law for intersections with subgroup schemes over O_K. Watch for an n-uniform version. **open**
18. **K.-H. Nguyen-Dang**, *On the sequence gcd(a^n−1, b^n−1)*, arXiv:2606.07959 (2026). — https://arxiv.org/abs/2606.07959
    **Quote:** "We prove that (g_n) satisfies a constant-coefficient linear recurrence if and only if a and b are multiplicatively dependent"
    **Note:** The gcd sequence has no recurrence structure for independent bases. So there is no closed-form f(w) for the 2-run G. **kill**
19. **Y. F. Bilu**, *The many faces of the Subspace Theorem (after Adamczewski, Bugeaud, Corvaja, Zannier…)*, Séminaire Bourbaki 2006/07, exp. 967. — https://arxiv.org/abs/0907.2098
    **Quote:** "Bugeaud, Corvaja and Zannier proved [12] that an − 1 and bn − 1 cannot have a large common divisor. This was extended by Corvaja and Zannier [24, 29]."
    **Note:** The standard survey of the Subspace-theorem toolkit behind items 1–4 and 20–22. **keep** (reference)

### B. S-parts and sums of S-units

20. **J.-H. Evertse**, *On sums of S-units and linear recurrences*, Compositio Math. 53 (1984) 225–244. — http://www.numdam.org/item/CM_1984__53_2_225_0/
    **Quote:** "It is our intention to generalize these results by a uniform approach based on Schlickewei's p-adic version of the method of Thue-Siegel-Roth-Schmidt." / "THEOREM 2: Let n be a non-negative integer and S a finite set of primes on K, enclosing S∞. Then for every ε > 0 a constant C exists, depending only on ε, S, K, n"
    **Note:** The S-free part of a non-degenerate sum of n+1 S-units is ≥ C·max|x_i|^{1−ε} (the formula is an image in the scan; its shape is confirmed by Bugeaud–Evertse 2017 citing it). **H5: the 6-free axis buys only ε for bounded-term ceilings.** The constant C depends on n, so it gives nothing for (b). **keep** (limit)
21. **Y. Bugeaud, J.-H. Evertse**, *S-parts of terms of integer linear recurrence sequences*, Mathematika 63 (2017) 840–851. — https://arxiv.org/abs/1611.00485 · DOI 10.1112/S0025579317000298
    **Quote:** "Then for every sufficiently large n we have |u_n|^{δ−ε} ≤ [u_n]_S ≤ |u_n|^{δ+ε}." / "The proof of Theorem 1.1 depends ultimately on the p-adic Schmidt Subspace Theorem, therefore we cannot compute the set of n for which (1.5) does not hold." / Thm 1.2: "[u_n]_S ≤ |u_n|^{1−c_1}, for every n ≥ c_2" (c₁, c₂ effective, dominant root).
    **Note:** Applies directly to one-parameter ceiling families C_L (roots 2^d, 3, 1 ⇒ δ = 0). An effective |C_L|^{c₁} lower bound on sixfree(C_L) is available; extracting c₁ would quantify H5. **keep**
22. **Y. Bugeaud, J.-H. Evertse, K. Győry**, *S-parts of values of univariate polynomials, binary forms and decomposable forms at integral points*, Acta Arith. 184 (2018) 151–185. — https://arxiv.org/abs/1708.08290
    **Quote:** "As an easy application of the p-adic Thue-Siegel-Roth theorem we show that if f(X) has degree n ≥ 2 and no multiple roots, then an inequality such as (*) holds for all d>1/n, provided we do not require effectivity of c."
    **Note:** Binary-form version: [F(x,y)]_S ≤ c|F(x,y)|^{d}. Relevant if a ceiling is a binary form in (2^a, 3^b). **open**
23. **R. Gross, J. Vincent**, *On the factorization of f(n) for f(x) in Z[x]*, Int. J. Number Theory 9 (2013) 1225–1236. — DOI 10.1142/S179304211350022X (statement fetched from BEG 2018 abstract).
    **Quote:** "In 2013, Gross and Vincent proved that if f(X) is a polynomial with integer coefficients and with at least two roots in the complex numbers, then for every integer x at which f(x) is non-zero, we have (*) [f(x)]_S ≤ c·|f(x)|^d, where c and d are effectively computable and d<1."
    **Note:** The effective prototype of H5. **keep (low)**
24. **C. L. Stewart, K. Yu**, *On the abc conjecture, II*, Duke Math. J. 108 (2001) 169–181. — DOI 10.1215/S0012-7094-01-10815-6 · https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/s0012-7094-01-10815-6.pdf
    **Quote:** "There exists an effectively computable positive number c such that, for all positive integers x, y, and z with x + y = z and (x, y, z) = 1, z < exp(c G^{1/3}(log G)^3)."
    **Note:** For 2^E − 3^o it gives rad ≫ (log)^{3−} only. D is coprime to 6, so sixfree(D) = |D| trivially and this is useless next to Ellison. **kill**
25. **J.-H. Evertse, H. P. Schlickewei, W. M. Schmidt**, *Linear equations in variables which lie in a multiplicative group*, Ann. of Math. 155 (2002) 807–836. — DOI 10.2307/3062133 (abstract via Semantic Scholar API) — *dup*
    **Quote:** "We derive an explicit upper bound for A(a 1 ,.., a n , r) which depends only on the dimension n and on the rank r."
    **Note:** New use: this is the best uniformity in the number of terms n. The bound is explicit but super-exponential in n (usually cited as exp((6n)^{3n}(r+1)); that form was not re-read here). It counts solutions and does not bound gcds. With n ≈ o it is useless for (b). **kill** for (b)

### C. Unlikely intersections / cyclotomic rigidity

26. **M. Laurent**, *Équations diophantiennes exponentielles*, Invent. Math. 78 (1984) 299–327. — DOI 10.1007/BF01388597 (statement from Aliev–Smyth abstract).
    **Quote:** "It was conjectured by S. Lang and proved by M. Laurent that all such solutions can be described in terms of a finite number of parametric families called maximal torsion cosets."
    **Note:** Lang's G_m conjecture. The cyclotomic-collapse families of §3.3 are torsion cosets of {F|_H = 0}, so there are finitely many. **keep**
27. **I. Aliev, C. Smyth**, *Solving algebraic equations in roots of unity*, arXiv:0704.1747. — https://arxiv.org/abs/0704.1747 — *dup*
    **Quote:** "the proofs of our results are constructive. This allows us to obtain a new algorithm for determining maximal torsion cosets on an algebraic subvariety of G_m^n."
    **Note:** New use: the *effective* half of the m-run programme (H4). It computes the collapse families exactly. **keep**
28. **E. Bombieri, D. Masser, U. Zannier**, *Intersecting a curve with algebraic subgroups of multiplicative groups*, Internat. Math. Res. Notices 1999, no. 20, 1119–1140. — DOI 10.1155/S1073792899000628 (statement from BMZ, Ann. SNS Pisa (5) 7 (2008) 51–80, abstract).
    **Quote:** "In an earlier article from 1999 bearing almost the same title, we studied the intersection of the curve and the union of all algebraic subgroups of some fixed codimension. With codimension one the resulting set has bounded height properties, and with codimension two it has finiteness properties."
    **Note:** Framework only. Our points (t_i) lie in a rank-2 group (generated by 2 and 3), not on a curve. **open (low)**
29. **T. Y. Lam, K. H. Leung**, *On vanishing sums for roots of unity*, arXiv:math/9511209 (published J. Algebra 2000, per THREADS; not re-verified). — https://arxiv.org/abs/math/9511209 — *dup*
    **Quote:** "We prove that the answer is exactly the set of linear combinations with non-negative integer coefficients of the prime factors of m."
    **Note:** It bounds which collapse indices can occur for an m-term F. It complements Filaseta–Schinzel (already mined). **open (low)**
30. **J. H. Conway, A. J. Jones**, *Trigonometric diophantine equations (On vanishing sums of roots of unity)*, Acta Arith. 30 (1976) 229–240. — https://eudml.org/doc/205475 · DOI 10.4064/aa-30-3-229-240 — *dup*, **verified: false** (metadata only; scan has no text layer).
    **Note:** The γ(m) weight is already used in `drafts/lit-filaseta-schinzel.md`. Nothing new. **kill** (dup)
31. **W. D. Brownawell, D. W. Masser**, *Vanishing sums in function fields*, Math. Proc. Cambridge Philos. Soc. 100 (1986) 427–434. — DOI 10.1017/S0305004100066184 — *dup*, **verified: false** (metadata only).
    **Note:** The n-term function-field abc, the Layer-1 analogue of Evertse 1984. Layer 1 is closed. **kill**

### D. Primitive divisors and large prime factors (verified by helper; statements re-read)

32. **K. Zsigmondy**, *Zur Theorie der Potenzreste*, Monatsh. Math. Phys. 3 (1892) 265–284. — DOI 10.1007/BF01692444 (statement from GLNP arXiv PDF) — *dup* (named, not read)
    **Quote:** "Given coprime integers q > r ⩾ 1 and n > 2, Zsigmondy [22] proved in 1892 that there exists a prime p dividing q^n − r^n but not q^k − r^k for 1 ⩽ k < n except when q = 2, r = 1, and n = 6."
    **Note:** For 3^n − 2^n there is no exception for n ≥ 2. So BHV is *not needed* there (THREADS line 13 says "n > 30 via BHV"). For D = A^g − B^g with g = gcd(E,o) ≥ 2 there is always a primitive prime ≡ 1 mod g. When gcd(E,o) = 1 (typical for critical words) it says nothing. **kill** for D; keep for periodic words
33. **A. S. Bang**, *Taltheoretiske undersøgelser*, Tidsskr. Math. (5) 4 (1886) 70–80, 130–137. — https://zbmath.org/?q=an:19.0168.02 (JFM review) — *dup*
    **Quote:** "Derselbe wird eine ganzzahlige rationale Function von a sein vom Grade φ(t) und wird, mit einzelnen Ausnahmen, wenigstens einen Primfactor von der Form αt+1 enthalten."
    **Note:** The b = 1 case. **kill**
34. **C. L. Stewart**, *On divisors of Fermat, Fibonacci, Lucas, and Lehmer numbers*, Proc. London Math. Soc. (3) 35 (1977) 425–447. — DOI 10.1112/plms/s3-35.3.425 (statement from Stewart 2013 intro) — *dup*
    **Quote:** "if n (> 3) has at most κ log log n distinct prime factors then P(Φn(α, β)) > C(ϕ(n) log n)/q(n), where C is a positive number which is effectively computable in terms of α, β and κ only."
    **Note:** Effective growth of the primitive part's largest prime for equal exponents. **kill** for D
35. **C. L. Stewart**, *On divisors of Lucas and Lehmer numbers*, Acta Math. 211 (2013) 291–314. — https://arxiv.org/abs/1008.1274 · DOI 10.1007/s11511-013-0105-y — *dup*
    **Quote:** "Specifically, if a and b are integers with a > b > 0 then P(a^n − b^n) > n exp(log n/104 log log n), for n sufficiently large in terms of the number of distinct prime factors of ab."
    **Note:** Equal exponents only. Theorem 2 (ord_p(a^n − b^n) bounded) may bound how much of D one prime can carry. That is a lead, not a lever. **open (low)**
36. **A. Schinzel**, *On primitive prime factors of a^n − b^n*, Proc. Cambridge Philos. Soc. 58 (1962) 555–562. — DOI 10.1017/S0305004100040561 (statement from Stewart 2013 intro)
    **Quote:** "He proved that if a and b are coprime and ab is a square or twice a square then P(a^n − b^n) ≥ 2n + 1 provided that one excludes the cases n = 4, 6, 12 when a = 2 and b = 1."
    **Note:** ab = 6 is neither a square nor twice a square, so there is no Aurifeuillian boost for bases (3, 2). **kill**
37. **S. P. Glasby, F. Lübeck, A. C. Niemeyer, C. E. Praeger**, *Primitive prime divisors and the n-th cyclotomic polynomial*, J. Aust. Math. Soc. 102 (2017) 122–135. — https://arxiv.org/abs/1504.02598 · DOI 10.1017/S1446788715000269 — *dup*
    **Quote:** "If n ⩾ 3, then Φ∗n(q) ⩽ n^4 if and only if (n, q) is listed in Tables 1, 3 or 4."
    **Note:** **Correction to THREADS line 45**: the classification is for q^n − 1 with q a *prime power*. It does not cover Φ_n(2^E, 3^o) or 3^n − 2^n, so it cannot replace the collapse rule for (2,3). **kill**
38. **Yu. Bilu, G. Hanrot, P. M. Voutier**, *Existence of primitive divisors of Lucas and Lehmer numbers*, J. reine angew. Math. 539 (2001) 75–122. — DOI 10.1515/crll.2001.080 (zbMATH 0995.11010) — *dup*
    **Quote:** "Main result of the paper: Every integer N> 30 is totally non-defective."
    **Note:** Needed only for non-rational Lucas pairs. For a^n − b^n Zsigmondy suffices. **kill** (for this program)
39. **Y. Bugeaud**, *On the greatest prime factor of ax^m + by^n. II*, Bull. London Math. Soc. 32 (2000) 673–678. — DOI 10.1112/S0024609300007487 (zbMATH 1043.11033)
    **Quote:** "P[αx^m+βy^n] ≥ c_1 log log max{|N(x)|, |N(y)|} / (d m^3 n^3 h_K), provided that max{|N(x)|, |N(y)|} ≥ c_2."
    **Note:** Via 2^a − 3^b = αx² + βy³ the helper derives P(2^a − 3^b) ≫ log max(a,b) (effective, unchecked). Tiny growth. **kill**
40. **Y. Bugeaud**, *On the difference between perfect powers and integral S-units*, arXiv:2604.27490 (2026). — https://arxiv.org/abs/2604.27490
    **Quote:** "|x − u| ≥ (log∗ log X)^κ1 and P[x − u] ≥ κ2 log∗ log∗ log X · log∗ log∗ log∗ log X / log∗ log∗ log∗ log∗ log X, where we have set X := max{x, u}."
    **Note:** Iterated-log growth only. **kill**
41. **K. Győry, K. Yu**, *Bounds for the solutions of S-unit equations and decomposable form equations*, Acta Arith. 123 (2006) 9–41. — DOI 10.4064/aa123-1-2 — **verified: false** (quote from the zbMATH review; the P-bound itself was not reached).
    **Note:** Explicit S-unit bounds with good dependence on |S|. Not usable without the exact rate. **open (low)**

### E. Pillai and 2^x − 3^y (verified by helper)

42. **S. S. Pillai**, *On the inequality 0 < a^x − b^y ≤ n*, J. Indian Math. Soc. 19 (1931) 1–11. — https://zbmath.org/?q=an:57.0236.01 (JFM review)
    **Quote:** "daß es zu jeder Zahl δ > 0 eine Zahl x_0(δ) gibt, so daß für x > x_0 am^x − bn^y > m^{x(1−δ)} ist, wenn am^x > bn^y"
    **Note:** The origin of the ineffective |2^x − 3^y| > 2^{x(1−δ)}. Ellison made it effective. **keep (history)**
43. **S. S. Pillai**, *On a^x − b^y = c*, J. Indian Math. Soc. (N.S.) 2 (1936) 119–122. — https://zbmath.org/?q=an:62.0134.01
    **Quote:** "1) a^x − b^y = c hat für genügend großes c höchstens eine Lösung. 2) Die Anzahl derjenigen Zahlen ≦ n, die sich in der Form a^x − b^y darstellen lassen, ist asymptotisch gleich (log n)^2/(2 log a log b)."
    **Note:** Part 2 counts how many |D|-values exist below N: (log N)²/(2 log 2 log 3). That is the sparsity of the "near-miss tier". **keep**
44. **S. S. Pillai**, *On the equation 2^x − 3^y = 2^X + 3^Y*, Bull. Calcutta Math. Soc. 37 (1945). — https://zbmath.org/?q=an:0063.06245 (statement via Bennett 2003)
    **Quote:** "In the special case where a = 3 and b = 2, Pillai [Pi3], conjectured that c0(3,2) = 13"
    **Note:** History. **keep (low)**
45. **R. J. Stroeker, R. Tijdeman**, *Diophantine equations*, in Computational Methods in Number Theory II, Math. Centre Tracts 155 (1982) 321–369. — https://zbmath.org/?q=an:0521.10013 (statement via Bennett 2003) — *dup*
    **Quote:** "…the Diophantine equation 3^x − 2^y = c has, for |c| > 13, at most one solution in positive integers x and y"
    **Note:** Baker method. **keep**
46. **M. A. Bennett**, *On some exponential equations of S. S. Pillai*, Canad. J. Math. 53 (2001) 897–922. — DOI 10.4153/CJM-2001-036-6 (zbMATH 0984.11014)
    **Quote:** "the author proves that (1) has at most two solutions in positive integers x,y, without any conditions imposed on a,b,c other than a,b≥2, c≥1."
    **Note:** Uses Laurent–Mignotte–Nesterenko. **keep (low)**
47. **M. A. Bennett**, *Pillai's conjecture revisited*, J. Number Theory 98 (2003) 228–235. — https://secure.math.ubc.ca/~bennett/B-Pillai.pdf · DOI 10.1016/S0022-314X(02)00049-5 — *dup*
    **Quote:** "Theorem 1.1. If N and c are positive integers with N≥2, then the equation |(N+1)^x − N^y| = c has at most one solution in positive integers x and y, unless (N,c)∈{(2,1),(2,5),(2,7),(2,13),(2,23),(3,13)}."
    **Note:** New use: the complete list of repeated |D|-values (H8). Cheapest exceptional-tier enumeration. **keep**
48. **R. Scott, R. Styer**, *On p^x − q^y = c and related three term exponential Diophantine equations with prime bases*, J. Number Theory 105 (2004) 212–234. — DOI 10.1016/j.jnt.2003.11.008
    **Quote:** "If c is positive and q≡ 3 (mod 4), then N≤ 1 except when (p,q,c)=(2,3,5), (2,3,13) or (13,3,10)."
    **Note:** The signed version for 2^x − 3^y = c > 0. **keep (low)**
49. **D. E. Iannucci**, *On duplicate representations as 2^x+3^y for nonnegative integers x and y*, arXiv:1907.03347 (2019). — https://arxiv.org/abs/1907.03347 — *dup*
    **Quote:** "there are exactly five positive integers that can be written in more than one way as the sum of a nonnegative power of 2 and a nonnegative power of 3."
    **Note:** About sums, not differences. **kill**
50. **R. Tijdeman**, *On integers with many small prime factors*, Compositio Math. 26 (1973) 319–330. — http://www.numdam.org/item?id=CM_1973__26_3_319_0
    **Quote:** "THEOREM 1. Let a and b be positive integers, 3 < a < b. Put r = ω(ab), p = P(ab). Then b − a > a/(log a)^{C_1}, where C_1 = c_1^{r^4}(log p)^{14r^2} and c_1 is an e.c. absolute constant."
    **Note:** An effective |2^E − 3^o| > m/(log m)^C with m = min(2^E, 3^o), the same shape as Rhin. Theorem 2 says the shape is sharp (C ≥ π(p) − 1). **keep**
51. **W. J. Ellison**, *On a theorem of S. Sivasankaranarayana Pillai*, Sém. Théorie Nombres Bordeaux 1970–71, exp. 10 (header: 12). — http://www.numdam.org/item?id=STNB_1970-1971____A10_0 — *dup*
    **Quote:** "Let S be the following set of integers {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 16, 19, 27}. Then we have |2^x − 3^y| > 2^x e^{−x/10} for all pairs of positive integers (x, y) with x ∉ S."
    **Note:** New use: combined with the 2-run identity it excludes all two-run {1,2} positive cycles with E > 27 (§3.1). **keep**

### F. Linear forms in logarithms and log₂3 (verified by helper)

52. **I. V. Bondareva, M. Yu. Luchin, V. Kh. Salikhov**, *Symmetrized polynomials in a problem of estimating of the irrationality measure of number ln 3*, Chebyshevskii Sbornik 19(1) (2018) 15–25. — https://www.mathnet.ru/eng/cheb619 · DOI 10.22405/2226-8383-2018-19-1-15-25
    **Quote:** "Теорема 1. Пусть h1, h2, h ∈ Z, H = max(|h1|, |h2|), H ⩾ H0. Тогда |h1 ln 2 + h2 ln 3 + h| > H^−μ, где μ = 4.116201. Следствие 1. Справедлива оценка μ(ln 3) ⩽ 5.116201."
    **Note:** **The record for this exact form.** With h = 0: Λ > E^{−4.116201}, μ(log₂3) ≤ 5.116201. H₀ is not explicit (H6). **keep**
53. **Q. Wu, L. Wang**, *On the irrationality measure of log 3*, J. Number Theory 142 (2014) 264–273. — DOI 10.1016/j.jnt.2014.03.007 (zbMATH review via MaRDI)
    **Quote:** "In the present paper the authors improved Salikhov's method and found a better upper bound μ(log 3)<5.117."
    **Note:** The previous record. **keep (low)**
54. **V. Kh. Salikhov**, *On the irrationality measure of ln 3*, Doklady Math. 76 (2007) 955–957. — **verified: false** (primary not fetched; value from the Wu–Wang review)
    **Note:** 5.125/5.126. PROGRAM.md cites it. **kill** (superseded)
55. **W. Zudilin**, *An essay on irrationality measures of π and other logarithms*, Chebyshevskii Sbornik 5(2) (2004) 49–65. — https://arxiv.org/abs/math/0404523
    **Quote:** "Theorem 3. The irrationality exponent of any nonzero γ ∈ Q log 2+Q log 3 satisfies the inequality µ(γ) < 8.616."
    **Note:** Attributes 8.616 to Rhin. Note it is for γ ∈ ℚlog2 + ℚlog3, not for the ratio log 3/log 2. **keep (low)**
56. **G. Rhin**, *Approximants de Padé et mesures effectives d'irrationalité*, Sém. Théorie Nombres Paris 1985–86, Progr. Math. 71 (1987) 155–164. — **verified: false** (statement via Rozier–Terracol's restatement) — *dup*
    **Quote (secondary):** "Proposition 6.3. (Rhin) If u0, u1, u2 are rational integers such that H = max(|u1|, |u2|) ≥ 2, then the form Λ = u0 + u1 log 2 + u2 log 3 verifies |Λ| ≥ H^−13.3."
    **Note:** The explicit all-range bound used by SdW. "7.616" was not seen on any fetched page. **keep**
57. **Q. Wu**, *On the linear independence measure of logarithms of rational numbers*, Math. Comp. 72 (2003) 901–911. — DOI 10.1090/S0025-5718-02-01442-4
    **Quote:** "In this paper we give a general theorem on the linear independence measure of logarithms of rational numbers and, in particular, the linear independence measure of 1, log 2, log 3, log 5 and of 1, log 2, log 3, log 5, log 7."
    **Note:** Method source (LLL choice of polynomials). **keep (low)**
58. **M. Laurent, M. Mignotte, Yu. Nesterenko**, *Formes linéaires en deux logarithmes et déterminants d'interpolation*, J. Number Theory 55 (1995) 285–321. — DOI 10.1006/jnth.1995.1141 — **verified: false** (statement via arXiv:2208.05752) — *dup*
    **Quote (secondary):** "log |Γ| > −24.34 d^4 (max{log b′ + 0.14, 21/d, 1/2})^2 log B1 log B2"
    **Note:** A general two-log bound. Weaker than Rhin for (2,3). **keep (low)**
59. **M. Laurent**, *Linear forms in two logarithms and interpolation determinants II*, Acta Arith. 133 (2008) 325–348. — DOI 10.4064/aa133-4-3 — **verified: false** (via arXiv:1603.08901) — *dup*
    **Quote (secondary):** "log|Λ| ≥ −25.2D^4 (max{log b′ + 0.38, 10/D, 1})^2 log A1 log A2"
    **Note:** **keep (low)**
60. **N. Gouillon**, *Explicit lower bounds for linear forms in two logarithms*, J. Théor. Nombres Bordeaux 18 (2006) 125–146. — https://www.numdam.org/articles/10.5802/jtnb.537 — *dup*
    **Quote:** "Corollary 2.3. Suppose moreover that α1 and α2 are real numbers > 0. Then log |Λ| ≥ −7200 (3.409 + 1.705/D + 0.946 log D) D^4 h log A1 log A2, with h = max{log b + 3.1, 1000/D, 512 + 256/D + 142 log D}."
    **Note:** The h ≥ 1000 floor makes it weak at our sizes. THREADS hoped it would beat Ellison. It does not, for this pair. **kill** (for (2,3))
61. **E. M. Matveev**, *An explicit lower bound for a homogeneous rational linear form in the logarithms of algebraic numbers. II*, Izv. Math. 64 (2000) 1217–1269. — https://mathnet.ru/eng/im314 · DOI 10.1070/IM2000v064n06ABEH000314 — *dup*
    **Quote:** "Corollary 2.3. Suppose that Λ ≠ 0, Aj are given by (2.4), and B by (1.3). Then ln |Λ| > −C1(n)D^2 Ω ln(eD) ln(eB), C1(n) = C1(n, κ) = min{(1/κ)(en/2)^κ 30^{n+3} n^{3.5}, 2^{6n+20}}"
    **Note:** For n = 2: about 5.7·10⁸·ln(eB). **kill** (for (2,3))
62. **A. Baker, G. Wüstholz**, *Logarithmic forms and group varieties*, J. reine angew. Math. 442 (1993) 19–62. — DOI 10.1515/crll.1993.442.19 — **verified: false** (statement via Stewart's lecture notes)
    **Quote (secondary):** "If Λ ≠ 0, then |Λ| > exp(−(16nd)^{2n+4} · log A1 · · · log An · log B)."
    **Note:** **kill** (for (2,3))
63. **Y. Bugeaud**, *Linear Forms in Logarithms and Applications*, IRMA Lect. Math. Theor. Phys. 28, EMS (2018). — https://ems.press/books/irma/157 · DOI 10.4171/183
    **Quote:** "The aim of this book is to serve as an introductory text to the theory of linear forms in the logarithms"
    **Note:** Reference text. **keep (reference)**
64. **J. Simons, B. de Weger**, *Theoretical and computational bounds for m-cycles of the 3n+1-problem*, Acta Arith. 117 (2005) 51–70. — DOI 10.4064/aa117-1-3 — *dup*
    **Quote:** "For our specific case x log 2 + y log 3 however, the result of Rhin [Rh] is best. From it we derive the following estimate. Lemma 12. Λ > e^−13.3(0.46057+log K)."
    **Note:** Venue correction: Acta Arith., not Math. Comp. (PROGRAM.md's reference line). 0.46057 = ln log₂3. **keep**
65. **O. Rozier, C. Terracol**, *Paradoxical behavior in Collatz sequences*, Discrete Math. 349 (2026) 115167; arXiv:2502.00948. — https://arxiv.org/abs/2502.00948
    **Quote:** "Lemma B.1. For every positive integers j and q with q > 12, there holds |2^j − 3^q| > 2.56^q/2."
    **Note:** A citable modern packaging of Ellison in o-units. It confirms F3's "≈2.56^o". **keep**
66. **OEIS A028507**, *Continued fraction expansion for log_2(3)*. — https://oeis.org/A028507
    **Quote:** "Continued fraction expansion for log_2(3)."
    **Note:** [1;1,1,2,2,3,1,5,2,23,2,2,1,1,55,1,4,3,1,1,15,1,9,2,5,7,…]. A100977 is unrelated. **keep**
67. **OEIS A005664**, *Denominators of convergents to log_2 3* (numerators A005663). — https://oeis.org/A005664
    **Quote:** "Denominators of convergents to log_2 3."
    **Note:** q = 1,1,2,5,12,41,53,306,665,15601,31867,79335,111202,190537,10590737,… These are the o-values where ceilings are hardest. **keep**
68. **T. L. Draper, F. A. Saad**, *Space-entropy lower bounds for random sampling*, arXiv:2607.14503 (2026). — https://arxiv.org/abs/2607.14503
    **Quote:** "the current best known bound on the irrationality exponent of log(3) is µ(log(3)) ≤ 5.116201, which is a corollary of the stronger result ν(1, ln(2), ln(3)) ≤ 4.116201 [BLS18, Theorem 1]."
    **Note:** Independent 2026 confirmation that BLS 2018 is still the record (their log = log₂). **keep (support)**
69. **M. Mignotte, P. Voutier** (appendix M. Laurent), *A kit for linear forms in three logarithms*, arXiv:2205.08899 (accepted Math. Comp.). — https://arxiv.org/abs/2205.08899
    **Quote:** "We provide a technique to obtain explicit bounds for problems that can be reduced to linear forms"
    **Note:** Three logs (2, 3 and one more) would be needed for 5x+1 or for "letter-weighted" forms. **open (low)**
70. **R. K. Jha**, *An upper bound of three for the irrationality exponent of log 3/log 2*, GitHub/Zenodo preprint (2026). — https://github.com/rohitkrjha/log23-measure · DOI 10.5281/zenodo.23256301
    **Quote:** "For θ = log(3)/log(2), the paper establishes"
    **Note:** **Caution.** It claims μ ≤ 3. Unrefereed, AI-assisted per its README, unchecked. It must not be used as the record. **kill** (until vetted)

*(70 entries. Entries 30, 31, 41, 54, 56, 58, 59 and 62 are `verified: false`: 8 unverified, 62 verified. 21 entries are tagged dup because they were named in the dedup files; each still extracts something new.)*

---

## 5. Leads for round 2

1. **Levin 2019, full text** (Invent. Math., paywalled). It has a linear-recurrence application ("classifies when terms from simple linear recurrence sequences can have a large gcd"). Rotation families S(w_j) along a run are such recurrences. Get the exact exceptional-set statement for n = 3.
2. **Huang–Levin 2022 §4** (exceptional set). Which subtori actually occur, and whether any effective description exists.
3. **Bondareva–Luchin–Salikhov 2018**. Extract an explicit H₀ (or reconstruct it from their integral construction). An explicit Λ > E^{−4.12} would cut the bounded-ceiling threshold (o ≈ 60) and F3's crossover drastically.
4. **Bugeaud–Evertse 2017, proof of Thm 1.2**. Compute c₁ for the lever-type recurrences (roots 2^d, 3, 1) to make H5 quantitative and effective.
5. **Grieve–Wang (moving targets)**. Can slowly growing letters be absorbed? This would extend H3 to families with growing letter values beyond SdW.
6. **Corvaja–Zannier, *Applications of Diophantine Approximation to Integral Points and Transcendence*** (Cambridge Tracts 212, 2018). The gcd chapter. The page was not fetchable here.
7. **Stewart 2013, Theorem 2**: ord_p(a^n − b^n) < p·exp(−log p/(52 log log p))·log a + ord_p n. A possible bound on how much of D a single prime p can supply, for periodic words.
8. **Lagarias 1990, rational cycles** (other theme, dedup). The empirical distribution of k(w) = D/G over words. It tests whether the 2-run and m-run predictions (k ≥ |D|^{1−ε}) are visible numerically.
9. **Campagna–Dill–Wilms 2026**. Follow for any n-uniform statement (the only conceivable route to (b) inside this theory).
10. **F. Luca, "On the greatest common divisor of u−1 and v−1 with u and v near S-units"** (Monatsh. Math., c. 2005; not verified here). It may allow "near-S-unit" coefficients such as the c_i.

---

## 6. Claims in BRIEF.md / PROGRAM.md that the literature (or the algebra above) contradicts or corrects

1. **F2 "…and therefore unboundedly many runs".** This does not follow. Two-parameter families such as 1^{L₁}2^{L₂} with L₂/L₁ → (log₂3 − 1)/(2 − log₂3) have slope → log₂3 with only two runs. They are excluded anyway (§3.1: the gcd identity plus Ellison, elementary for m = 2), and fixed-m families are covered by Levin (ineffective). So the practical conclusion survives, but for m ≥ 3 only ineffectively unless the size test of §3.3 succeeds.
2. **Task brief: "bounded m runs = Simons–de Weger m-cycles".** This is inaccurate. SdW's m counts letters ≥ 2 (local minima). 1^{L₁}2^{L₂} is an L₂-cycle.
3. **PROGRAM §3: Rhin's μ(1, log 2, log 3) ≤ 7.616 is "best for this case", and Salikhov is "a different number, not the one that governs |2^E − 3^o|".** Bondareva–Luchin–Salikhov 2018 Thm 1 bounds |h₁ln2 + h₂ln3 + h| > H^{−4.116201}, which *is* the form E ln 2 − o ln 3 (h = 0). So asymptotically the Salikhov line governs and beats Rhin. Rhin remains best only as an explicit all-H statement (H^{−13.3}).
4. **PROGRAM references: "Simons–de Weger, Math. Comp. 74 (2005)".** The paper is Acta Arith. 117 (2005) 51–70.
5. **PROGRAM §2 / "exclusion lives on the 6-free axis".** Not contradicted, but sharply limited. For ceilings with a bounded number of S-unit terms and growing exponents, sixfree(C) ≥ |C|^{1−ε} (Evertse 1984; Bugeaud–Evertse 2017). A small 6-free part needs a constant ceiling (the lever) or unboundedly many terms.
6. **THREADS (dedup file, not BRIEF).** (a) "3^n − 2^n has a primitive prime > 3 for all n > 30" via BHV: Zsigmondy already gives it for all n ≥ 2. (b) GLNP 2017 classifies Φ*_n(q) only for prime powers q, so it cannot serve as the (2,3) collapse atlas.
7. **F3 is confirmed.** Ellison's 2.56^o beats Rhin/SdW up to o ≈ 570. Rozier–Terracol 2026 state |2^j − 3^q| > 2.56^q/2 for q > 12.
