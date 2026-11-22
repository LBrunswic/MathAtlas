# Literature review, round 2: theme `chase-arithmetic` (citation chase from the arithmetic hooks)

*Agent: chase-arithmetic. Date: 2026-10-30. 39 entries: **29 new verified sources** and 10 already-cited sources (tagged `dup`). Eight of the dups were re-read for new content. The other two (Aliyev, Kaneda) were added in parallel by `chase-words-limits`. Bibliography lines: `bib-chase-arithmetic.jsonl`.*

*Method. Forward citations came from the Semantic Scholar API (Corvaja–Zannier 2005, Levin 2019). Abstracts came from the arXiv API, review texts from the zbMATH Open API, and full texts from arXiv PDFs, numdam (Ellison 1971), chebsbornik.ru (Bondareva–Luchin–Salikhov 2018), the CWI repository (de Weger's thesis, a scanned book) and the TeX source of Lagarias's annotated bibliography. Items marked **(derived here)** are my own algebra. The arithmetic constants and the 1^a2^b identity were checked with a few lines of Python. That was arithmetic only: no engine run and no word search.*

---

## 1. Executive summary

1. **There is no effective gcd bound for differences of S-units, even with bases 2, 3, 4.** Every successor of Bugeaud–Corvaja–Zannier relies on the Subspace theorem: Corvaja–Zannier, Hernández–Luca, Luca 2005, Varjú, Levin, Xiao, Huang–Levin–Xiao and Yasufuku. Luca's zbMATH reviewer and Varjú both state that the threshold is ineffective.
   * Varjú's Theorem 4 is the sharpest two-binomial statement: α = 7ε²/512 and N = ⌊32/(7ε)⌋ are explicit, but C is ineffective.
   * The only explicit statement fit for Lean is an elementary pigeonhole/lattice bound **(derived here)**: if g ⊥ 6 divides both 2^{x₁}−3^{y₁} and 2^{x₂}−3^{y₂}, then (ln g)² ≤ 2·ln2·ln3·|x₁y₂−x₂y₁|.
2. **No gcd theorem is uniform in the number of terms (round 1 confirmed).** The nearest is Yasufuku 2025: ε(n) is explicit (ε(3) ≤ 0.35), but the exceptional hypersurface is ineffective.
3. **de Weger 1987 gives a better explicit floor than Ellison.** |2^x−3^y| < min(2^x,3^y)^{0.9} with min > 10¹⁵ has the single solution (84, 53), which has D < 0.
   * Every positive cycle with o ≥ 32 therefore has ln D ≥ 0.98875·o.
   * This beats Ellison everywhere and beats Rhin up to o ≈ 876.
4. **BLS 2018's H₀ is not explicit, confirmed in the primary source.** It enters through Hata's Lemma 2.1 ("H ⩾ H₀(μ)"). No improvement of 5.116201 was found up to Oct 2026.
5. **The 6-free axis has an explicit tool.** Bugeaud–Laurent 1996 is fully explicit and p-adic. It makes v₂ and v₃ of two-term ceilings explicitly O((log o)²).
6. **The 1^a2^b exclusion was not found in the literature.**
   * It is a b-cycle in Simons–de Weger's sense, and Hercher covers only b ≤ 91.
   * Rozier 1991 bounds cycles with ≤ k parity blocks, but 1^a2^b has 2b blocks.
   * The proof has the shape of Steiner's 1-circuit theorem: a two-sided Davison equation (§3.1).

---

## 2. Hook-by-hook: the best statements, and what they give for (a) two-run words, (b) three-run words and (c) the 6-free axis

### Hook 1: Corvaja–Zannier gcd(u−1, v−1) and effective forms (bases 2, 3, 4)

**Best results.**
* **Varjú, arXiv:2104.04367, Theorem 4.** The setup: "Let a₁, b₁, a₂, b₂ ∈ Z be numbers that are not divisible by any prime in S_f. Let s₁, t₁, s₂, t₂ ∈ S … Assume further that (1) gcd(a₁s₁ − b₁t₁, a₂s₂ − b₂t₂) ≥ H^ε." The conclusion is one of three cases:
  * "(a) H ≤ C";
  * "(b) max(a₁, b₁, a₂, b₂) ≥ H^α";
  * "(c) there are n₁, n₂ ∈ Z not both 0 such that |n₁|, |n₂| ≤ N − 1 and (a₁s₁/b₁t₁)^{n₁} = (a₂s₂/b₂t₂)^{n₂}."

  Varjú adds: "The constant C is ineffective, but α and N can be made explicit … provided N = ⌊32/(7ε)⌋, α = (7/512)ε²."
* **Luca 2005**, from the zbMATH review: "gcd(f(n)aⁿ+g(n), f₁(m)b^m+g₁(m)) < exp(ε max{m,n}) holds for all but finitely many pairs of positive integers (m,n)". The review adds: "bounds on the largest exceptional pair are not effectively computable." This version has *independent* exponents (m, n), which is the shape of the two-run gcd.
* **Hernández–Luca 2003** (dup; now verified on zbMATH): "gcd(s₁−1,s₂−1) < (max{|s₁|,|s₂|})^ε".
* **Corvaja–Rudnick–Zannier 2004**: the order of a non-exceptional matrix modulo N "goes to infinity faster than any constant multiple of log N". For diag(2,3) this is the order of ⟨2,3⟩ mod N.
* **The lattice lemma (derived here; §3.2)**: the explicit, effective baseline that Varjú's Corollary 3 ("ord(Q)/(log Q)² → ∞") improves ineffectively.

**(a) Two-run words** w = 1^a2^b, with u = 3^a − 2^a and v = 4^b − 3^b.
* Literature: log gcd(u, v) ≤ ε·max(a ln3, 2b ln2) once max(a, b) > C(ε). This is ineffective. Varjú's alternative (c) never occurs, because (3/2)^{an₁} = (4/3)^{bn₂} forces n₁ = n₂ = 0.
* Explicit: gcd(u, v) ≤ min(u, v) trivially, and gcd(u, v) ≤ exp(1.2341·√(ab)) by the lattice lemma (Δ = ab).
* For 3x+1 the trivial bound already suffices (§3.1). For general letters, gcd(A₁, A₂) ≤ exp(1.2341·√(|d₁−d₂|·L₁L₂)).

**(b) Three-run words.**
* The m = 3 representative is not a pair of binomials: C₃ has three terms (round 1, §3.1). So pairwise-binomial theorems apply only if the main loop's expression bounds G by c·gcd(A_i, A_j) for some pair. In that case:
  * Varjú applies with bounded coefficients (ineffective);
  * the lattice lemma gives gcd(A_i, A_j) ≤ exp(1.2341·√(|d_i−d_j|·L_iL_j)) explicitly.
* With de Weger's floor (Hook 5), any such pairwise ceiling excludes a three-run word once min(|A_i|, |A_j|)·c < 3^{0.9·o}. Since min_i log|A_i| ≤ (2/3)·o·ln3 for three runs, the trivial bound suffices *if* the pairwise reduction holds.
* No literature result gives an effective bound for a genuine 3-variable gcd.

**(c) The 6-free axis.** Not applicable: these gcds are prime to 6.

### Hook 2: follow-ups to Levin 2019 (effective, partially effective, uniform)

**Best results.**
* **Xiao 2021 (Math. Z. 2024)**: extends Levin to "two coprime multivariable polynomials evaluated at algebraic numbers" and to gcds of two non-simple linear recurrences. "The proofs rely on Schmidt's Subspace Theorem."
* **Huang–Levin–Xiao 2024**: gcd inequalities on surfaces that are complements of three numerically parallel curves, including "families of S-unit equations".
* **Yasufuku 2025 (Monatsh.)**, an unconditional n-variable result: "gcd(x₁−α₁,…,x_n−α_n) < max{|x_i|}^{ε(n)} (|x₁⋯x_n|'_S)^{1/(n−1)} … one can take ε(2) ≤ 0.45, ε(3) ≤ 0.35", outside "a possibly reducible hypersurface Z". Yasufuku 2026 (BLMS) extends this to codimension-2 blowups.
* **Guo–Nguyen–Sun–Wang 2021**: over *function fields*, the Vojta abc conjecture for tori holds "with exceptional sets that can be determined effectively". This is a Layer-1 analogue only.
* **Levin 2014 (ANT)**: an *effective* solution of f(u,v) = w in S-units for |S| ≤ 3. This is the only effective higher-dimensional S-unit tool, and S = {∞, 2, 3} has exactly |S| = 3. It is a unit equation, not a gcd bound.

**Verdict on effectivity and uniformity.**
* No effective version of the S-unit gcd theorem in 𝔾_mⁿ (n ≥ 2) exists over number fields. The partial exceptions are explicit *exponents* (Varjú's α and N; Yasufuku's ε(n)) and *function-field* effectivity (Guo–Nguyen–Sun–Wang).
* No version is uniform in the number of terms: every statement is for a fixed polynomial pair or a fixed n, and Z depends on it. **Round 1's "none found" is confirmed.**

**What this gives.**
* (a) Two-run: nothing beyond Hook 1.
* (b) Three-run: G ≤ e^{ε·o} off Z (Levin, Xiao), ineffectively. If G divides a 3-fold simultaneous gcd of shifted S-units, Yasufuku's fixed ε(3) ≤ 0.35 applies, still off an ineffective Z.
* (c) 6-free axis: nothing.

### Hook 3: Evertse 1984, Bugeaud–Evertse 2017, and effective S-parts

**Best results.**
* **Bugeaud–Evertse 2017** (dup, re-read):
  * Theorem 1.1 (ineffective): |u_n|^{δ−ε} ≤ [u_n]_S ≤ |u_n|^{δ+ε}, with δ = −Σ_{p∈S} log max|α_i|_p / log max|α_i|. For the program's ceilings (roots 2^d, 3, 1) δ = 0.
  * Theorem 1.2 (effective, dominant root): "[u_n]_S ≤ |u_n|^{1−c₁}, for every n ≥ c₂".
  * The proof shows that c₁ ≈ c₉/(C₂^s·Q·log Q) with Q = ∏ log q_i, and that C comes from Matveev's three-log bound. So c₁ is astronomically small (≈ 10⁻¹⁰ order; my estimate, not stated in the paper).
* **Győry–Mignotte–Shorey 1990**, Theorem 2 (two-term sums, effective): "Q(N_S(β)) ≥ exp{C₃(log log N_S(β))²/log log log N_S(β)}". Here N_S(β) is exactly the S-free part. The bound is on its *radical*, not its size.
* **Bugeaud–Laurent 1996** (explicit p-adic two-log bound), in the restatement of Batte–Ddamulira–Kasozi–Luca 2024, Lemma 2.2: "v_p(γ₁^{b₁}γ₂^{b₂} − 1) ≤ 24pg/((p−1)(log p)⁴) E² D⁴ h′(γ₁)h′(γ₂)", with "E := max{log E′ + log log p + 0.4, 10, 10 log p}". The leading constants are:
  * p = 2: 24·2/(log 2)⁴ = **207.94·g**;
  * p = 3: 72/(2(log 3)⁴) = **24.71·g**.
* **Yamada 2010**: removes a hypothesis of Bugeaud–Laurent and gets "ν_p(x^{p−1}−1) ≤ 283(p−1)(log xy)(log y)/(log p)²+4".
* **Bérczes–Evertse–Győry 2009**: explicit height bounds for a₁x₁ + a₂x₂ = 1 over a division group. **Yu 2007**: the explicit p-adic n-log bound, needed for three-term sums.

**(c) The 6-free axis, quantitatively.**
* For a *two-term* ceiling C = A·2^x − B·3^y, fixed A and B prime to 6:
  * v₂(C) = v₂((B/A)·3^y − 1) once x > v₂(A), and similarly v₃(C) = v₃((A/B)·2^x − 1).
  * Bugeaud–Laurent bounds each by an explicit K·(log max(x,y))².
  * So sixfree(C) ≥ |C|·exp(−K′(log o)²), fully explicit. When B/A is a power of 3 (pure binomials), lifting-the-exponent (LTE) gives v ≤ v(exponent) + 2 elementarily.
* For *three-term* ceilings, Yu 2007 (three logarithms) is needed. It is explicit, with constants of order 10¹⁰.
* Effective S-part bounds for 2^a − 3^b are not needed (D ⊥ 6).

### Hook 4: Bondareva–Luchin–Salikhov 2018 (H₀, later improvements, μ(log₂3))

**Best results.**
* **BLS 2018, primary text** (dup, now read in full).
  * Theorem 1 holds for "H ⩾ H₀".
  * The proof ends with Hata's Lemma 2.1, applied to Θ₁ = ln(4/3) and Θ₂ = ln(9/8) under the hypotheses "𝐻 = max(|𝐿1|, |𝐿2|), 𝜇 > 𝜆/𝜏, 𝐻 ⩾ 𝐻0(𝜇)".
  * The constants are τ = 1.422145 and λ ≤ 5.853833, giving λ/τ = 4.116201.
  * **H₀ is never computed.** It depends on how fast (1/n)·ln|ε_n| converges to −τ, computed by Laplace and saddle-point asymptotics without error terms. An explicit H₀ would require explicit error terms in those asymptotics (and in Hata's lemma).
* **Salikhov 2007** (dup; now verified on zbMATH) has the same pattern: "Q ≥ Q₀, where Q₀ is a sufficiently large number. Then |q+p₁ ln 2+p₂ ln 3| > 1/Q^{4.125}."
* **Later improvements.** None was found up to Oct 2026. Draper–Saad 2026 (round 1) still cite BLS as the record. A 2026 constant-discovery survey (Leibtag et al., not added) lists nothing newer for log 3.
* **The explicit all-range record for (1, log 2, log 3)** is still Rhin 1987. It is now verified on zbMATH ("une très bonne mesure d'indépendance linéaire sur Z effective de 1, log 2 et log 3"), and its usable form is Simons–de Weger's Lemma 12, |Λ| ≥ H^{−13.3}.
  * Rhin–Toffin 1986 show what such fully explicit Padé bounds look like: "|a+b log(3/4)+c log(5/4)| ≥ exp(−(88 log H+196))".
  * The simplest explicit irrationality measure of log 3/log 2 *for all q* is Waldschmidt's "|log 3/log 2 − p/q| > q^{−15}, when (p,q) = 1". This is quoted via Lagarias's annotation of Rozier 1990; the primary is a popular article and was not fetched.
* **Bugeaud 2015 (HRJ)** gives effective measures for log(a₁/a₂)/log(b₁/b₂). Its sharp form needs a₁ < 6a₂/5 with a₁ > 16, which (2,3)-ratios do not satisfy. So it is no help here, but it records Gouillon's constant 8550 in a usable rational-number form.

**What this gives.**
* μ(log₂3) ≤ 5.116201 asymptotically. Usable explicitly: Rhin (exponent 14.3 for log₂3) and Waldschmidt (exponent 15, all q).
* For (a)/(b): every exclusion that reduces to "0 < E·ln2 − o·ln3 < 3^{−cb}" needs only *some* explicit finite measure, because the left side is exponentially small (§3.1).

### Hook 5: Ellison 1971 and sharper explicit floors for |2^x − 3^y|

**Best results.**
* **Ellison 1971** (dup; re-read in the numdam scan).
  * Statement: S = {1,…,11,13,14,16,19,27} and |2^x − 3^y| > 2^x·e^{−x/10} for x ∉ S.
  * Remark (a): "The smallest value of the ration c/2^x occurs when x = 19, y = 12; it is 0.0136…"
  * Remark (b): the continued fraction of log₂3 was computed until the denominators exceeded 10⁵⁵⁰, so the constant 1/10 can be traded for a larger exceptional set.
  * **Theorem 3(2) is exactly the requested shape**: "There exist two effectively computable numbers K = K(a, b, m, n)" and x₀ such that min_y |a·m^x − b·n^y| > m^x·x^{−K} for x > x₀. Ellison gives no explicit K. Rhin/SdW makes it explicit with K = 13.3.
* **de Weger 1987 (JNT 26) and thesis (CWI Tract 65, 1989), Theorem 5.2(a).** All solutions of |p₁^{x₁} − p₂^{x₂}| < min(·)^{0.9} for primes p₁ < p₂ < 200 with min > 10¹⁵ are listed. The thesis applies it on p. 122: "By Theorem 5.2(a) we see that the inequality |x − y| < min(x,y)^{0.9} has only two solutions: (x,y) = (2⁶⁵, 5²⁸), (2⁸⁴, 3⁵³)."
  * Hence |2^x − 3^y| ≥ min(2^x, 3^y)^{0.9} whenever min > 10¹⁵ and (x, y) ≠ (84, 53).
  * 2⁸⁴ − 3⁵³ < 0, so the exception is irrelevant for positive cycles.
  * The thesis also restates Ellison as "|2^x − 3^y| > exp(x·(log 2 − 1/10))".
  * Caveat: the scan lacks the pages with the statement of Theorem 5.2 itself (printed pp. 104–105). Its content is taken from the zbMATH review and from the p. 122 application above.
* **Tijdeman 1973 / Shorey–Tijdeman 1986, Theorem 1.1**, as restated by de Weger: "x − y > y/(log y)^c" for 3-smooth x > y ≥ 3, with c computable. This is the "2^x/x^c" shape, and c = 13.3 via Rhin.

**Thresholds at critical E** (ln|D| lower bounds; Ellison and Rhin columns as in ledger §3):

| o | de Weger 0.9·o·ln3 | Ellison | Rhin/SdW |
|---|---|---|---|
| 32 | 31.6 | 30.3 | −17.1 |
| 60 | 59.3 | 56.9 | 5.3 |
| 100 | 98.9 | 94.3 | 42.5 |
| 306 | 302.6 | 287.7 | 253.9 |
| 570 | 563.6 | 536.2 | 535.7 |
| 1000 | 988.8 | 940.1 | 1000.6 |

de Weger applies from o = 32 (3³² = 1.85·10¹⁵ > 10¹⁵) and beats Rhin until o ≈ 876. Below o = 32, check D directly.

**What this gives.**
* (a) 1^a2^b, positive cycle with o ≥ 32: D ≤ 3^a − 2^a < 3^a and D ≥ 3^{0.9(a+b)} together force b < a/9. Then E/o < 1.1 < log₂3, so D < 0, a contradiction (§3.1).
* (b) Any three-run ceiling of size < 3^{0.9o} is excluded.
* The Lean form is one Prop, `deWeger1987 : ∀ x y, 10^15 < min (2^x) (3^y) → (x,y) ≠ (84,53) → (min (2^x) (3^y) : ℝ)^(9/10) ≤ |2^x − 3^y|`. It replaces `Ellison1971` as the floor for o ≥ 32.

### Hook 6: cycles with two blocks; is the 1^a2^b exclusion known?

**Dictionary.** Gap d corresponds to the Terras parity block 1·0^{d−1}. So the gap word 1^a2^b has parity vector 1^a(10)^b, i.e. cyclically 1^{a+1}0(10)^{b−1}:
* b blocks of consecutive odd steps (b local minima), so it is a Simons–de Weger **b-cycle**, not a 2-cycle (round 1 noted the same);
* 2b parity blocks;
* b descents.

**What the literature covers.**
* **Steiner 1977/78** (1-circuits; gap word 1^{k−1}(l+1)) via Davison's equation (2^{k+l} − 3^k)·h = 2^l − 1. Rozier 1990 gave a simpler proof using Waldschmidt's q^{−15}.
* **Rozier 1991**: "for any k there are only a finite number of cycles having ≤ k blocks". This does not cover 1^a2^b, which has 2b blocks.
* **Brox 2000**: few descents (d(C) < 2 log|C|). 1^a2^b has b ≈ 0.585·o descents.
* **Simons 2005/2007**: 2-cycles. **Simons–de Weger 2005 and Hercher 2023**: m-cycles with m ≤ 91. These exclude 1^a2^b only for b ≤ 91.
* **Farruggia–Lawrence–Waterhouse 1996**: the parity vector 1 0^k, i.e. one-letter gap words.
* **Knight 2026** (dup): Christoffel ("high") cycles.
* **Chisala 1994**: a least-element bound.

**Verdict.** No source excludes 1^a(10)^b, or two periodic blocks in general, for unbounded b. The search covered Lagarias's two annotated bibliographies (TeX source grepped), arXiv title search, and EXCLUDED_PATTERNS.md. The exclusion appears **new as a stated result**, though it is a direct analogue of Steiner's method (§3.1).

---

## 3. Derived items for the main loop (not literature)

### 3.1 The two-sided Davison equation for 1^a2^b (derived here; identities checked numerically for a, b < 7)

Put u = 3^a − 2^a and v = 4^b − 3^b. With S = 3^b·u + 2^a·v and D = 2^{a+2b} − 3^{a+b} = 2^a·v − 3^b·u:

$$S - D = 2\cdot 3^{b}\,u,\qquad S + D = 2^{a+1}\,v .$$

On a 3x+1 cycle with x₀ = S/D (the element starting the 1-run):

$$D\cdot\frac{x_0-1}{2\cdot 3^{b}} = 3^{a}-2^{a},\qquad D\cdot\frac{x_0+1}{2^{a+1}} = 4^{b}-3^{b}.$$

Both cofactors are integers. So x₀ ≡ 1 (mod 2·3^b) and x₀ ≡ −1 (mod 2^{a+1}). Example: a = b = 1 gives the negative cycle −5 → −7, with D = −1 and cofactors −1 and −1. The second equation is Davison's (2^{k+l}−3^k)·h = 2^l − 1 with h = (n+1)/2^k, now with a second partner.

* **Exclusion, elementary part.** A positive cycle needs 0 < D ≤ 3^a − 2^a. So 0 < (a+2b)·ln2 − (a+b)·ln3 < 3^{−b}, while D > 0 needs b > 1.41·a, i.e. b > 0.585·o.
* **Exclusion, arithmetic input.** Any explicit finite irrationality measure of log₂3 finishes the proof: Waldschmidt's q^{−15}, Rhin's H^{−13.3}, Ellison, or de Weger's 0.9-floor (cleanest: b < a/9).
* **For 3x+k.** The same identities hold. G = D/k turns the equations into k·u ≡ 0 (mod D), so the bound becomes D ≤ k·u. It excludes 3x+k cycles of this shape for b > log₃k + O(log o).

### 3.2 The lattice lemma (derived here; standard pigeonhole)

**Lemma.** Let g ≥ 1 with gcd(g, 6) = 1, and let v₁ = (x₁, −y₁) and v₂ = (x₂, −y₂) satisfy 2^{x_i}·3^{−y_i} ≡ 1 (mod g). Let Δ = |x₁y₂ − x₂y₁| > 0. Then

$$(\ln g)^2 \le 2\ln 2\,\ln 3\cdot\Delta,\qquad\text{i.e.}\qquad g\le \exp\big(1.23410\sqrt{\Delta}\big).$$

**Proof.**
* H = ⟨2, 3⟩ ≤ (ℤ/g)^× is the image of ℤ², and the kernel contains ℤv₁ + ℤv₂, so |H| ≤ Δ.
* The integers 2^m·3^n < g with m, n ≥ 0 are distinct mod g. There are at least as many as the area of the triangle, (ln g)²/(2 ln2 ln3): each such point owns its unit square, and these squares cover the triangle.

**Uses.**
* Two-run (1, 2): Δ = ab.
* Two-run (d₁, d₂): Δ = |d₁ − d₂|·L₁L₂.
* gcd(2^a − 3^b, 2^c − 3^d) ≤ exp(1.2341·√|ad − bc|).
* Spot check: max over a, b < 60 of ln gcd(3^a − 2^a, 4^b − 3^b)/√(ab) is 0.726, against 1.234.

**Context.** This is the trivial (ln Q)² lower bound for ord_Q⟨2, 3⟩ that Varjú's Corollary 3 ("ord(Q)/(log Q)² → ∞") and Corvaja–Rudnick–Zannier improve *ineffectively*. Varjú's box-principle remark ("|a|, |b| ≤ Q^{1/2} such that Q | as − b") shows that coefficient sizes cannot be relaxed beyond H^{Cε}. The lemma needs only finite group order and a lattice-point count.

---

## 4. Idea → hook map

| # | idea | source(s) | touches | what it would give | verdict | cheapest first test |
|---|---|---|---|---|---|---|
| C1 | de Weger 0.9-floor replaces Ellison | de Weger 1987/1989; Ellison 1971 | F3, ledger §3, OP1 | ln D ≥ 0.98875·o for o ≥ 32 (vs 0.940·o); best explicit floor until o ≈ 876 | **keep** | State `deWeger1987` as a Prop; re-run the threshold table; check D directly for o < 32 |
| C2 | Two-sided Davison equation for 1^a2^b | §3.1 (derived); Steiner 1977; Rozier 1990 | OP3, F2 (2 runs) | Elementary exclusion of all positive 1^a2^b cycles (o ≥ 32 by C1, direct check below) | **keep** | Lean: prove S − D = 2·3^b·u and S + D = 2^{a+1}·v, then D ∣ u |
| C3 | Lattice lemma for binomial gcds | §3.2 (derived); Varjú Cor. 3; CRZ 2004 | OP1, OP3 | Explicit gcd ≤ exp(1.234·√Δ) for any two 2/3-binomials; feeds m = 3 if G reduces to a pairwise gcd | **keep** | Lean: card(⟨2,3⟩ ≤ (ℤ/g)ˣ) ≤ Δ and ≥ #{2^m3^n < g} |
| C4 | Varjú Thm 4 (two binomials, explicit α, N) | Varjú 2021/22; Luca 2005; Hernández–Luca 2003 | OP3, F1 | G ≤ H^ε for pairs of binomials with coefficients ≤ H^{7ε²/512}; ineffective C | **open** (qualitative) | — |
| C5 | Explicit p-adic two-log bound for v₂, v₃ of ceilings | Bugeaud–Laurent 1996; Batte et al. 2024; Yamada 2010; Yu 2007 | PROGRAM §2 (6-free axis), OP1 | sixfree(C) ≥ \|C\|·exp(−K(log o)²) for two-term ceilings, explicit K (p = 2: 207.94·g·E²·h′h′) | **keep** (as a limit and a tool) | Evaluate the bound for a lever ceiling family; compare with LTE |
| C6 | Explicit H₀ for BLS | BLS 2018; Hata 1993; Salikhov 2007 | F3, H6 | Λ > E^{−4.12} with an explicit range | **open** (hard: needs explicit saddle-point error terms) | Not worth it now: C1 and Rhin cover o < 10⁴ |
| C7 | Effective n-dimensional gcd | Xiao; Huang–Levin–Xiao; Yasufuku 2025/26; Guo–Nguyen–Sun–Wang; Levin 2014 | OP3, F2 (b) | None effective over ℚ; ε(3) ≤ 0.35 explicit but ineffective Z | **kill** for exclusion; keep as a citation | — |
| C8 | Uniformity in the number of terms | (same; none found) | (b) words | — | **kill** (confirmed) | — |
| C9 | Explicit Bugeaud–Evertse c₁ | Bugeaud–Evertse 2017 (proof of Thm 1.2) | H5 | c₁ ≈ 1/(Matveev constant); numerically useless | **kill** | — |
| C10 | Block-count finiteness | Rozier 1991; Brox 2000; Hercher 2023 | OP2, OP3 | Finitely many cycles with ≤ k parity blocks (Rozier) or few descents (Brox); covers 1^a2^b only for b ≤ 91 | **keep** (context) | — |

---

## 5. Annotated bibliography

Format: citation; URL/DOI; **quote** (verbatim from the fetched page; math is rendered in plain text, and the note says when the page is a secondary); note; **verdict**.

### A. gcd of S-unit differences (hooks 1–2)

1. **P. P. Varjú**, *On the multiplicative group generated by two primes in Z/QZ*, arXiv:2104.04367 (v2 2022; "to appear in Analysis at Large: Dedicated to the Life and Work of Jean Bourgain"). https://arxiv.org/abs/2104.04367
   **Quote:** "This is intimately related to the problem of bounding the greatest common divisor of S-unit differences, which we revisit." / "The constant C is ineffective, but α and N can be made explicit. The theorem always holds (with a suitably large C depending on ε and S) provided N = ⌊32/(7ε)⌋, α = (7/512)ε²."
   **Note:** Theorem 4 bounds gcd(a₁s₁ − b₁t₁, a₂s₂ − b₂t₂) with *non-S coefficients up to H^α*. This is the sharpest form for two binomials, and it covers both two-run gcds and any pairwise reduction for three runs. It improves Luca 2005, which fails when the S-units are of comparable size. Its box-principle remark caps any improvement in α. **keep** (open as a route; qualitative)
2. **F. Luca**, *On the greatest common divisor of u−1 and v−1 with u and v near S-units*, Monatsh. Math. 146 (2005) 239–256. DOI 10.1007/s00605-005-0303-6; zbMATH 1107.11029.
   **Quote (zbMATH review, S. T. Parsell):** "for every ε > 0 the inequality gcd(f(n)a^n+g(n), f_1(m)b^m+g_1(m)) < exp(ε max{m,n}) holds for all but finitely many pairs of positive integers (m,n)" / "the author notes that bounds on the largest exceptional pair are not effectively computable."
   **Note:** Independent exponents (m, n), exactly the two-run shape gcd(3^a−2^a, 4^b−3^b). The reviewer's explicit statement of ineffectivity answers hook 1 negatively. **keep** (limit)
3. **P. Corvaja, Z. Rudnick, U. Zannier**, *A lower bound for periods of matrices*, Comm. Math. Phys. 252 (2004) 535–541; arXiv:math/0309215. DOI 10.1007/s00220-004-1184-6
   **Quote:** "In contrast, we show that if the matrix is not exceptional, then the order of A modulo N goes to infinity faster than any constant multiple of log N."
   **Note:** For A = diag(2,3) this concerns ord_N⟨2,3⟩, the index in the lattice lemma (§3.2). Ineffective, but it tells which side the improvement lies on. **keep (low)**
4. **Z. Xiao**, *Greatest common divisors for polynomials in almost units and applications to linear recurrence sequences*, arXiv:2110.01751; Math. Z. (2024). DOI 10.1007/s00209-024-03453-4
   **Quote:** "We bound the greatest common divisor of two coprime multivariable polynomials evaluated at algebraic numbers, generalizing work of Levin, and going towards conjectured inequalities of Silverman and Vojta." / "The proofs rely on Schmidt's Subspace Theorem."
   **Note:** "Almost units" may absorb bounded non-S coefficients, such as c_i = 2^{d_i} − 3. It also gives gcds of terms of non-simple recurrences, i.e. rotation families. Ineffective. **open**
5. **K. Huang, A. Levin, Z. Xiao**, *A new Diophantine approximation inequality on surfaces and its applications*, arXiv:2406.18879 (2024). https://arxiv.org/abs/2406.18879
   **Quote:** "As applications, we study various Diophantine problems on affine surfaces given as the complement of three numerically parallel ample projective curves: inequalities involving greatest common divisors, degeneracy of integral points, and related Diophantine equations including families of S-unit equations."
   **Note:** The newest Levin-school gcd inequality. Still Subspace-based, with a fixed surface. **kill** (for exclusion)
6. **J. Guo, K. D. Nguyen, C.-L. Sun, J. T.-Y. Wang**, *Vojta's abc conjecture for algebraic tori and applications over function fields*, arXiv:2106.15881 (2021).
   **Quote:** "We prove Vojta's generalized abc conjecture for algebraic tori over function fields with exceptional sets that can be determined effectively."
   **Note:** The only *effective exceptional set* found, and only in function fields (the ℤ[X,Y]/ℂ[T] layer, which is closed). **kill** (Layer 1)
7. **Y. Yasufuku**, *GCD inequalities inspired by Vojta's conjecture*, Monatsh. Math. 206 (2025) 259–279. DOI 10.1007/s00605-024-02018-1; zbMATH 1570.11089.
   **Quote (zbMATH review, F. Luca):** "gcd(x_1−α_1,…,x_n−α_n)<max{|x_1|,…,|x_n|}^{ε(n)} (|x_1⋯x_n|'_S)^{1/(n−1)} … Here, ε(n) is not arbitrarily small but one can take ε(2)≤0.45, ε(3)≤0.35"
   **Note:** An unconditional n-variable simultaneous gcd with *explicit fixed exponents*. It is the nearest thing to "uniform in n" (ε(n) → 0), but Z is ineffective and depends on n. **open (low)**
8. **Y. Yasufuku**, *GCD inequalities arising from codimension-2 blowups*, Bull. London Math. Soc. (2026). DOI 10.1112/blms.70349 (abstract via the Semantic Scholar API)
   **Quote:** "Assuming a deep Diophantine geometry conjecture by Vojta, Silverman proved an inequality giving an upper bound for the greatest common divisor (GCD). In this paper, we unconditionally prove a weaker version of this inequality."
   **Note:** {S = D = 0} is codimension 2, so this is the program's geometric setting. Ru–Vojta method; ineffective. **open (low)**
9. **B. Barrios**, *An upper bound for the generalized greatest common divisor of rational points*, arXiv:2411.06050; Bull. Aust. Math. Soc. (2025), DOI 10.1017/s0004972724001229.
   **Quote:** "We give an upper bound for the generalized greatest common divisor of a point x∈X with respect to an irreducible subvariety Y⊆X also defined over K."
   **Note:** Gives h_gcd ≤ (c + ε)·h with a *fixed* c < 1 from Riemann–Roch (after García-Fritz–Pastén), not an arbitrary ε. There is still an exceptional Zariski-closed set. **kill**
10. **S. Hernández, F. Luca**, *On the largest prime factor of (ab+1)(ac+1)(bc+1)*, Bol. Soc. Mat. Mexicana (3) 9 (2003) 235–244. zbMATH 1108.11030. *dup* (unverified in round 1; now verified)
    **Quote (zbMATH review):** "one has gcd(s_1−1,s_2−1) < (max{|s_1|,|s_2|})^ε"
    **Note:** The S-unit form over ℤ, with s_i multiplicatively independent integers. **keep (low)**
11. **Y. Bilu, F. Luca**, *Multiplicative dependence in the sumset of multiplicative groups*, arXiv:2607.28857 (2026).
    **Quote:** "We show that, up to finitely many exceptions, non-zero sums x_1+y_1 and x_2+y_2, with x_1, x_2∈Γ and y_1,y_2∈Δ, are multiplicatively dependent only if x_1/x_2=y_1/y_2 is a root of unity."
    **Note:** Shows that values 2^a + 3^b-type sums rarely satisfy multiplicative relations. Tangential to G. **kill**
12. **A. Levin**, *Linear forms in logarithms and integral points on higher-dimensional varieties*, Algebra Number Theory 8 (2014) 647–687; arXiv:1303.4125. DOI 10.2140/ant.2014.8.647
    **Quote:** "we generalize an effective result of Vojta on the three-variable unit equation by giving an effective solution of the polynomial unit equation f(u,v)=w, where u,v, and w are S-units, |S|\leq 3, and f is a polynomial satisfying certain conditions (which are generically satisfied)."
    **Note:** S = {∞, 2, 3} has |S| = 3, so this is the one Baker-type *effective* higher-dimensional tool that fits (2,3) exactly. It solves "F(t₁,t₂) is an S-unit", not "F is divisible by D". It could serve an exceptional tier (k(w) ∈ {2^i3^j}). **open**
13. **P. Corvaja, U. Zannier**, *Applications of Diophantine Approximation to Integral Points and Transcendence*, Cambridge Tracts in Math. 212 (2018). DOI 10.1017/9781108348096; zbMATH 1452.11004.
    **Quote (zbMATH review):** "Chapter 2 addresses the subspace theorem (Schmidt/Schlickewei) and S-unit equations."
    **Note:** The textbook route to the gcd theorems (round-1 lead 6). Whether there is a dedicated gcd chapter was not confirmed. **keep (reference)**

### B. S-parts and explicit p-adic bounds (hook 3)

14. **K. Győry, M. Mignotte, T. N. Shorey**, *On some arithmetical properties of weighted sums of S-units*, Math. Pannon. 1 (1990) 25–43. zbMATH 0738.11034.
    **Quote (zbMATH review, J.-H. Evertse):** "Theorem 2: Let n=1. There are effectively computable numbers C_2,C_3, depending only on a,K,S such that for every β∈B_{1,a} with N_S(β)≥C_2 one has Q(N_S(β))≥exp{C_3(log log N_S(β))^2/log log log N_S(β)}."
    **Note:** N_S(β) is the S-free part; Q is the greatest squarefree divisor. An effective two-term statement, but about the *radical* of the 6-free part, not its size. **kill** (for size)
15. **A. Bérczes, J.-H. Evertse, K. Győry**, *Effective results for linear equations in two unknowns from a multiplicative division group*, Acta Arith. 136 (2009) 331–349. DOI 10.4064/aa136-4-3
    **Quote (zbMATH summary):** "In our result, we give an explicit upper bound in terms of a_1,a_2 and Γ for the heights of the solutions (x_1,x_2)."
    **Note:** An explicit two-term S-unit equation solver, also for points "close to" the group. It is the effective base under any two-term exceptional tier. **keep (low)**
16. **Y. Bugeaud, M. Laurent**, *Minoration effective de la distance p-adique entre puissances de nombres algébriques*, J. Number Theory 61 (1996) 311–342. DOI 10.1006/jnth.1996.0152; zbMATH 0870.11045.
    **Quote (zbMATH review, P. Bundschuh):** "Die zahlreichen, völlig effektiven Ergebnisse der Verff. sind zu umfangreich formuliert, als daß sie hier im einzelnen zitiert werden könnten."
    **Note:** The explicit p-adic two-log bound; the formula is quoted in entry 17. It makes v₂ and v₃ of two-term ceilings explicitly O((log o)²) (C5). **keep**
17. **H. Batte, M. Ddamulira, J. Kasozi, F. Luca**, *On a problem of Pillai involving S-units and Lucas numbers*, arXiv:2401.06555 (2024).
    **Quote:** "Then v_p(γ_1^{b_1} γ_2^{b_2} − 1) ≤ 24pg/((p − 1)(log p)^4) E^2 D^4 h′(γ_1)h′(γ_2), where g > 0 is the smallest integer such that v_p(γ_i^g − 1) > 0." with "E := max {log E′ + log log p + 0.4, 10, 10 log p}".
    **Note:** A verbatim modern restatement of Bugeaud–Laurent's Corollary 1, in the {2,3}-S-unit setting (Pillai with L_n − 2^x3^y). The Lean-ready explicit form. **keep**
18. **T. Yamada**, *A note on the paper by Bugeaud and Laurent …*, J. Number Theory 130 (2010) 1889–1897; arXiv:math/0607072. DOI 10.1016/j.jnt.2010.02.018
    **Quote (zbMATH review):** "Ist p eine Primzahl und sind x,y∈Z∖pZ multiplikativ unabhängig, so gilt ν_p(x^{p−1}−1)≤283(p−1)(log xy)(log y)/(log p)^2+4."
    **Note:** Removes the condition log A_i ≥ (log p)/D from Bugeaud–Laurent. Relevant if a ceiling's 2-adic or 3-adic valuation must be bounded with small heights. **keep (low)**
19. **B. İ. Aydın, H. Batte, İ. İnam, F. Luca, Z. D. Özkaya**, *On the Diophantine inequality |x² − 2^a·3^b| < 3 max{a,b}*, arXiv:2606.18500 (2026).
    **Quote:** "a p-adic lower bound for a linear form in logarithms due to Bugeaud and Laurent is applied to find a rather large bound on max{a,b}. We finish with an application of the LLL algorithm to reduce this bound."
    **Note:** A 2026 worked example of the Bugeaud–Laurent → LLL pipeline for bases {2, 3}, with a complete list (57 solutions). A template for any exceptional-tier enumeration. **keep (low)**
20. **K. Yu**, *p-adic logarithmic forms and group varieties. III*, Forum Math. 19 (2007) 187–280. DOI 10.1515/FORUM.2007.009
    **Quote (zbMATH review, M. Waldschmidt):** "In this final contribution, the author completes his study by reaching estimates in the p-adic case which are likely to be the sharpest ones that the present theory is able to produce."
    **Note:** The explicit p-adic bound for n ≥ 3 logs, needed for v₂ and v₃ of *three-term* ceilings. The constants are huge. **keep (reference)**
21. **Y. Bugeaud, J.-H. Evertse**, *S-parts of terms of integer linear recurrence sequences*, Mathematika 63 (2017) 840–851; arXiv:1611.00485. *dup*
    **Quote:** "there exist effectively computable positive numbers c1 and c2, depending only on (un)n≥0 and S, such that [un]S ≤ |un|^{1−c1}, for every n ≥ c2." / (proof) "n ≤ c11 C3^s Q (log Q)^2".
    **Note:** New extraction: the effective c₁ is about c₉/(C₂^s·Q·log Q), with C from Matveev's bound, so it is numerically negligible (C9). Round-1 lead 4 is answered: not worth computing. **kill** (as a quantitative tool)

### C. Linear forms in log 2, log 3 and irrationality measures (hook 4)

22. **I. V. Bondareva, M. Yu. Luchin, V. Kh. Salikhov**, *Symmetrized polynomials in a problem of estimating of the irrationality measure of number ln 3*, Chebyshevskii Sb. 19(1) (2018) 15–25. DOI 10.22405/2226-8383-2018-19-1-15-25 (full PDF: chebsbornik.ru galley 422/362). *dup*
    **Quote:** "𝐿1 , 𝐿2 , 𝐿 ∈ Z, 𝐻 = max(|𝐿1 |, |𝐿2 |), 𝜇 > 𝜆/𝜏 , 𝐻 ⩾ 𝐻0 (𝜇)." / "𝜏 = min(𝜏1 , 𝜏2 ) = 1.422145" / "𝜆/𝜏 = 4.116201"
    **Note:** New extraction: H₀ comes from Hata's Lemma 2.1 and is never computed. The forms are in Θ₁ = ln(4/3) and Θ₂ = ln(9/8). Making H₀ explicit needs error terms in Laplace and saddle-point asymptotics. Round-1 lead 3 is answered: no H₀ anywhere. **keep** (but C6 is hard)
23. **M. Hata**, *Rational approximations to π and some other numbers*, Acta Arith. 63 (1993) 335–349. DOI 10.4064/aa-63-4-335-349; zbMATH 0776.11033.
    **Quote (zbMATH review, J. Hančl):** "Let us note, that the above measures contain roots of cubic equations with integral coefficients."
    **Note:** The source of Lemma 2.1 (the "H ≥ H₀(μ)" lemma) used by Salikhov 2007 and BLS 2018. An explicit H₀ for the BLS line would start by making this lemma quantitative. **open**
24. **G. Rhin**, *Approximants de Padé et mesures effectives d'irrationalité*, Sém. Théorie Nombres Paris 1985–86, Progr. Math. 71 (1987) 155–164. zbMATH 0632.10034. *dup* (unverified in round 1; now verified)
    **Quote (zbMATH review, P. Philippon):** "Il obtient également μ(√3 log(2+√3)) = 17,207… ainsi qu'une très bonne mesure d'indépendance linéaire sur Z effective de 1, log 2 et log 3."
    **Note:** Confirms that Rhin's (1, log 2, log 3) measure is *effective*, which is what SdW's Lemma 12 (H^{−13.3}) uses. **keep**
25. **G. Rhin, P. Toffin**, *Approximants de Padé simultanés de logarithmes*, J. Number Theory 24 (1986) 284–297. DOI 10.1016/0022-314X(86)90036-3
    **Quote (zbMATH review, F. Beukers):** "| a+b log (3/4)+c log (5/4)| ≥ exp(-(88 log H+196)), where a,b,c∈Z not all zero, H=max(|b|,|c|)."
    **Note:** Shows that Padé methods can yield *all-range, fully explicit* forms (constant 196 included), as opposed to the H₀-type Salikhov line. It is the model for an explicit log₂3 measure. **keep (low)**
26. **V. Kh. Salikhov**, *On the irrationality measure of ln 3*, Doklady Math. 76 (2007) 955–957. DOI 10.1134/S1064562407060361; zbMATH 1169.11032. *dup* (unverified in round 1; now verified)
    **Quote (zbMATH review):** "Suppose that q, p_1, p_2∈Z and Q=max(|q|,|p_1|,|p_2|), Q≥Q_0, where Q_0 is a sufficiently large number. Then |q+p_1 ln 2+p_2 ln 3|>1/Q^{4.125}."
    **Note:** Same non-explicit Q₀ pattern as BLS. **kill** (superseded)
27. **Y. Bugeaud**, *Effective irrationality measures for quotients of logarithms of rational numbers*, Hardy-Ramanujan J. 38 (2015) 45–48. https://hrj.episciences.org/1359
    **Quote:** "There exists an absolute, effectively computable, constant C such that µeff(log(a1/a2)/log(b1/b2)) ≤ C(log a1)(log b1)." / (Theorem G, after Gouillon) "log |y log(a1/a2) − x log(b1/b2)| ≥ −8550(log A)(log B)(log X)(4 + log E)(log E)^{−3}."
    **Note:** Explicit measures for log-quotients. The sharp Theorem 1.2 needs ratios close to 1 (a₁ < 6a₂/5, a₁ > 16), so it does not apply to log₂3 directly. Theorem G is a citable explicit two-log bound for rationals. **kill** (for (2,3))

### D. Explicit floors for |2^x − 3^y| (hook 5)

28. **W. J. Ellison**, *On a theorem of S. Sivasankaranarayana Pillai*, Sém. Théorie Nombres Bordeaux 1970–71, exp. 10. http://www.numdam.org/item/STNB_1970-1971____A10_0/ *dup*
    **Quote:** "There exist two effectively computable numbers K = K(a, b, m, n)" [Theorem 3(2), continuing: … and x₀ such that ω(x) > m^x·x^{−K} for all integral x > x₀] / "The smallest value of the ration c/2^x occurs when x = 19, y = 12; it is 0.0136…" (OCR spacing repaired)
    **Note:** New extraction:
    * Theorem 3(2) is the requested "|2^x−3^y| > 2^x/x^K" with K effective but unstated.
    * The proof is Baker plus a continued fraction computed to 10⁵⁵⁰, so the constant 1/10 is a free trade-off parameter (Remark (b)).
    * The minimal ratio over the exceptional x is 0.0136.

    **keep**
29. **B. M. M. de Weger**, *Solving exponential diophantine equations using lattice basis reduction algorithms*, J. Number Theory 26 (1987) 325–367 (DOI 10.1016/0022-314X(87)90088-6); also *Algorithms for Diophantine Equations*, CWI Tract 65 (1989), Ch. 5–6, https://ir.cwi.nl/pub/13190/
    **Quote (thesis p. 122):** "By Theorem 5.2(a) we see that the inequality | x − y | < min(x,y)^0.9 has only two solutions: (x,y) = (2^65, 5^28), (2^84, 3^53)." / (p. 101) "Ellison [1971b] has proved the following result: for all but finitely many explicitly given exceptions, | 2^x − 3^y | > exp(x·(log 2 − 1/10)) for all x, y ∈ ℕ." / (zbMATH review, A. Pethő) "the diophantine inequality |p_1^{x_1}−p_2^{x_2}| < min(p_1^{x_1},p_2^{x_2})^ϑ under the assumptions: (a) p_1 and p_2 are primes such that p_1<p_2<200"
    **Note:** **The new best explicit floor (C1).**
    * The context of the p. 122 quote assumes min(x,y) > 10¹⁵. For (2,3) the only solution there has 2⁸⁴ < 3⁵³ (D < 0).
    * Positive cycles with o ≥ 32 therefore have ln D ≥ 0.9·o·ln3.
    * The scan lacks printed pp. 104–105 (the theorem statement). Confirm the exact Theorem 5.2(a) wording in the JNT paper before stating the Prop.

    **keep**
30. **T. N. Shorey, R. Tijdeman**, *Exponential Diophantine Equations*, Cambridge Tracts in Math. 87 (1986). zbMATH 0606.10011.
    **Quote (zbMATH review):** "The authors' aim is to give explicitly computable upper bounds for the unknown exponents in the EDE's so that one should be able to apply the known results for polynomial diophantine equations." / (de Weger's restatement of Thm 1.1, thesis p. 101) "there exists a computable number c, depending on max(p_i) only, such that for all x, y ∈ S with x > y ≥ 3, x − y > y/(log y)^c."
    **Note:** The standard reference for the "2^x/x^c" floor shape. c = 13.3 is made explicit by Rhin. **keep (reference)**
31. **T. Miyazaki, R. Scott, R. Styer**, *Handling some Diophantine equation via Euclidean algorithm and its application to purely exponential equations*, arXiv:2604.18991 (2026).
    **Quote:** "We also contribute to the estimation of the number of positive integer solutions (x,y) to the equation a^x−b^y=c for any fixed positive integers a,b and c with both a and b greater than 1."
    **Note:** The current Pillai-count frontier. It is relevant only to the near-miss tier, which Bennett 2003 already settles for (3,2). **kill**

### E. Cycles with block structure (hook 6)

32. **R. P. Steiner**, *A theorem on the Syracuse problem*, Proc. 7th Manitoba Conf. Numer. Math. (1977), Congr. Numer. 20 (1978) 553–559. zbMATH 0474.10004. *dup*
    **Quote (zbMATH review, E. Heppner):** "Dazu wird diese Ungleichungskette zunächst in eine diophantische Gleichung umgeformt, deren Lösungen gute rationale Approximationen an log_2(3/2) liefern."
    **Note:** New use: the 1^a2^b exclusion (§3.1) follows exactly this template, with two Davison equations instead of one. **keep**
33. **O. Rozier**, *Démonstration de l'absence de cycles d'une certaine forme pour le problème de Syracuse*, Singularité 1 no. 3 (1990) 9–12. Quoted via Lagarias, *The 3x+1 problem: an annotated bibliography (1963–1999)*, arXiv:math/0309224 (TeX source).
    **Quote (Lagarias's annotation):** "This paper proves that there are no cycles except the trivial cycle whose iterates (mod 2) repeat a pattern of the form 1^m 0^{m'}." / "Rozier's proof uses effective transcendence bounds similar to Steiner's, but is simpler since he can quote the recent bound |log 3/log 2 − p/q| > q^{−15}, when (p,q) = 1, which appears in M. Waldschmidt"
    **Note:** Gives an all-range explicit measure of log₂3 (exponent 15), enough to close C2 with no Baker constants. The primary was not fetched. **keep**
34. **O. Rozier**, *Problème de Syracuse : « Majorations » élémentaires des cycles*, Singularité 2 no. 5 (1991) 8–11. Via Lagarias, arXiv:math/0309224.
    **Quote (Lagarias's annotation):** "This paper proves that if the integers in a cycle of the 3x+1 function are grouped into blocks of integers all having the same parity, for any k there are only a finite number of cycles having ≤ k blocks."
    **Note:** A bounded-block-count finiteness result. 1^a2^b has 2b blocks, so it is *not* covered. It is the closest published family result to "fixed number of runs". **keep (context)**
35. **C. Farruggia, M. Lawrence, B. Waterhouse**, *The elimination of a family of periodic parity vectors in the 3x+1 problem*, Pi Mu Epsilon J. 10 (1996) 275–280. Via Lagarias, arXiv:math/0309224.
    **Quote (Lagarias's annotation):** "This paper shows that the parity vector 1 0^k is not the parity vector of any integral periodic orbit of the 3x+1 mapping whenever k ≥ 2."
    **Note:** One-letter gap words (k+1) only; trivial in the program. **kill**
36. **B. P. Chisala**, *Cycles in Collatz sequences*, Publ. Math. Debrecen 45 (1994) 35–39. DOI 10.5486/pmd.1994.1379; zbMATH 0820.11005.
    **Quote (zbMATH review, H. Müller):** "Here the author proves that for any m- cycle of positive rationals the least element is at most 1/(2^{(⌈log_2 3⌉/m)} −3)."
    **Note:** A cycle-length lower bound via convergents; m is the number of odd terms. The review says "at most" where Lagarias says "at least as large as (2^{⌈mθ⌉/m} − 3)^{−1}", which looks like a reviewer slip. Superseded by Eliahou and Hercher. **kill**
37. **C. Hercher**, *There are no Collatz-m-Cycles with m ≤ 91*, J. Integer Seq. 26 (2023) Art. 23.3.5; arXiv:2201.00406. *dup*
    **Quote:** "Let $m$ be the number of local minima in such a nontrivial cycle." / "In this paper, we prove $m \geq 92$."
    **Note:** New use: 1^a2^b has b local minima, so Hercher excludes it only for b ≤ 91. That confirms the two-run exclusion is not a corollary of the m-cycle literature. **keep**
38. **Y. N. Aliyev**, *On (special) integer linear combinations of terms of rational cycles for the generalized 3x+1 problem*, Notes Number Theory Discrete Math. 31(3) (2025) 658–666; arXiv:2307.11990. DOI 10.7546/nntdm.2025.31.3.658-666. *dup* (also `aliyev2025special` in `bib-chase-words-limits.jsonl`)
    **Quote:** "It is proved that if the coefficients of the linear combinations satisfy some conditions then these linear combinations are integers."
    **Note:** Prior art adjacent to F1: integer combinations of rotation sums S^{(j)}/D, i.e. the rotation ideal seen from the cycle side. Small. **open (low)**
39. **M. Kaneda**, *Two remarks on the Collatz cycle conjecture*, arXiv:1010.6206 (2010); published in Fibonacci Quart. 53(2) (2015) 168–174, per `bib-chase-words-limits.jsonl`. *dup* (`kaneda2015two`)
    **Quote:** "We also reformulate the Collatz cycle conjecture which is rather a algorithmic problem into a purely arithmetic problem."
    **Note:** Another prior statement of F1's "cycle ⇔ D divides S" dictionary, including the 3x+d view (a cycle element of some 3x+d cycle). It cites Belaga. **keep (low, priority)**

*(39 entries. 29 are new: entries 1–9, 11–20, 23, 25, 27, 29–31 and 33–36. 10 are dup: entries 10, 21, 22, 24, 26, 28, 32, 37, 38 and 39. All quotes come from fetched pages; entries 33–35 quote Lagarias's annotations (a secondary source), and entry 2 and others quote zbMATH reviews. No entry is `verified: false`.)*

---

## 6. Leads for round 3

1. **de Weger 1987, JNT 26, §5 (Theorem 5.2(a) and Table I).** Get the exact statement, including the 10¹⁵ condition and the x_i ≥ 2 hypothesis, before formalizing `deWeger1987`. The CWI scan lacks printed pp. 104–105.
2. **Hata 1993, Lemma 2.1** and the saddle-point step in BLS §2. Estimate what an explicit H₀ would cost. Probably ≥ 10⁵ digits, which would make it useless next to C1 + Rhin; confirm.
3. **Rhin–Toffin 1986 / Rhin 1987 primaries.** The fully explicit (88 log H + 196) style suggests an explicit all-range measure for (1, ln 2, ln 3) better than 13.3 may already be derivable from Rhin's integrals.
4. **Varjú 2021, §2**: whether the proof gives *effective* control when only two primes (2,3) are involved and the coefficients are 1. It does not appear to, but the line structure (Theorem 2) may help OP2 by forbidding two independent returns.
5. **Yasufuku 2025, Theorem 2**: check whether "G divides a 3-fold simultaneous gcd" can be arranged for three-run words. If so, ε(3) ≤ 0.35 gives a qualitative three-run result with an explicit exponent.
6. **Waldschmidt 1987 (Revue du Palais de la Découverte)** and Rozier 1990 primary: verify the all-range q^{−15} statement for log 3/log 2. It is the cheapest arithmetic input for C2.
7. **Levin 2014, §6**: the f(u,v) = w theorem with |S| = 3. Test whether the exceptional tier "D/G ∈ {2^i 3^j}" fits its hypotheses.
8. **Lagarias, annotated bibliography (2010–2019)**, if it exists on arXiv: grep for later two-block or few-run cycle results not found here.

---

## 7. Corrections to round 1 and the ledger

1. **Ledger §3 / F3, "Ellison is the floor up to o ≈ 570".** de Weger 1987 gives a *better* explicit floor: ln D ≥ 0.9·o·ln3 for o ≥ 32 (positive cycles). It beats Ellison at every o ≥ 32 and Rhin up to o ≈ 876. The squeeze threshold and every Ellison-conditional Lean statement can switch Props.
2. **Round 1, H6 / lead 3.** BLS's H₀ is now confirmed absent from the primary. It enters through Hata's Lemma 2.1.
3. **Round 1 entries 3 (Hernández–Luca), 54 (Salikhov) and 56 (Rhin)** were unverified. All three are now verified on zbMATH.
4. **Round 1, lead 4 (compute Bugeaud–Evertse c₁).** Not worth it: c₁ is of order 1/Matveev's constant. Bugeaud–Laurent gives far better explicit control of v₂ and v₃ for two-term ceilings.
5. **Round 1, §3.1 "with Ellison alone this excludes d ≤ 4".** For d = 2 the cleaner route is §3.1 here: D ∣ 3^a − 2^a exactly, with no (2^{d−1} − 1) factor.
