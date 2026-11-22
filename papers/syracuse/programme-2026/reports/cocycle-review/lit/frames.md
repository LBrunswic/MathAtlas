# Theme `frames`: the cocycle seen in other frames

*Literature agent, theme `frames`. Date: 2026-10-29. 39 entries: 35 verified (31 new, 4 re-read
duplicates), 4 unverified. The bibliography lines are in `bib-frames.jsonl`.*

Scope: (1) the affine/metabelian group and its cohomology, (2) Livšic theory, (3) transfer
operators, generating functions and Siegel's (p,q)-adic numina, (4) gcds of rational series and
divisibility sequences, (5) formal and automated approaches, (6) ×2×3 rigidity and Mahler's 3/2
problem.

---

## Executive summary

The prior holds. Several frames restate the program's own cocycle.

- **Siegel's numen** χ₃ : ℤ₂ → ℤ₃ *is* S on infinite words, read 3-adically. His Correspondence
  Principle is "a vast generalization of the Böhm-Sontacchi Criterion" (his words). The 467-page
  thesis excludes no cycle; its Tauberian theorem is unconditional one way only and gives no
  bound.
- **Cohomology.** H¹(affine group, ℚ_λ) is one-dimensional, spanned by [S]. Restricted to ⟨H_w⟩,
  the cycle obstruction lives in H¹(ℤ, ℤ[1/6]_λ) ≅ ℤ/|D| and equals S mod D, which is exactly F1.
  The Bieri–Neumann–Strebel Σ-invariants concern finiteness properties only.
- **Livšic and Kalinin** need trivial periodic data; ours never is (3^o/2^E ≠ 1).
- **Transfer operators and generating functions** (Berg–Meinardus, Neklyudov, Bell–Lagarias) give
  non-effective equivalences. Opfer's 2011 proof was withdrawn. A 2026 spectral-gap claim was
  retracted because the 3x−1 operator passes the same test: F4 in the wild.
- **×2×3 rigidity**, including the effective version of Bourgain–Lindenstrauss–Michel–Venkatesh,
  is about density, while a cycle is an exact zero-sum mod D. No bridge exists.

**Surprise lever.** In Mahler's 3/2 problem, Dubickas (2009) applies the *same* affine cocycle to
two equal digit windows: x_{m+j} − x_{m+i} = (p/q)^m(x_j − x_i), so q^m divides a nonzero
integer. Sturmian complexity (m+1 factors) forces such a repeat, and archimedean size finishes the
proof. This upgrades F5's "a shared prefix strips only a power of 2".

Transferred to cycles as the **repeat lemma** (derived here): a window u at two cyclic positions
forces 2^{E(u)} and 3^{|u|} below x_max ≤ 152·o^{14.3}·M(w), with M the stark ratio. It is
non-vacuous only for low-discrepancy, low-complexity words. Status: open, narrow.

---

## Idea → hook map

| idea | source(s) | open problem / F-item | what it would give | verdict | cheapest first test |
|---|---|---|---|---|---|
| Numen χ₃ = the cocycle S on ℤ₂ (3-adically continuous); Correspondence Principle | Siegel 2020, 2024, 2026 | F1; structure.md §2–3 (C5) | vocabulary only. CP ≡ Böhm–Sontacchi (Siegel's own Remark 15). The functional equations χ(2z)=χ(z)/2, χ(2z+1)=(3χ(z)+1)/2 are C5 | **kill** as a lever (keep the "frames" vocabulary) | none |
| (p,q)-adic Wiener Tauberian "spectral theorem" | Siegel 2024 thesis Thm 4.6 | open problem 1 | "periodic ⇒ translates of χ̂ − x·1₀ not dense"; the converse holds only under extra hypotheses; no quantitative output | **kill** | none |
| L¹ method: archimedean bound \|χ(φ(z))\| ≤ ‖η̂‖_{L¹} | Siegel 2024 Thm 4.11 | open problem 1 (size axis) | size bounds on cycle elements over structured subfamilies; at best reproduces S/D bounds | **kill** (weaker than Böhm–Sontacchi + Rhin) | none |
| Generating functions / functional equations on the disk | Berg–Meinardus 1994/95; Neklyudov 2021; Bell–Lagarias 2015; Opfer 2011 | F4 | equivalent reformulations: "no extra holomorphic solution", rationality vs natural boundary, operator index ≥ #cycles; nothing effective | **kill** (Opfer = cautionary tale) | none |
| Transfer operator on ℤ/2^k, spectral gap | m4cd4r4 2026 (retracted cycle claim) | F4 | none: the 3x−1 operator passes the same certificate (cert ≈ 0.606) and 3x−1 has cycles | **kill** (it is the F4 control in the wild) | none |
| Random-walk / structure theorem | Kontorovich–Sinai 2002; Tao 2022 | F5 counting | density-1 statements; drift log g − (d/(d−1)) log d; cycles are a null set | **kill** for cycles | none |
| Livšic / Kalinin periodic-data theorems | Livšic 1972; Kalinin 2011 | F1 | the hypothesis "trivial periodic data" fails for every periodic word (linear part 3^o/2^E ≠ 1); over ℚ₃ the cocycle is already a coboundary through χ₃; integrality is not a cohomological invariant | **kill** | none |
| H¹ frame: obstruction ∈ H¹(⟨H_w⟩, ℤ[1/6]_λ) ≅ ℤ/\|D\|, class = S mod D | derived here; group-cohomology background | F1; "Layer 1 closed" | H¹(Γ, ℚ_λ) ≅ ℚ·[S]. This confirms that Layer 1 is closed and that the cycle condition is purely the residue S mod D | **keep** as framing, **kill** as a lever | none |
| BNS / Bieri–Strebel Σ-invariants of ℤ[1/6] ⋊ ⟨2,3⟩, BS(1,n) | BNS 1987; Brown 1987; Bieri–Strebel 1980 | Layer 1 | finiteness properties (finite presentability, finitely generated kernels); blind to integer fixed points | **kill** | none |
| Mahler's "double convergence": one series, two limits (ℝ and ℚ₂) | Mahler 1968; Siegel's "frames" | F1 | for an *aperiodic* digit word the two limits differ (fractional part vs −integer part); for a *periodic* word (a cycle) both equal S/D, so there is no information | **kill** for cycles | none |
| **Repeat lemma** (Dubickas pigeonhole transferred to cycles) | Dubickas 2009; Bugeaud–Dubickas 2005; Dubickas–Novikas 2005 (lead) | **open problem 2; F5** | u repeated at distinct cyclic positions i, j ⇒ 2^{E(u)} \| x_i − x_j ≠ 0 and 3^{\|u\|} \| x_{i+\|u\|} − x_{j+\|u\|} ≠ 0, so E(u) < log₂ x_max ≤ 14.3·log₂ o + log₂ M(w) + 7.3. Excludes words with M = O(poly o) and a repeated window above that scale (e.g. Christoffel words for o ≳ 80, which Knight already excludes Baker-free); vacuous when log₂ M ~ √o | **open** (narrow) | on bench words: longest repeated cyclic factor's E(u) vs log₂(152·o^{14.3}·M(w)); find the discrepancy threshold where the inequality bites |
| AFS pumping lemma: uv^k admissible ⇒ q^{(k−1)\|v\|} \| π(uv) − π(u) | Akiyama–Frougny–Sakarovitch 2008 | F2 (u^p·β families), F5 | the same telescoping as P0/P1; 2-power divisibility along powers | **kill** (duplicates F2/F5) | none |
| Base-3/2 numeration: odd step = append digit 1 | Eliahou–Verger-Gaugry 2025; AFS 2008 | — | a second numeration in which odd steps are shifts (dual to base 2 for halvings); a cycle is a word read in both systems at once | **open** (vocabulary) | write one cycle candidate's orbit in base 2 and base 3/2 and see whether the gap word becomes a digit pattern |
| ×2×3 rigidity (Furstenberg, Rudolph, Host, BLMV) | Furstenberg 1967; Rudolph 1990; Host 1995; Tal 2021; BLMV 2009 | F1, F3 | density/measure rigidity; the finite-N form (BLMV Thm 1.10: {2^k3^l m/N} is (log log log N)^{−c}-dense) is still only density; a cycle is an exact additive relation | **kill** | none |
| Counting S(w) ≡ 0 mod D with exponential sums over ⟨2,3⟩ mod D | BLMV §1.5 (cites Bourgain, BGK); Tao 2022 (mod 3^n analogue) | F5 counting budget | expected number ≈ C(E−1,o−1)/D ≈ e^{(1.04−1.099)o}; a rigorous version needs error ≤ #words·D^{−δ} with δ > 0.95, which is far beyond known bounds | **open**, likely out of reach | none |
| gcd of S-unit expressions | Bugeaud–Corvaja–Zannier 2003 (dup, B1); Corvaja–Zannier 2005 | F1 | gcd(u−1, v−1) < max(\|u\|,\|v\|)^ε for two S-units; S has o terms (growing), outside the theorem | **kill** (reference) | none |
| Divisibility sequences | Bézivin–Pethő–van der Poorten 1990 | open problem 3 | recurrence divisibility sequences divide products of Lucas sequences; D(w^k) is of this type, so this is the cyclotomic picture already in hand | **kill** | none |
| Formal verification | Merle (Lean, unrefereed); Yolcu–Aaronson–Heule (dup); mathlib4 has 0 Collatz files; AFP has none | — | Lean formalisations of Halbeisen–Hungerbühler 1997, Lagarias 1990 and Steiner 1978 exist; a "BakerSeparation" exponent-6 hypothesis circulates unproven | **keep** (substrate + caution) | check whether C1–C11 port onto the Merle `ContentDescent`/`ContentSeparation` files |

---

## 1. Analysis by question

### 1.1 "S is a 1-cocycle on a metabelian group": what does it imply?

Let Γ = ⟨a, b⟩ ⊂ Aff(ℚ), with a(x) = (3x+1)/2 and b(x) = x/2. Write λ : Γ → ⟨2,3⟩ ⊂ ℚ^× for the
linear part, τ for the translation part (the pushed-forward S), and N = Γ ∩ ℚ for the translation
subgroup, so that Γ/N ≅ ℤ². The following is standard group cohomology, derived here and not
taken from a source.

- **Inflation–restriction.** 0 → H¹(ℤ², ℚ_λ) → H¹(Γ, ℚ_λ) → Hom_{ℤ²}(N, ℚ_λ).
  H¹(ℤ², ℚ_λ) = 0 because λ is nontrivial, and Hom_{ℤ²}(N, ℚ_λ) is one-dimensional. Hence
  **H¹(Γ, ℚ_λ) = ℚ·[τ]**: up to scale and coboundary, S is the *only* cocycle. The coboundaries
  are c·(λ − 1), which is C6 (c·D). This is the cohomological form of "Layer 1 is closed".
- **The cycle condition is a restriction class.** Fix g = H_w. Then
  H¹(⟨g⟩, ℤ[1/6]_λ) = ℤ[1/6]/(λ(g) − 1) ≅ ℤ/|D|, and the class of τ|_{⟨g⟩} is S(w) mod D.
  An integer fixed point exists ⇔ this class vanishes ⇔ D | S. This is F1, stated in
  cohomological language: the program's G = gcd(S, D) is the order of the restriction class.
- **The Σ-invariant literature.** BNS (1987), Brown (1987) and Bieri–Strebel (1980) classify
  characters χ : Γ → ℝ by finite generation of kernels and by finite presentability. For
  ℤ[1/6] ⋊ ℤ², the complement Σ^c comes from the places 2, 3 and ∞ of ℚ (Bieri–Strebel). None of
  this sees the restriction to a cyclic subgroup, so it says **nothing beyond F1**.
  Verdict: null, confirmed.

### 1.2 Livšic: why periodic data give nothing

- Livšic's theorem (1972), and Kalinin's GL(m,ℝ) version (2011), say: *trivial* periodic data
  imply a coboundary.
- Our periodic data along the period-o orbit of the shift on ℤ₂ is the affine map H_w, with
  linear part 3^o/2^E ≠ 1. It is never trivial, so the hypothesis fails at every periodic point.
- Over ℚ₃ the cocycle is a coboundary on the nose: Siegel's χ₃ is the transfer function
  (χ₃(2z+j) = H_j(χ₃(z))). But χ₃ takes non-integer values, and integrality of a fixed point is
  not a cohomology invariant.
- The non-uniform hyperbolicity is a further obstacle: H₀ = x/2 is a 3-adic isometry. So neither
  Livšic nor Kalinin constrains which periodic orbits are integral. **Null, confirmed.**
- A *positive* Livšic theorem or sub-action theory (ergodic optimization) is the only adjacent
  idea with content. Lead only: it would recast the Halbeisen–Hungerbühler "Christoffel is
  extremal" result.

### 1.3 Transfer operators, generating functions, numina

- **Berg–Meinardus (1994; 1995).** The bivariate generating function satisfies a linear
  functional equation, and Collatz ⇔ no holomorphic solution of the homogeneous equation other
  than h₀ + h₁z/(1−z) (zbMATH review). The reviewer: "it still remains open whether these methods
  will be suitable".
- **Neklyudov (2021).** The index of Id − 𝒯 on H²(D) bounds the number of cycles from above, and
  the Berg–Meinardus adjoint has no nontrivial fixed points in H²(D). Nothing effective follows.
- **Bell–Lagarias (2015).** Inverse-orbit generating functions have the unit circle as natural
  boundary except possibly for m = 1, 2, 4, 8. Collatz ⇔ those four are rational.
- **Opfer (2011)** claimed a proof by this route and withdrew it (Parabola editorial). The gap
  analysis is cited as de Weger 2011 (TU/e report, not retrieved).
- **Zeta functions.** I found no dynamical zeta function of the 3x+1 map, and no "expected number
  of cycles" series Σ 1/|D(w)|, in the literature (searched; negative result). The heuristic count
  is the F5 budget.
- **Siegel (2020–2026).** χ₃ is the cocycle on ℤ₂. It converges 3-adically on non-natural z (his
  "frames": series whose topology of convergence varies with the point). The thesis gives an
  explicit χ̂_H and a (p,q)-adic Wiener Tauberian theorem, and turns the periodic-point question
  into density of translates. In the paper's own words, Part I.5's contour-integral version is
  blocked by "hypergeometric growth".
  **Assessment:** the most cocycle-like frame in the theme, and identical to the program's object
  on rational z. No exclusion, no bound, unrefereed (math.GM). Kill as a lever.
- **Spectral-gap retraction (2026, GitHub).** A uniform gap for the Syracuse mod-2^k transfer
  operator was first claimed to eliminate cycles, then retracted. The 3x−1 operator passes the
  same certificate even more strongly, yet 3x−1 has cycles. Averaging over lifts erases orbits.
  This is F4 observed independently.

### 1.4 Rational series, gcd, divisibility

- **Bugeaud–Corvaja–Zannier (2003) and Corvaja–Zannier (2005)** bound gcd(u−1, v−1) for *two*
  S-units. S is a sum of o S-units with o growing, so the theorem does not apply.
- **Bézivin–Pethő–van der Poorten (1990).** Recurrence divisibility sequences divide products of
  Lucas sequences. D(w^k) along powers is a Lucas-type sequence, which is already the
  cyclotomic/Bang–Zsigmondy picture of open problem 3.
- **For a fixed modulus m**, {w : S(w) ≡ 0 mod m} is a regular language: S mod m is a rational
  series over ℤ/m (Berstel–Reutenauer, dup). But m = D varies with w, so decidability results do
  not transfer. Kill.

### 1.5 Formal and automated approaches

- **Yolcu–Aaronson–Heule** (dup): the value-preserving base-swap rules commute a binary digit
  past a ternary digit. That is the cocycle relation at digit level. Already covered in
  `syracuse_words`.
- **mathlib4** has 0 files matching "collatz" (GitHub code search, 2026-10-29). The AFP mirror
  has 3 hits, all examples inside unrelated theories.
- **Merle (Lean 4, unrefereed).**
  - Formalisations of Halbeisen–Hungerbühler 1997, Lagarias 1990 and Steiner 1978.
  - A "no cycle with k ≤ 1322" result conditional on `BakerSeparation`, i.e.
    (2^s − 3^k)·k⁶ ≥ 3^k. The author's erratum says this is *not* a published bound (Rhin's
    exponent is 13.3) and that the headline theorem was circular.
  - **Caution for the program:** never import that hypothesis.
- **Barina** (dup): no new method item.

### 1.6 ×2×3 rigidity and Mahler's 3/2 problem

- **×2×3.**
  - Furstenberg (1967): non-lacunary semigroup orbits of irrationals are dense.
  - Rudolph (1990): a non-Lebesgue ×2,×3-ergodic measure has zero entropy.
  - Host (1995): the normality criterion behind those results.
  - BLMV (2009): effective versions, including finite-N density of {2^k 3^l m/N} for (N, 6) = 1.
  - None of these speaks to an exact additive relation Σ_k 2^{e_k}3^{o−1−k} ≡ 0 mod D. The
    Lagarias overview cites Furstenberg only as a neighbouring dynamics book. Tao (2022) works
    3-adically with characteristic functions, not with ×2×3 rigidity. **No bridge exists:
    confirmed null.**
- **Mahler's 3/2 problem** uses the *same* affine group, maps x ↦ (3x + ε)/2.
  - **Mahler (1968):** "the same series converges in two different senses and to two different
    limits" (ℝ: 3r₀; ℚ₂: −3g₀). For cycles the word is periodic and both limits equal S/D, so
    there is no lever.
  - **AFS (2008):** the base-p/q language is not context-free, and no expansion is eventually
    periodic. The proof (Lemma 8) is the cocycle telescoping along v^k: the program's P1/F2.
  - **Eliahou–Verger-Gaugry (2025):** in base 3/2, an odd Collatz step appends the digit 1.
  - **Dubickas (2009) / Bugeaud–Dubickas (2005):** these supply the **repeat lemma**
    (§2 below). Flatto–Lagarias–Pollington (1995) and Lu–Zheng (2026) give the interval bounds
    1/p and (1 + q/p − q²/p²)/p.

---

## 2. The repeat lemma (derived here; the one surprise lever)

**Setting.** A primitive cycle with gap word w of length o has distinct odd elements
x₀, …, x_{o−1}. For a window u = w[i, i+m) define
S_u = Σ_{k<m} 3^{m−1−k}2^{e_k(u)}. Then x_{i+m} = (3^m x_i + S_u)/2^{E(u)}.

**Statement.** Suppose u = w[i, i+m) = w[j, j+m) with i ≠ j (mod o). Subtracting the two
equations gives 2^{E(u)}(x_{i+m} − x_{j+m}) = 3^m(x_i − x_j). Hence:

- **2-adic (prefix) form:** 2^{E(u)} | x_i − x_j ≠ 0, so 2^{E(u)} < x_max. This is F5's
  "shared prefix strips a power of 2".
- **3-adic (suffix) form:** 3^m | x_{i+m} − x_{j+m} ≠ 0, so 3^m < x_max. Its rotation-sum form
  is S(vu) − S(v′u) = Y^m(S(v) − S(v′)): a shared *suffix* strips a pure power of 3, the dual of
  F5.

**Size bound.** x_j = S^{(j)}/D ≤ o·3^{o−1}·M(w)/D, where M(w) = max_{j,k} 2^{e_k}/3^k over all
rotations (the stark ratio). With the Rhin / Simons–de Weger bound
|D| > 0.00219·3^o/o^{13.3}, this gives

> **x_max < 152·o^{14.3}·M(w), hence every repeated cyclic window u has
> E(u) < 14.3·log₂ o + log₂ M(w) + 7.3.**

**Why the 6-free axis missed it.** On the 6-free axis the stripped 2- and 3-powers are invisible,
which is why F5 called the shared prefix useless. Dubickas's point is that they are visible on the
**archimedean** axis: a nonzero integer divisible by 2^{E(u)} has size at least 2^{E(u)}.

**What it excludes.** By pigeonhole, a cyclic word whose factor complexity p_w(m) is < o at
m ≈ (14.3 log₂ o + log₂ M + 7.3)/1.585 has a repeated window above the threshold.

- **Christoffel words** have cyclic complexity m+1, and M ≤ 2. So for large o (o ≳ 80 with Rhin)
  they are excluded. This is a Baker-*dependent* echo of Knight's Baker-*free* high-cycle
  theorem.
- **More generally**, the lemma kills low-discrepancy (M ≤ poly(o)) and low-complexity words.

**Where it is vacuous.** For generic balanced-slope words, e_k − k·log₂3 behaves like a bridge
with fluctuations ~√o. Then log₂ M ~ √o and the bound is empty. Also, the longest repeat in a
random word is only ≈ 2 ln o/1.04 letters, i.e. E ≈ 2.1·log₂ o.

**Dependence on Baker.** The lemma depends on Baker through x_max. If the irrationality measure of
log₂3 were 2, the threshold would drop to ≈ (2+ε)·log₂ o + log₂ M. That is the same order as the
typical longest repeat, which makes it borderline interesting.

**Verdict:** open, narrow. It covers open problem 2 only on the low-discrepancy stratum. It is
blind to 3 vs 5 (F4): the identical lemma holds for 5x+1.

---

## 3. Annotated bibliography

*Entries marked (dup) are re-reads of already-cited sources with a new note. "Verified" means the
quote was taken from a page or PDF I fetched.*

### A. Siegel's (p,q)-adic analysis and the numen

**[siegel2020numen]** M. C. Siegel, *The Collatz Conjecture & Non-Archimedean Spectral Theory:
Part I — Arithmetic Dynamical Systems and Non-Archimedean Value Distribution Theory*, arXiv
preprint (v1 2020, v3 2023). https://arxiv.org/abs/2007.15936 — doi:10.48550/arXiv.2007.15936.
- Quote (abstract): "we construct a function $χ_{q}:\mathbb{Z}_{2}\rightarrow\mathbb{Z}_{q}$
  (the Numen of $T_{q}$) and prove the Correspondence Principle (CP): $x\in\mathbb{Z}\backslash\left\{ 0\right\}$
  is a periodic point of $T_{q}$ if and only there is a $\mathfrak{z}\in\mathbb{Z}_{2}\backslash\left\{ 0,1,2,\ldots\right\}$
  so that $χ_{q}\left(\mathfrak{z}\right)=x$."
- From the PDF: χ₃ is the unique f with "f(2z) = f(z)/2", "f(2z+1) = (3f(z)+1)/2", and
  Remark 15: "The functional equation (2.16) is a vast generalization of the Böhm-Sontacchi
  Criterion (1.10)."
- Note: χ_q(j) = H_j(0) is the translation part of the affine composite, i.e. S/2^E. The
  functional equations are C5, and χ_q(B₂(n)) = χ_q(n)/(1 − M_q(n)) is S/D.
- Verdict: kill as a lever; the numen is the program's cocycle.

**[siegel2021contour]** M. C. Siegel, *The Collatz Conjecture & Non-Archimedean Spectral Theory —
Part I.5 — How To Write The (Weak) Collatz Conjecture As A Contour Integral*, arXiv preprint
(2021). https://arxiv.org/abs/2111.07883
- Quote: "The hypergeometric growth of the series as $\textrm{Re}\left(s\right)\rightarrow-\infty$
  seems to preclude direct evaluation of the contour integrals via residues, but asymptotic results
  may still be achievable."
- Note: a Dirichlet-series (Perron) frame for periodic points. The author records that it is
  blocked. Verdict: kill.

**[siegel2024thesis]** M. C. Siegel, *(p,q)-adic Analysis and the Collatz Conjecture*, PhD
dissertation, Univ. of Southern California (2022); arXiv 2024, 467 pp.
https://arxiv.org/abs/2412.02902 — doi:10.48550/arXiv.2412.02902.
- Quote (abstract): "one can show that the question 'is $x\in\mathbb{Z}\backslash\left\{ 0\right\} $
  a periodic point of $H$?' is essentially equivalent to 'is the span of the translates of the
  Fourier transform of $χ_{H}\left(\mathfrak{z}\right)-x$ dense in an appropriate non-archimedean
  function space?'"
- Thm 4.6 (PDF): "I. If x is a periodic point of H, then the translates of the function
  χ̂H(t) − x1_0(t) are not dense". Part II (the converse) needs H integral plus extra conditions.
- Thm 4.11 (the "L¹ method") bounds |χ(φ(z))| ≤ ‖η̂‖_{L¹}. Its sample application to χ₃ is
  self-described as "relatively poor".
- Note: "frames" are Siegel's device for series that converge in different topologies at
  different points. That is Mahler's 1968 double-convergence phenomenon (see [mahler1968unsolved]).
- Verdict: kill (reformulation, no bound, unrefereed math.GM).

**[siegel2026hydra]** M. C. Siegel, *The Hydra Map and Numen Formalisms for Collatz-Type
Problems*, arXiv preprint (v1 Jan 2026, v4 Sep 2026). https://arxiv.org/abs/2601.17030
- Quote: "This paper is meant to serve as a technical manual for use of Hydra maps and numens in
  future research."
- Note: generalises to O_K of global fields. Since F4 already says every ℤ[X,Y] identity holds for
  every Syracuse-type map, this is the same "generic layer" again. Verdict: kill.

**[siegel2021functional]** M. C. Siegel, *Functional Equations Associated to Collatz-Type Maps on
Integer Rings of Algebraic Number Fields*, arXiv (2021), **withdrawn**.
https://arxiv.org/abs/2111.07882
- Quote (abstract): "In 1995, Meinardus & Berg presented a reformulation of the Collatz
  Conjecture in terms of a functional equation in a single complex variable over the open unit
  disk."
- Comment field: "Withdrawn due to an error in section three".
- Note: a second cautionary withdrawal in the functional-equation line. Verdict: kill.

### B. Generating functions, functional equations, operators

**[berg1994functional]** L. Berg, G. Meinardus, *Functional equations connected with the
Collatz problem*, Results in Mathematics 25 (1994) 1–12. doi:10.1007/BF03323136; zbMATH
0810.11013.
- Quote (zbMATH review): "the authors prove that the ``Collatz''-conjecture holds if and only if
  in \(z=0\) there exists no holomorphic solution \(h(z)= \sum_{n=0}^ \infty h_ n z^ n\) of the
  functional equation \(h(z^ 3)= h(z^ 6)+ {1\over {3z}} \sum_{\nu=0}^ 2 e^{2\pi\nu i/3} h(e^{2\pi\nu i/3} z^ 2)\)
  other than \(h_ 0+ h_ 1 {z\over {1-z}}\)."
- Note: the generating-function frame. It is linear in the indicator of orbits, so it cannot see
  the multiplicative cocycle. Verdict: kill.

**[berg1995collatz]** L. Berg, G. Meinardus, *The 3n+1 Collatz Problem and Functional
Equations*, Rostock. Math. Kolloq. 48 (1995) 11–18.
https://www.math.uni-rostock.de/math/pub/romako/heft48/berg2.html
- Quote: "This paper reports on some functional equations, which arise in connection with the
  famous 3n+1 Collatz problem."
- Note: survey of two analytic versions of the conjecture. Verdict: kill.

**[parabola2011opfer]** Editorial, *Parabola* 47(2) (2011), UNSW.
https://parabola.unsw.edu.au/sites/default/files/2024-04/vol47_no2_e.pdf
- Quote: "Opfer updated his preprint on 17 June 2011 with “the statement ‘that the Collatz
  conjecture is true’ has to be withdrawn, at least temporarily”."
- Note: documents the withdrawal of Opfer's functional-equation "proof". Siegel's thesis adds
  that it was "thought to have actually proved Collatz until a gap was discovered", citing
  de Weger 2011. Verdict: kill (cautionary tale).

**[opfer2011analytic]** G. Opfer, *An analytic approach to the Collatz 3n+1 problem*, Hamburger
Beiträge zur Angewandten Mathematik 2011-09 (2011). **Unverified**: the Hamburg epub server is
offline and redirects to a catalogue. The bibliographic data come from Siegel's thesis
bibliography [118]. Verdict: kill.

**[berg2013negative]** L. Berg, G. Opfer, *An analytic approach to the Collatz 3n+1 problem
for negative start values*, Comput. Methods Funct. Theory 13 (2013) 225–236.
doi:10.1007/s40315-013-0017-z. **Unverified**: only the zbMATH/Crossref metadata could be
fetched; the review text is unavailable. Note: the 3n−1 case through the same equations; the
negative cycles exist (F4). Verdict: kill.

**[neklyudov2021functional]** M. Neklyudov, *Functional analysis approach to the Collatz
conjecture*, arXiv (2021, v9). https://arxiv.org/abs/2106.11859
- Quote: "We prove that absence of nontrivial cycles of $T$ leads to hypercyclicity of operator
  $\mathcal{T}$. In the second part we show that the index of operator
  $Id-\mathcal{T}\in\mathcal{L}(H^2(D))$ gives upper estimate on the number of cycles of $T$."
- Note: the index bound is non-effective. Verdict: kill.

**[bell2015natural]** J. P. Bell, J. C. Lagarias, *3x+1 inverse orbit generating functions
almost always have natural boundaries*, Acta Arith. 170 (2015) 101–120.
https://arxiv.org/abs/1408.6884
- Quote: "The $3x+1$ Conjecture is equivalent to the assertion that $f_{1, m}(z)$ is a rational
  function of $z$ for the remaining values $m=1,2, 4, 8$."
- Note: the rigidity sits in the analytic continuation of orbit-indicator series. No cycle
  information beyond the conjecture itself. Verdict: kill.

**[kontorovich2002structure]** A. V. Kontorovich, Ya. G. Sinai, *Structure Theorem for
(d,g,h)-Maps*, Bull. Braz. Math. Soc. 33 (2002) 213–224. https://arxiv.org/abs/math/0601622;
zbMATH 1055.11009.
- Quote: "the probability distribution corresponding to the density converges to the Wiener
  measure with the drift log(g) - d/(d-1)log(d) and positive diffusion constant."
- Note: for 3x+1 the drift is log 3 − 2 log 2 < 0. This is a statistical statement, and cycles
  are a null set. Verdict: kill for cycles.

**[tao2022almost] (dup)** T. Tao, *Almost all orbits of the Collatz map attain almost bounded
values*, Forum Math. Pi 10 (2022) e12. https://arxiv.org/abs/1909.03562
- Quote (PDF, eq. 1.22): "Syrac(Z/3n Z) ≡ Fn (Geom(2)n ) mod 3n". Also: "It is then a routine
  matter to then deduce that almost all positive integers do not lie in a periodic Collatz orbit".
- New note: Tao's offset map F_n is the cocycle S/2^E with i.i.d. geometric gaps, read mod 3^n.
  His Fourier-decay estimate is the 3-adic analogue of what a mod-D counting argument would need
  (§1.6). Verdict: kill for cycles; lead for counting.

**[m4cd4r42026spectral]** m4cd4r4 (GitHub), *A uniform spectral gap for the Syracuse transfer
operator*, repository README (2026, unrefereed).
https://github.com/m4cd4r4/collatz-conjecture-spectral-gap
- Quote: "A uniform spectral gap of the transfer operator does NOT imply the absence of cycles.
  Decisive control: the `3x-1` map has known non-trivial cycles (`{5,7}`, `{17,25,...}`) yet its
  transfer operator passes the identical certificate".
- Note: an independent, documented instance of F4. A transfer-operator frame on ℤ/2^k is blind
  to cycles. Verdict: kill.

### C. Livšic theory

**[livsic1972cohomology]** A. N. Livšic, *Cohomology of dynamical systems*, Math. USSR-Izv. 6
(1972) 1278–1301. doi:10.1070/IM1972v006n06ABEH001919. https://mathnet.ru/eng/im2373
- Quote: "In this paper criteria for the cohomological nullity of functions on phase spaces of
  various dynamical systems".
- Note: periodic-data criteria for coboundaries over U-systems and topological Markov chains. Our
  periodic data (affine maps with linear part 3^o/2^E) are never trivial. Verdict: kill.

**[kalinin2011livsic]** B. Kalinin, *Livšic theorem for matrix cocycles*, Ann. of Math. 173 (2011)
1025–1042. doi:10.4007/annals.2011.173.2.11. https://arxiv.org/abs/0808.0350
- Quote: "We show that if $A$ has trivial periodic data, i.e. $A(f^{n-1} p) ... A(fp) A(p) = Id$
  for each periodic point $p=f^n p$, then there exists a Hölder continuous function
  $C: X \to GL(m,\mathbb R)$ satisfying $A (x) = C(f x) C(x) ^{-1}$".
- Note: the affine cocycle embeds in GL(2) (C1). Its periodic data M(w) has eigenvalues 2^E and
  3^o, never Id, so the theorem does not apply. Verdict: kill.

### D. Metabelian group, Σ-invariants

**[bieri1987geometric]** R. Bieri, W. D. Neumann, R. Strebel, *A geometric invariant
of discrete groups*, Invent. Math. 90 (1987) 451–477. doi:10.1007/BF01389175; zbMATH 0642.57002.
- Quote (review): "One important result of the paper under review is the following theorem
  improving a result of Bieri and Strebel: If \(G\) is finitely presented and has no nonabelian
  free subgroup then \[ \Sigma\cup(-\Sigma)=S(G), \]".
- Note: Σ concerns finiteness of kernels and presentability, not restrictions of a cocycle to
  cyclic subgroups. See §1.1. Verdict: kill.

**[brown1987trees]** K. S. Brown, *Trees, valuations, and the Bieri–Neumann–Strebel invariant*,
Invent. Math. 90 (1987) 479–504. doi:10.1007/BF01389176; zbMATH 0663.20033.
- Quote (review): "In particular, he computes \(\Sigma\) for one relator groups G, which yields a
  description of the set of finitely generated normal subgroups of G with abelian quotients."
- Note: covers BS(1,n), a one-relator group. Same verdict: kill.

**[bieri1980valuations]** R. Bieri, R. Strebel, *Valuations and finitely presented
metabelian groups*, Proc. LMS (3) 41 (1980) 439–464. doi:10.1112/plms/s3-41.3.439. **Unverified**:
only zbMATH/Crossref metadata could be fetched, with no review or abstract text. Note: the
metabelian Σ for ℤ[1/6] ⋊ ℤ² is governed by the places 2, 3, ∞. Verdict: kill.

### E. ×2×3 rigidity

**[furstenberg1967disjointness]** H. Furstenberg, *Disjointness in ergodic theory, minimal sets,
and a problem in Diophantine approximation*, Math. Systems Theory 1 (1967) 1–49.
doi:10.1007/BF01692494; zbMATH 0146.28502.
- Quote (review): "The main result of the final Part IV says that if \(\Sigma\) is a non-lacunary
  (multiplicative) semigroup of integers and if \(\alpha\) is irrational then
  \(\{n\alpha \bmod 1: n\in\Sigma\}\) is dense in the unit interval."
- Note: irrational orbits. Cycles are rational and finite (x = S/D). Verdict: kill.

**[rudolph1990x2x3]** D. J. Rudolph, *×2 and ×3 invariant measures and entropy*, Ergodic Theory
Dynam. Systems 10 (1990) 395–406. doi:10.1017/S0143385700005629.
https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/article/2-and-3-invariant-measures-and-entropy/64243AD8323B37089540F911F8CC77EB
- Quote: "We show that if μ is not Lebesgue measure, then with respect to μ both T 0 and S 0 have
  entropy zero."
- Note: measure rigidity. A cycle carries an atomic measure, excluded by hypothesis. Verdict:
  kill.

**[host1995nombres]** B. Host, *Nombres normaux, entropie, translations*, Israel J. Math. 91 (1995)
419–428. doi:10.1007/BF02761660; zbMATH 0839.11030.
- Quote (review): "This paper establishes a very interesting criterion for a measure \(\mu\) on
  the unit circle to satisfy: \(\mu\)-almost every point is normal in a given basis."
- Note: normality and entropy; no finite-orbit content. Verdict: kill.

**[tal2021furstenberg]** M. Tal, *Furstenberg's Times 2, Times 3 Conjecture (a Short Survey)*, arXiv
(2021, v18). https://arxiv.org/abs/2110.05989
- Quote: "The following is a concise exposition of the conjecture and three of its proofs for the
  case of positive entropy by D. Rudolph [23] , B. Host [15] and W. Parry [22]."
- Note: a survey; no Collatz link anywhere in this line. Verdict: kill.

**[bourgain2009effective]** J. Bourgain, E. Lindenstrauss, Ph. Michel, A. Venkatesh, *Some
effective results for ×a×b*, Ergodic Theory Dynam. Systems 29 (2009) 1705–1722.
doi:10.1017/S0143385708000898. PDF:
https://infoscience.epfl.ch/record/129276/files/blmv.pdf?version=1
- Quote (Thm 1.10): "Let a, b be multiplicatively independent and (ab, N ) = 1. Then for any
  m ∈ (Z/N Z)× the set {a^k b^l . m/N : 0 < k, l < 3 log N} is κ7 (log log log N)^{−κ2/100} -dense".
- Note: the only finite-N ×2×3 statement, applicable with N = |D| (coprime to 6). It controls
  density of the ⟨2,3⟩-orbit mod D, not the zero-sum Σ_k 2^{e_k}3^{o−1−k} ≡ 0 mod D. Its §1.5
  points to Bourgain and to Bourgain–Glibichuk–Konyagin exponential sums: the counting lead.
  Verdict: kill as a bridge; open as a counting lead.

### F. Mahler's 3/2 problem and the rational base 3/2

**[mahler1968unsolved]** K. Mahler, *An unsolved problem on the powers of 3/2*, J. Austral. Math.
Soc. 8 (1968) 313–321. doi:10.1017/S1446788700005371. Reprint: Documenta Math. Extra Vol. Mahler
Selecta (2019) 639–648, https://ems.press/content/book-chapter-files/27426?nt=1
- Quote: "It is rather interesting that the same series converges in two different senses and to
  two different limits." And (11): "For any given non-negative integer g0 ⩾ 0 there exists at
  most one Z-number in the interval [g0, g0+1)".
- Note: the digit series Σ ε_n (2/3)^n converges in ℝ (to 3r₀) and in ℚ₂ (to −3g₀). This is the
  ancestor of Siegel's frames. For a *periodic* digit word (our cycles) the two limits coincide
  with the rational S/D. Verdict: kill for cycles (insightful framing).

**[flatto1995range]** L. Flatto, J. C. Lagarias, A. D. Pollington, *On the range of fractional
parts {ξ(p/q)^n}*, Acta Arith. 70 (1995) 125–147. doi:10.4064/aa-70-2-125-147. **Unverified for the
quote**: the IMPAN abstract page was fetched but has no abstract, and the PDF download failed.
Main result as restated by Dubickas 2009 (fetched): lim sup{ξ(p/q)^n} − lim inf{ξ(p/q)^n} ≥ 1/p.
Verdict: kill (background).

**[bugeaud2005sturmian]** Y. Bugeaud, A. Dubickas, *Fractional parts of powers and
Sturmian words*, C. R. Math. Acad. Sci. Paris 341 (2005) 69–74. doi:10.1016/j.crma.2005.06.007.
https://comptes-rendus.academie-sciences.fr/mathematique/item/10.1016/j.crma.2005.06.007.pdf
- Quote: "In terms of combinatorics on words we describe all irrational numbers ξ > 0 with the
  property that the fractional parts {ξ bn }, n ⩾ 0, all belong to a semi-open or an open interval
  of length 1/b."
- Note: the "Sturmian words control a (p,q) cocycle" mechanism, in the integer-base case.
  Verdict: open (method).

**[dubickas2009powers]** A. Dubickas, *Powers of a rational number modulo 1 cannot lie in a small
interval*, Acta Arith. 137 (2009) 233–239. doi:10.4064/aa137-3-4.
https://www.impan.pl/shop/en/publication/transaction/download/product/82938
- Quote: "Since w is Sturmian, we have p(w, m) = m + 1, so at least two of these m + 2 words must
  be equal". Also "(6) x_{m+j} − x_{m+i} = (p/q)^m (x_j − x_i)", "so (6) implies that the number
  q^m divides the difference x_j − x_i."
- Theorem 1: for 1 < q < p < q², no interval of length 1/p contains all {ξ(p/q)^n}.
- Note: **the surprise lever.** A cocycle identity on equal windows, plus the pigeonhole from
  factor complexity, plus an archimedean size bound, gives a contradiction. It transfers verbatim
  to cycles as the repeat lemma (§2). Verdict: **open**.

**[akiyama2008powers]** S. Akiyama, Ch. Frougny, J. Sakarovitch, *Powers of rationals modulo 1 and
rational base number systems*, Israel J. Math. 168 (2008) 53–91. doi:10.1007/s11856-008-1056-4.
https://www.irif.fr/~cf/publications/IJM.pdf
- Quote: "Above all, the set L p/q of all p/q -expansions is not a regular language (not even a
  context-free one)." Lemma 8: "uv^k belongs to L p/q only if q^{(k−1)|v|} divides π(w) − π(u)."
- Note: Lemma 8 is the program's power telescoping (P1/F2) in another numeration. No
  p/q-expansion is eventually periodic, for the same reason. Verdict: kill (duplicates F2/F5);
  keep as a citation that the mechanism is known.

**[eliahou2025base]** S. Eliahou, J.-L. Verger-Gaugry, *The number system in rational base 3/2 and
the 3x+1 problem*, C. R. Math. (to appear); arXiv 2025. https://arxiv.org/abs/2504.13716
- Quote (PDF): "Symmetrically, Corollary 3.2 shows that the map n 7→ (3n + 1)/2 for n odd is
  straightforward in the base 3/2 representation of n: just add 1 as rightmost digit."
- Note: a numeration in which odd steps are digit shifts, dual to base 2 for halvings. A cycle is
  a word read in both systems. Verdict: open (vocabulary only).

**[lu2026negative]** Q. Lu, W. Zheng, *Fractional parts of powers of negative rationals*, arXiv
(2026, v4). https://arxiv.org/abs/2603.16794
- Quote: "the image in $\mathbb{R}/\mathbb{Z}$ of the sequence $(ξ(-p/q)^n)_{n\ge 0}$ is not
  contained in any interval of length less than $(1+q/p-q^2/p^2)/p$."
- Note: the current frontier of the FLP-type bound. No cycle content. Verdict: kill.

### G. gcds, S-units, divisibility sequences

**[bugeaud2003gcd] (dup, B1 — reference only)** Y. Bugeaud, P. Corvaja, U. Zannier,
*An upper bound for the g.c.d. of a^n − 1 and b^n − 1*, Math. Z. 243 (2003) 79–84. zbMATH
1021.11001.
- Quote (review): "if \(a\) and \(b\) are multiplicatively independent then, for every
  \(\varepsilon>0\) and \(n\) sufficiently large, \(\gcd(a^n-1,b^n-1)\) is no greater than
  \(\exp(\varepsilon n)\)."
- Verdict: kill (two-term S-units only).

**[corvaja2005height]** P. Corvaja, U. Zannier, *A lower bound for the height of a rational
function at S-unit points*, Monatsh. Math. 144 (2005) 203–224. zbMATH 1086.11035.
- Quote (review): "\(\gcd (u-1,v-1)<\max(| u| ,| v| )^{\varepsilon}\) with finitely many
  exceptions for multiplicatively independent S-units \(u,v\)."
- Note: G = gcd(S, D) has D a two-term S-unit difference but S an o-term sum. The fixed-length
  hypothesis fails. Verdict: kill.

**[bezivin1990divisibility]** J.-P. Bézivin, A. Pethő, A. J. van der Poorten, *A full
characterisation of divisibility sequences*, Amer. J. Math. 112 (1990) 985–1001. zbMATH
0716.11008.
- Quote (review): "there is a recurrence sequence \((\overline a_h)\) of the form
  \[ \overline a_h = h^k \prod_i \left(\frac{\alpha_i^h - \beta_i^h}{\alpha_i-\beta_i}\right) \]
  such that \(a_h\mid \overline a_ h\)".
- Note: confirms the Lucas/cyclotomic picture for D along powers (open problem 3). Nothing new.
  Verdict: kill.

### H. Formal and automated

**[merle2026nocycle]** E. Merle, *collatz-nocycle-lean4*, GitHub (2026, unrefereed).
https://github.com/ericmerle3789/collatz-nocycle-lean4
- Quote (erratum): "What is actually proved, without circularity: `no_cycle_k_le_1322` — no
  non-trivial cycle with k ≤ 1322 odd steps, assuming `BakerSeparation` and
  `BarinaVerification`."
- Note: `BakerSeparation` ((2^s − 3^k)·k⁶ ≥ 3^k) is an unproven hypothesis, by the author's own
  erratum. Do not import it. Verdict: kill as a result; caution.

**[merle2026obstruction]** E. Merle, *one-obstruction-three-faces-lean*, GitHub (2026,
unrefereed). https://github.com/ericmerle3789/one-obstruction-three-faces-lean
- Quote: "They prove nothing new about Collatz cycles and do not prove the Collatz conjecture."
- Note: Lean 4.34 formalisations of Halbeisen–Hungerbühler 1997, Lagarias 1990 and Steiner 1978,
  plus kernel-checked "content descent" and "adjacent-transfer difference" lemmas close to C3/C7.
  A possible substrate if the program ever formalises C1–C11. Verdict: keep (substrate).

**[yolcu2023automated] (dup)** E. Yolcu, S. Aaronson, M. J. H. Heule, *An Automated Approach to the
Collatz Conjecture*, J. Autom. Reasoning 67 (2023); CADE-28 (2021).
https://arxiv.org/abs/2105.14697
- Quote: "We prove that the termination of this rewriting system is equivalent to the Collatz
  conjecture."
- New note: the mixed binary–ternary encoding is a digit-level cocycle (base swap). Its proved
  weakenings are termination statements, not cycle exclusions. Verdict: kill for cycles.

**[lagarias2010overview] (dup)** J. C. Lagarias, *The 3x+1 Problem: An Overview*, in *The Ultimate
Challenge* (AMS 2010) 3–29. https://arxiv.org/abs/2111.02635
- Quote: "It addresses two questions: (1) What can mathematics currently say about this problem?
  (as of 2010). (2) How can this problem be hard, when it is so easy to state?"
- New note: a full-text grep finds Furstenberg only as a general dynamics reference ("The book of
  Furstenberg [30] considers various well structured arithmetical dynamical systems"). There is no
  ×2×3 ↔ 3x+1 bridge and no Mahler Z-number discussion. Verdict: kill (confirms null).

---

## 4. Leads for round 2

1. **Dubickas–Novikas 2005**, *Integer parts of powers of rational numbers*, Math. Z. 251 —
   their Lemma 2 (aperiodicity of the digit word s_n) is the cocycle aperiodicity lemma behind
   [dubickas2009powers]. Check for quantitative repeat bounds.
2. **Berthé–Holton–Zamboni 2006**, *Initial powers of Sturmian sequences*, Acta Arith. 122 — the
   constant I_S. Quantitative repeat lengths in balanced words feed the repeat-lemma threshold.
3. **Bugeaud 2004**, *Linear mod one transformations…*, Acta Arith. 114, and **Flatto 1992**,
   *Z-numbers and β-transformations* (Contemp. Math. 135) — the linear-mod-one / β-shift frame for
   the same cocycle.
4. **Akiyama**, *Mahler's Z-number and 3/2-number system* (preprint, AFS ref. [1]) — Z-numbers
   recast as constraints on minimal words, a covering-type statement.
5. **Morgenbesser–Steiner–Thuswaldner 2013**, *Patterns in rational base number systems*,
   J. Fourier Anal. Appl. 19 — digit-pattern equidistribution in base 3/2, the analogue of
   equidistribution of S along words.
6. **Bourgain 2005** (exponential sums over subgroups of ℤ_q^*, q arbitrary) and
   **Bourgain–Glibichuk–Konyagin 2006** — for a rigorous count of words with S(w) ≡ 0 mod D. The
   needed saving (δ > 0.95) is probably out of reach; confirm.
7. **Bousch 2000** (*Le poisson n'a pas d'arêtes*) and **Jenkinson 2006** (ergodic optimization
   survey) — Sturmian maximizing measures. "Christoffel words extremise x_min"
   (Halbeisen–Hungerbühler) is an ergodic-optimization statement; a sub-action might give
   "positive Livšic" constraints.
8. **Pollicott–Sharp 2004**, *Livsic theorems, maximizing measures and the stable norm*,
   Dynamical Systems 19 — the same thread (Crossref-confirmed, not read).
9. **de Weger 2011**, *Comments on Opfer's alleged proof* (TU/e report, cited in Siegel's thesis
   [159]) — locate the exact gap for the cautionary note.
10. **Siegel thesis §4.2–4.3** — the explicit χ̂₃: test whether, restricted to periodic z with
    fixed (E, o), it yields a closed generating function of S/D over words (an "expected cycles"
    series).
