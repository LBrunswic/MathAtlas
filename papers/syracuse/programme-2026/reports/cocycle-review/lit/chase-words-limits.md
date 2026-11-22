# Theme `chase-words-limits`: round-2 citation chase from six hooks

*Round-2 literature agent. Date: 2026-10-30. Bibliography lines: `bib-chase-words-limits.jsonl`.
47 entries: 39 new and verified, 5 unverified (reason given in each), 3 re-reads of already-cited
sources with new content (`dup: true`). Deduplicated against every `bib-*.jsonl` in `lit/` and the
dedup files listed in BRIEF.md.*

*Method: forward citations via the OpenAlex API (`filter=cites:`), backward citations via
`referenced_works`, then each quote fetched from the arXiv API, the author PDF, numdam, HAL, the
Crossref record deposited by the publisher, or a zbMATH review (api.zbmath.org). Semantic Scholar was
rate-limited, and Google Scholar was not used. Sections marked **[derived]** are short deductions made here.
They are not literature claims, and each comes with a check.*

---

## Executive summary

1. **Balanced ⇒ Christoffel conjugate has a ten-line proof with no Lyndon theory.** Rotate to the
   minimum of the potential k·p − n·h(k): the cycle lemma (Lothaire L2.1.15 after Tijdeman 1996;
   Fernández–Ibáñez 2026, L6.1). Circular balance then forces h(k) = ⌈kp/n⌉, so the rotation *is*
   `Christoffel.upper p n`, whether or not gcd(p, n) = 1. C-balance gives a band of width C − 1. Next
   Lean target: L1–L3.
2. **Christoffel words maximise x_min.** Fernández–Ibáñez (July 2026) prove Christoffel words are the
   unique maximisers of C_min = D·x_min. The cycle lemma plus monotonicity of C in the positions of the
   ones gives a shorter proof, which also closes a gap in their Theorem 7.3 (L5).
   - With Knight (now refereed, Discrete Math. 349 (2026) 114812), the extremal class is the excluded
     class.
   - Houze 2026 reports a Lean 4 proof of an "elementary exclusion of balanced Collatz cycles".
3. **Unbalance witnesses are explicit:** 0v0 / 1v1 with v a palindrome (Lothaire P2.1.3); minimal
   forbidden words (Fici 2014); the most balanced unbalanced words u²v² (Provençal 2011).
4. **Rational base 3/2 gives no handle on S mod D.** Halvings are not tree edges; the language is not
   context-free; Stérin–Woods 2020 recast cycles as 2-adic reachability. Kill as a lever on G.
5. **Near-miss data.** No paper studies the distribution of k(w) or G/|D|; no LLL search for small-k
   cycles was found. Data: Belaga–Mignotte 2000, Wegner 2021.
6. **Barriers.** None for 2-branch maps. Conway 2013 alone claims explicitly that a proof of "no cycles
   of large numbers only" is unlikely.

**Strongest hooks:** L1–L2 (cycle lemma ⇒ balanced case closed in Lean), L5 (extremality of
Christoffel words), L4 (witness pair), L6 (exact rotation Hamming distance).

---

## 0. Derived facts [derived]

Notation:
- w ∈ {0,1}^n is a parity vector with p ones.
- h_j(k) is the number of ones among the first k letters of w rotated by j.
- `upper p n` is the Lean word with letters ⌈(i+1)p/n⌉ − ⌈ip/n⌉ (phase n − 1 in `Christoffel.lean`).

**D1. Cycle lemma.** Let j minimise φ(j) = n·h_0(j) − j·p over 0 ≤ j < n. Then n·h_j(k) ≥ k·p for
every k ≤ n.
- *Proof:* n·h_j(k) − kp = φ(j + k mod n) − φ(j) ≥ 0, using φ(n) = φ(0).
- This is the inf-ρ step of Lothaire Lemma 2.1.15 ("from Tijdeman (1996)") and Fernández–Ibáñez Lemma
  6.1, where μ-minimisation gives tail densities ≤ r/N.
- *Check:* Lean (L1).

**D2. Circularly balanced ⇒ rotation of `upper p n`, coprime or not.**
- Summed over the n starting points, the circular factors of length k contain kp ones in total.
- If their counts lie in {m, m+1}, then every count is ≤ ⌈kp/n⌉. This includes the integer case,
  where all counts are equal.
- By D1, h_j(k) ≥ ⌈kp/n⌉. Hence h_j(k) = ⌈kp/n⌉ for all k, i.e. w rotated by j equals `upper p n`.
- If gcd(p, n) = d > 1, `upper p n` is the d-th power of `upper (p/d) (n/d)`, so the word is a proper
  power.
- *Check:* Lean (L2).

**D3. C-balance ⇒ a band.** If the counts lie in [m, m+C], the same averaging gives
⌈kp/n⌉ ≤ h_j(k) ≤ ⌊kp/n⌋ + C.
- So the min-potential rotation is a lattice path inside a band of width C − 1 above the upper
  Christoffel path.
- This is the cleanest quantitative "C-balanced ⇒ close to Christoffel" found. The literature has only
  qualitative or coloured-Sturmian versions (Sano et al. 2004; Dvořáková et al. 2024).
- *Check:* Lean (L3).

**D4. Fernández–Ibáñez Theorem 7.3, with a short proof and a fixed gap.**
- Write C(d) = Σ_j 2^{k_j−1}3^{r−j}, where k_j is the position of the j-th one. This is Knight's g(v),
  i.e. the program's S for a rotation that starts with 1. C is strictly increasing in each k_j.
- **Upper bound.** By D1, the min-potential rotation d^c has its ones componentwise left of those of
  `upper`. So C_min(d) ≤ C(d^c) ≤ C(upper), with equality iff d^c = upper. The transposition chain of
  their Theorem 6.4 is not needed.
- **Gap.** The paper argues C_min(upper) = C(upper) on p. 12 from an empty transposition chain starting
  at `upper` itself. That says nothing about the other rotations of `upper`.
- **Fix.** By D2's averaging, every rotation of `upper` has prefix counts ≤ ⌈kr/N⌉. So its ones lie
  componentwise right of those of `upper`, and C(rotation) ≥ C(upper).
- **Uniqueness.** If C_min(d) = C(upper), then C(d^c) = C(upper), hence d^c = upper.
- *Hand check:* (N, r) = (5, 2). The upper word is 10100 with C = 3 + 4 = 7. Its rotations give
  22, 11, 28, 14, so the minimum is 7.

**D5. Rotation Hamming distance of a Christoffel word.** For 0 < p < n coprime and
t = s·p mod n,

  d_H(upper p n, (upper p n).rotate s) = 2·min(t, n − t, p, n − p).

- *Why:* a rotation shifts the phase by t (`word_rotate`), and letter i is the indicator of
  (ip + c) mod n lying in an arc of length p. Since p is a unit mod n, d_H is the size of the symmetric
  difference of two arcs offset by t.
- *Hand check:* (5, 2) gives s = 1 → 4 and s = 2 → 2, which agrees with direct comparison of 10100
  against 01001 and 10010.
- For s = q_k (a convergent denominator), t ≈ n/q_{k+1}. This recovers round 1's "about 2o/q_{k+1}
  letters".
- *Check:* Lean (L6).

**D6. Jenkinson-style majorisation cannot transfer to cycle elements.**
- For every word of type (E, o) with D > 0, the rational cycle satisfies ∏_j(1 + 1/(3x_j)) = 2^E/3^o.
  This is the product formula already proved in `CycleLiterature`.
- So Σ_j φ(x_j) is the same for all such words, with φ(x) = log(1 + 1/(3x)) strictly convex and
  decreasing.
- Weak supermajorisation x(upper) ≺^w x(w) would force Σφ(x(upper)) < Σφ(x(w)) for x(w) ≠ x(upper),
  by Marshall–Olkin 3.C.1.b with strict convexity. Since the two sums are equal, that is impossible.
- Hence **the Christoffel cycle dominates only at the first partial sum (x_min, D4), never at every
  level.** Jenkinson 2009, where full majorisation holds in base 2, does not transfer to the (2,3) orbit.
- *Check:* compute the sorted partial sums of x_j for upper vs one non-Christoffel word at (E, o) =
  (8, 5).

---

## 1. Idea → hook map

| # | idea | source(s) | touches | what it would give | verdict | cheapest first test |
|---|---|---|---|---|---|---|
| 1 | Cycle-lemma proof of balanced ⇒ Christoffel conjugate | Lothaire L2.1.15 (Tijdeman 1996); Fernández–Ibáñez 2026 L6.1; De Luca–Fici 2024 P18, P20; BLRS 6.9 (dup) | OP2 (balanced half of the cover), F2 | Lean closure of the balanced case **without coprimality** | **keep** | L1 + L2 in `Christoffel.lean` |
| 2 | No positive cycle has a circularly balanced parity vector | Knight 2026 (refereed); Houze 2026 (Lean claim); D2 | ledger C9, OP2 | unconditional "balanced ⇒ trivial": coprime case via `no_high_cycle`, non-coprime via the power reduction | **keep** | L2′ |
| 3 | C-balanced ⇒ band around the Christoffel path | **[derived] D3**; Sano–Miyoshi–Kataoka 2004 (U); Dvořáková et al. 2024 | F2, OP2, words D6 | quantitative "close to Christoffel"; with D4, x_min(w) is within a factor of x_min(upper) computable from C | **open** | L3; then bound C(upper) − C(d^c) |
| 4 | Explicit unbalance witnesses | Lothaire P2.1.3 (dup); Fici 2014; De Luca–Fici T37; Provençal 2011 | OP2 (unbalanced half) | a canonical pair 0v0 / 1v1 at which to anchor a two-rotation move | **open** | L4; then the queue.md §5.2 engine test |
| 5 | Christoffel words maximise x_min | Fernández–Ibáñez 2026; Knight 2026; H–H 1997 (dup); Allouche–Glen 2010; Sidorov 2011 | OP1, F3 | elementary x_min ≤ C(upper)/D; the extremal class is exactly the excluded class | **keep** | L5 |
| 6 | Majorisation or convex domination of cycle elements | Jenkinson 2009; Vesti 2015; Bousch 2015 | OP4 (AM–GM estimator) | full majorisation is impossible (D6); Bousch's affine-functional domination on integer gap words stays open | **kill** (full) / **open** (Bousch) | D6 check; test whether e_k − k·log₂3 fits Bousch's ≤₂-increasing affine class |
| 7 | Anchor geometry: exact rotation distances | Alessandri–Berthé 1998; Puzynina–Zamboni 2013; Fici 2016 (dup); Vukusic 2026 | OP1 (f(w)), F2 | d_H between rotations is 2·min(t, n−t, p, n−p) (D5); abelian returns take 2–3 values | **keep** | L6 |
| 8 | Cyclic abelian powers | Peltomäki–Whiteland 2020 | words D4, F5 | over {0,1}, long words cannot avoid cyclic abelian cubes but can avoid cyclic abelian 4-powers (𝒜_∞(2) = 4); local, not rotation differences | **kill** | none |
| 9 | Rational base 3/2 as a handle on S mod D | AFS 2008 (dup); Akiyama 2008; Akiyama–Marsault–Sakarovitch 2018; Morgenbesser–Steiner–Thuswaldner 2013; Kari–Kopra 2017; Dubickas 2008 | F1, OP2 | none: halvings are not tree moves, the language is not context-free, the subtrees are all distinct | **kill** | none |
| 10 | Joint base-2/base-3 automaton: cycle = reachability | Stérin–Woods 2020 | F1; hook 5 | a reformulation; bit prediction is NC¹ but not AC⁰ | **open** (vocabulary) | none |
| 11 | Repeat-lemma pigeonhole (Dubickas) | Dubickas 2009 (dup); Bugeaud–Kim 2019; Borel–Reutenauer 2006; Berthé–Holton–Zamboni 2006; Dubickas 2009b | OP2 (narrow), F5 | a repeated parity window of length L forces 2^L ∣ y_i − y_j ≠ 0; Christoffel conjugates repeat at L = n − 2 | **open** (narrow; Knight dominates) | L7 |
| 12 | Distribution of k(w) and near-miss data | Belaga–Mignotte 2000 (dup re-read); Wegner 2021; Simons–de Weger 2004; Kaneda 2015; Aliyev 2025 | F4, OP1 | no theory of the distribution was found; data only | **open** | L8 certificate |
| 13 | Barriers ("any proof must use …") | Conway 2013; Zabolotskii 2026; Stérin–Woods 2021; Tao 2011 (dup) | F4, F5 | no formal barrier for 2-branch maps; undecidability only *adjacent* to Collatz | **kill** (as an obstruction) | none |
| 14 | Ergodic optimisation ("balanced is optimal") | Bousch 2000; Jenkinson 2006; Sidorov 2011; Allouche–Glen 2010 | OP1, OP4 | the general principle behind items 5–6 | **open** | as item 6 |

---

## 2. Lean-formalisable statements

These are stated against the existing names (`Christoffel.mech/word/upper`, `CocycleCombine.pv`,
`IsSyrCycle`, `gapWord`). Here h(v, k) := (v.take k).count true, and `~r` is `List.IsRotated`.

**L1 (cycle lemma; D1).**
`∀ w : List Bool, ∃ j, ∀ k ≤ w.length, k * w.count true ≤ w.length * h (w.rotate j) k`.
- Source: Lothaire L2.1.15; Fernández–Ibáñez L6.1.
- Elementary: argmin of an integer potential over `Fin n`.

**L2 (balanced ⇒ upper; D2).**
- Define `CircBalanced w := ∀ k ≤ |w|, ∀ i i', h (w.rotate i) k ≤ h (w.rotate i') k + 1`.
- Statement: `CircBalanced w → w ~r upper (w.count true) w.length`. No coprimality hypothesis.
- Proof route: averaging Σ_i h(w.rotate i, k) = k·p, then L1, then letters as differences of ceilings,
  matching `mech p n (n-1)`.

**L2′ (no balanced cycle).**
`IsSyrCycle x o → 0 < x → CircBalanced (pv (gapWord x o)) → x = 1`.
- Coprime case: `no_high_cycle`.
- Non-coprime case: `upper p n = (upper (p/d) (n/d))^d`, so the cycle has period o/d; recurse.
- This turns the "balanced half" of `covering-reductions.md` Part 3 into a theorem.
- Houze 2026 claims a Lean 4 proof of a "balanced-cycle theorem". The sources were not located, so the
  repository should prove it itself.

**L3 (C-band; D3).**
`(∀ k i i', h (w.rotate i) k ≤ h (w.rotate i') k + C) → ∃ j, ∀ k ≤ n, ⌈k p / n⌉ ≤ h (w.rotate j) k ∧ h (w.rotate j) k ≤ ⌊k p / n⌋ + C`.

**L4 (witness).**
`¬ CircBalanced w → ∃ v, v.reverse = v ∧ IsCircFactor (false :: v ++ [false]) w ∧ IsCircFactor (true :: v ++ [true]) w`.
- Source: Lothaire P2.1.3, by minimal length and a first/last-letter argument.
- Easier first step: a minimal pair has the shape 0v0 / 1v1. The palindromicity of v is a second lemma.

**L5 (Christoffel maximises x_min; D4).**
- Let Cf(d) := Σ_{i<|d|, d_i} 2^i·3^{(d.drop (i+1)).count true}. This is Fernández–Ibáñez's C, equal
  to Knight's g and to the program's S on rotations that start with 1.
- Then `∃ j, Cf (d.rotate j) ≤ Cf (upper p n)`, with ∀ j equality forcing `d ~r upper p n`.
- Also `∀ j, Cf (upper p n) ≤ Cf ((upper p n).rotate j)`.
- Corollary: a positive cycle has D·x_min ≤ Cf(upper o E). This is the Halbeisen–Hungerbühler /
  Eliahou-type bound, proved elementarily.

**L6 (rotation Hamming distance; D5).**
`Nat.Coprime p n → 0 < p → p < n → hammingDist (upper p n) ((upper p n).rotate s) = 2 * min (min t (n - t)) (min p (n - p))`,
with t = s·p % n. Proof route: `word_rotate` plus counting the arc symmetric difference.

**L7 (repeat identity; Dubickas).** For T-cycle elements y with parity vector v: if
v[i, i+L) = v[j, j+L) contains t ones, then 2^L·(y_{i+L} − y_{j+L}) = 3^t·(y_i − y_j).
- This is two lines from the affine composition.
- Combined with Borel–Reutenauer (n − 1 circular factors of length n − 2 for a Christoffel class) it
  gives a repeated window of length n − 2. This is a Baker-free cross-check of the Christoffel case
  only.

**L8 (near-miss certificate).** For w = 11111211212321115 (E = 27, o = 17):
- D = 5 077 565;
- `Nat.gcd (S w) D = 1 015 513`, so k(w) = 5.

Verify by `norm_num` or `decide`. Do the same for the (65,41) words with k = 29. These are regression
fixtures showing that no ceiling G ≤ |D|/c with c > 5 can hold at these sizes (generalized-maps, F4).

---

## 3. Per-hook findings: best follow-ups

### Hook 1. Balanced ⇔ Christoffel conjugate

**(a) Cleanest self-contained proof.**

- **Lothaire 2002, ch. 2 (dup; fetched this round from the author's PostScript).**
  > "Lemma 2.1.15. Let s be a balanced infinite word. If s is aperiodic, then s is irrational
  > mechanical. If s is purely periodic, then s is rational mechanical."

  The notes add: "The argument of the proof of Lemma 2.1.15 is from Tijdeman (1996)."
  - The proof sets ρ = inf{ρ : h_n ≤ ⌊nα + ρ⌋ for all n}.
  - For a periodic word the infimum is attained, which is D1 + D2. Applying it to w^ω gives the
    circular statement at once.
  - This is shorter than the BLRS route, which goes through Berstel–de Luca's balanced-Lyndon theorem.
- **Fernández–Ibáñez 2026, Lemma 6.1:**
  > "(1/(N−k)) Σ_{j=k+1}^N d^c_j ≤ r/N" for the μ-minimising rotation.

  This is the same cycle lemma, stated in Collatz notation (C(d) = Σ 2^{i−1}3^{r_i(d)}d_i, eq. (4)).
- **De Luca–Fici 2024:**
  > "Proposition 18 (see for instance [13]). A word is circularly balanced if and only if it is a
  > conjugate of a Christoffel word, i.e., if and only if it is a row of a Christoffel matrix."

  Proposition 20 has a two-paragraph proof: every balanced word with Parikh vector (a, b) has its
  length-k prefix Parikh vector equal to that of the lower or upper Christoffel word. It is a direct
  template for L2.
- **Borel–Reutenauer 2006:**
  > "We characterize conjugation classes of Christoffel words (equivalently of standard words) by the
  > number of factors."

  This is the k+1-factor criterion, useful for the repeat pigeonhole (L7).

**(b) Quantitative versions.**
- No source gives "C-balanced ⇒ distance d from Christoffel" for finite circular words. D3 fills this,
  and L3 is the formal target.
- Dvořáková–Masáková–Pelantová 2024 build 2-balanced words by colouring Sturmian words ("These sequences
  are obtained by colouring of Sturmian sequences"). These are ternary and over-specific: **kill**.
- Sano–Miyoshi–Kataoka 2004 (m-balanced words) could not be fetched.

**(c) Explicit unbalance witnesses.**
- **Lothaire P2.1.3 (dup):**
  > "The set X is unbalanced if and only if there exists a palindrome word w such that 0w0 and 1w1
  > are in X."
- **Fici 2014 / De Luca–Fici T37:**
  > "MF(Bal) = {yvx | {x, y} = {0, 1}, xvy is a non-primitive Christoffel word}."

  So the *minimal* unbalanced words are a Christoffel power with its two end letters swapped. The
  shortest witness pair is therefore tied to a period of the word. For a cycle word this gives a
  shift s at which two rotations nearly agree.
- **Provençal 2011:**
  > "by considering the most balanced among the unbalanced words, we obtain a second characterization …
  > of the form u2v2".

  These are words with a *unique* imbalance pair. They are the natural "one defect beyond Knight"
  family to test next.

### Hook 2. Anchor geometry in balanced and Sturmian words

- **Alessandri–Berthé 1998** (survey of the three-distance theorem from rotations to block complexity).
  The anchor spacings and factor frequencies take at most 3 values. D5/L6 is the exact rational-slope
  form for two rotations.
- **Puzynina–Zamboni 2013:**
  > "a recurrent infinite word is Sturmian if and only if each of its factors has two or three abelian
  > (or semi-abelian) returns."

  The χ-matched return times of an anchor take 2–3 values. This characterises the 1-balanced regime,
  which is already closed by L2′.
- **Peltomäki–Whiteland 2020** (answers round-1 lead D4):
  > "Moreover, we show that 𝒜_∞(2) = 4".

  Over {0,1}, cyclic abelian cubes of period < |w| are unavoidable in long words, while cyclic abelian
  4-powers are avoidable. These are local trains, not rotation differences: **kill** for covering.
- **Vukusic 2026:** the balance of m×n blocks is controlled by Ostrowski digits. **Kill** (2-D).
- **Verdict.** The anchor geometry is exact only on the Christoffel class, which L2′ now closes. For
  C ≥ 2 the only usable geometry is the D3 band.

### Hook 3. Dubickas 2009 and rational base 3/2

**Does rational-base 3/2 numeration give a handle on S(w) mod D? No.**
- **Akiyama–Marsault–Sakarovitch 2018:**
  > "Its nodes are the integers, its edges bear labels taken in {0,1,...,p-1}, and its subtrees are all
  > distinct."

  An odd step x ↦ (3x+1)/2 is an edge of the 3/2 tree (Eliahou–Verger-Gaugry, dup). A halving is not.
  A cycle is a closed walk that uses non-edges.
- **Morgenbesser–Steiner–Thuswaldner 2013:**
  > "the language of the representations of integers in these number systems is not context-free."

  No automaton recognises the cycle words through this numeration.
- **Stérin–Woods 2020:**
  > "We show that vertical columns simultaneously iterate the map in base 3. … our automaton encodes
  > the cyclic Collatz conjecture as a natural reachability problem."

  This is the honest form of "read the cycle in base 2 and in base 3 at once". It is a
  reformulation, not a modular invariant.
- **Dubickas follow-ups** (Dubickas 2008 Math. Nachr.; Dubickas 2009 RAIRO; Kwon 2015;
  Kari–Kopra 2017; Akiyama 2008) all concern {ξ(p/q)^n}.
  - The only transferable mechanism is the repeat identity (L7) with a factor-complexity pigeonhole.
  - Bugeaud–Kim 2019 sharpen the pigeonhole: "Theorem 2.4 … (i) x is a Sturmian word; (ii) x
    satisfies r(n, x) ≤ 2n + 1 for n ≥ 1".
  - **Kill** as a G-lever; keep L7 as a narrow inequality (frames theme: Baker-dependent, dominated by
    Knight on the Christoffel class).

### Hook 4. Near-miss words and 3x+k cycle data

- **OEIS A226670–A226672** cite exactly one source, Belaga–Mignotte 2000 (re-read in full via HAL;
  dup). Its Conjecture 6 is the program's gcd problem for *every* prime pair (r, q): only finitely many
  gap words have |r^ℓ − q^k| dividing the corona sum. Example 2.4 gives the largest datum,
  "a T16819–cycle of the length 4686" (|D| > 10^{1409}).
- **Wegner 2021:**
  > "Positive and negative limit cycles are given up to k=9997".

  This is fresh k(w) data for both signs of D.
- **Simons–de Weger 2004 (NAW, in Dutch).**
  - Lemma 1: if q = 2^r − 3^s then 3x+q has a second 1-cycle. This is the F1 dictionary at the
    circuit word.
  - Their verdict: 3x+1 is a "grensgeval" (a boundary case) where "de ‘ruimte’ voor niet triviale
    cykels zo klein is geworden, dat zij niet voor blijken te komen" ("the room for nontrivial cycles
    has become so small that they turn out not to occur").
- **Kaneda 2015** gives a short proof of Belaga's perigee bound and an arithmetic reformulation.
- **Aliyev 2025:** integer combinations of rational-cycle terms. These are rotation-ideal elements
  (F1): **kill**.
- **Not found:** any paper on the distribution of G(w)/|D(w)| or k(w) over critical words, and any LLL
  search for small-k cycles. The Simons–de Weger literature uses continued fractions and Baker bounds,
  and the NAW survey mentions no LLL.

### Hook 5. "Any proof must use …"

- **Conway 2013, postscript:**
  > "In my view the fact that this probability, though very small, is positive, makes it extremely
  > unlikely that there can be a proof that the Collatz game has no cycles that contain only large
  > numbers."

  His "mountain" 2^k·m − 1 → 3^k·m − 1 is the program's run telescoping (P1). His probability
  estimate is the F5 counting budget in words.
- **Stérin–Woods 2020.** Predicting about half the bits of T^i(x) for i = O(log x) is "in the
  complexity class NC¹ but outside AC⁰". This is the only circuit-complexity lower bound found. It
  rules out constant-depth "local" certificates, not cycle proofs.
- **Zabolotskii 2026.** A canonical additive system is equivalent to Collatz, and a "well-behaved
  family" is undecidable (Fractran). Undecidability is adjacent to Collatz, not at it.
- **Stérin–Woods 2021:** BB(15) encodes Erdős's ternary-digit conjecture on 2^n.
- **Verdict.**
  - Tao's Prop. 7 (dup) remains the only *implication-type* constraint: a cycle-free 3x+1 needs
    exponential separation.
  - No 2020–2026 paper gives a relativisation-type or independence result for 2-branch maps.

### Hook 6. Who cites Cohn 1972 and Halbeisen–Hungerbühler 1997 on cycles

- **Forward citations of H–H 1997** (OpenAlex, 21 citers): Brox 2000 (dup), Cox–Ghosh–Sultanow 2021
  (dup), López–Stoll 2009 (dup), Merle 2026 (dup), Kaneda 2015, **Knight 2026**, **Houze 2026**, and
  three off-topic works.
- **Cohn 1972** (82 citers) is cited on Collatz cycles only by Knight. The rest is Markoff, F₂ and
  quasicrystal literature.
- **Fernández–Ibáñez 2026** (cites Knight; does not cite H–H):
  > "We prove that Christoffel words are, up to rotation, the unique maximizers of C_min(d) on D_{N,r}".

  Proposition 5.2 is a one-line cocycle identity: C(d₁01d₂) − C(d₁10d₂) = 2^{N₁}3^{r₀(d₂)} > 0. Their
  Theorem 8.1(2) (no cycle with N > 2r) is weaker than the program's sandwich. The value is L5 and the
  uniqueness (see D4 for the gap and the fix).
- **Houze 2026:**
  > "an elementary exclusion of balanced Collatz cycles … The main theorem, the balanced-cycle theorem
  > and several further results are proved in Lean 4 with Mathlib using only the standard axioms."
- **Base-2 analogues of H–H.**
  - Jenkinson 2009: balanced words maximise the product of the base-2 orbit and are majorised by every
    word of the same slope.
  - Vesti 2015: 0^{q−p}1^p is the opposite extreme, the analogue of the circuit.
  - Bousch 2015: convex domination by Sturmian orbits, **for N-periodic integer sequences**, i.e.
    gap words.
  - D6 shows that full majorisation cannot hold for cycle elements.
- **"Almost balanced" exclusions.** None was found beyond the balanced case. Provençal's u²v² words
  (unique imbalance pair) are the natural next family. With D3–D4, the first quantitative step is to
  bound C(upper) − C_min(d) from below for a 2-balanced d.

---

## 4. Annotated bibliography

"V" = verified (page fetched, quote from it); "U" = unverified (reason given). Math in zbMATH quotes is
transliterated from LaTeX.

### 4.1 Hook 1: balanced and Christoffel

**deluca2024some** (V). A. De Luca, G. Fici, *Some results on digital segments and balanced words*,
Theor. Comput. Sci. 1021 (2024) 114935. https://arxiv.org/abs/2211.09417 · doi:10.1016/j.tcs.2024.114935
> "Proposition 20. Let a, b > 0 and n = a + b. For every balanced word u with Parikh vector (a, b), and
> for every 1 < k < n, the prefix of length k of u has the same Parikh vector as the prefix of length k
> of either wa,b or Wa,b."

This is the elementary template for L2. It also restates the circular characterisation (P18) and the
minimal forbidden words (T37). **Keep.**

**fici2014structure** (V). G. Fici, *On the structure of bispecial Sturmian words*, J. Comput. Syst.
Sci. 80(4) (2014) 711–719. https://arxiv.org/abs/1311.4904
> "bispecial Sturmian words are precisely the maximal internal factors of all Christoffel words … We also
> investigate the minimal forbidden words for the language of Sturmian words."

It gives the exact list of shortest unbalanced words (witness shapes). **Keep.**

**fernandez2026christoffel** (V). C. Fernández, S. Ibáñez, *Christoffel words as extremal structures in
Collatz dynamics*, arXiv:2607.24844 (July 2026).
> "We prove that Christoffel words are, up to rotation, the unique maximizers of C_min(d) on D_{N,r}, the
> set of binary words of length N with exactly r ones".

PDF read: the cycle lemma (L6.1), position comparison (T6.3) and the cocycle swap identity (P5.2).
Theorem 7.3 has a gap that D4 fixes. **Keep** (source for L5).

**provencal2011minimal** (V, HAL). X. Provençal, *Minimal non-convex words*, Theor. Comput. Sci. 412
(2011). https://hal.science/hal-00943826 · doi:10.1016/j.tcs.2010.06.025
> "by considering the most balanced among the unbalanced words, we obtain a second characterization for a
> special class of minimal non-convex words that are of the form u2v2".

This gives the "one defect beyond Christoffel" family. **Open.**

**borel2006christoffel** (V, numdam). J.-P. Borel, C. Reutenauer, *On Christoffel classes*, RAIRO ITA
40(1) (2006) 15–27. doi:10.1051/ita:2005038
> "We characterize conjugation classes of Christoffel words (equivalently of standard words) by the
> number of factors."

The circular complexity k+1 is a pigeonhole input for L7. **Keep.**

**reutenauer2019christoffel** (V, publisher abstract via Crossref). C. Reutenauer, *From Christoffel
Words to Markoff Numbers*, OUP 2019 (2nd ed. 2026), ch. "Conjugates and Factors".
doi:10.1093/oso/9780198827542.003.0016
> "the number of them of length k is k+1, if k is smaller than the length of the Christoffel word, and it
> is a characteristic property (Borel and the author)".

This is the single textbook reference for the Pirillo, Borel–Reutenauer and MRS characterisations.
**Keep.**

**altman2000balanced** (V, zbMATH). E. Altman, B. Gaujal, A. Hordijk, *Balanced sequences and optimal
routing*, J. ACM 47(4) (2000) 752–775. doi:10.1145/347476.347482
> "is it possible to construct an infinite sequence over n letters where each letter is distributed as
> "evenly" as possible and appears with a given rate?"

This is the scheduling face of "balanced is optimal". **Kill.**

**jenkinson2004characterisations** (U: zbMATH review withheld; Elsevier not reachable). O. Jenkinson,
L. Q. Zamboni, *Characterisations of balanced words via orderings*, TCS 310 (2004) 247–271. The quote is
via BLRS: "He calls a word strongly balanced if it satisfies the conditions of the theorem." It is the
origin of "circularly balanced". **Keep.**

**deluca2006some** (U: no abstract reachable). A. de Luca, A. De Luca, *Some characterizations of finite
Sturmian words*, TCS 356 (2006) 118–125. It is cited by De Luca–Fici for P18. **Keep.**

**tijdeman1996complementary** (U: zbMATH metadata only). R. Tijdeman, *On complementary triples of
Sturmian bisequences*, Indag. Math. 7(3) (1996) 419–424. doi:10.1016/0019-3577(96)83728-1. It is the
origin of the inf-ρ argument (via Lothaire's notes). **Keep.**

**mantaci2003burrows** (U: statement via BLRS). S. Mantaci, A. Restivo, M. Sciortino, *Burrows–Wheeler
transform and Sturmian words*, IPL 86 (2003) 241–246. "w is a conjugate of a Christoffel word iff
BWT(w) takes the form y^q x^p, p ⊥ q". This is a fast decision procedure. **Open.**

**lothaire2002sturmian** (V, dup). M. Lothaire, *Algebraic Combinatorics on Words*, ch. 2 (2002). Fetched
as `C2.ps` from Berstel's page (http).
> "Proposition 2.1.3. Let X be a factorial set of words. The set X is unbalanced if and only if there
> exists a palindrome word w such that 0w0 and 1w1 are in X."

The new extracts are L2.1.15 and P2.1.3 (see Hook 1). **Keep.**

**dvorakova2024balanced** (V). L. Dvořáková, Z. Masáková, E. Pelantová, *2-balanced sequences coding
rectangle exchange transformation*, Theory Comput. Syst. 68 (2024) 1537–1555.
https://arxiv.org/abs/2403.12791
> "These sequences are obtained by colouring of Sturmian sequences."

**Kill.**

**sano2004mbalanced** (U: title and metadata only). S. Sano, N. Miyoshi, R. Kataoka, *m-balanced
words: a generalization of balanced words*, TCS 314 (2004) 97–120. **Open** (fetch it for D3
precedents).

### 4.2 Hook 2: anchor geometry

**peltomaki2020avoiding** (V). J. Peltomäki, M. A. Whiteland, *Avoiding abelian powers cyclically*, Adv.
Appl. Math. 121 (2020) 102095. https://arxiv.org/abs/2006.06307
> "A finite word w avoids abelian N-powers cyclically if for each abelian N-power of period m occurring
> in the infinite word w^ω, we have m ≥ |w|. … 𝒜_∞(2) = 4".

**Kill** (local).

**puzynina2013abelian** (V). S. Puzynina, L. Q. Zamboni, *Abelian returns in Sturmian words*, J. Combin.
Theory A 120(2) (2013) 390–408. https://arxiv.org/abs/1204.5755. Quoted in Hook 2. **Keep.**

**cassaigne2017cyclic** (V). J. Cassaigne, G. Fici, M. Sciortino, L. Q. Zamboni, *Cyclic complexity of
words*, J. Combin. Theory A 145 (2017) 36–56. https://arxiv.org/abs/1402.5843
> "Unlike most complexity functions, cyclic complexity distinguishes between Sturmian words of different
> slopes."

**Kill.**

**alessandri1998three** (V, zbMATH). P. Alessandri, V. Berthé, *Three distance theorems and combinatorics
on words*, Enseign. Math. 44 (1998) 103–132.
> "a very nice survey on the three distance theorem … going from codings of rotations to block
> complexities".

Background for D5. **Keep.**

**vukusic2026balanced** (V). I. Vukusic, *Balanced rectangles over Sturmian words and minimal discrepancy
intervals*, arXiv:2602.12801. Quoted in Hook 2. **Kill.**

**berthe2006initial** (V, zbMATH). V. Berthé, C. Holton, L. Q. Zamboni, *Initial powers of Sturmian
sequences*, Acta Arith. 122 (2006) 315–347.
> "every sequence outside the shift orbit of this sequence begins in arbitrary long words repeated at
> least three times".

**Kill** (repeat-lemma input only).

### 4.3 Hook 3: Dubickas and rational base

**dubickas2009squares** (V, numdam). A. Dubickas, *Squares and cubes in Sturmian sequences*, RAIRO ITA
43(3) (2009) 615–624.
> "every sturmian word ω has infinitely many prefixes of the form U_nV_n^3, where |U_n| < 2.855|V_n|".

**Kill.**

**dubickas2008powers** (V, zbMATH). A. Dubickas, *On the powers of 3/2 and other rational numbers*, Math.
Nachr. 281 (2008) 951–958.
> "there is no ξ > 0 such that these fractional parts all lie in the set I = [8/39,18/39] ∪
> [21/39,31/39]".

**Kill.**

**akiyama2008mahler** (V, zbMATH). S. Akiyama, *Mahler's Z-number and 3/2 number systems*, Unif. Distrib.
Theory 3(2) (2008) 91–99.
> "criteria for deciding whether a number has multiple representations in a rational based number
> system".

**Kill.**

**akiyama2018subtrees** (V). S. Akiyama, V. Marsault, J. Sakarovitch, *On subtrees of the representation
tree in rational base numeration systems*, DMTCS 20(1) (2018). https://arxiv.org/abs/1706.08266. Quoted
in Hook 3. **Kill.**

**morgenbesser2013patterns** (V). J. F. Morgenbesser, W. Steiner, J. M. Thuswaldner, *Patterns in
rational base number systems*, J. Fourier Anal. Appl. 19 (2013) 225–250.
https://arxiv.org/abs/1203.4919. Quoted in Hook 3. **Kill.**

**kari2017cellular** (V). J. Kari, J. Kopra, *Cellular automata and powers of p/q*, RAIRO ITA 51 (2017)
191–204. https://arxiv.org/abs/1710.05737
> "cellular automata F_{p,q} which multiply numbers by p/q in base pq".

**Kill.**

**sterin2020collatz** (V). T. Stérin, D. Woods, *The Collatz process embeds a base conversion
algorithm*, RP 2020, LNCS 12448, 131–147. https://arxiv.org/abs/2007.06979. Quoted in Hooks 3 and 5.
This is a different paper from the ancestor-regex work in `syracuse_words/references`. **Open**
(vocabulary).

**bugeaud2019new** (V). Y. Bugeaud, D. H. Kim, *A new complexity function, repetitions in Sturmian words,
and irrationality exponents of Sturmian numbers*, Trans. AMS 371 (2019) 3281–3308.
https://arxiv.org/abs/1510.00279
> "r(n, x) denotes the length of the smallest prefix of x containing two (possibly overlapping)
> occurrences of some word of length n."

**Open** (sharp pigeonhole for L7).

**allouche2010extremal** (V). J.-P. Allouche, A. Glen, *Extremal properties of (epi)Sturmian sequences
and distribution modulo 1*, Enseign. Math. 56 (2010) 365–401. https://arxiv.org/abs/0907.2430
> "we focus on extremal properties of (epi)Sturmian sequences, some of which have been rediscovered
> several times."

This is the common root of Dubickas and H–H. **Keep.**

**kwon2015exceptional** (V). D. Kwon, *Exceptional parameters of linear mod one transformations and
fractional parts {ξ(p/q)^n}*, C. R. Math. 353 (2015) 291–296. **Kill.**

**dubickas2005integer** (V, zbMATH). A. Dubickas, A. Novikas, *Integer parts of powers of rational
numbers*, Math. Z. 251 (2005) 635–648.
> "the sequence ([ξa^n]) contains infinitely many elements divisible by at least one of the set P(a)".

This was the round-1 lead. There is no quantitative repeat bound. **Kill.**

### 4.4 Hook 4: near-miss data

**wegner2021collatz** (V). F. Wegner, *The Collatz problem generalized to 3x+k*, arXiv:2101.08060.
Quoted in Hook 4. **Keep** (data).

**kaneda2015two** (V). M. Kaneda, *Two remarks on the Collatz cycle conjecture*, Fibonacci Quart. 53
(2015) 168–174. https://arxiv.org/abs/1010.6206
> "We give a short proof of Belaga's result on bounds to perigees of (3x+d)-cycles of a given
> oddlength."

**Keep.**

**aliyev2025special** (V). Y. N. Aliyev, *On special integer linear combinations of terms of rational
cycles for the generalized 3x+1 problem*, NNTDM 31(3) (2025) 658–666. https://arxiv.org/abs/2307.11990
**Kill** (F1 restated).

**simons2004mersenne** (V, author PDF). J. Simons, B. de Weger, *Mersenne en het Syracuseprobleem*, NAW
5/5(3) (2004) 218–220. Quoted in Hook 4. **Keep** (F4 statement).

**belaga2000cyclic** (V, dup). E. G. Belaga, M. Mignotte, *Cyclic structure of dynamical systems
associated with 3x+d extensions of Collatz problem*, Strasbourg preprint 2000/17, HAL hal-00129656.
Conjecture 6 is quoted in the jsonl. It is the only reference of OEIS A226670–2. **Keep.**

### 4.5 Hook 5: barriers

**conway2013unsettleable** (V). J. H. Conway, *On unsettleable arithmetical problems*, Amer. Math.
Monthly 120(3) (2013) 192–198. doi:10.4169/amer.math.monthly.120.03.192. Quoted in Hook 5. **Keep** (as
the meta-statement).

**zabolotskii2026additive** (V). A. Zabolotskii, *Additive systems for ℤ are undecidable*, J. Combin.
Math. Combin. Comput. 130 (2026) 241–253. https://arxiv.org/abs/2508.17285. **Kill.**

**sterin2021hardness** (V). T. Stérin, D. Woods, *Hardness of busy beaver value BB(15)*,
arXiv:2107.12475. **Kill.**

### 4.6 Hook 6: extremality and citers

**knight2026collatz** (V, dup). K. Knight, *Collatz high cycles do not exist*, Discrete Math. 349 (2026)
114812 (HAL hal-04261183, 2023).
> "The circuit contains the smallest member of S, while the high cycle contains the largest."

The new fact is the refereed venue: cite the journal version. **Keep.**

**houze2026sharp** (V, SSRN abstract via Crossref). W. C. Houze, *Sharp exit bounds for the critical
Sturmian parity word of the 3x+1 map*, SSRN (2026). doi:10.2139/ssrn.7671945. Quoted in Hook 6. Its Lean
sources were not located. **Keep** (prior art for L2′).

**jenkinson2009balanced** (V, author PDF). O. Jenkinson, *Balanced words and majorization*, DMAA 1(4)
(2009) 463–483.
> "Theorem 1.2. Suppose 1 ≤ p < q are coprime integers. For w ∈ Wp,q, the product P(w) = ∏ Ii(w) is
> maximized precisely when w is balanced."

**Open.** The base-2 version holds; D6 shows the (2,3) version must fail beyond x_min.

**vesti2015most** (V). J. Vesti, *The most unbalanced words 0^{q−p}1^p and majorization*, DMAA 7(3)
(2015) 1550028. https://arxiv.org/abs/1501.00871. Quoted in the jsonl. **Kill.**

**bousch2015convex** (V, Crossref + zbMATH). T. Bousch, *Une propriété de domination convexe pour les
orbites sturmiennes*, Canad. J. Math. 67 (2015) 90–106.
> "Let x = (x0; x1; … ) be a N-periodic sequence of integers … the average of |∝| on the orbit of x is
> greater than its average on the orbit of s."

This applies to integer gap words directly. **Open.**

**bousch2000fish** (V, zbMATH). T. Bousch, *Le poisson n'a pas d'arêtes*, Ann. IHP Probab. Stat. 36
(2000) 489–508. It is the Sturmian maximising-measure theorem (frames lead 7). **Kill.**

**jenkinson2006ergodic** (V, zbMATH). O. Jenkinson, *Ergodic optimization*, DCDS 15 (2006) 197–224.
**Kill** (background).

**sidorov2011optimizing** (V). N. Sidorov, *Optimizing properties of balanced words*, EPTCS 63 (2011)
240–246. https://arxiv.org/abs/1108.3639
> "optimization problems … which yield - sometimes quite unexpectedly - balanced words as optimal."

**Keep** (index of "balanced is optimal" results).

---

## 5. Leads for round 3

1. **Houze 2026 Lean sources** (SSRN 7671945). Locate them to compare against L2′ and to avoid
   duplicate work.
2. **Sano–Miyoshi–Kataoka 2004** and **Jenkinson–Zamboni 2004** (full text). Check whether D3's band
   statement or the cycle-lemma proof of circular balance is already in print.
3. **Bousch 2015**, full text. Is S^{(j)}, or log x_j, an increasing affine functional for the order ≤₂
   after the substitution d_k − E/o? If yes, Sturmian gap words minimise an explicit discrepancy average
   of the cycle elements: a positive version of D6.
4. **Provençal 2011 u²v² words.** Test the queue.md §5.2 witness-pair move on the unique-imbalance-pair
   family first. It is the next family after Knight.
5. **Fernández–Ibáñez 2026.** Contact or erratum: the C_min(upper) step (D4).
