# Literature review, theme `generalized-maps`: what any proof must use

*Agent theme: the limits side. The cocycle identities hold for every Syracuse-type map; this file
collects what the literature on 3x+k, qx+1, px+q, Conway maps and 2-adic conjugacy says about the
inputs any no-cycle proof needs. Bibliography lines: `bib-generalized-maps.jsonl` (48 entries, all
fetched; 14 tagged `dup`). Date: 2026-10-30.*

---

## Executive summary

**F1 is classical.**
- Lagarias (1990): integer cycles of 3x+k = rational cycles of 3x+1.
- Belaga–Mignotte (2006, Thm 4–5): every word with ℓ ≥ ⌈k·log₂3⌉ is a primitive (3x+d)-cycle, with
  d = B/gcd(A,B). "The original, 3n + 1 Collatz conjecture is equivalent to … no member of the
  Collatz corona A_{k,ℓ} is devisible by the Collatz number B_{k,ℓ}" (|A_{k,ℓ}| = C(ℓ−1,k−1)).
- The program's gcd problem is this formulation; the report should cite it.

**Limits.**
- Tao (2011, Prop. 7, sketch): no cycles ⇒ 2^a − 3^k ≥ (1+ε)^k. So "any proposed proof … must
  either use transcendence theory, or introduce new techniques … to create exponential separation".
  The Baker/Rhin squeeze is therefore required.
- Baker machinery is map-uniform (Steiner 1981 finds the 5x+1 cycles; Simons 2008 covers 3x+q and
  px+1). The 3x+1-specific input is the verification bound N₀ (Hercher 2023).
- Every (ax+b)/2 with ab odd is conjugate to the 2-adic shift (Akin; Bernstein–Lagarias). 2-adic
  prefix pigeonholes cannot see 3 vs 5.
- Undecidability is proved only for many-branch maps (Conway; modulus 396; Kurtz–Simon Π⁰₂;
  Lehtonen). Nothing is known for 2-branch maps.

**F4 corrected.** The sibling cycles (5x+1: o ≤ 3; negative 3x+1: o ≤ 7) force only o₀ ≥ 7. The
binding data are p = 3, D > 0 near-misses:
- k(w) = 5 at (E,o) = (27,17);
- k(w) = 29 at the convergent (65,41);
- log G/log|D| = 0.9997 at o = 31913.

So no ceiling G ≤ |D|^θ with θ < 1 holds.

**Hooks:**
1. Tao's separation implication.
2. The corona formulation.
3. 2-adic blindness.
4. The near-miss slack test.
5. N₀ is the only 3x+1-specific input.

---

## LIMITS SECTION (for the report)

### (a) Map × known cycles × known results

S, D, G and k are the program's quantities with (X,Y) = (2,p): D = 2^E − p^o, G = gcd(S,D), and
k = D/G. The cycle elements are S^{(j)}/G. The words were recomputed by iterating the map from the
published cycle elements; this is arithmetic on cited data, not a search.

| map | cycle (smallest odd / all odd) | gap word w | o | E | E/o | D | G | k = D/G | what is proved | source |
|---|---|---|---|---|---|---|---|---|---|---|
| 3x+1, x>0 | {1} | (2) | 1 | 2 | 2 | +1 | 1 | **1** | only cycle with min < 2^71; m ≤ 91 excluded | SURVEY; Hercher 2023 |
| 3x+1, x<0 | {−1} | (1) | 1 | 1 | 1 | −1 | 1 | D/G = −1 | listed | Lagarias 1985 |
| 3x+1, x<0 | {−5,−7} | (1,2) | 2 | 3 | 1.5 | −1 | 1 | D/G = −1 | circuit | Lagarias 1985 |
| 3x+1, x<0 | {−17,…} | (1,1,1,2,1,1,4) | 7 | 11 | 1.571 | −139 | 139 | D/G = −1 | the unique 2-cycle of 3x−1 (Simons 2007) | Lagarias 1985; Simons 2007 |
| 5x+1 | {1,3} | (1,4) | 2 | 5 | 2.5 | +7 | 7 | **1** | circuit (Steiner: "1 → 8 → 1") | Akin 2004; Steiner 1981 |
| 5x+1 | {13,33,83} | (1,1,5) | 3 | 7 | 2.333 | +3 | 3 | **1** | the only nontrivial circuit-cycle (Baker + CF of log₂(5/2)) | Steiner 1981 |
| 5x+1 | {17,43,27} | (1,3,3) | 3 | 7 | 2.333 | +3 | 3 | **1** | "double circuit" (m=2) | Steiner 1981 |
| 181x+1 | {27,611} | (3,12) | 2 | 15 | 7.5 | +7 | 7 | **1** | Crandall's counterexample; period-2 orbits only for q ∈ {±1,±3,5,−11,−91,181}, \|q\|<10^11 | Crandall 1978; Franco 1990 |
| 3x+5 | 19 / 23 | (1,1,3) / (1,2,2) | 3 | 5 | 1.667 | +5 | 1 | 5 | primitive (G = 1) | OEIS A226607 |
| 3x+5 | 187 / 347 | 11111211212321115 / 11113111122412122 | 17 | 27 | 1.5882 | +5 077 565 | 1 015 513 | **5** | near-miss: E − o·log₂3 = 0.056 | OEIS A226607/9/10 |
| 3x+13 | 131 | (1,1,1,3,1,1,1,1,1,2,1,2,1,2,5) | 15 | 24 | 1.600 | +2 428 309 | 186 793 | 13 | one of 9 primitive cycles of 3x+13 | OEIS A226607 |
| 3x+29 | 3811 / 7055 | 41-letter words (below) | 41 | 65 | 1.5854 | ≈ +4.2·10^17 | ≈ 1.45·10^16 | **29** | at the **convergent 65/41**, E − o·log₂3 = 0.0165 | OEIS A226670–2 |
| 3x+61 | 235 | 41 letters | 41 | 66 | 1.610 | ≈ 3.7·10^19 | ≈ 6.1·10^17 | 61 | | OEIS A226670–2 |
| 3x+125 | 899 | 74 letters | 74 | 118 | 1.595 | ≈ 10^35 | | 125 | E − o·log₂3 = 0.71 | OEIS A226670–2 |
| 3x+308219 | 67 | 31913 letters | 31913 | 63330 | 1.984 | ≈ 10^19064 | \|D\|/308219 | 308219 | longest known primitive 3x+k cycle (record) | OEIS A226670–2 |

The words of the critical-slope near-misses (concatenated digits; letters ≥ 10 bracketed):

```
3x+5   (27,17)  x_min=187  11111211212321115
3x+5   (27,17)  x_min=347  11113111122412122
3x+29  (65,41)  x_min=3811 11111112311121121111112111311512211116233
3x+29  (65,41)  x_min=7055 12111211111112312211111121531311113212232
3x+61  (66,41)  x_min=235  11221211111111211131222311232111231232132
3x+125 (118,74) x_min=899  11111111131121211121211541111111511211221112112214111113441111121214211322
```

**Exact statements on 3x+d cycle counts and lengths (literature).**
- **Belaga 2003.** For a 3x+d cycle with k odd elements and length l:
  - prg(C) ≤ d/(2^{l/k} − 3), so log₂3 < l/k ≤ log₂(d+3), and the upper bound is sharp;
  - #cycles of oddlength k ≤ d·k^{c₀}, with c₀ = 32;
  - max element < d·k^{c₀}(3/2)^k.

  These are effective via linear forms in logarithms and **uniform in d**.
- **Belaga–Mignotte 1998.** At most d·k^c periodic orbits contain ≤ k odd integers (Baker–Wüstholz).
- **Lagarias 1990.** Infinitely many k have ≥ k^{1−ε} primitive cycles of period ≤ log k, and
  infinitely many k have none of period < k^{1/3}. He conjectures that every T_k has a primitive
  cycle and that each has finitely many.
- **Belaga–Mignotte 2006 (data).** All 6667 systems with d < 20000 have a primitive cycle. There
  are 42765 cycles in total (OEIS A226607 corrects this to 42757). The count ω(d) ranges from 1
  (1481 systems) to 944 (d = 14303).
- **Simons 2008 ("Exotic").** For each p ≥ 5 some q gives arbitrarily many primitive m-cycles
  (modulo a conjecture).
- **Franco–Pomerance 1995.** For a density-1 set of q, the map qx+1 has no m with C^{(2)}(m) = 1.

### (b) The F4 meta-statement, restated and corrected

**What is confirmed.**

- *ℤ[X,Y] identities are p-uniform, and q never enters.* S(w) and D(w) depend only on the word and
  on Y = p. The shift q is an *output*, q = k(w) = D/G (Belaga–Mignotte 2006, Thm 4(2)–(3); Lagarias
  1990). Steps that use only:
  - generic identities,
  - "D odd" and gcd(D,6) = 1,
  - |D|-based ceilings

  prove statements "G(w) < |D(w)|" that are equally true or false at Y = 3, 5 or 181 and for either
  sign of D. These steps cannot exclude (1,4), (1,1,5), (1,3,3) at Y = 5, (3,12) at Y = 181, or
  (1), (1,2), (1,1,1,2,1,1,4) at Y = 3 with D < 0.
- *Literature parallels.*
  - Lagarias (2010 overview): "the methods generally apply to the 3x + k function as well".
  - Simons 2008 generalizes the m-cycle criteria to 3x+q and px+1, noting "such problems may have
    m-cycles for various small values of m".
  - Steiner's Baker + continued-fraction (CF) machinery that kills 3x+1 circuits *finds*
    {13,208} for Q = 5.
  - Akin: the 2-adic method "is too general. It will work just as well … for a any odd 2-adic".

**What needs correcting.**

1. *The sibling obstruction is weak.* The sibling cycles force only o₀ ≥ 7 (sign-blind) or o₀ ≥ 3
   (p-blind), and 5x+1 and 3x−1 are themselves conjectured to have finitely many cycles
   (Kontorovich–Lagarias: "It is expected there are finitely many cycles"). A p-uniform method that
   proves "no cycle with o > o₀" plus a finite check is therefore **not** ruled out by any known
   sibling cycle.

   *The binding constraint is the near-miss words of p = 3 itself.* Words with D > 0 and small k(w)
   are genuine cycles of 3x+5 and 3x+29. A ceiling f(w) ≥ G(w) must satisfy f(w) ≥ |D|/k(w) there,
   and exclusion requires f(w) < |D|. A lever must therefore resolve G within log₂k(w) bits:
   - 2.3 bits at (27,17);
   - 4.9 bits at (65,41);
   - ≤ 18.2 bits at o = 31913, where log G / log|D| = 0.99971.

   **No universal bound G ≤ |D|^θ with θ < 1, or G ≤ |D|/c with c > 5, is true.**

2. *Counting and pigeonhole budgets are p-uniform.* This is my own derivation, not from the
   literature. The F5 budget ln C(E−1,o−1)/o at the critical slope equals s·H(1/s) with s = log₂p.
   Its gap to ln p is s·(ln 2 − H(1/s)) ≥ 0:

   | p | gap (nats/letter) |
   |---|---|
   | 3 | 0.055 |
   | 5 | 0.022 |
   | 7 | 0.118 |

   The gap is smallest for p = 5, the map that *has* cycles. Tao's heuristic Σ_{a,k} C(a−1,k−1)/q
   (2011) is the same count. Counting alone cannot single out 3: it predicts finitely many cycles for
   every p, which is consistent with 5x+1 having three.

**Strongest literature-backed formulation (proposed replacement for F4).**

> **(F4′)** Any proof of the 3x+1 no-cycle conjecture must:
>
> 1. **imply an exponential separation** |2^a − 3^k| ≥ (1+ε)^k (Tao 2011, Prop. 7). It must therefore
>    import transcendence (Baker/Rhin), as the squeeze does, or prove a new separation theorem.
> 2. **use an input that is not p-uniform and not sign-blind for short words.** It must separate
>    (1,1,5), (1,3,3) at p = 5 and (1,1,1,2,1,1,4) at p = 3, D < 0, from the 3x+1 positive case.
>    Steps that are uniform in p and in the sign of D can prove at best "no cycle with o > o₀",
>    with o₀ ≥ 7.
> 3. **resolve G(w) to within the factor k(w)** on near-miss words. The known examples are
>    k = 5 at o = 17, k = 29 at o = 41, and k ≤ 3.1·10^5 at o ≈ 3.2·10^4. Ceilings that lose a
>    power of |D| are false.
> 4. **be effective.** In every published exclusion (Steiner, Simons–de Weger, Hercher) the
>    3x+1-specific input is the numerical bound N₀. It enters through the minimal-element merging
>    lemma and the computational verification, and gives o ≥ 1.375·10^11. Map-uniform transcendence
>    then gives "finitely many m-cycles for each m".
>
> No theorem of the form "any method valid for all 3x+k cannot prove X" was found. The literature
> has only:
> - Tao's *implication*, which is positive and constraining;
> - heuristic statements: Akin; Lagarias; Kontorovich–Lagarias on stochastic models; the
>   Dhiman–Pandey v1 heuristic "the non-existence of integer cycles cannot be proven solely through
>   algebraic manipulation of the cycle equation itself", which v2 drops in favour of a narrower
>   Büchi-arithmetic theorem.

**Undecidability scope (item 3 of the brief).**

| result | maps covered | branches / modulus | what is undecidable |
|---|---|---|---|
| Conway 1972 | g(n) = a_j·n for n ≡ j (mod N), a_j rational | arbitrary N | whether the orbit of 2^k hits another power of 2 (r.e.-complete: "m-complete", Michel 2015) |
| Kaščák 1992 (via bbchallenge wiki) | GCFs | universal at modulus **396** | |
| Burckel 1994 | periodically linear | arbitrary | whether f^(k)(1) = 0 for some k, and "for each n some f^(k)(n) = 0" |
| Kurtz–Simon 2007 | a_i·x + b_i mod m | arbitrary m | the uniform problem (every x reaches 1) is **Π⁰₂-complete** |
| Endrullis–Grabmayer–Hendriks 2009 | FRACTRAN | arbitrary | halting on all inputs is Π⁰₂-complete |
| Lehtonen 2008 | 3x+t, t ∈ {−9,…,9} chosen by **recursive, non-periodic** sets A_t; x/2 on evens | 19 affine branches on the odds, non-periodic selection | reaching 1 |
| Dhiman–Pandey 2026 v2 | T_{q,d}, q an odd prime, d odd | 2 | not BA₂-definable (an automata obstruction, not undecidability) |

No undecidability or independence result is known for any 2-branch map (px+q)/2^ν with periodic
branch selection.
- Belaga–Mignotte 2006: "the question of what is the minimal p > 2 which guarantees the existence of
  universal computational devices T_{Mp,Rp} … remains an open problem".
- Lagarias 2010: 3x+1 "might conceivably belong to a smaller class of generalized 3x + 1 functions
  that evade undecidability results".

The smallest unresolved machines are 2-branch 3/2-maps, for example Antihydra (BB(6)), which is
*open*, not undecidable.

### (c) Slack-test data for program levers

**Test 1 (calibration, critical slope).** Run each lever on the six near-miss words above. The
claimed ceiling f(w) must satisfy |D|/k(w) ≤ f(w):

| (E,o) | k(w) | lower bound on f(w) |
|---|---|---|
| (27,17) | 5 | ≥ 1 015 513 |
| (65,41) | 29 | ≥ 1.45·10^16 |
| (66,41) | 61 | ≥ 6.1·10^17 |
| (118,74) | 125 | |

A lever that *excludes* these words, i.e. proves f(w) < |D|, has correctly separated k = 1 from
k = 5 or 29. Report log₂(f/|D|): it must lie in [−log₂k, 0) to count as a pass.

**Test 2 (sign and p).** Run each lever on (1,1,1,2,1,1,4) at (2,3), with D = −139 and G = 139,
and on (1,1,5) and (1,3,3) at (2,5), with D = 3 and G = 3. Any lever that "excludes" them is
unsound, or else uses an input that is specific to p = 3 or to D > 0. Record which input.

**Test 3 (no power saving).** For the record cycles (OEIS A226670–2), log₁₀ k(w) / log₁₀|D(w)|:

| o | E | k | log₁₀ k / log₁₀\|D\| |
|---|---|---|---|
| 1000 | 1922 | 3299 | 3.52 / 578.6 |
| 2253 | 4531 | 11491 | 4.06 / 1364 |
| 31913 | 63330 | 308219 | 5.49 / 19064 |

Any claimed G ≤ |D|^{1−ε} with ε > 3·10^{−4} is falsified at o = 31913. These record words have
slope ≈ 2, not log₂3, because x_min ≪ k there (Belaga's l/k ≤ log₂(3 + k/x_min)). They test
universal ceilings, not critical-slope levers.

**Test 4 (forced divisors).** Holden 2011 constructs words (1^{k−2}, e, e′) with e ≤ φ(q). For any
q with 2 a primitive root mod q and 3^{k−1} − 2^{k−1} prime to q, these words have q | S. So
G ∋ q can be forced on run-of-1s words with a growing tail letter, a shape adjacent to the
bounded-defect family.

---

## Idea → hook map

| idea | source(s) | touches | what it would give | verdict | cheapest first test |
|---|---|---|---|---|---|
| F1 = Belaga–Mignotte "Collatz corona" formulation; rational cycles = 3x+k cycles | Lagarias 1990; Belaga–Mignotte 2006 Thm 4–5; Holden 2011 | F1 | a citation for F1 and the exact equivalence "3x+1 ⇔ B ∤ A for all corona members"; corona size C(ℓ−1,k−1) (Lyndon-type count) | **keep** | check the tool's word → (k(w), S^{(j)}/G) map against Thm 4(3) on the 3x+5 (27,17) words |
| No-cycle ⇒ exponential separation of 2^a, 3^k | Tao 2011 blog, Props 6–7 | F3, F4 | justifies the squeeze architecture: transcendence input is *necessary* unless a new separation theorem is proved | **keep** | none (conceptual); state in the report as the meta-limit |
| 2-adic conjugacy: every (ax+b)/2, ab odd, is conjugate to the shift | Akin 2004 (Ex. 4); Bernstein–Lagarias 1996 §4; Lagarias 1985 | F4, F5 (shared-prefix pigeonhole) | kills any lever that factors through 2-adic prefixes or congruences mod 2^j alone | **kill** (as a stand-alone lever) | verify the F5 prefix congruence on the 5x+1 word (1,1,5) |
| Near-miss slack test | OEIS A226607/9/10/70–72; Belaga–Mignotte 2006b tables | F4, open problem 1 (f(w)) | an empirical bar for f(w): f ≥ \|D\|/k(w); no \|D\|^θ ceilings | **keep** | Tests 1–3 above (6 words + 3 records) |
| Counting budget is p-uniform | Tao 2011 heuristic Σ C(a−1,k−1)/q; Belaga–Mignotte corona count; derived gap table | F5, open problem 2 | shows pigeonhole by counting cannot single out p = 3 (gap at p = 5 is smaller) | **kill** (as a 3-specific tool) | recompute the gap table for p = 3, 5, 7 |
| Map-uniform Baker machinery for m-cycles | Steiner 1977/1981; Simons–de Weger 2005; Simons 2008; Brox 2000; Hercher 2023 | F4 (effectivity), open problem 3 | benchmarks the lever's o₀ against "finitely many m-cycles for each m" and against o ≥ 1.375·10^11 | **keep** | restate the bounded-defect lever's exclusion as an m-cycle statement (which m does βd^L have?) |
| N₀ is the only 3x+1-specific input | Hercher 2023 Lemmas 8–9, Thm 16; Barina | F4 | identifies what the program must import (N₀, D>0) to beat sibling maps | **keep** | list which program steps use D>0 or N₀ |
| Contraction thresholds (Möller m ≤ d^{d/(d−1)}; Matthews–Watts ∏ m_i < d^d) | Möller 1978; Matthews–Watts 1984/85; Kontorovich–Sinai 2002 | divergence only | separates 3x+k (contracting) from 5x+1 (expanding) for *divergence*, not for cycles | **kill** for cycles | none |
| Undecidability | Conway; Kaščák; Burckel; Kurtz–Simon; Lehtonen; Endrullis et al.; Poonen | F4 | no known logical obstruction for 2-branch maps; no independence result | **kill** as an obstruction | none |
| Presburger / automata obstruction | Dhiman–Pandey 2026 v1/v2 | F4 | rules out automata-only proofs for every T_{q,d}; the program's ℤ[X,Y] layer uses exponentials and is not Presburger, so it is not directly affected | **kill** (not binding) | none |
| Sturmian words and 2-adic depth | Dejesus 2026 (SSRN; Lean-checked) | F2 (balanced words), F5 (prefix depth) | "2-adic approximation depth of a periodic shadow equals a longest common prefix": the same mechanism as F5; periodic shadows of Sturmian words are the critical words, with denominators 2^ℓ − 3^k | **open** | read §§3–5: does the prefix-depth estimate bound G for Christoffel words? |
| Numen χ_q and Correspondence Principle | Siegel 2020 | F1 | χ_q(z) for periodic z is S/D, so the same object in (p,q)-adic dress; q-uniform | **open** (low) | none |
| Forced-divisor construction | Holden 2011 | bounded-defect lever, open problem 3 | for (1^{k−2}, e, e′) words, any prime q with 2 a primitive root can be forced into G | **open** | apply the lever to Holden words with q = 5, 11, 13 |
| Elementary 2-cycle method that sees q and sign | Simons 2007 | F4, open problem 3 | an elementary (no-transcendence) m = 2 exclusion; a model for a sign-aware lever | **keep** | compare with the bounded-defect lever on m = 2 words |
| Long cycles sit at convergent denominators | Keller 1999 (permutations); the (65,41) 3x+29 pair | F2 | supports the "balanced/Sturmian" picture of critical words | **open** | check E/o of the near-miss table against convergents and intermediate fractions |
| Stochastic models | Lagarias–Weiss 1992; Kontorovich–Lagarias 2009; Volkov 2006 | none for cycles | "cannot see" measure-zero sets | **kill** | none |
| Rewriting / automated termination | Yolcu–Aaronson–Heule 2021 | open problem 2 (covering) | a word-rewriting system whose termination ⇔ Collatz; must be map-specific | **open** (low) | none |

---

## Annotated bibliography

Quotes are verbatim from the fetched page or PDF. "[Lagarias bib I/II, #n]" marks a quote from
Lagarias's annotated bibliographies (arXiv:math/0309224 v13, arXiv:math/0608208 v6), which were
fetched; these are reviewer statements, in the role of a MathSciNet review. The full quotes are in
the JSONL.

### A. 3x+k and rational cycles

1. **J. C. Lagarias, "The set of rational cycles for the 3x+1 problem," Acta Arith. 56 (1990)
   33–53.** DOI 10.4064/aa-56-1-33-53.
   - *Quote* [Lagarias bib I, #108]: "These correspond to rational cycles x/k of the 3x+1 function
     T. It conjectures that every Tk has such an integer cycle. It shows that infinitely many k have
     at least k^{1−ε} distinct such cycles of period at most log k, and infinitely many k have no
     such cycles having period length less than k^{1/3}."
   - *Note:* this is the origin of F1. "k(w) ≠ 1" is the k = 1 slice of Lagarias's Finite Primitive
     Cycles Conjecture. The full text (Table 3.1) is behind an IMPAN redirect (403). *Verdict:*
     keep (dup).
2. **E. G. Belaga, M. Mignotte, "Walking cautiously into the Collatz wilderness…," DMTCS Proc. AG
   (2006) 249–260.** https://dmtcs.episciences.org/3512
   - *Quote:* "(7) The original, 3n + 1 Collatz conjecture is equivalent to the following claim: for
     any nontrivial pair (k, ℓ) ∈ Λ \ {(1, 2)}, no member of the Collatz corona A_{k,ℓ} is devisible
     by the Collatz number B_{k,ℓ}." Also: "αk,ℓ = #Ak,ℓ = C(ℓ−1, k−1), if gcd(k, ℓ) = 1", and
     "ω(d) … to 944 for the system D14303".
   - *Note:* this is exactly F1, with A = S and B = D. Theorem 5(5)–(6) adds that for narrow pairs
     ℓ = ⌈k·log₂3⌉ one has B < 3^k − 2^k = min A, so the floor lies below every S. Section 3 also
     states that the minimal modulus for universality is open. *Verdict:* **keep**.
3. **E. G. Belaga, "Effective polynomial upper bounds to perigees and numbers of (3x+d)-cycles of a
   given oddlength," Acta Arith. 106 (2003) 197–206.** DOI 10.4064/aa106-2-9.
   - *Quote* [Lagarias bib II, #11]: "prg(C) ≤ d/(2^{l/k} − 3). From this follows log2 3 <
     length(C)/oddlength(C) ≤ log2(d + 3) … one may take c0 = 32."
   - *Note:* F2's ratio sandwich holds uniformly in d. The count bound d·k^{32} is too weak to give
     finiteness. *Verdict:* keep (dup).
4. **E. Belaga, M. Mignotte, "Embedding the 3x+1 conjecture in a 3x+d context," Exp. Math. 7
   (1998).**
   - Not re-fetched: the Project Euclid page was empty. It is covered by SURVEY/EXCLUDED_PATTERNS
     (≤ d·k^c orbits with ≤ k odd elements). No new entry.
5. **OEIS A226607 / A226609 / A226610** (G. H. Morley): smallest elements, lengths and odd counts of
   primitive 3x+k cycles. https://oeis.org/A226607
   - *Quote:* "The 42757 primitive cycles found for k < 20000 [...] are suspected to be complete."
     The data rows are reproduced in the JSONL.
   - *Note:* the source of the near-miss table. The (27,17) pair for k = 5 and the (65,41) pair for
     k = 29 are verified by recomputation. *Verdict:* **keep**.
6. **OEIS A226670 / A226671 / A226672.** https://oeis.org/A226670
   - *Quote:* "Record-breaking values, for increasing positive integers k == 1 or 5 mod 6, of the
     conjectured length of the longest primitive cycle(s) … DATA: 2, 27, 31, 43, 65, 66, 100, …,
     49711, 63330", with k = "1, 5, 17, 23, 29, 61, 85, …, 273641, 308219".
   - *Note:* gives Test 3 (no power saving). *Verdict:* **keep**.
7. **OEIS A226613.** Conjectured number of primitive cycles per k.
   - *Quote:* "a(n) is the conjectured number of primitive cycles … DATA: 1, 5, 1, 2, 9, 2, …".
   - *Note:* 3x+5 has 5 cycles and 3x+13 has 9. *Verdict:* keep.
8. **D. Holden, "Results on the 3x+1 and 3x+d conjectures," Fibonacci Quart. 49(2) (2011) 131–134.**
   DOI 10.1080/00150517.2011.12428057.
   - *Quote:* "Theorem 1.4. Let q, k, and j be positive integers such that q is relatively prime to
     6, 2 is a primitive root mod q, 2^j − 3^k is positive, k − 2 + φ(q) < j, and 3^{k−1} − 2^{k−1}
     is relatively prime to q. Then there exist positive integers e1, …, ek−1 such that q divides n
     = 3^{k−1} + … [proof:] Choose … e1 = e2 = ··· = ek−2 = 1."
   - *Note:* constructs words with prescribed prime divisors of S. This is a forced-gcd mechanism on
     a run of 1s plus a tail. *Verdict:* open.
9. **B. Brent, "3x+1 dynamics on rationals with fixed denominator," arXiv:math/0204170 (2002).**
   - *Quote:* "We propose the existence of an infinite class of exact analogues of the 3x+1
     conjecture for rational numbers with fixed denominators."
   - *Note:* for denominators k with a single primitive cycle, 3x+k is an "exact analogue" of 3x+1.
     Such k are natural test cases where the program's ceiling must still be correct. *Verdict:*
     open.

### B. qx+1, px+q, Hasse–Möller–Matthews–Watts

10. **R. P. Steiner, "On the 'Qx+1' problem, Q odd," Fibonacci Quart. 19 (1981) 285–288.**
    Scanned primary: https://www.mathstat.dal.ca/FQ/Scanned/19-3/steiner.pdf
    - *Quote (OCR):* "13 → 208 → 13 and 1 → 8 → 1 are the only circuits which are cycles … using a
      result of Baker … The largest partial quotient is found to be 5393 … [Note: n = 17 also gives
      rise to a cycle under f. But this cycle results from a double circuit: 17 → 108 → 27 and
      27 → 68 → 17.]"
    - *Note:* the same Baker + CF machinery that excludes 3x+1 circuits *finds* the 5x+1 cycles.
      This is the cleanest literature instance of F4. *Verdict:* **keep** (dup, new primary quote).
11. **R. E. Crandall, "On the '3x+1' problem," Math. Comp. 32 (1978) 1281–1292.**
    - *Quote* [Lagarias bib I, #47]: "he formulates the conjecture that, aside from (q, r) = (3, 1),
      every map Cq,r(·) has at least one orbit that never visits 1 … true whenever r ≥ 3 … for q =
      5, q = 181 and q = 1093."
    - *Note:* 3x+1 is conjecturally the *unique* (q,r) with no exotic orbit. The 181 cycle is (3,12)
      with D = 7. *Verdict:* keep (dup).
12. **Z. Franco, C. Pomerance, "On a conjecture of Crandall concerning the qx+1 problem," Math. Comp.
    64 (1995) 1333–1336.** DOI 10.1090/S0025-5718-1995-1297468-4.
    - *Quote* [bib I, #64]: "{q : Crandall's conjecture is true for q} has asymptotic density 1, by
      showing … {q : C^(2)(m) ≠ 1 for all m ∈ Z} has asymptotic density one."
    - *Note:* qx+1 fails generically already at height 2. *Verdict:* keep.
13. **Z. Franco, "Diophantine approximation and the qx+1 problem," PhD thesis, Berkeley 1990.**
    - *Quote* [bib I, #63]: "for |q| < 10^11, only q = ±1, ±3, 5, −11, −91, and 181 have such
      orbits [period 2]. The method uses an inequality of F. Beukers."
    - *Note:* this is a complete map-uniform answer for o = 2. It shows that uniform Diophantine
      methods give exact lists across q. *Verdict:* keep.
14. **H. Möller, "Über Hasses Verallgemeinerung des Syracuse-Algorithmus," Acta Arith. 34 (1978)
    219–226.** DOI 10.4064/aa-34-3-219-226.
    - *Quote* [bib I, #130]: "if m ≤ d^{d/(d−1)} then the set of positive integers n which have some
      iterate H^(k)(n) < n, has full natural density 1 − 1/d."
    - *Note:* for d = 2 the threshold is m ≤ 4, which separates 3 from 5 for stopping times, not
      for cycles. *Verdict:* kill (for cycles).
15. **K. R. Matthews, A. M. Watts, "A generalization of Hasse's generalization of the Syracuse
    algorithm," Acta Arith. 43 (1984) 167–175.** DOI 10.4064/aa-43-2-167-175.
    - *Quote* [bib I, #123]: "if {T^(k)(m)} is unbounded and uniformly distributed (mod d) then m1 m2
      · · · md > d^d … T … is shown to be strongly mixing, hence ergodic, on Zd."
    - *Note:* d-adic ergodicity is generic across the whole class. *Verdict:* keep (as a limit).
16. **K. R. Matthews, A. M. Watts, "A Markov approach to the generalized Syracuse algorithm," Acta
    Arith. 45 (1985) 29–42.** DOI 10.4064/aa-45-1-29-42.
    - *Quote* [bib I, #124]: "if A = Π_{i∈S}(mi/d)^{αi} < 1 then all trajectories … eventually be
      periodic, while if A > 1 almost all trajectories … diverge."
    - *Note:* Conjecture 1(iii) in Belaga–Mignotte 2006 adds "the number of cycles is finite" for all
      Conway maps. *Verdict:* kill (for cycles).
17. **J. L. Simons, "A simple (inductive) proof for the non-existence of 2-cycles for the 3x+1
    problem," J. Number Theory 123 (2007) 10–17.** DOI 10.1016/j.jnt.2006.05.011.
    - *Quote* [bib II, #95]: "the 3x − 1 function … has a single 2-cycle with minimal element n0 =
      17 … The author's method applies to the 3x ± q problem … however it does not extend to
      classify m-cycles with m ≥ 3."
    - *Note:* an elementary method that sees the sign and q. It is a model for a sign-aware lever.
      *Verdict:* keep (dup).
18. **J. L. Simons, "On the (non)-existence of m-cycles for generalized Syracuse sequences," Acta
    Arith. 131 (2008) 217–254.** DOI 10.4064/aa131-3-2.
    - *Quote* [bib II, #96]: "criteria for the non-existence of m-cycles … such as the 3x + q problem,
      the px + 1 problem … (Note that such problems may have m-cycles for various small values of
      m.)"
    - *Note:* the m-cycle machinery is map-uniform. *Verdict:* keep (dup). Full text is a round-2
      lead.
19. **J. L. Simons, "Exotic Collatz cycles," Acta Arith. 134 (2008) 201–209.** DOI 10.4064/aa134-3-1.
    - *Quote* [bib II, #97]: "for each p there exist a q with the number of cycles being arbitrarily
      large."
    - *Verdict:* keep (dup).
20. **D. Cox, S. Ghosh, E. Sultanow, "Collatz cycles and 3n+c cycles" (2021).** Already in
    EXCLUDED_PATTERNS; not re-fetched; no entry.

### C. Stochastic models (contrast 3x+1 vs 5x+1)

21. **A. V. Kontorovich, J. C. Lagarias, "Stochastic models for the 3x+1 and 5x+1 problems,"
    Ultimate Challenge (2010) 131–188, arXiv:0910.1944.**
    - *Quote:* "it is conjectured that almost all 5x + 1 trajectories diverge … There could
      potentially be a set of measure zero escaping to infinity, which the model simply cannot see
      … It is expected there are finitely many cycles."
    - *Note:* 5x+1 is conjectured to have finitely many cycles, so the 5x+1 obstruction to p-uniform
      methods lives at small o only. *Verdict:* **keep**.
22. **J. C. Lagarias, A. Weiss, "The 3x+1 problem: two stochastic models," Ann. Appl. Probab. 2
    (1992) 229–261.** DOI 10.1214/aoap/1177005779.
    - *Quote* [bib I, #112]: "The models are branching random walks … c0 = 41.677…"
    - *Verdict:* open (irrelevant to cycles).
23. **S. Volkov, "A probabilistic model for the 5k+1 problem and related maps," Stoch. Proc. Appl.
    116 (2006) 662–674.** DOI 10.1016/j.spa.2005.11.007.
    - *Quote* [bib II, #115]: "the number of values of n ≤ x that have some iterate equal to 1
      appears to grow like x^α, where α ≈ 0.68."
    - *Verdict:* open.
24. **A. V. Kontorovich, Ya. G. Sinai, "Structure theorem for (d,g,h)-maps," Bull. Braz. Math. Soc.
    33 (2002) 213–224.** DOI 10.1007/s005740200010.
    - *Quote* [bib II, #49]: "exactly (d − 1)^m triples … produce a given path … converges to a
      Brownian motion with drift log g − (d/(d−1)) log d."
    - *Note:* the path (word) structure is identical across (d,g,h). *Verdict:* keep (as a limit).

### D. Undecidability and logic

25. **J. H. Conway, "Unpredictable iterations," Proc. 1972 Number Theory Conf., Boulder, 49–52.**
    - *Quote* [bib I, #43]: "g(n) = aj n if n ≡ j (mod N) … Given an f(·) in this class and an input
      value n = 2^k decide whether or not some iterate of n is a power of 2."
    - *Note:* many branches; the computation is encoded in prime exponents. *Verdict:* keep (as a
      limit).
26. **J. H. Conway, "FRACTRAN: a simple universal programming language for arithmetic," Springer
    1987.** DOI 10.1007/978-1-4612-4808-8_2.
    - *Quote* [bib I, #44]. *Verdict:* keep.
27. **S. A. Kurtz, J. Simon, "The undecidability of the generalized Collatz problem," TAMC 2007, LNCS
    4484, 542–553.** DOI 10.1007/978-3-540-72504-6_49.
    - *Quote* [bib II, #52]: "The problem GCP is Π^0_2-complete."
    - *Note:* the modulus is unbounded. Springer page blocked. *Verdict:* keep.
28. **E. Lehtonen, "Two undecidable variants of Collatz's problems," TCS 407 (2008) 596–600.** DOI
    10.1016/j.tcs.2008.08.029.
    - *Quote* [bib II, #57]: "f(x) = 3x + t if n ∈ At, for t = −9, …, 9 … {At} are recursive sets …
      undecidable."
    - *Note:* the closest that undecidability comes to 3x+k. It needs non-periodic shift selection.
      *Verdict:* keep.
29. **S. Burckel, "Functional equations associated with congruential functions," TCS 123 (1994)
    397–406.** DOI 10.1016/0304-3975(94)90136-8.
    - *Quote* [bib I, #30]. *Verdict:* keep.
30. **J. Endrullis, C. Grabmayer, D. Hendriks, "Complexity of Fractran and productivity," CADE-22,
    LNAI 5663 (2009).** arXiv:0903.4366.
    - *Quote:* "We prove that the question whether a Fractran program halts on all positive integers
      is Pi^0_2-complete." *Verdict:* keep.
31. **B. Poonen, "Undecidable problems: a sampler," arXiv:1204.0299.**
    - *Quote:* "Generalized Collatz problem. input: m ∈ Z>0, a0, …, am−1, b0, …, bm−1 ∈ Q … question:
      Is it true that for every n ∈ Z>0 there exists k such that f^k(n) = 1?"
    - *Verdict:* keep (states the scope precisely).
32. **M. Margenstern, "Frontier between decidability and undecidability: a survey," TCS 231 (2000)
    217–251.**
    - *Quote* [bib II, #69]: "small state Turing machines, which are so small they are not known to
      simulate a universal Turing machine." *Verdict:* open.
33. **P. Michel, "Problems in number theory from busy beaver competition," LMCS 11(4) (2015).**
    DOI 10.2168/LMCS-11(4:10)2015.
    - *Quote:* "mostly by simulating Collatz-like functions … These functions … lead to new unsolved
      problems."
    - *Note:* the small-modulus frontier is *open*, not undecidable. *Verdict:* open.
34. **bbchallenge wiki, "Antihydra."** https://wiki.bbchallenge.org/wiki/Antihydra
    - *Quote:* "whether repeatedly applying f(n) = ⌊3n/2⌋ + 2 will at some point produce more odd
      values of n than twice the number of even values … Does Antihydra run forever?"
    - *Verdict:* open.
35. **bbchallenge wiki, "Generalized Collatz Function."**
    - *Quote:* "Kascak proved in 1992 that there exists a Universal GCF with modulus 396."
    - The Kaščák primary (DOI 10.1007/3-540-55808-X_31) was not reachable. *Verdict:* keep.
36. **K. G. Monks, "3X+1 minus the +," DMTCS 5 (2002) 47–53.**
    - *Quote* [bib II, #76]: "a FRACTRAN program … such that the 3x + 1 Conjecture is true if and only
      if the R-orbit of 2^m contains 2."
    - *Note:* 3x+1 is one FRACTRAN program. Universality says nothing about this one. *Verdict:*
      open.
37. **M. Dhiman, R. Pandey, arXiv:2601.12772, v1 (Jan 2026) and v2 (Jun 2026).**
    - *Quote (v2):* "the arbitrary-step transition relation of the generalized Collatz map T_{q,d} is
      not first-order definable in Base-2 Büchi Arithmetic."
    - *Quote (v1):* "the non-existence of integer cycles cannot be proven solely through algebraic
      manipulation of the cycle equation itself."
    - *Note:* **the SURVEY entry describes v1. v2 retitles the paper and drops the ghost-cycle
      heuristic from the abstract.** The program's identities use exponentials, so they are not
      Presburger. *Verdict:* open (dup).
38. **E. Yolcu, S. Aaronson, M. Heule, "An automated approach to the Collatz conjecture," J. Autom.
    Reasoning (2023).** DOI 10.1007/s10817-022-09658-8.
    - *Quote:* "We prove that the termination of this rewriting system is equivalent to the Collatz
      conjecture … we find automated proofs of nontrivial weakenings."
    - *Verdict:* open.

### E. 2-adic and 3-adic universality

39. **E. Akin, "Why is the 3x+1 problem hard?," Contemp. Math. 356 (2004) 1–20.** DOI
    10.1090/conm/356/06495.
    - *Quote:* "The method is too general. It will work just as well if instead of using τ we
      define, for a any odd 2-adic, the map τa … With a = 5, for example, 13, 33, 83, 208, 104, 52,
      26, 13 and 1, 3, 8, 4, 2, 1 are disjoint cycles … a proof of the conjecture will have to
      provide an explanation of the essential role of the number 3 (as opposed to 5 say)."
      Exercise 4 adds: "µb ◦ τa = τa,b ◦ µb".
    - *Note:* establishes the brief's item 4. Every (ax+b)/2 with a, b odd is conjugate to the shift,
      and the conjugacy for b is multiplication by b. *Verdict:* **keep**.
40. **D. J. Bernstein, J. C. Lagarias, "The 3x+1 conjugacy map," Canad. J. Math. 48 (1996)
    1154–1169.** DOI 10.4153/CJM-1996-060-x.
    - *Quote:* "The results generalize to the ax + b map, where ab is odd … Thus T is Bernoulli."
    - *Verdict:* keep (dup in KNOWLEDGE_MAP).
41. **D. J. Bernstein, "A non-iterative 2-adic statement of the 3x+1 conjecture," PAMS 121 (1994)
    405–408.** DOI 10.2307/2160415.
    - *Quote* [bib I, #22]: "Φ(x) = −Σ_j 2^{dj}/3^{j+1} … Φ^{−1} ∘ T ∘ Φ = S."
    - *Note:* Φ of a periodic word is S/D, which is F1's rational cycle. *Verdict:* keep.
42. **M. C. Siegel, "The Collatz conjecture & non-archimedean spectral theory: Part I,"
    arXiv:2007.15936.**
    - *Quote:* "x ∈ Z\{0} is a periodic point of T_q if and only there is a z ∈ Z2\{0,1,2,…} so that
      χ_q(z) = x."
    - *Note:* this is F1 for all odd primes q. *Verdict:* open (low).
43. **E. Dejesus, "Transcendence of the 3x+1 conjugacy map on Sturmian words," SSRN (2026).** DOI
    10.2139/ssrn.7584439. Abstract fetched via Crossref.
    - *Quote:* "by the Bernstein-Lagarias isometry, the 2-adic approximation depth of a periodic
      shadow equals a longest common prefix … the shadow denominators 2^ℓ − 3^k are not S-units …
      machine-checked in Lean 4 with Mathlib, assuming only Ridout's theorem."
    - *Note:* this touches F2 and F5 directly. It concerns divergence (aperiodic Sturmian words), not
      cycles. It is unrefereed and only the abstract was read (via Crossref); listed as a round-2
      lead. *Verdict:* open.

### F. Quantitative cycle results (3x+1), re-read for map-specificity

44. **C. Hercher, "There are no Collatz m-cycles with m ≤ 91," JIS 26 (2023), arXiv:2201.00406.**
    - *Quote:* "Lemma 8 … n ≡ −1 (mod 2^k) … Lemma 9 … the Collatz sequences of ni and n′i :=
      (ni−1)/2 merge … Theorem 16 … δ < (K+L)/K … we arrive at a proven lower bound on K which is
      larger than the upper bound for this value of m given by Simons and de Weger."
    - *Note (brief item 5):* the 3x+1 specificity enters at three points:
      - Lemma 8: "+1" gives n ≡ −1 mod 2^k; for 3x+q it is n ≡ −q.
      - Lemma 9: merging with a smaller preimage, which feeds the minimal element ≥ N₀.
      - Positivity: δ < (K+L)/K, i.e. D > 0.

      The convergent and Simons–de Weger steps are map-uniform. *Verdict:* **keep** (dup).
45. **T. Tao, "Almost all orbits of the Collatz map attain almost bounded values," Forum Math. Pi 10
    (2022).**
    - *Quote:* "most odd numbers do not lie in a periodic Syracuse orbit, or more precisely that
      P(Syr^n(Ny) = Ny for some n) ≪ x^{−c}." Remark 1.15: entropy "4^{n+o(n)}" vs "3^n".
    - *Note:* on cycles it gives only a density statement. 3-adic mixing says nothing about D | S for
      a single word. The entropy count is over *all* words; at the critical slope the budget drops to
      1.04 nats (F5). *Verdict:* kill (for cycles; dup).
46. **T. Tao, "The Collatz conjecture, Littlewood–Offord theory, and powers of 2 and 3," blog
    (2011).**
    - *Quote:* "Thus we see that any proposed proof of the Collatz conjecture must either use
      transcendence theory, or introduce new techniques that are powerful enough to create
      exponential separation between powers of 2 and powers of 3." The heuristic count is
      "Σ_{a,k} (1/q) C(a−1, k−1)".
    - *Note:* **the key meta-statement**. Prop. 6 gives 2^a − 3^k ≫ k and Prop. 7 gives (1+ε)^k, both
      conditional on weak Collatz. It also says Littlewood–Offord "can be used to show that S is
      highly equidistributed in Z/qZ, but this does not directly give any way to prevent S from
      containing 0". That is the obstruction to equidistribution-style pigeonholes. *Verdict:*
      **keep** (dup, new extraction).
47. **J. C. Lagarias, "The 3x+1 problem: an overview," Ultimate Challenge (2010) 3–29,
    arXiv:2111.02635.**
    - *Quote:* "The 3x+k problem seems to be the correct level of generality for studying rational
      cycles … the methods generally apply to the 3x + k function as well … The 3x + 1 function
      might conceivably belong to a smaller class of generalized 3x + 1 functions that evade
      undecidability results."
    - *Verdict:* **keep**.
48. **J. C. Lagarias, "The 3x+1 problem and its generalizations," Amer. Math. Monthly 92 (1985)
    3–23.** HTML edition at cecm.sfu.ca.
    - *Quote:* "There is a cycle of period 1 starting from n = -1 … cycles of length 3 and 11
      starting from n = -5 and n = -17."
    - *Verdict:* keep (dup).
49. **T. P. Keller, "Finite cycles of certain periodically linear functions," Missouri J. Math. Sci.
    11 (1999).**
    - *Quote* [bib I, #94]: "if L ≥ s0(p) is the minimal period of a periodic orbit of gp, then L is
      a denominator of a convergent … g7 has an orbit of period 265 … and … 293."
    - *Note:* long cycles at convergents, in line with F2. *Verdict:* open.
50. **G. J. Wirsching, *The Dynamical System Generated by the 3n+1 Function*, LNM 1681 (1998).** DOI
    10.1007/BFb0095985.
    - *Quote* [bib I, #186]: "It studies the problem of showing that for each positive integer a ≢ 0
      (mod 3) a positive proportion of integers less than x iterate to a."
    - *Note:* predecessor counting, not cycles. *Verdict:* kill (for this program).

*(Entries 4 and 20 are discussed but have no JSONL line; each of the other 48 entries has exactly
one. JSONL: 48 lines, all `verified: true`, 14 tagged `dup`. Quotes marked [Lagarias bib] are the
reviewer's words, not the authors'.)*

---

## Leads for round 2

| paper | why |
|---|---|
| Belaga–Mignotte 2000, "Cyclic structure of dynamical systems associated with 3x+d extensions," HAL hal-00129656 (57 pp.) | the structural theorems behind the corona and duality picture; possibly statements on how G = gcd(A,B) distributes |
| Belaga–Mignotte 2006c, Table 2: factorizations of 2^ℓ − 3^k for ℓ ≤ 114 (Strasbourg preprint 2006-16/18) | direct data on which primes divide D; "Numbers D of this form give 3x + D problems having many primitive cycles". A ready-made dataset for G |
| Simons 2008, Acta Arith. 131, full text | exactly where p, q and the sign enter the m-cycle criteria; compare with the bounded-defect lever |
| Simons–de Weger v1.44 (2010) and Simons 2008a+ | the m ≤ 75 extension and its N₀ dependence |
| Lagarias 1990 full text (Table 3.1; the counting function C(k,y)) | the rigorous counting of rational cycles by period |
| Franco 1990 thesis (Beukers inequality, 2-odd-step cycles for all q) | a complete map-uniform Diophantine classification at o = 2, the cleanest model for a "p-uniform lever with exact output" |
| Kaščák 1992, MFCS, LNCS 629 | the minimal known universal modulus (396); is anything known below it? |
| Dejesus 2026 (SSRN 7584439) | the prefix-depth ↔ repetition mechanism (F5) made quantitative with a Lean proof; check whether it bounds G on Christoffel words |
| Matthews, "Generalized 3x+1 mappings: Markov chains and ergodic theory" (Ultimate Challenge ch. 4) | numbertheory.org PDF not reachable (TLS); the cycle-count conjecture for Conway maps |
| Chamberland, "A 3x+1 survey: number theory and dynamical systems" (Ultimate Challenge) | Lagarias cites it for "methods generally apply to the 3x + k function as well" |
| Halbeisen–Hungerbühler 1997, Acta Arith. 78 | optimal length bounds for *rational* cycles, i.e. uniform in k; the EXCLUDED_PATTERNS eudml id is wrong (207094 is Brindza–Pintér) |
| Tao 2011 blog, comment thread (offset > 100 000 characters) | possible remarks on 3x+k and 5x+1 versions of Props 6–7 |
