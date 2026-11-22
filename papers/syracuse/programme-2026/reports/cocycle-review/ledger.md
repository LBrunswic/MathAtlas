# Consolidation ledger: the cocycle program (2026-10-29)

**Closures since first draft** (2026-10-29/31):
- F1 G = gcd(S, D) and the k(w) dictionary: proved (`Limits`).
- F2 the fixed-slope sandwich bounds: proved (`Limits`).
- The Ellison exclusion: conditional (`Limits`).
- Knight C9: unconditional for coprime slope (`Christoffel`).
- The two-run family: excluded by a resultant ceiling (`TwoRun`, from a parallel session's new
  approach `places-elimination`).
- r ≥ 2 run parameters: conditional on Levin (`Vojta`).
- **F2 corrected** (arithmetic review). Two-run words 1^a 2^b reach the critical slope, so "every
  relevant word has unboundedly many runs" is false. They are now **excluded**, conditional on Ellison
  1971 (`TwoBackground.no_cycle_one_two`), via G = gcd(S, D) ⇒ D ∣ gcd(3^a − 2^a, 4^b − 3^b).
- Three or more backgrounds: Levin's gcd theorem (ineffective).
- **Two-block identity** for u^a v^b: D ∣ C(u,v)·D(u^a) and D ∣ C(u,v)·D(v^b) (`TwoBackground.dvd_of_cycle_block`). This is the first step of continued-fraction renormalisation (direction D4).

- **Balanced half closed** (direction D2, coprime slope): circularly balanced ⇒ Christoffel conjugate (Lothaire 2.1.15). So no nontrivial positive cycle has a balanced parity vector (`Balanced.no_balanced_cycle`).
- **Near-miss benchmark started** (direction D3): `NearMiss.lean`.

- **Two growing runs closed for every letter pair, and Steiner's theorem proved** (direction D1). No positive cycle on 1^a d^b (d ≥ 2), and `CycleLiterature.Steiner1977` (no nontrivial circuit), both conditional on Ellison 1971 (`Circuits.no_cycle_two_letters`, `Circuits.steiner_of_ellison`).

- **Balanced half closed for every gcd**, unconditionally (`BalancedPow.no_balanced_cycle_all`). The proof uses averaging, non-reduced mechanical words as powers, and Knight's C9 for powers.

- **Renormalisation, two runs at any Christoffel level** (direction D4): the wedge core of every standard pair is 6-smooth, so given Ellison there is no cycle (either sign) on u^a v^b for any standard pair (`StdPairs.no_cycle_std_pair`).

- **Frontier theorem** (`Frontier.frontier`): one statement of what a nontrivial positive cycle must look like, given Ellison + Barina. Barina also removes the small-E exceptions (E ≥ 45).
- **Level-(u,v) 2-cycles, comparable runs** (`TwoCycles.no_cycle_runs`): no cycle on u^{a₁}v u^{a₂}v with a₂ < a₁ ≤ 3a₂, given Ellison. Open: a₁ > 3a₂.

- **Re-bracketing closes the level-(u,v) 2-cycles**: u^{a₁}v u^{a₂}v = u^{a₁−a₂}(u^{a₂}v)², where (u, u^{a₂}v) is standard; equal runs go through power reduction (`Renormalize.no_pos_two_cycle`, `no_pos_cycle_std_pair_pow`). Open: three or more unequal runs at every level.

- **Near-standard pairs** (`NearStd.no_cycle_near_std`): a core of 6-smooth × c excludes u^a Z^b once c²·15^E ≤ 16^E. **Literature frontier** (`NearStd.frontier_lit`): o > 1.375·10^11 and at least 92 blocks, given Hercher.

- **Balanced cycles classified, both signs** (`BalancedClass.balanced_cycle_classification`): the only cycles with a balanced parity vector are 1, −1 and −5 → −7. No literature input.

- **Standard-pair two-run cycles classified, both signs** (`StdClass.std_pair_cycles`): given Ellison, only −5 → −7. The small exceptional E are settled by a kernel-checked Stern–Brocot enumeration, so no Barina is needed.

- **Closed classes on ℤ, both signs, Ellison only** (`SignedCycles.closed_classes`): balanced, at most one gap ≥ 2 (Steiner on ℤ: 1, −1, −5, −7), two letter runs (only −5 → −7; the negative case needs no window), powers of standard two-run words and level-(u,v) 2-cycles (Barina dropped). The −17 cycle lies outside every class (`neg_seventeen_outside`). Its two-block wedge core is −2³·3·139 with D = −139, so the certificate holds but carries no information.

- **D7 repeat lemma closed** (`Repeat`): a window repeated at two positions of a minimal cycle gives 2^o·2^{E(u)}·|D| < 2^E 3^o, unconditionally and for either sign. Given Ellison and Barina, a repeated window in a nontrivial positive cycle covers < 51.37 % of E and < 52.79 % of o. Narrow, as predicted: vacuous on generic words.

- **Simons 2-cycles with equal big gaps closed, both signs, Ellison only** (`EqualTwoCycles.equal_two_blocks`): only 1 and −5 → −7. Re-bracketing gives the pair (1, 1^m d) with core −2^{m+1}(2^{d−1} − 1); Ellison and the sign bound leave no window. Distinct big gaps (the −17 shape) stay open; that is Simons 2005's regime (Baker + LLL).

- **Two runs over the near-standard spine (1, 1^m d), every exponent** (`NearPairs.near_pair_cycles`): only −5 → −7; for b ≥ 3 Ellison alone. This closes the equal-big-gap words whose 1-runs are all equal but one longer one.
- **The {1, d} Christoffel trees** (`DPairs`): every core is 6-smooth × (2^{d−1} − 1). Two-run cycle words over a d-pair have E < 20(d − 1) given Ellison, and the **{1,3} tree is closed** by a kernel-checked enumeration (`dpair_three_cycles`). Residual regions for d = 4..7 are empty numerically; a uniform argument is open.

- **{1,d} trees, positive side closed for every d** (`DTrees.pos_dpair_cycles`, Ellison + Simons–de Weger 2005; only m ≤ 20 used). Negative side reduced to 3–7 equal big gaps with E < 20(d − 1) (`neg_dpair_residual`).
- **Negative cycles with ≤ 2 big gaps are known** (`NegTwoCycles.only_known_of_few_blocks`): −1, −5 → −7, −17, given Ellison + Simons 2007's sketched negative 2-cycle classification (stated as `Simons2007Neg`).
- **Literature cross-references added:** Mimuro 2001 and Luca 2005 (finiteness for two-letter runs and bounded ascents, by linear forms in logarithms) precede `Circuits`; the Lean versions are outright exclusions given Ellison.

- **{1,d} trees closed for 3 ≤ d ≤ 7, both signs** (`DTreeChecks.dpair_cycles_le_seven`): a sound exponent-bounded kernel check per d. The negative residual is open only for d ≥ 8.
- **Effective two-run rung for arbitrary blocks** (`Trees.no_cycle_tree`): over the tree from any root (u₀, v₀) with C(u₀,v₀) ≠ 0, two-run cycle words have E < 20 log₂|C(u₀,v₀)|, given Ellison. The two-run rung of the run-count hierarchy is now effective block by block. The open part is words with three or more runs at every level of every small-core tree.

- **Three runs, effective** (`ThreeRuns`): the three-core identity; three letter runs 1^a d^b e^c closed beyond E ≥ 11(d+e+2); **any three blocks** beyond E ≥ 20(K+2) given the three T's nonzero (`three_runs_bounded`, Ellison).
- **The method's limit, computed:** LP suprema 0.613 / 0.804 / 0.890 for 2 / 3 / 4 runs. Ellison's 0.8557 covers two and three runs and not four. A Rhin/Baker bound would reach every fixed m. Next ledger item: the m-run identity with `SimonsDeWegerLemma12` (Rhin), stated in `CycleLiterature`.

- **Four runs, effective with Rhin** (`FourRuns.four_runs_bounded`): any four blocks, positive cycles, given Simons–de Weger Lemma 12 and T's nonzero: E < 3500 + 16K. The m-run pattern of the core identity is visible; each fixed m is one finite check, but no proof is uniform in m.

- **The reach of the wedge cores, exactly:** c_m = 1 − (log₂3 − 1)/((log₂3)^m − 1) (LP, all patterns m ≤ 6; lower bound proved on paper). Ellison reaches m ≤ 3, Rhin each fixed m. The four-run failure under Ellison is realised on actual words (6^{a₀}(1^{20}2)^{a₁}(1^{21}2)^{a₂}(1^{22}2)^{a₃}, ratio 0.878).
- **Run frontier** (`RunsFrontier`): with Barina + Hercher Cor. 29, a nontrivial positive cycle with ≤ 4 runs needs block coefficients above ~2^{6·10^9} (~2^{5.7·10^9} with Barina alone, `BarinaFrontier`).

- **The exact reach, proved** (`Reach`): for every m, wedge-core certificates need a lower-bound exponent above c_m = 1 − 1/Σ_{i<m}λ^i, and this is sharp. With Ellison they reach exactly three runs (`ellison_reach`). This settles §7 item 2 for core-type certificates: a bounded family of cocycle moves certifies few-run words and provably no more.

- **m runs, end to end** (`MRuns`): the general m-block identity, D ∣ T on cycles, rotations, and the bound (θ − c_m)·max(E, o log₂3) ≤ K + L + log₂ m from any separation exponent θ. With Ellison: every m ≤ 3, any blocks, either sign (`mruns_ellison`). The method is now one theorem whose reach, `Reach`, is exact.

- **m ≤ 3, no nonvanishing hypothesis** (`MRunsExplicit`): the T's are nonzero by a 2-adic argument when runs are long. Given Ellison, any 2 or 3 runs of non-commuting base blocks (total weight B), each of weight above 6B+1, satisfy E < 20(6B+3.6). With Barina + Hercher, no nontrivial positive cycle has this shape when B ≤ 10^9.

- **≤ 3 runs, no side conditions** (`MRunsDichotomy`): T = 0 ⇒ an orbit point lies on a base block's cycle. Given Ellison: cycles on ≤ 3 runs of any blocks have such a point or bounded E. With Barina + Hercher: **no nontrivial positive cycle is a word of at most three runs over base blocks of total weight ≤ 10^9** (`frontier_le_three`).

- **Every m, with Rhin** (`MRunsRhin`): the all-m dichotomy for positive cycles. Frontier: no nontrivial positive cycle on ≤ 10 runs over base weight ≤ 5·10^7, nor on ≤ 20 runs over ≤ 6·10^5. The admissible weight decays like (log₂3)^{−m}, reaching nothing near 40 runs.

- **Every m, both signs** (`MRunsSigned`): Rhin's absolute linear-form bound (stated as `Rhin1987`, quoted by Rukhin 2018; numerically safe for E ≤ 2·10^5) gives a separation for every word, and with it the all-m dichotomy for negative cycles too.

- **PROGRAM.md §5 / §9.1, the first objective** (`ExplicitF`): an explicit f(w) for every m-run word, with no cycle assumed. Some rotation gives the rotation-ideal combination D'S − A·D = 2^{E}·T with |T| ≤ m·2^{6B+1}·2^{c_m·max(E, o log₂3)}. It lies below 3^o by 2^{−(1−c_m)·o·log₂3} up to the block term, and the exponent is sharp.

- **PROGRAM.md §9.4** (`Estimators`): S(w) is odd and prime to 3, so its 6-free part is S itself, and the AM–GM sandwich is already a two-sided estimate of it: n·3^{n−1}·G* ≤ sixfree(S) ≤ C·n·3^{n−1}·G*. On a cycle |x|·|D| = S.
- **Cycle words are C-balanced** (`Estimators.c_balanced`, `c_balanced_cycle`), previously derived: for windows of equal length ℓ ≤ o in a positive cycle, E(u) − E(u') ≤ 2·log₂(x_max/x_min) + (E − o·log₂3). The derivation's "+1" is the defect E − o·log₂3, which is below 1 only when 2^E < 2·3^o.

- **Cycle length from Barina alone** (`CycleLength.cycle_length_ge`): Eliahou's 1993 method with Barina's 2^71, fully proved. Certified log 2 / log 3 inequalities (series at 1/9 and 13/256) put E/o strictly between the Farey neighbours 103768467013/65470613321 and 10439860591/6586818670, so every nontrivial positive cycle has o ≥ 72 057 431 991 and E ≥ 114 208 327 604. The mediant itself is not excludable by this inequality; Hercher's Cor. 29 (o > 1.375·10^11) stays stated.
- **The run frontier without Hercher** (`BarinaFrontier`, `*_of` versions): ≤ 3 runs over base weight ≤ 9.5·10^8 (Ellison + Barina), ≤ 10 runs over ≤ 5·10^7 and ≤ 20 runs over ≤ 5.5·10^5 (Rhin + Barina). The Hercher versions are instances of the same general theorems.

- **Eliahou 1993, proved** (`Eliahou.eliahou1993`): the stated literature Prop is now a theorem with no literature input. Consecutive Farey neighbours (85137581, 53715833) < log₂3 < (17087915, 10781274) < log₂3 + 1/(3·2^40 ln 2) < (301994, 190537), certified with 30-digit logarithms, and unimodular cones. The same form at Barina's 2^71: (E, o) = a·(103768467013, 65470613321) + b·(114208327604, 72057431991) + c·(124648188195, 78644250661), b ≥ 1, ac = 0 (`eliahou_barina`).
- **Terras 1976, proved** (`Terras.terras`): the first k parities of the T-orbit depend only on n mod 2^k and determine it; residues ↔ parity vectors is a bijection. This is the arithmetic behind the 2-adic-blindness limit (§4 of the report).

The audit now covers 2,675 declarations.

The audit now covers 1,611 declarations across 18 files.

**Scope:**
- `PROGRAM.md`
- `approaches/cocycle-combine` (structure.md C1–C11, reports P0–P11)
- `approaches/bounded-defect-lever`
- `ideas/cocycle-combinatorics` (STRUCTURE, LOG, drafts)

**Lean names** refer to `~/Syracuse/lean/Syracuse/Approaches/*.lean`. The 2026-10-29 build passes the
axiom audit (1,438 declarations; no sorry, axiom or native_decide).

**Status vocabulary:**
- **proved:** Lean, unconditional.
- **cond:** Lean, proved assuming a stated Prop.
- **stated:** a Lean Prop, not proved.
- **cert:** certified by a Python check script.
- **num:** numerical observation.
- **refuted:** shown false.
- **open:** unresolved.
- **lit:** a verdict reached by reading literature.

**Scope tags:**
- **gen:** a generic ℤ[X,Y] identity. It holds for every Syracuse-type map: 3x+k, 5x+1, negative cycles.
- **23:** uses the (2,3) arithmetic.
- **sand:** the family is already excluded for positive 3x+1 cycles by the elementary ratio sandwich (§2
  below).

---

## 1. The dictionary that reorganises the program

**F1, the rotation ideal is (S, D):**

> For a nonempty positive word w, write G(w) := gcd_j S^{(j)}. Then G(w) = gcd(S(w), D(w)).

*Proof.*
- The rotation recursion (`Basic.rotation_recursion`) gives 2^{d₀}·S^{(1)} = 3·S^{(0)} + D.
- So g := gcd(S, D) divides 2^{d₀}·S^{(1)}.
- g is odd, because D is odd for E ≥ 1. Hence g divides S^{(1)}, and by induction every S^{(j)}.
- Conversely G divides S = S^{(0)} and G divides D (`Program.rotGcd_dvd_Dz`).

Lean: **proved** as `Limits.G_eq_gcd`. Also proved: `Limits.every_word_is_a_cycle`, `positive_cycle_iff_kOf_eq_one` (a positive 3x+1 cycle exists iff k(w) = 1), and `isSyrCycle_iff_isCycleK_neg_one` (the 3x−1 duality).

**Consequences:**
- **Two terms suffice.** The ℤ-span of all rotation sums is the ideal (S, D)·ℤ = G·ℤ. Every "move"
  produces an element αS + βD. The simplest representative over ℤ is G itself. The move calculus is
  therefore a calculus of *certificates that G is small*, i.e. explicit Bézout-type combinations.
- **Every word is a cycle of some 3x+k.** Put k(w) := D(w)/G(w). Every positive word with D > 0 is
  the gap word of a primitive positive integer cycle of x ↦ (3x + k)/2^{ν₂(3x+k)}, with elements
  S^{(j)}/G. This is Lagarias 1990, "rational cycles", in the program's language.
- **The no-cycle conjecture in this language** is "k(w) ≠ 1 for every primitive positive word other
  than (2)".
- **What the program is.** It is an upper-bound problem for gcd(S, D), the gcd of two S-unit
  expressions: S = Σ_k 2^{e_k}3^{o−1−k} is a sum of o S-units, and D = 2^E − 3^o.

## 2. The ratio sandwich retires every fixed-slope family

**The sandwich.** Write x_min for the smallest cycle element. A positive cycle satisfies
2^E/3^o = ∏_k(1 + 1/(3x_k)). Hence

> 1 < 2^E/3^o ≤ (1 + 1/(3x_min))^o, i.e. log₂3 < E/o ≤ log₂(3 + 1/x_min).

This is proved in `CycleLiterature.lean`, together with the product formula.

**Bounds on x_min:**
- Unconditionally, a nontrivial positive cycle has x_min ≥ 5 (the cycles through 1 and 3 are known),
  so E/o ≤ log₂3.2 ≈ 1.678.
- With verification up to N₀ (Barina 2025: below 2⁷¹, stated as a Prop in `CycleLiterature`),
  E/o − log₂3 ≤ log₂(1 + 1/(3N₀)) ≈ 2.0·10⁻²².

**Which families this retires.** A family whose words have a fixed rational limiting slope s ≠ log₂3
is excluded for positive cycles in two ways:
- If s < log₂3, then D < 0 eventually, so only negative cycles remain.
- If s > log₂3, the sandwich bounds the growing parameter.

| family | limiting slope | positive-cycle status |
|---|---|---|
| bounded-defect βd^L, d = 1 | 1 | D < 0 for L large (e.g. β = (2,3): D < 0 once L ≥ 4). Only negative cycles; −5→−7 = (1,2) is in the single-defect family |
| bounded-defect βd^L, d ≥ 2 | d ≥ 2 > 1.678 | L bounded by the unconditional sandwich (x_min ≥ 5) |
| periodic background u^pβ (F1), fixed u | avg(u) ∈ ℚ | retired. Unconditionally if avg(u) ≥ 1.678 or < log₂3; for 1.585 < avg(u) < 1.678 it needs N₀ |
| eventually periodic u^q v (cycle-gcd, P0) | avg(u) | same as F1. `finite_q` is a Baker-free version; the sandwich + N₀ already gives it |
| single defect d^a e d^b (P2) | d | same as bounded-defect |

**Verdict.**
- Every family the program has *excluded* is already excluded for positive cycles by elementary means.
  The program's exclusions add an o-independent *ceiling*, not new exclusions.
- The real exception is **negative cycles**, where the sandwich does not apply. There the levers are
  genuinely informative, and they are consistent with the three known negative cycles.
- A positive-cycle-relevant word has slope within ~10⁻²² of log₂3.
  - **Correction:** that does *not* force unboundedly many runs. Two runs 1^a 2^b with
    b/a ≈ (log₂3 − 1)/(2 − log₂3) reach it. That family is now excluded (conditional on Ellison;
    `TwoBackground`).
  - **What remains:** words with three or more growing runs, and the Sturmian-like words with
    unboundedly many runs. **Open problem 3 is the main problem, not a residue.**

Lean: **proved**. `Limits.one_background_bound` (d = 1: L + 3n < 2s, and D < 0 beyond), `steep_background_bound` (d ≥ 3: L ≤ n), `two_background_bound` (d = 2, nontrivial: L ≤ 3n), unified as `background_bound` (L ≤ 2|β| + 3·len β).

## 3. Thresholds (hand arithmetic at critical E = ⌈o·log₂3⌉)

**Ellison 1971:** |2^x − 3^y| > 2^x·e^{−x/10} for x > 27 (exceptional small x listed in
`CycleLiterature`). It applies from o = 18 at critical E. There it already gives |D| > 2.9·10⁷.

**Rhin / Simons–de Weger Lemma 12:** |D| > 0.00219·3^o/o^{13.3}. It exceeds 5 first at
**o = 56**. It overtakes Ellison only at **o = 574**.

ln|D| lower bounds at critical E:

| o | Ellison | Rhin | ln 3^o |
|---|---|---|---|
| 60 | 56.9 | 5.3 | 65.9 |
| 100 | 94.3 | 42.5 | 109.9 |
| 306 | 287.7 | 253.9 | 336.2 |
| 570 | 536.2 | 535.7 | 626.2 |
| 1000 | 940.1 | 1000.6 | 1098.6 |

**Consequences:**
- PROGRAM.md §3's "rigorous exclusion threshold o ≈ 60 for a constant ceiling" should read: **E > 27
  (o ≥ 18) by Ellison**, with smaller cases checked directly.
- The Lean-found regime restriction of Lemma 12 (δo < E < 1.000001δo) is irrelevant below o ≈ 574.
  Above that, E outside the regime makes |D| trivially large.

**Counting budget (heuristic).** At critical slope there are C(E−1, o−1) words of type (E, o), and a
"random" word satisfies D | S with probability about 1/|D| ≈ 1/(3^o·Λ).
- ln C(E−1, o−1)/o = 1.017 (o = 100), 1.039 (o = 1000), 1.043 (o = 10⁴), against ln 3 = 1.0986.
- So the expected number of cycles of length o is ≈ e^{−(0.056…0.08)·o}/Λ.
- A union-bound or pigeonhole argument has only **≈ 0.06 nats per letter** of room. Any covering
  argument must be nearly lossless.

## 4. Claim ledger

### PROGRAM.md

| § | claim | status | Lean | tags |
|---|---|---|---|---|
| 1 | G = gcd_j S^{(j)} = \|D\| on a cycle; G odd, prime to 3 | proved | `Program.rotGcd_cycle`, `rotGcd_odd`, `rotGcd_not_three_dvd` | 23 |
| 1 | floor: nonzero C in the rotation ideal ⇒ \|D\| ≤ sixfree(C) | proved | `Program.floor`, `floor_unit` | 23 |
| 2 | squeeze: lower bound B(o) + ceiling c < B(o) ⇒ no cycle | cond (`LowerBound`) | `Program.squeeze`, `no_cycle_of_ceiling_lt` | 23 |
| 3 | Rhin: \|D\| > 0.00219·3^o/o^{13.3} | stated; **corrected** (needs 2^E > 3^o; constant 0.0021862; the paper proves it only for δo < E < 1.000001δo) | `RhinBound`, `SdWLemma12`, `abs_two_pow_sub_three_pow_ge` | 23 |
| 3 | threshold o ≈ 60 for c = 5 | **superseded** (§3: E > 27 via Ellison); cond on `Ellison1971` | `Limits.no_cycle_of_ellison_ge` | 23 |
| 4 | frame strip, prefix | proved | `BoundedDefectLever.frame_strip_prefix` | gen |
| 4 | frame strip, suffix "Y^{\|z\|}" | **corrected**: Y^{len z} | `frame_strip_suffix` | gen |
| 4 | anchor split | proved (len u = len v) | `anchor_split` | gen |
| 4 | anchored free basis | proved for one anchor; **corrected**: grouped anchors miss cross-group differences | `diffIdeal_eq_anchored` | 23 |
| 4 | combination round finds "the simplest representative" | over ℤ the simplest is G itself (F1); not formalized | — | — |
| 5 | rep < 3^o ⇔ critical | proved, as a **characterisation** (it is not progress) | `Program.small_rep_iff_critical` | 23 |
| 5 | explicit f(w) < 3^o for critical words | **proved for m-run words**: f(w) = m·2^{6B+1}·2^{c_m·max(E, o log₂3)}, below 3^o by 2^{−(1−c_m)λo} up to the block term; exponent c_m sharp (`Reach.reach_tight`). Open for words with many runs (c_m → 1) | `ExplicitF.explicit_f`, `exists_small_T` | 23 |
| 6 | Layer-1 algebra closed (binomial Alexander polynomial) | lit (McMullen, Boden–Friedl verdicts) | — | gen |
| 6 | bounded-defect ceiling G ≤ sixfree(S(βd) − S(dβ)) | proved | `BoundedDefectLever.ceiling` | 23, **sand** |
| 7 | AM–GM estimator G* ≤ A ≤ C·G* | proved | `Program.amgm_sandwich` | 23 |
| 9.1 | explicit f(w) | **proved for m-run words** (see §5 row) | `ExplicitF.explicit_f` | 23 |
| 9.2 | covering / pigeonhole | open (see words review) | — | — |
| 9.3 | ≥ 2 growing runs no-go | **reframed**: the two-run family d^a e₁ d^a e₂ d^a is excluded by a resultant ceiling (`TwoRun.lean`, approach `places-elimination`), and "no unit scheme" was the wrong question. For r ≥ 2 independent run parameters: cond on Levin (`Vojta.lean`), now **effective**: m runs of any blocks are bounded given Ellison (m ≤ 3) or Rhin (every m), with exact reach c_m (`MRuns`, `MRunsDichotomy`, `MRunsRhin`, `MRunsSigned`, `Reach`). `TwoRunNoGo` itself stays stated | `TwoRun.*`, `Vojta.*`, `MRuns*`, `Reach` | 23, **sand** (integer slope) |
| 9.4 | normalise the abelian estimator | **resolved**: S(w) is odd and prime to 3, so sixfree(S) = S and n·3^{n−1}·G* ≤ S ≤ C·n·3^{n−1}·G*; on a cycle \|x\|·\|D\| = S | `Estimators.abelian_estimate`, `sixFree_Sz`, `cycle_abelian` | 23 |

### cocycle-combine (structure.md and reports)

| item | status | Lean | tags |
|---|---|---|---|
| C1–C11 (transfer matrix, conjugation, σ cocycle, coboundary, wedge, Plücker, Knight edge identities, Hankel rank 2, charpoly) | proved | `CocycleCombine.*` (`plucker`, `charpoly_Mw`, …) | gen |
| compensation principle | proved | `Dz_dvd_comb`, `abs_Dz_le` | 23 |
| Knight (C9), high cycle excluded | **proved** for coprime (o, E): upper and lower Christoffel words share the middle and are conjugate | `Christoffel.no_high_cycle`, `christoffel_shape`, `lower_isRotated_upper` | 23 |
| P0 telescoping u^q v | proved | `CycleGcd.telescoping`, `finite_q` | gen / 23, **sand** |
| P1 circuit (X^d − Y)·S = D | proved | `P1` | gen |
| P2 single defect, ceiling 2^{\|e−d\|} − 1 | proved; identity form **corrected** | `P2_adjacent`, `P2_ceiling` | 23, **sand** |
| P9 "q = 2 forces s₁ = s₂" | **refuted** (escape at (6,11)) | `P9_escape` | 23 |
| P10 "3-power G cannot strip" | **refuted** (gcd(G, 6) = 1) | `isCoprime_rotGcd_six` | 23 |
| P11 increment identities | proved; the uncovered word is the −17 cycle | `P11_*`, `P11_uncovered` | gen |

### bounded-defect lever and incubator

| item | status | Lean / check | tags |
|---|---|---|---|
| shared-frame extraction | proved (needs equal length and equal sum) | `S_frame_sub`, `S_frame_sub_general` | gen |
| [P1] inner-core extraction | proved | `inner_core*` | gen |
| Move 1 (repeated block) | proved (prefix strip) | `frame_strip_prefix` | gen |
| literal Move 2 (balanced swap) | refuted | `checks/move_checks.py` | — |
| [P2] full-rotation combinations ≥ G | proved | `Program.floor` | 23 |
| [P3] bounded-defect lever | proved | `ceiling`, `wedge` | 23, **sand** |
| F1 periodic background u^pβ | proved | `wedge_block`, `ceiling_block` | 23, **sand** |
| ceiling atlas (5, 65, 1103, 127; collapse iff \|e−d\| ∈ {1,2}) | proved (d = 1) | `ceiling_atlas_*`, `single_defect_collapse` | 23 |
| multi-anchor identity | proved | `multi_anchor` | gen |
| [P4] two-ended lever | refuted (diverges) | `checks/two_ended_lever.py` | — |
| reversal lattice | refuted (rank gap) | `checks/reversal_lattice_*.py` | — |
| F2/F3 (two runs, aligned anchors) | num: ceilings diverge | `checks/covering_reductions.py` | — |
| ≥ 2-growing-gap no-go (non-cyclotomic factor of degree → ∞) | reduced-but-open | `checks/multigap_nogo.py`; `TwoRunNoGo` | — |
| Layer-1 closure: R1, R3, R4, L1·8, L1·9, R2 | lit, null | drafts/lit-*.md | gen |
| covering Part 2 (pigeonhole / unavoidability) | open | — | — |
| covering Part 3 (balanced ⇒ pigeonhole, heavy ⇒ P3) | sketch; the junction is the wall | — | — |

## 5. Corrections that touch the program

All were found by the Lean formalization; details are in `lean/FINDINGS.md`.

**PROGRAM.md:**
1. Suffix strip factor is Y^{len z}.
2. §3's step |D| > 3^o·Λ needs 2^E > 3^o.
3. 0.00219 is rounded up from 0.0021862.
4. Lemma 12 is proved only in the Lemma 8 regime.
5. Grouped anchors lose cross-group differences.
6. The o ≈ 60 threshold is superseded by Ellison (§3).

**cocycle-combine:**
7. P9 "q = 2 forces s₁ = s₂" is false.
8. G is always coprime to 6, so P10's argument is invalid and P2 did not need the last pair.
9. The P2 identity is X^{(o−2)d}(X^e − X^d) in general.
10. structure.md §1 has a sign error.
11. C3's inverse form needs X and Y invertible.
12. C9's g = S needs a parity vector starting with 1.

**bounded-defect lever:**
13. "Only the trivial circuit" is true for positive cycles only (−5 → −7 lies in the family).
14. The atlas values need d = 1.

## 6. Incubator inconsistencies

- The drafts quote Ellison (2.56^o) while the tool audit (LOG "Tooling") computes the threshold from
  Rhin only. Resolved in §3.
- `LEVERAGE-ROADMAP-L1.md` L1·4 is still "queued" under the wrong arXiv id 1009.0381. It was done as
  R4 with 1011.0558.
- In `STRUCTURE.md` §4, the R2 row is unticked, although §5 and the roadmap declare R2 closed.
- In `covering-reductions.md`, "positive density" is the wrong target. Non-existence needs *every*
  cycle-relevant word covered, i.e. every word of slope log₂3 ± 10⁻²² (§2).

## 7. What is genuinely open after consolidation

1. **Bound gcd(S(w), D(w)) for near-critical words.** These are Sturmian-like words with unboundedly
   many runs. This is the whole problem (§1–§2).
2. **Certificates.** Can a *bounded number of cocycle moves* certify that G(w) is a proper divisor of
   D(w) for every such word? In the Bézout reading, can one exhibit small α, β with αS + βD small?
3. **Effectivity.** Any exclusion must beat the N₀-derived lower bound on cycle length (o > ~10¹¹,
   Hercher). Equivalently, it must give o₀ below that bound, or a uniform argument.
4. **What (2,3)-specific input is used,** and where. Generic steps cannot distinguish 3x+1 from
   3x+k or 5x+1 (`Limits`, Phase D).
