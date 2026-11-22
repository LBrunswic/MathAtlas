# Findings from the formalization

These are claims in the notes that the formalization found false, imprecise or stronger than
stated. In each case the corrected statement is the one proved in Lean, and the Lean name is
given. The notes themselves have not been edited.

## cycle-literature (`Approaches/CycleLiterature.lean`)

These were checked against primary sources where they were reachable.

- **Rhin / Simons–de Weger Lemma 12 constant.** The SURVEY's "C ≈ 0.46" is wrong. The statement
  is `Λ > exp(−13.3·(0.46057 + log K))`, so 0.46057 sits inside the exponent, and the
  multiplicative constant is ≈ 0.00219. `PROGRAM.md` §3 already has the right form.
- **Barina 2021** verified below 2^68, not 1.5·2^70. **Barina 2025** is a strict bound (< 2^71).
- **Hercher Thm 16** is not "verbatim" the `log₂(3 + 1/n_min)` form; that form is Sinisalo's.
  Hercher's verification bound is 695·2^60 in the journal version and 704·2^60 on arXiv.
- **Simons–de Weger.** The published paper excludes m ≤ 68 and v1.44 excludes m ≤ 75.
  `EXCLUDED_PATTERNS.md` says m ≤ 74, which matches neither.
- **de Weger's `2^{−0.158·o}` bound** could not be located in the published paper or in v1.44;
  it is unverified.
- **"Cycle iff D ∣ S with quotient > 1"** needs a positive word, and `D ∣ S` alone already
  gives a cycle (`isSyrCycle_of_dvd`, `exists_cycle_iff_dvd`). "D odd" needs E ≥ 1.
- **"3x−1 has three cycles":** only their existence is proved. That there are exactly three is
  open.
- **Width of the critical band:** ≈ 2.0·10⁻²², not ~10⁻²¹.
- **Ellison's bound** is in exposé 12 ("On a theorem of S. S. Pillai"). It has the exceptional
  set {1–11, 13, 14, 16, 19, 27}.

## punctured-torus (`Approaches/PuncturedTorus.lean`)

- **Property P "for every class"** is false for the class `b` (o = 0). There `S/D = 0/1` is an
  integer, but `b` is not a cycle (`b_fixed_point`). Property P holds for positive words with
  o ≥ 1 (`propertyP`).
- **"τ is a crossed homomorphism for whichever linear part L"** (spacetime-description §1) is
  false. The cocycle law at (a, a) forces L(a) to fix ∞ (`tau_cocycle_forces_borel`), which
  agrees with SYNTHESIS §2's dichotomy.
- **"Attracting fixed point x₀ = S/D"** holds only when D > 0. For the cycle −1, x₀ is repelling
  (`fixed_point_repelling_neg_one`).
- **ℓ(aab)** is log(9/8), not log(8/9) (markoff-coordinates §5).
- **"D = Lorentzian interval in null coordinates"** is imprecise. The exact statement is
  q(x⁰) = D²/4, so x⁰ is null exactly when D = 0.
- **Sharpening:** the "−2 unreachable" observation becomes tr[P,Q] ≥ 95/48 for every real pair
  with the Syracuse traces (`trace_commutator_ge`).

## diophantine-distribution (`Approaches/DiophantineDistribution.lean`)

- **"D odd ⇒ x* ∈ ℤ₂"** needs E ≥ 1, because E = 0 gives D = 1 − 3^o, which is even.
- **"Integer cycle iff D ∣ S and parities consistent":** for positive words the parity condition
  is automatic (`exists_cycle_iff`).
- **"S is injective"** (RATIONALE) is false: S(1) = S(2) = 1 and Z(1) = Z(1,1) = −1. S is
  injective among positive words with the same (E, o) (`eq_of_Sz_eq`). Z(u) = Z(v) iff u and v
  are powers of a common word (`xstar_eq_iff_common_root`).
- **"Every positive integer has finite flying time"** is false as stated. 1, 2, 3 and 4 return
  to 4 forever under the full map (`not_finiteFlyingTime_le_four`). The correct hypothesis is
  x ≥ 5 for the full map, or odd x ≥ 3 for the Syracuse map. With that hypothesis the
  reduction is an *equivalence* with the Collatz conjecture
  (`collatzConjecture_iff_finiteFlyingTime`).
- **RATIONALE regime 3** needs ε > log₂(7/6), i.e. β > 7/2; that is the form `fundamental.md`
  uses.

## cocycle-control (`Approaches/CocycleControl.lean`)

- **Now a theorem (was "numeric, not yet proved"):** 1 ≤ S(w) ≤ 3^E − 2^E for nonempty positive
  words with |w| = E (`Sn_range`, `Sz_range`). The minimum is reached exactly by one-letter
  words and the maximum only by 1^E.
- **New: the band at fixed (E, o).**
  3^o − 2^o ≤ S ≤ 3^{o−1} + 2^{E−o+1}(3^{o−1} − 2^{o−1}). Both edges are reached and both
  strictly increase with o (`Sn_band`).
- **New: monotone moves.** Moving one unit of gap to an earlier letter strictly increases S
  (`Sn_transfer_lt`). S is monotone in the prefix sums, compared position by position
  (`Sn_le_of_e_le`).
- **"Length dominates magnitude"** is not a strict separation: at E = 20,
  S(19,1) = 524291 > 19 = S(1,1,18) (`length_not_dominant`). Only the band edges are monotone
  in o.

## diophantine and cycle-gcd (`Approaches/Diophantine.lean`, `Approaches/CycleGcd.lean`)

- **The critical-band claim is false in general.** The abstract of `eventually-periodic.tex`
  and the proof of its Thm 2.13 put every positive cycle in the band 3^o < 2^E < 3^{o+1}. The
  trivial cycle traversed 4 times, word (2,2,2,2), has 2^8 = 256 > 243 = 3^5
  (`positive_cycle_not_in_band`). For primitive cycles with C ≠ 0 the claim is unproven rather
  than refuted. The exclusion does not need it: a positive cycle has E ≤ 2o, so `band_exclusion`
  holds (conditionally on the Matveev Prop) with no band hypothesis. "E pinned to ≤ 2 values"
  holds only once band membership is assumed (`InBand.E_eq`).
- **`2^E < 4^o` should be `2^E ≤ 4^o`** for positive cycles; equality holds for 1 → 1.
- **Typo in STATUS.md:** `(2,2,2) = 3×(2,1)` should read `3×(2)`.
- **The Matveev bound in periodic-words §5.2** (`|D| ≥ 2^E e^{−c log E}`) leaves c unspecified.
  The tex Prop 2.8 form is the one formalized (`MatveevTwoThree`), and its hypotheses
  E, o ≥ 2 are not needed.
- **"No hypothesis on u, q, v"** still relies on every gap being ≥ 1 (so that D is odd) and on
  q ≥ 1.
- **Unconditional finiteness:** `finite_q` gives finitely many q per (u, v) unless C = 0,
  without Matveev. Matveev is needed only for the explicit bound `q < Qbound` (proved
  conditionally on the stated Prop).
- **The (9,5) witness is verified:** the rotation sums are 431/781/653/557/485, and
  min = 431 > D = 269 (`decide`).

## cocycle-combine (`Approaches/CocycleCombine.lean`)

- **P9: "q = 2 always forces s₁ = s₂" is false.** At (o, E) = (6, 11) the balanced blocks
  u₁ = (1,1,3,2,1,3) and u₂ = (5,1,1,1,1,2) have s₁ = 1441 ≠ s₂ = 6995, yet
  2^11 + 3^6 = 2777 divides s₂ − s₁ = 5554 (`P9_escape`). The note's search stopped at (5, 9).
  A Python sweep found 912 such escapes.
- **"G may share factors of 3"** (P2, P4, P10) is false. G ∣ D, and gcd(D, 6) = 1 whenever
  o, E ≥ 1 (`isCoprime_rotGcd_six`). So Y-powers can always be stripped as well, P2 did not need
  to use the *last* rotation pair, and P10's "a 3-power odd G can't strip" argument is invalid
  as stated. Its conclusion would need a different justification.
- **P2 identity:** `X^{(o−1)d}(X^{e−d} − 1)` is a polynomial identity only for e ≥ d. The general
  form is `X^{(o−2)d}(X^e − X^d)` (`P2_adjacent`, `P2_last`). The ceiling `P2_ceiling` holds for
  all a, b.
- **structure.md §1 sign:** `D = λ₁ − λ₂` with `λ₁ = Y^o` is −D. The C11 paragraph has it right.
- **C3, inverse form:** this needs both X and Y invertible (det M(w) = X^E·Y^o), i.e. the target
  is GL₂(R[X⁻¹, Y⁻¹]), not GL₂(R[Y⁻¹]).
- **C9:** "g = S of the cyclic gap word" holds only for parity vectors that start with 1. In
  general g(0^k v) = X^k·g(v). The Knight argument is proved on genuine cycles
  (`knight_cycle`). Its one assumption is that 1u0 and 0u1 are rotations of the cycle's parity
  vector (Cohn's theorem, not formalized).
- **P3:** "(uv)^q with q ≥ 2 is never a cycle word" holds only at the minimal period. For
  example, `IsSyrCycle (-5) 4` has gap word (1,2)².
- **Notation:** in S^{|w|} (P0) and R^{|x|} (P10), |·| counts letters, not the gap sum. In P2,
  S^{(i)} means S(ρᵢ), not S(τ.rotate i).
- **The uncovered P11 word (1,1,1,2,1,1,4)** is the gap word of the genuine −17 cycle, with
  G = 139 (proved).

## parity-manipulation and zero-sum-combination (`Approaches/ParityManipulation.lean`, `Approaches/ZeroSumCombination.lean`)

- **"Bijection (b_n) ↔ ℤ₂" and "T : ℤ₂^× → ℤ₂^×"** are false as stated. T is undefined at −1/3,
  where 3x+1 = 0. The reconstruction map is injective (`x0_injective`). Its image is the set of
  odd x whose T-orbit never meets −1/3 (`range_x0`). The corrected bijection is `parityEquiv`.
  −1/3 and 2 are not in the image.
- **Finite-support no-go:** true as the note states it. But its hypothesis ("δ vanishes for
  k ≥ N") excludes the single-block shift itself, where δ = a·1_{k>q} never vanishes. The sharp
  hypothesis is "δ is constant on [N, ∞)", and under it x'_N = x_N exactly (`traj_eq_iff`).
- **"The shift family enumerates the depth-(q+1) predecessors"** is false. It reaches only
  predecessors that share the first q gaps. Counterexample: 13 → 5 → 1 has gaps (3,4), while
  every q = 1 shift of 1 keeps the first gap 2.
- **Integrality theorem:** the note's hypotheses are right. With x₀ ∈ ℤ, 3 ∤ x_{q+1} holds
  automatically (`integrality_padic`). The even case of the lifting-the-exponent lemma needs
  a ≠ 0.
- **"D = 2^E − 3^o is coprime to 6"** needs E ≥ 1 and o ≥ 1: D([0]) = −2 and D([]) = 0.
- **"The minimal generating set is the p−1 consecutive differences":** over ℤ the ideal Z is
  principal, so one generator suffices. p − 1 is the rank of the coefficient lattice A_{p−1}.
- **Proved:** ℤ[1/6] is a PID, Euclidean with φ = sixFree, with units exactly ±2^a3^b.

## bounded-defect-lever and PROGRAM.md (`Approaches/BoundedDefectLever.lean`, `Approaches/Program.lean`)

- **PROGRAM.md §4, suffix strip:** the factor is Y^{len z}, not Y^{|z|}. With u = (1,2),
  v = (2,1), z = (3) the difference is −6, not −54.
- **PROGRAM.md §3, from Λ to |2^E − 3^o|:** the boxed step holds only when 2^E > 3^o. The valid
  bound is |2^E − 3^o| ≥ 3^o(1 − e^{−Λ}). Also e^{−13.3·0.46057} ≈ 0.0021862, so the quoted
  0.00219 is rounded up.
- **Scope of Lemma 12:** Simons–de Weger prove it only inside their Lemma 8 regime
  δo < E < 1.000001δo, but PROGRAM.md applies it to all (E, o). Both forms are stated as Props:
  `RhinBound`, the unrestricted form PROGRAM.md uses, and `SdWLemma12`, the paper's scope. The
  squeeze is proved conditionally on a generic `LowerBound` hypothesis.
- **Grouped anchors (§4):** anchoring each group separately gives rank o − #groups and does not
  generate the cross-group differences unless anchor-to-anchor differences are added. A single
  anchor does generate everything (`diffIdeal_eq_anchored`).
- **Shared-frame extraction** needs both equal gap sum and equal length; each alone fails (Lean
  examples). If the lengths differ, there is a second correction term
  (Y^{len M+len Q} − Y^{len M'+len Q})·S(P) (`S_frame_sub_general`).
- **"Only the trivial circuit" in the single-defect atlas** is true for positive cycles
  (`no_positive_cycle_single_defect`). The negative cycle −5 → −7 (word (1,2)) lies in the
  ceiling-1 family with |D| = 1.
- **Atlas values 65, 1103 and 127** omit the background letter d; d = 1 reproduces all four
  values.
- **Proved:** the wedge exponents, which the note had right; the o-independent ceiling
  |2^E − 3^o| ≤ sixFree(S(βd) − S(dβ)); and §5, where a nonzero representative with
  |C| < 3^o is *equivalent* to criticality (`small_rep_iff_critical`). This confirms the
  note's own "characterisation, not proof" caveat. The AM–GM sandwich of §7 is also proved.

## circulant_matrix (`Approaches/CirculantMatrix.lean`)

- **Identity A, cosine form, is false for even o.** The ℓ = o/2 factor ends up squared: at
  (E, o) = (4, 2), |D| = 7 but the formula gives 49 (`identityA_cos_false`). The corrected form
  D² = ∏_{ℓ<o}(9 − 6β cos(2πℓ/o) + β²) is proved (`identityA_cos`). The modulus form
  |D| = ∏|3 − βω^ℓ| is correct (`identityA`).
- **STATUS: "v_p(S^{(j)}) is independent of j" is false.** For w = (1,3,1,3), D = 175 = 5²·7,
  and the rotation sums are 125, 275, 125, 275, so v₅ = 3, 2, 3, 2
  (`vp_not_rotation_invariant`). Only min(v_p(S^{(j)}), v_p(D)), i.e. gcd(S^{(j)}, D), is
  rotation-invariant, and that is what is proved (`gcd_S_rotate`).
- **The root-of-unity product needs an integral domain, not "any ring":** in ℤ/8ℤ, ζ = 3 is a
  primitive square root of 1, but (0−1)(0−3) = 3 ≠ 7 = 0² − 1².
- **Implicit side conditions:** the determinant formula needs o ≥ 1 (the empty word gives 1,
  not −1). The δ/gcd results need E ≥ 1, so that D is odd.
- **Proved in full:**
  - det M = (−1)^{o+1} D^{o−1} as an identity in any commutative ring (`det_Mrot`). The
    notes' 13⁴ check is reproduced.
  - The real form M = Δ⁻¹CΔ and the complex spectrum ĉ_ℓ = D/(βω^ℓ − 3).
  - The circuit factorisation D = ∏_{m<g}(2^a − 3^b ζ^m).
  - The norm identities N(x̂ − 3) = (−1)^{o+1}D and N(ĉ₀) = det M, in the étale algebra
    ℚ[x]/(x^o − 2^E).
  - The trace identity 2^{e_j}S^{(j)} = Tr(γ_W x̂^j ĉ₀).
  - The gcd law gcd_j S^{(j)} = |D| / lcm δ_j.

## polynomial-root (`Approaches/PolynomialRoot.lean`)

- **Prop 2.4 / Lehmer:** the printed factor t¹⁰ − t⁹ + t⁷ − … − t + 1 is L(−t), where L is
  Lehmer's polynomial. Lehmer's polynomial itself does **not** divide P_w (`lehmer_not_dvd`:
  evaluating at 2 gives 1291 ∤ 76073). The proved factorisation is P_w = Φ₇·L(−t). The Mahler
  measure is unaffected, since negating the roots does not change it, so "Lehmer's number is
  realised" stands.
- **Plastic word:** the factor t³ − t² + 1 is neither x³ − x − 1 nor its reciprocal. It equals
  x³ − x − 1 under t = −1/x (`plastic_factor_rel`).
- **Rem 1.10** ("at (X,Y) = (2,3), S(w)/(χ(w)−1) is the fixed point") is false. For `uv`, the
  {1,2} cycle, the ratio is 1/5, not 1 (`remark_1_10_counterexample`). The correct statement is
  fixed point = ½·S(wᴿ)/(1−χ(w)) at (X,Y) = (3/2, 1/2) (`tWord_fixed`).
- **The dictionary to the gap-word S** is not "swap X↔Y plus reversal" (as RATIONALE and
  `gen_table.py` say). The exact relation is
  S_Basic(A,B; w) = B^{o−1}·S(A/B, A; L) = A^{E−1}·S(B/A, 1/A; Lᴿ), where
  L = u v^{d₀−1} ⋯ u v^{d_{o−1}−1} (`S_eq_foxSP`, `S_eq_foxSP_reverse`).
- **Proved:**
  - Crowell–Fox, the cocycle law, and conjugacy invariance mod (1−χ(w)).
  - The coprime reparametrisation as an actual ring isomorphism (`reparamIso`).
  - The algebraic half of Thm 3.3: R is a gcd of S̄ and T̄, with R(1) = 1 (`core_gcd`).
  - The cohomological half (Alexander polynomial) is stated only, as `AlexanderClaim`.

## places-elimination (`Approaches/TwoRun.lean`, `Approaches/Vojta.lean`)

- **`TwoRunNoGo` asks the wrong question for exclusion.** It states that `d^a e₁ d^a e₂ d^a` has no
  *unit* scheme, i.e. no signed-monomial combination of rotation sums equal to a monomial times a
  fixed polynomial. That may still be true. But a certificate whose coefficients are polynomial in the
  run coordinates `u = Y^a`, `v = X^{da}` exists for every triple. Its core is
  `R* = Q₁²(P−Q₂)³ + Y·Q₂·(P−Q₁)³`, which is nonzero at `(2,3)` unless `e₁ = e₂ = d`, so the family is
  excluded (`TwoRun.twoRun_ceiling`, `TwoRun.noCycle_of_check`). The bounded-defect-lever STATUS line
  "the ≥2-growing-gap no-go boundary is reduced-but-open" is therefore about the unit-scheme class,
  not about cycles in that family.
- **The "≥ 2 growing gaps" obstruction is a dimension count.** Consider families with two different
  block slopes, or two independent lengths. The elimination ideal of `(D, S)` in the torus is zero
  (`approaches/places-elimination/elim.py`). So no polynomial core exists at all, unit or not, and the
  regime is Vojta/Levin (`Vojta.cycles_of_levin`).
- **`PROGRAM.md` §3: "|2^E − 3^o| ≥ 3^{o(1−ε)} is unproven".** I believe this is known ineffectively
  from Ridout's theorem. Flagged for verification and not formalized; the notes were not edited.

## limits (`Approaches/Limits.lean`)

What the cocycle data `(S^{(j)}, D)` can and cannot see. All items below are proved, except the
last bullet, which is conditional on the stated Ellison Prop.

- **F1, `G` is a two-term gcd.** For every nonempty word with `E ≥ 1`,
  `gcd_j S^{(j)} = gcd(S, D)` (`G_eq_gcd`, from `CirculantMatrix.gcd_S_rotate`). The `o` rotation
  sums carry no more gcd information than the single pair `(S, D)`.
- **Every positive word is a cycle of some `3x + k` map.** For a nonempty positive word `w`, put
  `k(w) = D/gcd(S, D)` and `a(w) = S/gcd(S, D)`. Then `a(w) > 0` is odd, `k(w)` is odd, `D a = k S`,
  and `a(w)` is a cycle point of the accelerated map `a ↦ (3a + k)/2^{ν₂(3a+k)}` with gap word exactly
  `w` (`every_word_is_a_cycle`; `k > 0 ⟺ D > 0`). Examples: `(1,4)` is the `3x + 23` cycle
  `5 → 19 → 5` (`word14_data`), and the `−17` word has `(G, k, a) = (139, −1, 17)`, the `3x − 1`
  cycle through `17` (`neg17_word_data`).
- **The `3x + 1` cycles are the words with `k(w) = 1`.** A positive word is the gap word of a
  positive `3x + 1` cycle iff `k(w) = 1`, i.e. iff `D > 0 ∧ D ∣ S`
  (`positive_cycle_iff_kOf_eq_one`, `kOf_eq_one_iff`). It is the gap word of a `3x + 1` cycle of
  either sign iff `|k(w)| = 1` (`exists_cycle_iff_natAbs_kOf`).
- **`3x − 1` duality.** `syrK (−k) (−a) = −syrK k a`, with the same gap word, so `a ↦ −a` maps
  `3x + 1` cycles to `3x − 1` cycles (`isSyrCycle_iff_isCycleK_neg_one`, `three_x_minus_one_cycles`).
- **Witnesses from other maps.** The `5x + 1` cycles `1 → 3 → 1` `(1,4)`, `13 → 33 → 83 → 13`
  `(1,1,5)` and `17 → 43 → 27 → 17` `(1,3,3)` are closed orbits at `(X, Y) = (2, 5)` with
  `D = 7, 3, 3 > 0`. The floor `D ∣ S^{(j)}` holds on them verbatim (`five_cycles_floor`,
  `floor_two_five`). The negative `3x + 1` cycles `−1, −5, −17` have `D = −1, −1, −139`
  (`negative_cycles_D`). Note that at `(2, 5)`, `D` need not be prime to `3` (`D = 3` above).
- **Sign-blindness.** `Program.floor` applies unchanged to the `−17` cycle: every nonzero
  combination `C` has `139 ∣ sixFree C` and `139 ≤ sixFree C` (`floor_neg17`). The bounded-defect
  ceiling of its word `(2,1,1,4)·1³` has core `565 − 287 = 278 = 2·139`, so the ceiling is exactly
  `139 = |D|` (`ceiling_neg17`). The ceiling is tight and cannot exclude a word that carries a genuine
  cycle of the other sign.
- **F2, fixed-slope families.** For a positive cycle with cyclic gap word `β d^L` (`n = len β`,
  `s = |β|`):
  - `d = 1`: `L + 3n < 2s` (`one_background_bound`). Equivalently `D < 0` as soon as
    `2s ≤ L + 3n` (`Dz_neg_one_background`), from the general fact that `2E ≤ 3o ⇒ D < 0`.
  - `d ≥ 3`: `(d − 2)L + s ≤ 2n`, so `L ≤ n` (`steep_background_bound`, from `E ≤ 2o`).
  - `d = 2`, nontrivial cycle: `L ≤ 3n` (`two_background_bound`). This uses the right edge of the
    sandwich with every element `≥ 3`, which gives `2^E 3^o ≤ 10^o`. `E ≤ 2o` alone is not enough,
    and nontriviality is necessary, since `1 → 1` has word `2^L` for every `L`
    (`trivial_two_background`).
  - Unified: `L ≤ 2s + 3n` for every nontrivial positive cycle (`background_bound`).
- **Ellison ⇒ ceiling exclusion (conditional on `Ellison1971`).** A family whose words all have a
  nonzero rotation-ideal representative with 6-free part `≤ c` contains no genuine cycle, of either
  sign, with `E ≥ 28` and `c² ≤ 2^E` (`no_cycle_of_ellison_ge`; general form `no_cycle_of_ellison`).
- **Not done:** the sharper `d = 2` bound from a minimum element `≥ 5` (about `L ≤ 2.1n` instead of
  `3n`), and naming the intermediate orbit points `a_j = S^{(j)}/G` individually.

## christoffel (`Approaches/Christoffel.lean`)

- **Knight's high-cycle theorem is now unconditional.** `CocycleCombine.knight_cycle` assumed
  that `1u0` and `0u1` are both rotations of the cycle's parity vector (Cohn's
  reverse-equals-conjugate theorem). For coprime `0 < p < n`, the upper and lower Christoffel words
  (mechanical words of phase `n − 1` and `0`) are `1u0` and `0u1` with the **same** middle
  (`christoffel_shape`), and they are rotations of one another (`lower_isRotated_upper`).
  - The proof is elementary. Shifting the index by `j` adds `jp` to the phase, the phase only
    matters mod `n`, and `jp ≡ n − 1` is solvable.
  - The palindrome property and the reversal are not needed.
- **Consequence** (`no_high_cycle`):
  - A positive cycle with `gcd(o, E) = 1` whose parity vector is a rotation of the upper Christoffel
    word of slope `o/E` is the trivial cycle `1 → 1`.
  - The rotation class of a Christoffel word is exactly the primitive, cyclically balanced words of
    that slope (Borel–Laubie; this equivalence is literature and not formalized here). So no
    nontrivial positive cycle with coprime `(o, E)` has a perfectly balanced parity vector.
  - The arithmetic finish is Gersonides, `2^E = 3^o + 1 ⇒ (E, o) ∈ {(1,0), (2,1)}`
    (`two_pow_eq_three_pow_add_one`).
- **Not done:** the non-coprime case (a power of a Christoffel word, i.e. the cycle traversed
  several times), and Cohn's full theorem that the reversal is a conjugate.

## two backgrounds (`Approaches/TwoBackground.lean`)

- **Correction to the review's F2.** It is not true that every positive-cycle-relevant word must have
  unboundedly many runs.
  - The two-run words `1^a 2^b` with `b/a ≈ 1.41` have slope tending to `log₂3`, so the ratio
    sandwich does not exclude them. Only families with a **single** growing parameter (fixed slope)
    are retired by the sandwich (`Limits.background_bound`).
  - This was found by the arithmetic literature review, round 1.
- **The "≥ 2 growing runs" obstruction is lifted for two backgrounds.**
  - The incubator's no-go (F2/F3: diverging unit prefactors) concerned combinations of rotations.
    Through `G = gcd(S, D)` the two-background words reduce to a gcd of two `S`-unit differences.
  - Generic identities: `D(d₁^a d₂^b) = X^{d₁a}V + Y^bU`, and
    `c₁c₂S − c₂D = (c₁ − c₂)X^{d₁a}V`, `c₁c₂S − c₁D = (c₂ − c₁)Y^bU`, with
    `U = X^{d₁a} − Y^a`, `V = X^{d₂b} − Y^b`, `c_i = X^{d_i} − Y` (`D_two`, `key_V`, `key_U`).
  - On a genuine cycle, `D ∣ (2^{d₁} − 2^{d₂})·V` and `D ∣ (2^{d₁} − 2^{d₂})·U` (`dvd_of_cycle`).
    This is the Corvaja–Zannier shape `gcd(u − 1, v − 1)`.
- **`{1, 2}` is excluded.**
  - `D ∣ 3^a − 2^a` and `D ∣ 4^b − 3^b` (`dvd_u_v_of_cycle`).
  - With Ellison (`D > 2^E e^{−E/10}`, `E = a + 2b ≥ 28`), the bound `D² ≤ 3^a 4^b` is impossible,
    since `e^{1/5} < 4/3` and `e^{2/5} < 4`.
  - The cases `E ≤ 27` are a `decide` check.
  - Result: no positive cycle has cyclic gap word `1^a 2^b` with `a, b ≥ 1` (`no_cycle_one_two`).
    It is conditional only on the stated Prop `CycleLiterature.Ellison1971`.
  - In Simons–de Weger terms these are `b`-cycles (`b` local minima), so `m ≤ 91` does not cover
    them. Whether the exclusion is already in the literature is being checked by the round-2
    arithmetic chase.
- **Block version, the first step of continued-fraction renormalisation.** For blocks `u`, `v` and
  `w = u^a v^b`, with the wedge core `C(u,v) = D(u)S(v) − D(v)S(u)`:
  `D(u)D(v)S(w) − D(v)S(u)D(w) = C(u,v)·X^{|u^a|}·D(v^b)`, and the `U` analogue (`key_block_V`,
  `key_block_U`). On a cycle, `D ∣ C(u,v)·D(v^b)` and `D ∣ C(u,v)·D(u^a)` (`dvd_of_cycle_block`).
  - The letter case is `C([1],[2]) = −2`.
  - With `u`, `v` Christoffel blocks at consecutive convergents of `log₂3`, this reaches words that
    have two runs at a deeper level of the continued fraction.
  - The size comparison (`|C(u,v)|` against `|D|`) is not done.
- **Not done:**
  - The general `1^a d^b` with `d ≥ 3` (same method, with the factor `2^{d−1} − 1` and finitely many
    small cases per `d`).
  - Three or more backgrounds: Levin's gcd theorem, which is ineffective (`Vojta.lean`).
- **Resolved: the decider's degenerate-case caveat.** `decide_family.py` checked the growth of `D/h`
  for degenerate r = 1 families only numerically. The Lean procedure `R1.decideR1` proves it. The
  bound `|D| ≤ |h(z,s)|` at a cycle, together with a growth test, gives every degenerate family with
  `deg δ' ≥ 1` a finite, decided cycle set (`R1.Family.finite_bound`). `(1,3)^a 2^a` is decided in
  `R1/Examples.lean`.
- **The r = 1 classification has no Baker input.** Families with one growing slope never need
  Matveev or Rhin. Exclusion uses only `2^p ≠ 3^q` and an explicit Bernoulli bound.

## near-miss benchmark (`Approaches/NearMiss.lean`)

- **Near-miss words, certified.** Each word below is a genuine positive cycle of `3x + k(w)` with
  `k > 1` at the critical slope. Data: OEIS A226607–A226672; Belaga–Mignotte 2000.
  - `(E, o) = (27, 17)`: `k = 5`, cycles through 187 and 347.
  - `(65, 41)`: `k = 29`, through 3811. This sits at the convergent `65/41` of `log₂3`.
  - `(66, 41)`: `k = 61`, through 235.
- Each comes with a `decide` certificate of `k(w)` and `a(w)`, the resulting `3x + k` cycle, and
  (for the first two shapes) a proof that it is **not** a positive `3x + 1` cycle.
- Any rotation-ideal ceiling must be at least `|D|/k(w)` on them. For example
  `G(w65a) = 14499716215459201`.

## balanced words (`Approaches/Balanced.lean`)

- **Lothaire 2.1.15, ⇒ direction, coprime slope** (Tijdeman's argument): a circularly balanced
  binary word is a rotation of the upper Christoffel word (`isRotated_upper`). The proof goes
  through the potential `F(i) = n·P(i) − i·p`:
  - Start at a minimiser of `F` (the cycle lemma).
  - Balance at the maximiser, together with `gcd(p, n) = 1`, gives `max F − min F < n`.
  - So every prefix count equals `⌈kp/n⌉`, which is exactly the upper Christoffel word.
- **No balanced cycle** (`no_balanced_cycle`). With `Christoffel.no_high_cycle`: a positive cycle
  with `gcd(o, E) = 1` whose parity vector is circularly balanced is the trivial cycle.
  - This closes the balanced half of the covering dichotomy. Every other positive cycle (coprime
    case) has a circularly unbalanced parity vector, hence two cyclic factors of equal length whose
    numbers of ones differ by at least 2.
- **Not done:**
  - the converse (Christoffel words are balanced);
  - the non-coprime case (`gcd(o, E) > 1`: a power of a balanced primitive word, i.e. a cycle
    traversed several times);
  - turning the unbalance witness into a move.

## circuits and all two-letter runs (`Approaches/Circuits.lean`)

- **Steiner 1977 is no longer only stated.** `CycleLiterature.Steiner1977` (no nontrivial positive
  circuit, i.e. `1`-cycle) is **proved conditional on Ellison 1971** (`steiner_of_ellison`).
- **Every two-letter-run word is excluded.** No positive cycle has a cyclic gap word `1^a d^b` with
  `a, b ≥ 1`, `d ≥ 2` (`no_cycle_two_letters`), conditional on Ellison. Circuits are the case
  `b = 1`. The proof is elementary apart from Ellison:
  - On the cycle, `D ∣ (2^{d−1} − 1)(2^{db} − 3^b)`, so `D < 2^{d−1+db}`.
  - Ellison, `D > 2^E e^{−E/10}`, then gives `6931471803·(a − d + 1) < 10⁹·E`, using Mathlib's
    `log 2 > 0.6931471803`.
  - The sandwich `2^E 3^o ≤ 10^o` (minimum element `≥ 3`) gives `1000·E < 1740·o`, because
    `2^{1740}·3^{1000} > 10^{1000}`.
  - These force `a ≥ d` and then `b = 1`, leaving `a ≤ 95` in a window of 35 explicit circuits,
    none of them a cycle.
  - The cases `E ≤ 27` are below Ellison's range. Both finite sets are checked with
    `decide +kernel` (kernel evaluation; no `native_decide`, no extra axioms).
- **Note on the literature.** Steiner's original proof goes through Davison's reduction and Baker's
  method. Here Ellison's effective bound (itself from linear forms in logarithms) plus the
  elementary sandwich suffices.

## balanced cycles, any gcd (`Approaches/BalancedPow.lean`)

- **The coprimality hypothesis is removed.** No nontrivial positive cycle has a circularly balanced
  parity vector, for every `gcd(o, E)` (`no_balanced_cycle_all`). The result is unconditional: it
  needs neither Ellison nor any other literature input.
- **Averaging replaces coprimality.** The `n` cyclic windows of length `k` contain `k·p` ones in total
  (`sum_window`). With balance this gives `max F − min F < n` for every balanced word
  (`F_range_lt'`). So balanced ⇒ rotation of the non-reduced upper mechanical word
  (`isRotated_upper'`), and that word is the `g`-th power of the primitive Christoffel word `1u0`
  (`upper_mul`; similarly `lower_mul` for `0u1`).
- **Knight's C9 for powers.** For `A = 1u0`, `B = 0u1`:
  - `Y·g(Aᵏ) − g(Bᵏ) + D(Aᵏ) = geo_k·(Y·g(A) − g(B) + D(A))` (`C9_lpow`);
  - `D(Aᵏ) = geo_k·D(A)` (`Dpv_lpow`);
  - so on a cycle `|D(A)| = 1` (`knight_pow`).
- **Finish.** Gersonides forces `A = 10`, hence `E = 2o`, and `12^o > 10^o` contradicts the
  sandwich `2^E·3^o ≤ 10^o` for any nontrivial positive cycle.
- **Consequence for the covering dichotomy.** The balanced half is closed in full. Every nontrivial
  positive cycle has a circularly unbalanced parity vector: two cyclic factors of equal length whose
  numbers of ones differ by at least 2.

## two runs at any Christoffel level (`Approaches/StdPairs.lean`)

- **The wedge core of every standard pair is `6`-smooth.** Standard pairs over `{1,2}` are generated
  from `((1),(2))` by `(u,v) ↦ (u, uv), (uv, v)`. Two generic identities do the work:
  `C(u, uv) = X^{|u|}·C(u,v)` and `C(uv, v) = Y^{len v}·C(u,v)`. Starting from
  `C((1),(2)) = −X(X−1)`, induction gives `C(u,v) = −2^{i+1}3^j` (`core_smooth`). Checked
  numerically on all 511 pairs to depth 9 before formalizing.
- **Consequence: no cycle on two runs of a standard pair.**
  - By the two-block identity, a cycle (of either sign) on `u^a v^b` has `D ∣ D(u^a)` and
    `D ∣ D(v^b)`.
  - So `|D|² < 3^{|u^a|}·3^{|v^b|} = 3^E`.
  - Ellison gives `|D|² > (4e^{−1/5})^E ≥ 3^E`.
  - Hence there is no cycle once `E` is outside Ellison's exceptional set (`no_cycle_std_pair`). No
    sandwich and no finite window are needed.
  - Up to the exceptional `E`, this covers two growing runs at **any** level of the continued
    fraction of the slope. The only cycle at an exceptional `E` is `−5 → −7`, word `(1)(2)`, `E = 3`.
- **What it does not cover:** Sturmian-like words that are not two runs of a standard pair at any
  single level (three or more runs at every level); these remain open. Small exceptional `E` are not
  checked here.

## the frontier (`Approaches/Frontier.lean`) and level-(u,v) 2-cycles (`Approaches/TwoCycles.lean`)

- **Barina removes Ellison's small exceptions.** Given `Barina2025`, every element of a nontrivial
  positive cycle exceeds `2^71 − 1`, and `|x| < 3^E` (Böhm–Sontacchi), so `E ≥ 45`
  (`E_ge_of_barina`). Positive cycles on standard-pair two-run words are therefore excluded with no
  exceptional-`E` hypothesis (`no_pos_cycle_std_pair`).
- **`frontier`** collects, in one theorem, what a nontrivial positive cycle must satisfy given Ellison
  and Barina:
  - elements `> 2^71 − 1`;
  - `E ≥ 45`;
  - `3^o < 2^E` and `2^E 3^o ≤ 10^o`;
  - the parity vector is not circularly balanced;
  - the gap word is not a rotation of `1^a d^b`;
  - it is not a rotation of `u^a v^b` for a standard pair;
  - one-run families have `L ≤ 2|β| + 3 len β`.
- **Level-(u,v) 2-cycles.** These are Simons-type 2-cycles with equal separators, at any Christoffel
  level.
  - For a standard pair `(u, v)` and `A = u^{a₁}v`, `B = u^{a₂}v`:
    `C(A,B)·D(u) = C(u,v)·Y^{len v}·(X^{a₁|u|}Y^{a₂ len u} − X^{a₂|u|}Y^{a₁ len u})` (`core_runs`,
    generic).
  - So on a cycle `D ∣ D(u^{a₁−a₂})` (`dvd_of_cycle_runs`).
  - Given Ellison, the comparable-runs regime `a₂ < a₁ ≤ 3a₂` is excluded (`no_cycle_runs`).
  - The regime `a₁ > 3a₂` and the equal-runs case `a₁ = a₂` (a power) are not done.

## re-bracketing (`Approaches/Renormalize.lean`)

- **Level-(u,v) 2-cycles are fully excluded** for positive cycles, given Ellison and Barina
  (`no_pos_two_cycle`), with no restriction on the run lengths.
  - For `a₁ > a₂`: `u^{a₁} v u^{a₂} v = u^{a₁−a₂}·(u^{a₂}v)²`, and `(u, u^{a₂}v)` is again a standard
    pair (`stdPair_left_pow`, `a₂` left Stern–Brocot moves). So the word is a two-run word over a
    standard pair, already excluded by `StdPairs`.
  - The comparable-runs restriction of `TwoCycles.no_cycle_runs` is therefore unnecessary for positive
    cycles.
  - For `a₁ = a₂`: power reduction (`pos_cycle_of_pow`). A positive cycle on a rotation of `Z^g`
    yields a positive cycle on `Z` (`D(Z^g) = D(Z)·geo`, `S(Z^g) = S(Z)·geo`, `geo > 0`).
- **Powers.** No positive cycle on any rotation of `(u^a v^b)^g` (`no_pos_cycle_std_pair_pow`).
- **Lesson.** The class "rotations of `P^a Q^b` over a standard pair" is closed under re-bracketing.
  What remains open are words with at least three *unequal* runs at every level of the Christoffel
  tree.

## near-standard pairs and the literature frontier (`Approaches/NearStd.lean`)

- **Certificate size against word length, made explicit.** If the wedge core of a block pair is
  `6`-smooth times `c` (`C(u,Z) = 2^i 3^j c`), then on a cycle `D ∣ c·D(u^a)` and `D ∣ c·D(Z^b)`.
  So `|D|² < c²·3^E`, and Ellison excludes every `u^a Z^b` with `c²·15^E ≤ 16^E`, i.e.
  `E ≳ 31·ln|c|` (`no_cycle_near_std`).
  - Standard pairs are `c = ±1`.
  - Letter pairs `(1), (d)` have `c = 2^{d−1} − 1`. That is why circuits also needed the ratio
    sandwich: there `E ≈ 1.7·o` and `o` is not large compared with `d`.
- **The literature frontier** (`frontier_lit`). Given Ellison, Barina and Hercher 2023 (Thm and
  Cor. 29), a nontrivial positive cycle has:
  - more than `1.375·10^11` odd steps;
  - a minimal period with at least `92` blocks;
  - an unbalanced parity vector;
  - no standard-pair two-run gap word;
  - no level-(u,v) 2-cycle gap word.

## classification of balanced cycles (`Approaches/BalancedClass.lean`)

- **Balanced cycles of both signs, classified.** A cycle of the accelerated 3x+1 map on `ℤ` whose
  parity vector is circularly balanced is the cycle through `1`, through `−1`, or through `−5 → −7`
  (`balanced_cycle_classification`). No literature input is used.
- The argument reuses the sign-free part of `BalancedPow`: balanced ⇒ rotation of `A^g` with `A = 1u0`
  primitive Christoffel. Then:
  - Knight for powers gives `2^{n'} − 3^{p'} = ±1`.
  - All gaps `1` (`E = o`) gives `x = −1`.
  - The sign `+` gives `A = 10` and `E = 2o`, so `D > 0`, so `x > 0`, so `x = 1` by the positive
    theorem.
  - The sign `−` gives `(p', n') = (2, 3)` (`3^p = 2^n + 1 ⇒ (1,1), (2,3)`, via mod 16 and mod 5), so
    `A = 110`. The parity vector is then `(110)^g` or `(101)^g`. Since `pv` is injective, the gap word
    is `(1,2)^g` or `(2,1)^g`, giving `x = −5` or `−7`.
- **Sanity check.** The known balanced cycles `1`, `−1` and `−5 → −7` are exactly the ones listed.
  The fourth known cycle, `−17` (word `(1,1,1,2,1,1,4)`), is unbalanced.

## classification of standard-pair two-run cycles (`Approaches/StdClass.lean`)

- **Both signs, no Barina.** Given Ellison, the only cycle of the accelerated 3x+1 map on `ℤ` whose
  gap word is a rotation of `u^a v^b` (standard pair, `a, b ≥ 1`) is `−5 → −7` (`std_pair_cycles`).
- **How the exceptional `E` are handled.** Outside Ellison's exceptional set this is
  `StdPairs.no_cycle_std_pair`. The exceptional set has `E ≤ 27`, and those cases are settled by
  enumeration:
  - `gen` walks the Stern–Brocot tree from `((1),(2))` while the total sum is at most `27`.
  - `mem_gen_of_std` proves that every standard pair with total sum `≤ 27` occurs in `gen`.
  - A `decide +kernel` check (`small_check`) shows that among all `u^a v^b` with `E ≤ 27`, only
    `(1,2)` satisfies `D ∣ S`.
- **Together with `BalancedClass`:** the small known cycles `1`, `−1` and `−5 → −7` are exactly the
  cycles that are balanced or two-run at some Christoffel level. Only `−17` lies outside these
  classes.

## the closed classes on ℤ (`Approaches/SignedCycles.lean`)

- **Negative two-letter runs need no window.** For a negative cycle `2^E < 3^o`, so `1000E < 1585o`
  (`sign_linear`, from `3^{1000} < 2^{1585}`). The divisibility `D ∣ (2^{d−1} − 1)(2^{db} − 3^b)` gives
  `|D| < 2^{d−1+db}` for either sign (`abs_D_lt`). With `db ≥ d + 3b − 3`, Ellison and the sign bound
  contradict `E ≥ 28` by linear arithmetic. The positive case needed a 35-word window; the negative
  case needs none. `E ≤ 27` is a kernel check of both signs (`small_check_signed`).
- **Two letter runs, both signs** (`two_letter_cycles`): given Ellison, the only cycle on `ℤ` whose gap
  word is a rotation of `1^a d^b` (`a, b ≥ 1`, `d ≥ 2`) is `−5 → −7`.
- **Steiner's theorem on ℤ** (`few_blocks_cycles`): given Ellison, the cycles with at most one gap `≥ 2`
  are exactly those through `1`, `−1`, `−5`, `−7`. The all-ones word gives `−1` (`all_ones_cycle`).
- **Barina is no longer needed** for level-(u,v) 2-cycles and powers of standard two-run words, and
  both signs are covered (`two_cycle_classification`, `std_pair_pow_cycles`). The positive-only
  versions in `Renormalize` assumed Barina to avoid Ellison's exceptional `E`. `StdClass` settles those
  by enumeration, and a signed power reduction (`cycle_of_pow`, via `rotate_bpow`) keeps the cycle point
  itself.
- **One statement** (`closed_classes`): given Ellison, every cycle on `ℤ` whose gap word is balanced,
  has at most one gap `≥ 2`, is two letter runs, a power of a standard two-run word, or a level-(u,v)
  2-cycle is `1`, `−1`, `−5` or `−7`. So `CycleLiterature.OnlyKnownNegativeCycles` holds on every closed
  class.
- **The `−17` cycle is outside** (`neg_seventeen_outside`). Its word `1,1,1,2,1,1,4` is two blocks
  `(1112)(114)`, a negative Simons 2-cycle with distinct big letters. For a single copy of two blocks,
  `D(u)S(uv) − S(u)D(uv) = X^{E(u)}·C(u,v)`, so on any cycle `D ∣ C(u,v)`. Here
  `C(1112, 114) = −3336 = −2³·3·139` and `D = −139`, so the wedge certificate holds with cofactor `139 = |D|`.
  It carries no information: the core is not near-standard (`139² > (16/15)^{11}`), and this is why the
  two-block levers stop at `−17`.

## the repeat lemma (`Approaches/Repeat.lean`)

- **Repeat identity** (`repeat_identity`, Dubickas 2009 for Mahler's 3/2 problem): if two points have the
  same gap word `u` for `ℓ` steps, `2^{E(u)}(y' − z') = 3^ℓ(y − z)`. Hence `2^{E(u)} ∣ y − z` and
  `3^ℓ ∣ y' − z'` (`repeat_dvd`).
- **Every point of a cycle** satisfies `2^o|x||D| < 2^E 3^o` (`abs_mul_abs_D_lt`), from
  `2^o S(w) ≤ 2^E(3^o − 2^o)` for positive words (`two_pow_mul_S_le`). The points of a cycle share
  `E`, `D` and the sign of `D` (`sum_gapWord_iterate`, `same_sign`).
- **Repeat bound** (`repeat_bound`, unconditional, either sign): a window repeated at two positions of a
  minimal cycle gives `2^o·2^{E(u)}·|D| < 2^E 3^o` and `2^o·3^ℓ·|D| < 2^E 3^o`.
- **Linear forms.** Given Ellison: `10000·E(u) < 5850·o + 1443·E` and `15840·ℓ < 5850·o + 1443·E`
  (`repeat_linear`, from `1584 log 2 < 1000 log 3 < 1585 log 2`). For a nontrivial positive cycle, with
  the sandwich and Barina, **a repeated window covers less than 51.37 % of `E` and 52.79 % of `o`**
  (`repeat_half`).
- **Correction to the report's D7 derivation.** The report's form `≤ 152·o^{14.3}·M(w)` bounded
  `x_max` via Rhin. The Lean version bounds every cycle point by `(3/2)^o e^{E/10}` via Ellison. That
  bound is simpler and is what is proved.
- **Reach.** Runs `d^r` and periodic stretches are windows repeated at a short distance, so they are
  bounded too. Christoffel words have a circular repeat of length `n − 2` (Borel–Reutenauer), so they
  are re-excluded. This is a cross-check of Knight, not new. Generic words repeat only about `2 log₂ o`
  letters, so the lemma is vacuous for them, as the review predicted.

## two-block cycles with equal big gaps (`Approaches/EqualTwoCycles.lean`)

- **Simons 2-cycles with `l₁ = l₂`, both signs, Ellison only.** Every cycle on `ℤ` with exactly two gaps
  `≥ 2`, both equal, is `1` or `−5 → −7` (`equal_two_blocks`). The literature result covering positive
  2-cycles, Simons 2005, uses linear forms in logarithms and lattice reduction. The equal-gap half needs
  only Ellison.
- **Mechanism.** `1^{k+m} d 1^m d = 1^k (1^m d)²` is a two-run word over `(1, Z)`, `Z = 1^m d`. Its
  core is `C(1, Z) = −2^{m+1}(2^{d−1} − 1)` (`core_blk`), not 6-smooth for `d ≥ 4`, so `StdPairs` does
  not apply. It is still small enough: `D ∣ (2^{d−1} − 1)(2^k − 3^k)` and
  `D ∣ (2^{d−1} − 1)(2^{2(m+d)} − 3^{2(m+1)})`. With Ellison (`lin_of_lt`) and the sign bound, `E ≥ 28`
  is contradicted by linear integer arithmetic. Unlike positive `1^a d^b`, no leftover window of words
  needs checking. `E ≤ 27` is a kernel check.
- **Where it stops.** With distinct big gaps `d₁ ≠ d₂` there is no re-bracketing. The single two-block
  divisibility `D ∣ C(B₁, B₂)` holds on every cycle and is equivalent to `D ∣ S`, so it gives nothing.
  `−17` (gaps `2`, `4`) lies there, outside the enlarged union `ClosedClass₂`
  (`neg_seventeen_outside₂`).
- **Numerical cross-check** (not in Lean): over all `1^{a₁} d 1^{a₂} d` with `E ≤ 130`, the only words
  with `D ∣ S` are `(2,2)` (the trivial cycle) and `(1,2,1,2)` (`−5 → −7`).

## two runs over the left spine `(1, 1^m d)` (`Approaches/NearPairs.lean`)

- **The family `1^k (1^m d)^b`** consists of the equal-big-gap words in which every run of `1`s has length
  `m` except one longer run. Given Ellison, its only cycle on `ℤ` is `−5 → −7` (`near_pair_cycles`).
- **For `b ≥ 3` Ellison alone suffices** (`no_cycle_near`). The two block divisibilities with core
  `−2^{m+1}(2^{d−1} − 1)` give `85573E < 100000(d−1) + 158500k` and either
  `85573E < 100000(d−1+b(m+d))` or `85573E < 100000(d−1) + 158500·b(m+1)`. These conflict once
  `b(m+d) ≥ 3(d+1)` or `b(d−1) ≥ 3(d−1)`. `b = 2` (`EqualTwoCycles`) also needed the sign bound.
- **Numerical cross-check** (not in Lean): over all `1^k (1^m d)^b` with `E ≤ 150`, the only words with
  `D ∣ S` are powers of `(2)` (the trivial cycle) and of `(1,2)` (`−5 → −7`).
- **What stays open among three equal-gap blocks.** `1^M d (1^m d)²` with `M < m` re-brackets to
  `1^c Z 1^c Z²` over `(1, 1^M d)`. That is two blocks at level `(1, Z)` with distinct big letters `Z`
  and `Z²`, the analogue of `−17`.

## the Christoffel tree over `{1, d}` (`Approaches/DPairs.lean`)

- **Any root works.** `C(u, uv) = X^{|u|}C(u,v)` and `C(uv, v) = Y^{len v}C(u,v)` hold for every pair.
  So in the tree grown from `([1],[d])` every core is `−2^{i+1}3^k(2^{d−1} − 1)` (`core_dpair`). For
  `d = 2` the tree is that of the standard pairs (`DPair.of_std`); the left spine is `NearPairs`.
- **Finiteness for each `d`.** `|D|² < 4^{d−1}3^E` on a two-run word over a `d`-pair. Ellison forbids
  this once `E ≥ 20(d−1)`, because `1.9 log 2 − log 3 > 0.2` (`no_cycle_dpair`).
- **The `{1,3}` tree is closed** (`dpair_three_cycles`). A Stern–Brocot enumeration with fuel, proved
  complete (`mem_genD`), plus a kernel check of the 1,947 words with `E < 40` (`small_check_three`,
  about 50 s), show there is no cycle of either sign on any two-run word over a `3`-pair.
- **Numerically** (not in Lean), the residual regions `E < 20(d−1)` for `d = 4, …, 7` (4,413 to 17,040
  words) contain no cycle either. The kernel check grows with `d`, so a uniform argument for all `d` is
  still missing.

## the `{1, d}` trees for every `d` (`Approaches/DTrees.lean`)

- **Below `E < 20(d−1)` the word has few big gaps.** All letters of a `d`-pair are `1` or `d`
  (`DPair.letters`), so `E = o + (d−1)t` with `t` the number of `d`s (`sum_add_numBlocks`).
- **Positive cycles, every `d`.** The sandwich `1000E < 1740o` and `E < 20(d−1) + 28` give `t ≤ 20`.
  Simons–de Weger 2005 (no positive `m`-cycle, `m ≤ 68`) then excludes them. So no nontrivial positive
  cycle lies on a two-run word over any `d`-pair (`pos_dpair_cycles`). Only `NoMCyclesUpTo 20` is used
  (`pos_dpair_cycles_of`).
- **Negative cycles: what is left.** The sign bound gives `t ≤ 7`; `t ≤ 2` is closed and would need the
  letter `2`. So a negative cycle on a two-run word over a `d`-pair, `d ≥ 3`, has `3 ≤ t ≤ 7` big gaps,
  all equal to `d`, and `E < 20(d−1)` (`neg_dpair_residual`). `d = 3` is closed outright
  (`DPairs.dpair_three_cycles`). Numerically, `d = 4..7` are empty.

## negative cycles with at most two big gaps (`Approaches/NegTwoCycles.lean`)

- **Literature input.** Simons 2007 (J. Number Theory 123, last section) *sketches* that the only
  positive 2-cycle of `3x − 1` is the one through `17`, i.e. the only negative 2-cycle of `3x + 1` is
  `−17` (Lagarias, annotated bibliography II, entry 95). It is stated as `Simons2007Neg`, faithful to
  the minimal-period, two-block notion.
- **Combination** (`only_known_of_few_blocks`): given Ellison and `Simons2007Neg`, every negative cycle
  with at most two gaps `≥ 2` is `−1`, `−5 → −7` or `−17`. So `OnlyKnownNegativeCycles` holds there.
  The equal-gap half of Simons's claim is already unconditional given Ellison (`EqualTwoCycles`).
- **Prior work on the two-letter family** (entries 74 and 68):
  - Mimuro 2001 proves finiteness of positive cycles with parity sequence `1^i(10^j)^k`, i.e. gap word
    `1^i (j+1)^k`, by linear forms in logarithms;
  - Luca 2005 extends this to "at least `C₁ log n` ascents in every cycle".

  `Circuits` and `SignedCycles` exclude the whole family outright with Ellison only. Lagarias notes
  two negative orbits of Mimuro's form, `−1` and `−5 → −7`, matching `two_letter_cycles`.

## closing the `{1, d}` trees for `d ≤ 7` (`Approaches/DTreeChecks.lean`)

- **A scalable check.** `pairOk N u v` loops only over admissible exponents (`a ≤ N/|u|`,
  `b ≤ (N − a|u|)/|v|`) and is proved sound. `treeOk` runs it over the complete enumeration of
  `d`-pairs. The `d = 4` check takes a few seconds in the kernel, against about 45 s for the brute
  `d = 3` loop in `DPairs`.
- **Result** (`dpair_cycles_le_seven`): given Ellison, no cycle of either sign lies on a two-run word over
  a `d`-pair for `3 ≤ d ≤ 7`. With `DTrees`, the negative residual is open only for `d ≥ 8`. The cost
  grows about like `d³`, so the checks stop at `7` to keep the build short.

## two runs over any tree (`Approaches/Trees.lean`)

- **Any root.** Every core in the tree grown from `(u₀, v₀)` is `2^i 3^k C(u₀, v₀)` (`core_tree`). So
  `|D|² < C(u₀,v₀)² 3^E` on a two-run cycle word, and Ellison excludes it once `|C|^{20} ≤ 2^E`
  (`no_cycle_tree`). Hence **for every pair of non-commuting blocks only finitely many two-run words,
  all with `E < 20 log₂ |C|`, can carry a cycle**, with an explicit bound. Levin gives the `m`-run analogue
  only ineffectively.
- **Instances:**
  - standard pairs: `C = −2`;
  - `{1,d}` trees: `C = −2(2^{d−1} − 1)`;
  - the `−17` blocks: `C(1112, 114) = −3336` (`core_neg_seventeen_blocks`), so cycles on
    `(1112)^a (114)^b` have `E < 234`. `−17` itself has `E = 11`.
- **Where it stops.** The bound depends on the blocks. The open words are those that are not two-run
  over any tree with a small root core: three or more runs at every level.

## three runs (`Approaches/ThreeRuns.lean`)

- **Three-core identity.** `D(u)D(v)D(w)S(UVZ) = −(D(v)c_{wu}Y^o + D(w)c_{uv}X^{E_U}Y^{o_V+o_Z} +
  D(u)c_{vw}X^{E_U+E_V}Y^{o_Z}) + S(w)D(u)D(v)D(W)`. On a cycle `D(W) ∣ T_U`, a three-term sum that does
  not involve the size of `U`. The rotations give `T_V`, `T_Z`. When `w = u` the identity reduces to the
  two-block divisibility.
- **Three letter runs** (`three_letter_runs`): given Ellison, no cycle of either sign on `1^a d^b e^c` once
  `E ≥ 11(d+e+2)`. The `T`s are nonzero by a `2`-adic count. A scan over `d, e ≤ 11`, `E ≤ 120` finds no
  cycle (not in Lean).
- **Any three blocks** (`three_runs_bounded`): given Ellison and `T_U, T_V, T_Z ≠ 0`, with coefficients
  `≤ 2^K`, no cycle has `E ≥ 20(K+2)`. The three-run rung is now effective block by block, under the
  nonvanishing hypothesis.
- **Correction to my own earlier estimate.** Bounding each `T` by the product of the other runs' sizes
  suggested failure when two runs have slope below `log₂ 3`. That was too lossy. The exact supremum of
  the 27 linear programs is `0.80381 < 0.85573`, so the method works for every triple.
- **The limit, computed** (scipy, not Lean). For `m` runs the corresponding suprema are `0.613, 0.804,
  0.890, 0.935, 0.961` for `m = 2, …, 6`. With Ellison's `0.8557` the wedge-core method is effective for
  `m ≤ 3` and fails from `m = 4` on. A Baker/Rhin lower bound (`|D| ≥ 2^E E^{−C}`) makes the effective
  exponent tend to `1`, which would cover each fixed `m`. Compare Levin's ineffective `m`-run theorem.

## four runs with Rhin's bound (`Approaches/FourRuns.lean`)

- **Four-core identity.** `D₁D₂D₃D₄·S(W) = −(D₂D₃c₄₁Y^o + D₃D₄c₁₂X^{E₁}Y^{o₂+o₃+o₄} +
  D₁D₄c₂₃X^{E₁+E₂}Y^{o₃+o₄} + D₁D₂c₃₄X^{E₁+E₂+E₃}Y^{o₄}) + S₄D₁D₂D₃·D(W)`. The `m`-run pattern is
  clear: one core per adjacent pair, times the `D`s of the two other blocks, times a split monomial.
- **Result** (`four_runs_bounded`): given Simons–de Weger 2005 Lemma 12 (Rhin's bound, stated in
  `CycleLiterature`) and the four `T_R ≠ 0`, with coefficients `≤ 2^K`, no nontrivial positive cycle on
  `p₁^{a₁}p₂^{a₂}p₃^{a₃}p₄^{a₄}` has `E ≥ 3500 + 16K`. The integer linear programs give a maximum of
  `≈ 3412 + 15.3K` (scipy, not Lean).
- **Why Rhin and not Ellison.** The four-run supremum `0.890` exceeds Ellison's `0.8557`. Rhin loses only
  `o^{13.3}`. Linearising `log o` needs `ℓ = ⌊log₂ o⌋ + 1` with `200ℓ ≤ o + 3000` (`log_bound`).
- **Proof engineering.** The `256 × 2` linear cases first ran out of heartbeats after 19 minutes, because
  `omega` split the four `T ≠ 0` hypotheses in every case. Clearing the context to the linear facts
  (`clear * -`) brings the whole file to about 1 minute.
- **Scope.** Positive cycles only, because Lemma 12 is stated for them. Each further `m` needs its own
  `m^m`-case check (suprema `0.935`, `0.961`, … below `1`), so fixed `m` can be done one at a time,
  but not uniformly in `m`.

## the reach of the wedge cores, exactly, and the run frontier (`Approaches/RunsFrontier.lean`)

- **Closed form, now proved in Lean for every `m`** (`Reach`, abstract, any cap `λ ≥ 1`). Earlier it was
  computed by linear programming over all `m^m` choice patterns for `m ≤ 6`. With `λ = log₂ 3`, the worst case of `min_R (bound for T_R)`
  over size profiles is `c_m = 1 − (λ−1)/(λ^m − 1)`: `0.613, 0.804, 0.890, 0.935, 0.961, 0.976, …`. The
  supremum is the same on the near-critical slice `E = o log₂3`, the only slice where Ellison-type bounds
  are needed.
- **Lower bound, proved on paper.** Take `x = (λ^{m−1}, 1, λ, …, λ^{m−2})`, `y = (1, λ, …, λ^{m−1})`
  (`x = E`, `y = o·λ` per run), so `X = Y = Σλ^i`. Run 0 has slope `λ^m`; runs `1..m−1` have slope `1`
  and weights in ratio `λ`. For every excluded run `R` one split telescopes to exactly `X − 1`. Hence no
  lower-bound exponent `θ ≤ c_m` can exclude this profile. With Ellison's `θ = 0.8557` the method covers
  exactly `m ≤ 3`. With Rhin `θ → 1` and it covers each fixed `m`, at a size cost growing like `λ^m`.
- **Realised on actual words** (Python, not Lean): `6^{a₀}(1^{20}2)^{a₁}(1^{21}2)^{a₂}(1^{22}2)^{a₃}`,
  tuned to `|E − λo| < 2`, keeps all four `T` bounds above `2^{0.8557E}` for `E = 3,488 / 13,862 / 55,539`.
  The limiting ratio for these block slopes is `0.878` (`0.884` for `1^{40}2…`). So the four-run failure
  under Ellison is not an artefact of the relaxation.
- **The run frontier** (`RunsFrontier`): with Barina and Hercher's Corollary 29, `E > 1.375·10^{11}`. So a
  nontrivial positive cycle is not:
  - a two-run tree word unless `log₂|C(u₀,v₀)| > 6.875·10^9`;
  - a three-letter-run word unless `d + e > 1.25·10^{10}`;
  - a three-run word unless `K > 6.87·10^9`;
  - a four-run word (with Rhin) unless `K > 8.59·10^9`.

## the exact reach, proved (`Approaches/Reach.lean`)

- **Upper bound** (`reach_upper`): for any `m ≥ 1`, cap `λ ≥ 1` and `m`-periodic profile with `0 ≤ y ≤ λx`,
  some excluded run `R` has every split `f_R(s) ≤ (1 − 1/σ_m)·max(X, Y)`. The proof:
  - writes `f_R(s) = Y − y_R + Φ(R+1+s) − Φ(R+1)`, with `Φ` the walk of `x − y`;
  - in the case `Y ≥ X`, takes the peak `p` of `Φ`. A failing configuration forces
    `h_{k+1} + τ ≤ λ(h_k + τ)`, so `y_{p−1+k} < λ^k τ`, and summing over a period gives `Y < Y`;
  - in the case `X > Y`, raises `y` until `Y = X`.
- **Tightness** (`reach_tight`): the profile `x = (λ^{m−1}, 1, λ, …)`, `y = (1, λ, …, λ^{m−1})` has
  `X = Y = σ_m`, and every excluded run has a split equal to `σ_m − 1`.
- **Ellison** (`ellison_reach`): `1 − 1/σ_3 < 1 − 1/(10 ln 2) < 1 − 1/σ_4` for `λ = log₂ 3`. So the
  cocycle's wedge-core certificates with Ellison reach exactly three runs. That is a theorem, not an
  estimate.
- **The link to words is now formal** (`MRuns`).

## `m` runs, end to end (`Approaches/MRuns.lean`)

- **General identity.** For blocks `Q₀, …, Q_{m−1}` and any `D'`, `A_i` with `D'·S(Q_i) = A_i·D(Q_i)`,
  the cocycle telescopes, and summation by parts gives `D'·S(W) = X^{E₀}·T + A₀·D(W)` with
  `T = Σ_j (A_{j−1} − A_{j mod m})·X^{E_{[1,j)}}Y^{o_{[j,m)}}`. On a cycle `D(W) ∣ T`. Rotations give one
  `T` per excluded run. The coefficient differences are the wedge cores times the other blocks' `D`s.
  The products `D' = ΠD(p_k)`, `A_i = S(p_i)Π_{k≠i}D(p_k)` always work (`exists_coeffs`).
- **End to end** (`mruns_bounded`): if `|A_i − A_{i+1}| ≤ 2^K`, every rotated `T ≠ 0`, and
  `|D| ≥ 2^{θ·max(E, o log₂3) − L}`, then `(θ − c_m)·max(E, o log₂3) ≤ K + L + log₂ m`. The monomials of
  `T` are exactly `Reach`'s splits, and `Reach.reach_upper` picks the excluded run.
- **Ellison as a separation** (`ellison_lower`): `|2^E − 3^o| ≥ 2^{θ_E·max(E, o log₂3) − 1}`,
  `θ_E = 1 − 1/(10 ln 2)`, for `E` outside the exceptions. It covers three regimes: `2^E ≥ 2·3^o`,
  `3^o ≥ 2·2^E`, and near-critical.
- **Every `m ≤ 3`, any blocks** (`mruns_ellison`): `(θ_E − c_3)·max(E, o log₂3) ≤ K + 1 + log₂ 3` with
  `θ_E − c_3 > 0`, so `E ≲ 19.3·(K + 2.6)`. This one theorem covers two and three runs of any blocks,
  of either sign, given the `T`s nonzero. `Trees` and `ThreeRuns` are special cases with sharper
  constants.
- **What the general theorem cannot do:** for `m ≥ 4` it needs `θ > c_m`, i.e. a Rhin/Baker-type
  separation (stated only for positive cycles); and the nonvanishing of the `T`s stays a hypothesis
  (proved for three letter runs in `ThreeRuns`).

## `m ≤ 3` runs with no nonvanishing hypothesis (`Approaches/MRunsExplicit.lean`)

- **`2`-adic nonvanishing** (`T_ne_zero`): the first term of `T` is `(A₀ − A₁)·3^{…}`; every other term
  carries `2^{E₁}`. So `2^{E₁} ∤ A₀ − A₁` gives `T ≠ 0`. That holds as soon as `A₀ ≠ A₁` and
  `|A₀ − A₁| < 2^{E₁}`, i.e. when the run after the excluded one is longer than the coefficient bound.
- **Product coefficients.** `A_i − A_{i+1} = −(Π_{k∉{i,i+1}}D(p_k))·C(p_i, p_{i+1})` (`Acoef_diff`). It
  is nonzero exactly when the adjacent core is (`D ≠ 0` for nonempty blocks), and
  `|A_i − A_{i+1}| ≤ 2^{6B+1}` with `B` the total base weight (`Acoef_diff_le`, via `S(w) ≤ 3^{E(w)}` and
  `|C(u,v)| ≤ 2·3^{E(u)+E(v)}`).
- **Result** (`mruns_explicit`): given Ellison, for `2 ≤ m ≤ 3` runs of any positive nonempty base blocks
  with nonzero adjacent cores and every run of weight above `6B + 1`:
  `(θ_E − c_3)·max(E, o log₂3) ≤ 6B + 2 + log₂3`, and `θ_E − c_3 > 1/20` (`margin`). So
  `E < 20(6B + 3.6)`. That is a finite window for each base family, with no unproved hypothesis besides
  Ellison.
- **Frontier** (`frontier_mruns`): with Barina and Hercher, no nontrivial positive cycle is such a word
  when `B ≤ 10^9`.
- **What remains.** Short runs (weight `≤ 6B + 1`) are not covered by this nonvanishing argument; other
  terms of `T` may then carry the minimal `2`-adic valuation.

## up to three runs, no side conditions (`Approaches/MRunsDichotomy.lean`)

- **What `T = 0` means.** By the key identity, `T = 0` exactly when the word's rational cycle point
  `S(W)/D(W)` equals the first block's point `S(p₀)/D(p₀)`. On a genuine cycle the word's point is an
  integer orbit point `y`, so `D(p₀)·y = S(p₀)`. Then `y` lies on the cycle of the base block `p₀`, of
  period `|p₀|` (`T_zero_alt`, via `gapWord_iterate`: orbit points read rotated words).
- **Dichotomy** (`mruns_dichotomy`): given Ellison, a cycle of either sign on `p₀^{a₀}⋯p_{m−1}^{a_{m−1}}`
  (`1 ≤ m ≤ 3`) either has an orbit point on a base block's cycle, or satisfies
  `(θ_E − c_3)·max(E, o log₂3) ≤ 6B + 2 + log₂3`. There is no long-run condition and no condition on the
  cores; `m = 1` (powers) is always the first branch.
- **Frontier** (`frontier_le_three`): with Barina and Hercher's `o > 1.375·10^{11}`, both branches are
  impossible for a nontrivial positive cycle when `B ≤ 10^9`. The first would give a cycle of period
  `≤ B`; the second gives `E < 20(6B + 3.6)`. So **no nontrivial positive cycle has a gap word of at most
  three runs over base blocks of total weight at most `10^9`.** Here "runs" means powers of base
  blocks, at any level of description.
- **Next.** The same dichotomy for every `m` needs only a separation exponent above `c_m`. Rhin's bound
  (`|D| ≥ 2^{max − 10 − 14⌈log₂ o⌉}` for positive cycles) supplies one for every `m`, since `1 > c_m`, at
  a cost `σ_m` that grows like `(log₂3)^m`.

## every number of runs, with Rhin (`Approaches/MRunsRhin.lean`)

- **Rhin as a separation** (`rhin_sep`): for nontrivial positive cycles,
  `|D| ≥ 2^{max(E, o log₂3) − 10 − 14ℓ}`, `ℓ = ⌊log₂ o⌋ + 1`, from Simons–de Weger's Lemma 12 and
  `rhin_pow`. Here `θ = 1 > c_m` for every `m`.
- **All-`m` dichotomy** (`mruns_rhin`): a nontrivial positive cycle on `m` runs over base weight `B`
  either has an orbit point on a base block's cycle, or satisfies
  `max(E, o log₂3)/σ_m ≤ 6B + 11 + 14ℓ + log₂ m`.
- **Frontier** (`frontier_rhin`): `c(⌊log₂ o⌋ + 1) ≤ o + c(2⌊log₂ c⌋ + 6)` (`log_lin`) absorbs the
  logarithm. With Barina and Hercher, a numerical condition `2σ_m(6B + 11 + 14(2⌊log₂c⌋+6) + log₂m) <
  1.375·10^{11}` (`c ≥ 28σ_m`) excludes the word. Instances in Lean: `≤ 10` runs with `B ≤ 5·10^7`
  (`frontier_ten`), `≤ 20` runs with `B ≤ 6·10^5` (`frontier_twenty`).
- **Admissible base weight by number of runs** (from the same condition, computed, not in Lean):

  | runs `m` | 4 | 5 | 6 | 8 | 10 | 12 | 15 | 20 | 25 | 30 | 35 | 40 |
  |---|---|---|---|---|---|---|---|---|---|---|---|---|
  | max `B` | 1.26·10^9 | 7.4·10^8 | 4.5·10^8 | 1.7·10^8 | 6.8·10^7 | 2.7·10^7 | 6.7·10^6 | 6.7·10^5 | 66,835 | 6,560 | 521 | none |

  The cost grows like `σ_m ≈ (log₂3)^m/0.585`. Hercher's `m ≤ 91` concerns blocks `1^k d` with
  unbounded `k`; these results concern powers of arbitrary base blocks, so the two are complementary.

## every number of runs, both signs (`Approaches/MRunsSigned.lean`)

- **Source of the two-sided bound.** Simons–de Weger's Lemma 12 is stated for positive cycles. Its source,
  Rhin 1987, bounds the absolute linear form. Rukhin (arXiv:1805.10496, eq. (3)) quotes it as
  `|−E log 2 + τ log 3| ≥ E^{−13.3}`, with no sign condition. It is stated as `Rhin1987` for `2 ≤ E`,
  `1 ≤ o ≤ E`.
  - Rhin's original text was not available.
  - Numerically, the smallest value of `|E log 2 − o log 3|·E^{13.3}` over `2 ≤ E ≤ 2·10^5` is about
    `2,901`, at `(2,1)`. So the statement is safe in the small range, where Rhin's own range might not
    apply.
- **Separation for every word** (`rhin_sep_signed`): `|2^E − 3^o| ≥ 2^{max(E, o log₂3) − 2 − 14ℓ}`,
  `ℓ = ⌊log₂E⌋ + 1`. Near the critical slope it uses `|r − 1| ≥ |log r|/2` for `r = 2^E/3^o ∈ [1/2, 2]`.
- **All-`m` dichotomy, both signs** (`mruns_signed`): a cycle of either sign on `m` runs over base weight
  `B` either has an orbit point on a base block's cycle, or satisfies
  `max(E, o log₂3)/σ_m ≤ 6B + 3 + 14ℓ + log₂ m`. For negative cycles this is the first effective
  statement for four or more runs. With no verification bound for negative cycles it constrains them
  (`E` is at most `σ_m`-linear in `B`, up to the logarithm) rather than excluding them. For example, it
  constrains the 1-runs of negative two-cycles `1^{a₁}d₁1^{a₂}d₂`: four letter runs, `B = 2 + d₁ + d₂`.

## PROGRAM.md §5: the first objective, for few-run words (`Approaches/ExplicitF.lean`)

- PROGRAM.md §5 asks for an explicit upper bound `f(w)` on a move representative (a combination in the
  rotation ideal), proved below `3^o` for critical words, and for how far below it goes.
- **For every `m`-run word, no cycle assumed** (`explicit_f`), some rotation `R` gives the combination
  `D'·S(W_R) − A_R·D(W_R) = 2^{E}·T_R` with `|T_R| ≤ m·2^{6B+1}·2^{c_m·max(E, o log₂3)}`. So
  `f(w) = m·2^{6B+1}·2^{c_m·max(E, o log₂3)}`; at the critical slope it lies below `3^o` by
  `2^{−(1−c_m)·o·log₂3}`, up to the block-dependent factor.
- **How far below, and the limit.** The exponent `c_m = 1 − 1/Σ_{i<m}(log₂3)^i` is sharp
  (`Reach.reach_tight`). The margin is `(1 − c_m)·o·log₂3 = o·log₂3/σ_m` bits. It is linear in `o` for each
  fixed `m` and shrinks like `(log₂3)^{−m}` as runs are added. For words whose number of runs grows with
  `o`, as all critical words must, this certificate gives no margin. That is the precise sense in which
  the first objective is met for few-run words and open in general.

## PROGRAM.md §9.4 and the C-balance claim (`Approaches/Estimators.lean`)

- **§9.4 resolved.** For a positive nonempty word, `S(w)` is odd (`Sz_odd`) and prime to `3`
  (`Sz_not_three_dvd`), so its `6`-free part is `S(w)` itself (`sixFree_Sz`). With `A(w) = S(w)/(n·3^{n−1})`
  the AM–GM sandwich is already the requested size estimate: `n·3^{n−1}·G_*(w) ≤ sixfree(S(w)) = S(w) ≤
  C(w)·n·3^{n−1}·G_*(w)` (`abelian_estimate`). On a cycle `|x|·|D| = S` (`cycle_abelian`), so the estimator
  locates every cycle point to within the factor `C(w)` once `D` is known. "Normalise to the 6-free part"
  needed no new idea: the normalisation is trivial because `S` has no factor `2` or `3`.
- **Window identity** (`window_identity`): along `ℓ` steps from `y > 0`,
  `2^{E(u)}·x_{ℓ} = 3^ℓ·y·Π_{k<ℓ}(1 + 1/(3x_k))`.
- **C-balance, proved and sharpened.** The report listed "cycle words are C-balanced with
  `C ≤ 2·log₂(x_max/x_min) + 1`" as derived. Two versions are now proved:
  - for any positive orbit with points in `[m, M]`, `2^{E(u)} ≤ (M/m)²·(1 + 1/(3m))^ℓ·2^{E(u')}` for
    windows of equal length `ℓ` (`c_balanced`; no cycle needed);
  - on a positive cycle, each window's product is a sub-product of the whole cycle's product, which is
    `2^E/3^o` (`window_prod_le`). So for `ℓ ≤ o`, `E(u) − E(u') ≤ 2·log₂(x_max/x_min) + (E − o·log₂3)`
    (`c_balanced_cycle`).
- **Discrepancy with the derivation.** The `+1` in the derived form is really the defect `E − o·log₂3`.
  That is below `1` exactly when `2^E < 2·3^o`. Nothing proved here forces that for a hypothetical cycle;
  the ratio sandwich only gives `E − o·log₂3 ≤ o·log₂(1 + 1/(3x_min))`. So the `+1` form holds only
  under that extra condition, and the proved form should replace it.

## Cycle length from Barina alone; the frontier without Hercher (`Approaches/CycleLength.lean`, `Approaches/BarinaFrontier.lean`)

- **Eliahou's method with `2^71`, fully proved.** On a nontrivial positive cycle every point is
  `≥ 2^71` (Barina), so `0 < E log 2 − o log 3 = Σ log(1 + 1/(3x_k)) < o/(3·2^71)`
  (`CycleLiterature.barina_sandwich`). The convergents `p/q = 103768467013/65470613321` (below `log₂3`)
  and `p'/q' = 10439860591/6586818670` (above) satisfy `p'q − pq' = 1` and bracket the whole interval
  `(log₂3, log₂3 + 1/(3·2^71 ln 2))`. A fraction strictly between Farey neighbours has denominator
  `≥ q + q'` (`farey`). So **every nontrivial positive cycle has `o ≥ 72 057 431 991` and
  `E ≥ 114 208 327 604`**, the mediant (`cycle_length_ge`). The only literature input is `Barina2025`.
- **Certified logarithms.** The two inequalities between `log 2` and `log 3` come from Mathlib's
  `Real.abs_log_sub_add_sum_range_le` at `x = 1/9` (`log(8/9) = 3 log 2 − 2 log 3`, 24 terms) and
  `x = 13/256` (`log(243/256) = 5 log 3 − 8 log 2`, 17 terms), error `< 10^{-23}`. The margins are
  `4.6·10^{-12}` and `9.2·10^{-12}` against coefficients up to `1.1·10^{10}`.
- **The bound is sharp for this inequality.** The mediant `114208327604/72057431991` itself lies in the
  interval (`(E − oλ)/o ≈ 1.10·10^{-22} < 1/(3·2^71 ln 2) ≈ 2.04·10^{-22}`), so the elementary sandwich
  cannot exclude it. Hercher's Corollary 29 (`o > 1.375·10^{11}` = the next convergent denominator
  `137528045312`, from the smaller verification bound `3·2^69`) therefore rests on a sharper analysis
  than the `x_min` sandwich; it stays stated, not proved.
- **The frontier without Hercher.** Every frontier theorem now has a general form over
  `CycleBounds No NE` (`*_of`); the Hercher versions are one-line instances with unchanged statements.
  Barina-only instances (`BarinaFrontier`): `≤ 3` runs over base weight `≤ 9.5·10^8` (was `10^9`),
  `≤ 10` runs over `≤ 5·10^7` (unchanged), `≤ 20` runs over `≤ 5.5·10^5` (was `6·10^5`), two runs
  with `20K ≤ 1.142·10^{11}`, three letter runs with `11(d + e + 2) ≤ 1.142·10^{11}`.
- **Lean pitfall.** `exact_mod_cast` on an `ℤ → ℝ` cast of 11-digit literals made the kernel hit deep
  recursion; `Int.cast_pos.mp` avoids the cast normalisation.

## Eliahou 1993 and Terras 1976, proved (`Approaches/Eliahou.lean`, `Approaches/Terras.lean`)

- **Eliahou 1993 is a theorem now**, with no literature input (`Eliahou.eliahou1993` proves the stated
  `CycleLiterature.Eliahou1993`). The three vectors `v₃ = (85137581, 53715833)`, `v₂ = (17087915, 10781274)`
  and `v₁ = (301994, 190537)` (numerator `E`, denominator `o`) are consecutive Farey neighbours
  (`det = 1`) with `v₃ < log₂3 < v₂ < log₂3 + 1/(3·2^40 ln 2) < v₁` (margins `3.5·10^{-9}` and
  `6.7·10^{-9}` in linear form, certified by `CycleLength.log_two_three`). A lattice point in a
  determinant-1 cone is a nonnegative combination of its two edges (`cone_decomp`, a two-line
  `linear_combination`). Splitting at `v₂` gives `E = 301994a + 17087915b + 85137581c`, `b ≥ 1`, `ac = 0`,
  and the same for `o` (`eliahou_40`). The proof needs no primitivity, which the stated form assumes.
- **Eliahou's form at `2^71`** (`eliahou_barina`): with Barina, `(E, o)` is
  `a·(103768467013, 65470613321) + b·(114208327604, 72057431991) + c·(124648188195, 78644250661)`, `b ≥ 1`,
  `ac = 0`. The middle vector is the mediant of `cycle_length_ge`; the upper one is the next mediant
  towards `10439860591/6586818670`, already outside the interval (margin `4.5·10^{-12}`).
- **Certified logarithms, 30 digits.** `CycleLength.log_two_three` gives `log 2` and `log 3` to
  `1.5·10^{-29}` and `2.3·10^{-29}` (series at `1/9` with 31 terms, at `13/256` with 23). Every
  inequality between `log 2` and `log 3` with coefficients up to `~10^{15}` is now a `linarith` call.
- **Terras 1976 is a theorem now** (`Terras.terras` proves the stated `CycleLiterature.Terras1976`).
  `n ≡ m (mod 2^{j+1})` gives equal parity and `T n ≡ T m (mod 2^j)` (`T_modEq`); conversely equal
  first `k` parities give `n ≡ m (mod 2^k)` by doubling the modulus one step back and cancelling the
  unit `3` (`modEq_of_parity_eq`). Injectivity plus `|Fin 2^k| = |{0,1}^k|` gives the bijection. This
  is the arithmetic of the report's "2-adic blindness": each finite parity pattern is realised by
  exactly one residue class mod `2^k`.
- **Remaining stated literature in `CycleLiterature`:** Steiner, Simons, Simons–de Weger (both),
  Hercher (and Cor. 29), Lemma 12 / Rhin, Ellison, Barina, Simons 2007 (negative). All but Barina
  (a computation) rest on Baker-type linear-forms bounds; Hercher's Cor. 29 cannot follow from the
  `x_min` sandwich alone (the `2^71` mediant lies inside the interval).
