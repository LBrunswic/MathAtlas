# Syracuse — Lean formalization of the cycle approaches

Lean 4 + Mathlib formalization of the approaches in [`../APPROACHES.md`](../APPROACHES.md)
toward the period (cycle) problem for the Syracuse / 3x+1 map.

* Lean `v4.34.1`, Mathlib `v4.34.1`.
* Build: `lake build`. Axiom audit: `lake env lean scripts/AuditAxioms.lean`.
* Trust policy: no `sorry`, no `axiom`, no `native_decide`. Every declaration under `Syracuse`
  depends only on `propext`, `Classical.choice` and `Quot.sound`, and the audit script checks this
  mechanically. Results from the literature that are not proved here appear as `def … : Prop`.
  They are never axioms, and they only ever enter as explicit hypotheses of *conditional* theorems.

## Layout

| file | approach folder | content |
|---|---|---|
| `Syracuse/Basic.lean` | `diophantine`, `cocycle-combine/structure` | gap words, `S`, `D`, concatenation cocycle, transfer matrix, orbits `Follows`, closed form, cycle equation, rotation recursion, the Syracuse map on `ℤ`, `IsSyrCycle`, Collatz, 6-free part |
| `Approaches/Diophantine.lean` | `diophantine` | closed form in the notes' (a, e, o) notation, Σ-form, reconciliation with parity-manipulation's (b, x, n), corollaries |
| `Approaches/CycleGcd.lean` | `cycle-gcd` | rotation recursion, gcd ∣ D for every word, gcd = abs D on cycles, criticality lemma, (9,5) witness, `u^q v` telescoping + q-free core, `finite_q`, Matveev exclusion (conditional) |
| `Approaches/CocycleCombine.lean` | `cocycle-combine` | structure.md C1–C11, compensation principle, P0/P1/P2 (ceiling), P3/P4/P9/P10/P11 identities |
| `Approaches/BoundedDefectLever.lean` | `bounded-defect-lever`, `ideas/cocycle-combinatorics` | shared-frame / inner-core extraction, move calculus, bounded-defect wedge, o-independent 6-free ceiling, atlas |
| `Approaches/Program.lean` | `PROGRAM.md` | floor, squeeze (conditional on a lower-bound Prop), "rep < 3^o ⇔ critical", AM–GM estimator |
| `Approaches/DiophantineDistribution.lean` | `diophantine-distribution` | FS1–FS5, x* in ℤ₂, conjugacy, rigidity, FS3 (integer starts), flying time ⇔ Collatz |
| `Approaches/CocycleControl.lean` | `cocycle-control` | range 1 ≤ S ≤ 3^E − 2^E (new), band at fixed (E, o), monotone moves |
| `Approaches/CirculantMatrix.lean` | `circulant_matrix` | rotation matrix, det = (−1)^{o+1} D^{o−1}, Δ⁻¹CΔ, spectrum, circuit factorisation, étale-algebra norms/traces, gcd law |
| `Approaches/ParityManipulation.lean` | `parity-manipulation` | 2-adic reconstruction (corrected bijection), shift formula, 3-adic lifting-the-exponent lemma, ord(2) mod 3^{q+1}, integrality, finite-support no-go |
| `Approaches/ZeroSumCombination.lean` | `zero-sum-combination` | zero-sum ideal = ideal of differences = gcd·ℤ, ℤ[1/6] PID / Euclidean via sixFree / units, transfer |
| `Approaches/PuncturedTorus.lean` | `punctured-torus` | affine generators, period map, Property P, hyperbolic axis + length, Markoff traces, commutator, Lorentzian Ad-spectrum, null τ, Margulis = 0 |
| `Approaches/PolynomialRoot.lean` | `polynomial-root` | Fox calculus on F₂, Crowell–Fox, bridge to S, conjugacy invariance, coprime reparametrisation iso, catalogue identities, core gcd |
| `Approaches/TwoRun.lean` | `places-elimination` | the two-run family `d^a e₁ d^a e₂ d^a`: closed forms in run coordinates, resultant certificate, uniform ceiling `D ∣ R*(2^d,2^{e₁},2^{e₂},3)`, `R* ≠ 0`, growth, exclusion from finite checks, decider-emitted instances |
| `Approaches/Vojta.lean` | `places-elimination` | the `S`-unit case of Vojta for blow-ups (Levin's gcd theorem) as a hypothesis; Weil heights from Mathlib; conditional finiteness for `r`-parameter families and for `d^a e d^b f` |
| `Approaches/R1/LPoly.lean` | `places-elimination` | computable coefficient-list polynomials; `toPoly` homomorphism; verified long division and extended Euclid over a field |
| `Approaches/R1/Family.lean` | `places-elimination` | r = 1 families (fixed words + growing blocks of one slope); closed form `μS = s^N γ(t)`, `D = s^N δ(t)`; degree, positivity and integrality invariants |
| `Approaches/R1/Decide.lean` | `places-elimination` | **`decideR1`, a verified total decision procedure for cycles in r = 1 families** (`decideR1_correct`); the classification (finite cycle set, or constant fixed point = powers of one cycle) |
| `Approaches/R1/Examples.lean` | `places-elimination` | families decided by kernel evaluation (`decide +kernel`): two-run, block, degenerate, the −5/−1/1 power families, the −17 family |
| `Approaches/R1/WPow.lean` | `places-elimination`, `cycle-gcd` | `w^a w'` uniformly in `(w, w')`: identity `D(w)S(w^a w') − S(w)D(w^a w') = X^{a\|w\|} C(w,w')`; `C ≠ 0` ⇒ `D ∣ C` and finitely many cycles; `C = 0` ⇒ cycle iff `w` is |
| `Approaches/R1/Nested.lean` | `places-elimination` | `(w^a w')^b w''` uniformly: Plücker step `D(w)C(w^a w',w'') = D(w^a w')C(w,w'') − 2^{a\|w\|}D(w'')C(w,w')`, zero set (≤ 1 point or all), joint bound (finitely many `a` with a `b ≥ 2` cycle and `C ≠ 0`), full classification |
| `Approaches/R1/Tower.lean` | `places-elimination` | **towers** `((u₀^{a₁}u₁)^{a₂}u₂)⋯` of any depth: tameness (bounded fixed points + band-finiteness) is preserved by `v ↦ v^b u`; **a tower meets only finitely many cycles** (`tower_cycleStarts_finite`), with no Baker input |
| `Approaches/R1/Skeleton.lean`, `Approaches/R1/Skel/*.lean` | `places-elimination` | skeleton families, uniformly in the words: closed form, universal resultant certificate (`ring`), ceiling `D ∣ c·R'(cocycle data)`, finiteness; generated by `skeleton.py` for seven skeletons (one, two and three blocks) |
| `Approaches/R1/TwoExp.lean` | `places-elimination` | same-side two-exponent families `u^a x v^b y` (r = 2): linear form `D(v)C(u,xv^by) = α2^{b\|v\|} − β3^{b len v}`, `a` bounded, rotation invariance of cycle words, **classification without Baker input**; chart in `approaches/places-elimination/PATTERNS.md` |
| `Approaches/R1/Straddle.lean` | `places-elimination` | **every** two-exponent family `u^a x v^b y`, either side of `log₂ 3`: Matveev ⇒ polynomial lower bound `PolyLB`; two ceilings multiply to `2^{a+b} ≤ K (a+b+1)^{2κ}` (`twoExp_pow_le_of_polyLB`); complete statement `twoExp_cycles_of_matveev` (finite set + two loci, each one point or everything) |
| `Approaches/CycleLiterature.lean` | `cycle-literature` | Böhm–Sontacchi (+ converse), ratio sandwich, finiteness per period, period 1, negative cycles; deep results (Steiner, Simons–de Weger, Hercher, Rhin, Ellison, Barina) stated as Props with conditional corollaries |
| `Approaches/Limits.lean` | review: limits of the cocycle approach | F1 `G = gcd(S, D)`; every positive word is a positive cycle of `3x + k(w)`, `k = D/gcd(S,D)` (3x+1 iff `k = 1`); `3x − 1` duality; `5x + 1` and negative-cycle witnesses; sign-blind floor and tight ceiling on the `−17` cycle; q-invariance at (2,5); F2 fixed-slope bounds `L ≤ 2\|β\| + 3 len β`; Ellison ⇒ ceiling exclusion (conditional) |
| `Approaches/Christoffel.lean` | review: ledger item C9 (Knight) | mechanical/Christoffel words, index shift = phase shift, upper `1u0` and lower `0u1` share the middle and are conjugate for coprime slope (the Cohn input), Gersonides `2^E = 3^o + 1`, **Knight's theorem unconditional**: no nontrivial positive cycle whose parity vector is a rotation of a Christoffel word (coprime `(o,E)`) |
| `Approaches/TwoBackground.lean` | review: ≥2 growing runs | two growing backgrounds `d₁^a d₂^b`: generic identities `D = X^{d₁a}V + Y^bU`, `c₁c₂S − c₂D = (c₁−c₂)X^{d₁a}V`; on a cycle `D ∣ (2^{d₁}−2^{d₂})·gcd-type terms`; `{1,2}`: `D ∣ 3^a−2^a` and `D ∣ 4^b−3^b`; **no positive cycle with cyclic word `1^a 2^b`** (critical slope reachable), conditional on Ellison 1971, small cases by `decide`; block version `u^a v^b`: `D ∣ C(u,v)·D(u^a)`, `D ∣ C(u,v)·D(v^b)` |
| `Approaches/NearMiss.lean` | review: D3 near-miss benchmark | critical-slope words with small `k(w)`: `(27,17)` k = 5 (a = 187, 347), `(65,41)` k = 29 (a = 3811, at the convergent 65/41), `(66,41)` k = 61; each certified by `decide` as a genuine `3x+k` cycle and not a positive `3x+1` cycle; slack bar `G = |D|/k` |
| `Approaches/Balanced.lean` | review: D2, balanced half | Lothaire 2.1.15 (Tijdeman's cycle-lemma argument, ⇒ direction, coprime slope): a circularly balanced binary word is a rotation of the upper Christoffel word (`isRotated_upper`); with Knight: **no nontrivial positive cycle with a circularly balanced parity vector** (`no_balanced_cycle`) |
| `Approaches/Circuits.lean` | review: D1 + cycle-literature (Steiner) | every two-letter-run word `1^a d^b` (`d ≥ 2`): no positive cycle (`no_cycle_two_letters`); **Steiner 1977 (no nontrivial circuit) proved, conditional on Ellison 1971** (`steiner_of_ellison`). Ingredients: `D ∣ (2^{d−1}−1)(2^{db}−3^b)`, Ellison linearised with Mathlib's `log 2` bounds, the sandwich `2^E 3^o ≤ 10^o` linearised (`1000E < 1740o`), and two kernel-checked finite checks (`decide +kernel`) |
| `Approaches/BalancedPow.lean` | review: D2 complete | averaging over cyclic windows; Lothaire 2.1.15 (⇒) for **any** gcd (`isRotated_upper'`); non-reduced mechanical words are powers (`upper_mul`, `lower_mul`); Knight's C9 for powers (`C9_lpow`, `knight_pow`); **no nontrivial positive cycle with a circularly balanced parity vector, unconditionally and for every `gcd(o,E)`** (`no_balanced_cycle_all`) |
| `Approaches/BalancedClass.lean` | review: D2, both signs | **classification of balanced cycles**: a Syracuse cycle of either sign with a circularly balanced parity vector is `1`, `−1` or `−5 → −7` (`balanced_cycle_classification`); `3^p = 2^n + 1 ⇒ (1,1),(2,3)`; `pv` injective on positive words, `pv(u ++ v) = pv u ++ pv v`; no literature input |
| `Approaches/StdPairs.lean` | review: D4 renormalisation | standard (Christoffel) pairs over `{1,2}` (`StdPair`, Stern–Brocot moves); their wedge core is `6`-smooth (`core_smooth`: `C(u,uv) = X^{|u|}C`, `C(uv,v) = Y^{len v}C`, base `−2`); **no cycle of either sign on `u^a v^b` for any standard pair** (two runs at any level of the Christoffel tree), conditional on Ellison, `E` outside Ellison's exceptions (`no_cycle_std_pair`) |
| `Approaches/StdClass.lean` | review: D4, both signs | Stern–Brocot enumeration of standard pairs with total sum ≤ 27, proved complete (`mem_gen_of_std`); kernel check of all `u^a v^b` with `E ≤ 27` (`small_check`); **the only cycle (either sign) on a standard-pair two-run word is `−5 → −7`**, given Ellison, no Barina (`std_pair_cycles`) |
| `Approaches/SignedCycles.lean` | review: D1, D4, both signs | negative two-letter runs need no window: `1000E < 1585o` (`sign_linear`) and Ellison contradict `E ≥ 28`; **the only cycle on `1^a d^b` (either sign) is `−5 → −7`** (`two_letter_cycles`); **Steiner on ℤ: the cycles with at most one gap `≥ 2` are `1, −1, −5, −7`** (`few_blocks_cycles`); rotation of a power (`rotate_bpow`) and signed power reduction (`cycle_of_pow`); level-(u,v) 2-cycles and powers, both signs, Ellison only (`two_cycle_classification`, `std_pair_pow_cycles`); one statement `closed_classes`; `−17` outside every class (`neg_seventeen_outside`) |
| `Approaches/Repeat.lean` | review: D7 | repeat identity `2^{E(u)}(x_{i+ℓ} − x_{j+ℓ}) = 3^ℓ(x_i − x_j)` and divisibility (`repeat_identity`, `repeat_dvd`); every cycle point `2^o|x||D| < 2^E 3^o` (`abs_mul_abs_D_lt`); `repeat_bound` (unconditional, either sign); Ellison linear form (`repeat_linear`); **a repeated window in a nontrivial positive cycle covers `< 51.37 %` of `E` and `< 52.79 %` of `o`**, given Ellison + Barina (`repeat_half`) |
| `Approaches/EqualTwoCycles.lean` | review: D1, Simons 2-cycles | re-bracketing `1^{k+m} d 1^m d = 1^k (1^m d)²` over the pair `(1, 1^m d)` with core `−2^{m+1}(2^{d−1} − 1)` (`core_blk`); Ellison + sign bound leave no window (`no_cycle_unequal`, either sign); **two-block cycles with equal big gaps are only `1` and `−5 → −7`** (`equal_two_blocks`); a word with two big gaps is a rotation of `1^{a₁}d₁1^{a₂}d₂` (`isRotated_two_blocks`); enlarged statement `closed_classes₂`, `−17` still outside |
| `Approaches/NearPairs.lean` | review: D4, equal big gaps | two runs `1^k (1^m d)^b` over the left spine `(1, 1^m d)` of the `{1,d}` tree; for `b ≥ 3` Ellison alone suffices, with no sign bound and no window (`no_cycle_near`); **the only cycle on `1^k (1^m d)^b` (`k, b ≥ 1`, `d ≥ 2`, either sign) is `−5 → −7`** (`near_pair_cycles`); `closed_classes₃`, `−17` still outside |
| `Approaches/DPairs.lean` | review: D4 generalised | Christoffel tree over `{1, d}` (`DPair`); its core is `−2^{i+1}3^k(2^{d−1} − 1)` (`core_dpair`); **two-run cycle words over a `d`-pair have `E < 20(d−1)`**, given Ellison (`no_cycle_dpair`); complete enumeration (`mem_genD`) and kernel check for `d = 3` close **the whole `{1,3}` tree** (`dpair_three_cycles`) |
| `Approaches/DTrees.lean` | review: D4, every `d` | letters of `d`-pairs (`DPair.letters`), counting `E + t = o + d t` (`sum_add_numBlocks`), minimal-period blocks (`numBlocks_minimal_le`), `NoMCyclesUpTo M` ⇒ few-block positive cycles trivial (`eq_one_of_numBlocks_le`); **no nontrivial positive cycle on any two-run word over any `d`-pair**, given Ellison + Simons–de Weger 2005 (`pos_dpair_cycles`; `NoMCyclesUpTo 20` suffices); negative residual: `3 ≤ t ≤ 7` equal big gaps and `E < 20(d−1)` (`neg_dpair_residual`) |
| `Approaches/NegTwoCycles.lean` | literature: Simons 2007 | negative `m`-cycles (`IsNegMCycle`); Simons 2007's sketched negative 2-cycle classification (`Simons2007Neg`, stated); **negative cycles with at most two big gaps are `−1`, `−5 → −7` or `−17`**, given Ellison + Simons 2007 (`only_known_of_few_blocks`) |
| `Approaches/DTreeChecks.lean` | review: D4, `d ≤ 7` | exponent-bounded Boolean check `pairOk`, proved sound (`pairOk_sound`); a passing tree check closes a `{1,d}` tree (`dpair_cycles_of_check`); kernel checks for `d = 4..7` (about 1 min in total); **no cycle of either sign on two-run words over `d`-pairs for `3 ≤ d ≤ 7`**, given Ellison (`dpair_cycles_le_seven`) |
| `Approaches/Trees.lean` | review: D4, any root | the tree from any root pair (`Tree`); cores `2^i 3^k C(u₀,v₀)` (`core_tree`); **effective two-run bound for arbitrary blocks**: given Ellison, a cycle on `u^a v^b` over the tree has `E < 20 log₂ \|C(u₀,v₀)\|` (`no_cycle_tree`, `no_cycle_two_blocks`); `C(1112, 114) = −3336` (`core_neg_seventeen_blocks`) |
| `Approaches/ThreeRuns.lean` | review: three-run rung | the three-core identity (`three_run_identity`) and `D(W) ∣ T_U` (`dvd_three_runs`); three letter runs `1^a d^b e^c`: no cycle once `E ≥ 11(d+e+2)` (`three_letter_runs`); **any three blocks**: no cycle once `E ≥ 20(K+2)` given the three `T`s nonzero (`three_runs_bounded`, Ellison, 81 cases by `omega`); the method stops at four runs (LP suprema, not in Lean) |
| `Approaches/FourRuns.lean` | review: four-run rung | four-core identity (`four_run_identity`), `D(W) ∣ T₁` (`dvd_four_runs`); Rhin linearised with `ℓ = ⌊log₂ o⌋ + 1` (`rhin_pow`, `log_bound`); **any four blocks**: no nontrivial positive cycle once `E ≥ 3500 + 16K`, given Simons–de Weger Lemma 12 (Rhin) and the four `T`s nonzero (`four_runs_bounded`; `2 × 256` cases by `omega` after clearing the context, about 1 min) |
| `Approaches/RunsFrontier.lean` | review: frontier | `E > 1.375·10^{11}` from Barina + Hercher Cor. 29 (`E_gt_of_lit`); a nontrivial positive cycle is not a two-run tree word, three-letter-run word, three-run or four-run word unless its block coefficients exceed about `2^{6·10^9}` (`frontier_two_runs`, `frontier_three_letters`, `frontier_three_runs`, `frontier_four_runs`) |
| `Approaches/Reach.lean` | review: limits, exact | **the exact reach of wedge-core certificates, for every `m` and cap `λ ≥ 1`**: some excluded run has all splits `≤ (1 − 1/σ_m)·max(X,Y)`, `σ_m = Σ_{i<m} λ^i` (`reach_upper`), and the bound is attained (`reach_tight`); Ellison's exponent lies strictly between `c_3` and `c_4` for `λ = log₂ 3` (`ellison_reach`) |
| `Approaches/MRuns.lean` | review: `m` runs, end to end | the cocycle telescopes over any `m` blocks (`telescope`); `D'·S(W) = X^{E₀}·T + A₀·D(W)` (`key_identity`); `D(W) ∣ T` on a cycle (`dvd_T`); rotations (`rot_cat`); **end to end for every `m`**: `(θ − c_m)·max(E, o log₂3) ≤ K + L + log₂ m` from any separation `|D| ≥ 2^{θ max − L}` (`mruns_bounded`); coefficients exist (`exists_coeffs`); Ellison as a separation (`ellison_lower`); **every `m ≤ 3`, any blocks, given Ellison** (`mruns_ellison`) |
| `Approaches/MRunsExplicit.lean` | review: `m ≤ 3`, no nonvanishing hypothesis | `2`-adic nonvanishing of `T` (`T_ne_zero`); product coefficients, `A_i − A_{i+1} = −(ΠD)·C(p_i,p_{i+1})`, bounded by `2^{6B+1}` (`Acoef_diff`, `Acoef_diff_le`); **given Ellison, `2 ≤ m ≤ 3` runs of any non-commuting blocks with all runs long: explicit bound on `E`** (`mruns_explicit`); with Barina + Hercher, no nontrivial positive cycle when the base weight is `B ≤ 10^9` (`frontier_mruns`) |
| `Approaches/MRunsDichotomy.lean` | review: `≤ 3` runs, no side conditions | orbit points read rotated words (`gapWord_iterate`); `T = 0` puts an orbit point on a base block's cycle (`T_zero_alt`); **given Ellison, a cycle on `≤ 3` runs of any blocks either has a point on a base block's cycle or a bounded `E`** (`mruns_dichotomy`); **with Barina + Hercher: no nontrivial positive cycle is a word of at most three runs over base blocks of total weight `≤ 10^9`** (`frontier_le_three`) |
| `Approaches/MRunsRhin.lean` | review: every `m`, Rhin | Rhin as a separation `|D| ≥ 2^{max − 10 − 14ℓ}` for positive cycles (`rhin_sep`); **all-`m` dichotomy** (`mruns_rhin`); `log_lin`; frontier for each `m` under a numerical condition (`frontier_rhin`); **no nontrivial positive cycle on `≤ 10` runs over base weight `≤ 5·10^7`, nor on `≤ 20` runs over base weight `≤ 6·10^5`** (`frontier_ten`, `frontier_twenty`) |
| `Approaches/MRunsSigned.lean` | review: every `m`, both signs | Rhin 1987 as an absolute linear-form bound (`Rhin1987`, stated, as quoted by Rukhin arXiv:1805.10496); separation for every word `|2^E − 3^o| ≥ 2^{max − 2 − 14ℓ}` (`rhin_sep_signed`); **all-`m` dichotomy for cycles of either sign** (`mruns_signed`) |
| `Approaches/ExplicitF.lean` | PROGRAM.md §5 / §9.1 | **explicit `f(w)` for every `m`-run word** (no cycle assumed): some rotation gives `D'S − A·D = 2^E·T` with `|T| ≤ m·2^{6B+1}·2^{c_m·max(E, o log₂3)}` (`exists_small_T`, `explicit_f`); exponent sharp by `Reach.reach_tight` |
| `Approaches/Estimators.lean` | PROGRAM.md §9.4; report §4 | **§9.4 normalised**: `S(w)` is odd and prime to 3, so `sixfree(S) = S` and `n·3^{n−1}·G_* ≤ S ≤ C·n·3^{n−1}·G_*` (`sixFree_Sz`, `abelian_estimate`); on a cycle `|x|·|D| = S` (`cycle_abelian`); window identity `2^{E(u)}x_{i+ℓ} = 3^ℓ x_i Π(1+1/(3x_k))` (`window_identity`); **cycle words are C-balanced**: `2^{E(u)} ≤ (M/m)²(1+1/(3m))^ℓ·2^{E(u')}` for windows of equal length, any positive orbit in `[m, M]` (`c_balanced`); on a cycle with the exact defect, `E(u) − E(u') ≤ 2 log₂(M/m) + (E − o log₂3)` for `ℓ ≤ o` (`window_prod_le`, `c_balanced_cycle`) |
| `Approaches/CycleLength.lean` | Eliahou 1993 method, Barina 2025 | **cycle length from Barina alone**: certified `65470613321·log 3 > 103768467013·log 2` and `10439860591·log 2 − 6586818670·log 3 > 6586818670/(3·2^71)` by the `log(1−x)` series at `1/9`, `13/256` (`log_bounds`); Farey neighbours (`farey`); every nontrivial positive cycle has `o ≥ 72 057 431 991`, `E ≥ 114 208 327 604` (`cycle_length_ge`); `CycleBounds` packages Barina-only and Hercher bounds |
| `Approaches/BarinaFrontier.lean` | run frontier without Hercher Cor. 29 | Barina-only instances of the `_of` frontier theorems: `≤ 3` runs over base weight `≤ 9.5·10^8` (Ellison), `≤ 10` runs over `≤ 5·10^7` and `≤ 20` runs over `≤ 5.5·10^5` (Rhin), two runs and three letter runs (`frontier_*_barina`) |
| `Approaches/Eliahou.lean` | Eliahou 1993 | **Eliahou's theorem proved** (`eliahou1993`, the stated `CycleLiterature.Eliahou1993`; no literature input): unimodular cones (`cone_decomp`) split at `(17087915, 10781274)` between `(85137581, 53715833)` below `log₂3` and `(301994, 190537)` above the `2^40` interval; both coordinates (`eliahou_40`); **the same form at Barina's `2^71`**: `(E, o) = a·(103768467013, 65470613321) + b·(114208327604, 72057431991) + c·(124648188195, 78644250661)`, `b ≥ 1`, `ac = 0` (`eliahou_barina`) |
| `Approaches/Terras.lean` | Terras 1976 | **Terras's theorem proved** (`terras`, the stated `CycleLiterature.Terras1976`): the first `k` parities of the `T`-orbit depend only on `n mod 2^k` (`parity_eq_of_modEq`) and determine it (`modEq_of_parity_eq`), so residues mod `2^k` ↔ parity vectors is a bijection |
| `Approaches/TwoCycles.lean` | review: level-(u,v) 2-cycles | run identity `C(u^{a₁}v, u^{a₂}v)·D(u) = C(u,v)·Y^{len v}(X^{a₁|u|}Y^{a₂ len u} − X^{a₂|u|}Y^{a₁ len u})`; on a cycle `D ∣ D(u^{a₁−a₂})`; no cycle on `u^{a₁}v u^{a₂}v` (standard pair) for `a₂ < a₁ ≤ 3a₂`, given Ellison (`no_cycle_runs`) |
| `Approaches/Frontier.lean` | review: summary | Barina ⇒ `E ≥ 45`; no positive cycle on standard-pair two-run words without exceptional-`E` hypothesis; **`frontier`**: everything a nontrivial positive cycle must satisfy (elements > 2⁷¹−1, `E ≥ 45`, sandwich, unbalanced parity vector, not two-letter-run, not standard-pair two-run, single-run bound), given Ellison + Barina |
| `Approaches/Renormalize.lean` | review: re-bracketing | `(u, u^k v)` standard; power reduction (`pos_cycle_of_pow`: a positive cycle on a rotation of `Z^g` gives one on `Z`); **no positive level-(u,v) 2-cycle `u^{a₁}v u^{a₂}v`, all `a₁, a₂ ≥ 1`** (`no_pos_two_cycle`, via `u^{a₁−a₂}(u^{a₂}v)²`); no positive cycle on `(u^a v^b)^g`; given Ellison + Barina |
| `Approaches/NearStd.lean` | review: certificate size vs length; literature frontier | **near-standard pairs**: if `C(u,Z) = 2^i 3^j c`, no cycle on `u^a Z^b` once `c²·15^E ≤ 16^E` (`no_cycle_near_std`, Ellison); **`frontier_lit`**: with Hercher 2023 and Cor. 29, a nontrivial positive cycle also has `o > 1.375·10^11` and a minimal period with `≥ 92` blocks |

## Conventions

A gap word is `w : List ℕ = (d₀, …, d_{o-1})`. The notes' `|w|` is the gap sum `E = w.sum`, and
`len w` is `o = w.length`. Write `e_k = Σ_{i<k} d_i`. Then

```
S(w) = Σ_{k<o} X^{e_k} Y^{o-1-k}      (Syracuse.S X Y w)
D(w) = X^E - Y^o                     (Syracuse.D X Y w)
```

A rotation sum is `S^{(j)} = S X Y (w.rotate j)`.

An identity proved for arbitrary `X Y` in an arbitrary commutative ring is the formal counterpart
of "certified as a `ℤ[X,Y]` identity" in the notes. The integer specialisation `(X, Y) = (2, 3)`
is `Sz`, `Dz`.

`Follows X Y w a b` says that the recurrence `X^{d_k} a_{k+1} = Y a_k + 1` carries `a` to `b` along
`w`. `syr`, `gapWord` and `IsSyrCycle` are the genuine accelerated Syracuse map on `ℤ`, so negative
cycles are included.

## Coverage

Each approach file opens with a coverage table:
note claim → Lean name → status (proved / proved conditional on a stated Prop / stated only /
empirical, not formalized / corrected).

Totals: 71 files and about 25,690 lines. The audit covers 2,675 declarations, all within
[propext, Classical.choice, Quot.sound].

**Proved here, beyond the notes' own status:**
- 1 ≤ S ≤ 3^E − 2^E (cocycle-control).
- Flying time ⇔ Collatz, as an equivalence (diophantine-distribution).
- Unconditional `finite_q` (cycle-gcd).
- The full circulant determinant, as an identity in any commutative ring.
- ℤ[1/6] is Euclidean with φ = sixFree.
- The coprime reparametrisation as a ring isomorphism.
- "Rep < 3^o ⇔ critical" as an exact equivalence (Program §5).
- **Classification of r = 1 families** with a verified, kernel-runnable decision procedure: the cycle set is finite (and computed), or the fixed point is constant and the members are powers of one cycle (R1/Decide).
- **Towers meet finitely many cycles**: every family `((u₀^{a₁}u₁)^{a₂}u₂)⋯` contains cycle words of only finitely many cycles (R1/Tower).
- **Skeleton ceilings uniform in the words**: for seven skeletons, every cycle has `D ∣ c·R'(S(βᵢ), S(σⱼ), 2^{|σⱼ|}, 3^{len σⱼ}, 2^p, 3^q)` (R1/Skel).
- Uniform classification of `w^a w'`: `C(w,w') ≠ 0` ⇒ every cycle has `D ∣ C` (finitely many); `C(w,w') = 0` ⇒ every member is a cycle iff `w` is (R1/WPow).
- Every two-run family `d^a e₁ d^a e₂ d^a` has the uniform ceiling `D ∣ R*(2^d,2^{e₁},2^{e₂},3) ≠ 0`, and is decided by finite checks (TwoRun).

**Stated, not proved:**
- The Lean names are `RhinBound`, `SdWLemma12`, `MatveevTwoThree`, `TwoRunNoGo`,
  `AlexanderClaim`, `LevinGcd` and `LevinTheorem`.
- The literature theorems in `CycleLiterature` (Steiner, Simons, Simons–de Weger, Hercher,
  Ellison, Barina) are also stated only. Eliahou 1993 and Terras 1976 were stated there too and are
  now proved (`Eliahou.eliahou1993`, `Terras.terras`).

**Out of reach, not formalized:**
- Brunswic's spacetime classification and the Teichmüller / Cauchy-compact identification.
- The Mahler-measure and Galois catalogue claims, which are computational.
- The case gcd(E, o) > 1 of the reparametrisation.
- Smith normal form.
- The statistics in RESULTS.md and the CDF plots, which are empirical.

**Claims in the notes found false or imprecise:** see [`FINDINGS.md`](FINDINGS.md).

