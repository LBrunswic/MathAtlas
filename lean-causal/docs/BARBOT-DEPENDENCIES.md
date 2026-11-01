<!-- Snapshot 2026-11-01 22:05Z by a read-only dependency audit (#print axioms + closure walk). Regenerate after each round. -->
# Barbot dependency report — node1, 2026-11-01 ~22:12 UTC

**Consistency of the view.** At 22:05:04 I copied `scaffold/CausalScaffold/Flat/` (all of it, including `Cla/`, `Geroch/`, `Lox/` and `Nonlox/`) to `/tmp/barbot-deps3/snap/` and recorded the md5 of every source and every olean. I took the md5s again at 22:12:25, after all runs. They were the same for all 77 sources and all 75 oleans, so nothing moved while the audit ran.

- **Timestamps.** Every olean is at least as new as its source. The modules being edited in this round were rebuilt by the builder that ran just before me:
  - `Cla/G9`: source 21:07, olean 22:03
  - `Cla/G9Pair`: source 21:15, olean 22:03
  - `Cla/G9PairLin`: source 21:03, olean 21:03
  - `Lox/SecondNullFix`: source 21:54, olean 21:54
  - `Loxodromic`: source 21:53, olean 22:03
  - `Classification`: source 21:17, olean 22:04
  - `GerochFlat` and `TheoremBInputs`: olean 22:04
- **Line ranges.** The declaration ranges the oleans report match the snapshot's line numbers. Each leaf's `sorry` line is the last line of its reported range.
- **This is the working tree, not HEAD.** HEAD is `c3d4f89`, and its `Flat/` equals `0436ed7`. Since then, `Cla/G9.lean`, `Classification.lean` and `Loxodromic.lean` have been modified, and `Cla/G9Pair.lean`, `Cla/G9PairLin.lean` and `Lox/SecondNullFix.lean` are untracked. The figures below include those changes.
  - At `0436ed7` the `Flat/` sources had **4** tagged `sorry`s. I counted these with `git grep`; I did not re-walk that commit. They were `[10.M]` (Loxodromic:2294), `bthm:cauclo, G9d-NE pair` (Cla/G9:2211), the smoothing step (Cla/CompactComplete:1281) and `finding 2` (Cla/CoverMGH:623).
  - The working tree closes the G9 pair.
- **Not imported.** `Flat/Abel.lean` and `Flat/Laoucapulse.lean` have no olean and no importer, and contain no `SORRY(` tag. They are not in scope.

**Scope.** All of `Flat/` is imported: 75 modules, including the 21 of `Lox/`, the 10 of `Nonlox/`, the 15 of `Cla/` and the 4 of `Geroch/`. No `Flat` module imports `CausalScaffold.CBG.*`. Which modules each closure reaches:

- **`Lox/`:** 18 of the 21 are reached by every A/B closure. `Lox.TwoNullNormalForm` is reached only by the B closures. `Lox.LevelComplete`, `Lox.QuotientComplete` and `Lox.SelbergMono` are imported but contribute no constant to any of the eleven closures.
- **`Nonlox/`:** all 10 are reached by `barbot_A₀`, `barbot_A`, `barbot_B`, `barbot_B_geroch` and `barbot_B_zero_geroch`.
- **`Cla/`:**
  - `barbot_A₀` reaches `FiniteCover`, `LTPConvex` and `TameNested`.
  - `barbot_A` reaches those three plus `LTPEnlarge`, `RegularComplete`, `UnipComplete` and `UnipEnvelope`.
  - The B closures reach `FiniteCover`, `LTPConvex`, `TameNested`, `RegularComplete` and `UnipComplete`, plus `CCComponent`, `CompactComplete`, `CoverComp`, `CoverMGH`, `G9`, `G9Pair`, `G9PairLin` and `LocallyCauchy`.
- **`Geroch/`** (all four): reached only by `barbot_B_geroch` and `barbot_B_zero_geroch`.
- **gx exports:** their closures stay among 7–15 top-level `Flat` modules (Develop, Developing, Loxodromic, Classification, etc.) and reach none of `Lox/`, `Nonlox/`, `Cla/` or `Geroch/`.

**Method.**
- Toolchain v4.31.0, mathlib v4.31.0. Every run was `taskset -c 0-11 lake env lean`.
- Files are in `/tmp/barbot-deps3/`:
  - `check.lean` / `check.out`: closure walk, leaves, statement constants, witnesses.
  - `check2.lean` / `check2.out`: `Lean.collectAxioms` on 55 names, plus a shortest path from each root to each leaf.
  - `check3.lean` / `check3.out`: every `sorryAx` user and every `axiom` declared in the 75 `Flat` modules.
  - `timestamps.tsv`, `src-md5-{before,after}.txt` and `olean-md5-{before,after}.txt`.
- The walk runs over `Environment`. It follows each declaration's type and value (opaque values included) through `Expr.getUsedConstants`, over the full transitive closure. Closure sizes are 69,431–71,194 constants for A/B and 30,126–37,706 for the gx exports.
- A **sorry leaf** is a declaration whose own type or value mentions `sorryAx`. For each leaf I counted the occurrences and their `synthetic` flag. Tags are read from `SORRY(...)` in the snapshot, over the range the olean reports.

## `#print axioms` (via `Lean.collectAxioms`)

| theorem | module : decl line | sorryAx |
|---|---|---|
| `barbot_A₀` | Classification:572 | **yes** |
| `barbot_A` | Classification:2502 | **yes** |
| `barbot_B` | Classification:2668 | **yes** |
| `barbot_B_geroch` | GerochFlat:136 | **yes** |
| `barbot_B_zero_geroch` | GerochFlat:147 | **yes** |
| `equality_of_absMax` | Classification:2692 | no (`propext`, `Classical.choice`, `Quot.sound` only) |
| `range_eq_omegaS_of_absMax` | Classification:2739 | no |
| `uniformization_injective` | Loxodromic:2106 | no |
| `uniformization_image` | Loxodromic:2113 | no |
| `uniformization_properlyDiscontinuous` | Loxodromic:2125 | no |
| `uniformization` | Loxodromic:2140 | no |

The six gx exports are **sorry-free** and have **no named external hypotheses**. No external predicate appears anywhere in their dependency closures. Their hypotheses are ordinary: `[T2Space M]`, `IsDevelopingPair`, `IsCausal`, `DevelopsCC`, the loxodromic hypothesis, and, for the two equality theorems, `IsQuotientOf`, `GH` and `AbsMax P`. `[T2Space M]` has been on the `Uniformization` section since at least `6120674`, so it is not new.

No `Flat` module declares an `axiom` (`check3`).

## Sorry leaves

The whole `Flat/` environment has **exactly 3** declarations that mention `sorryAx` (`check3`, a scan of all constants of the 75 modules). The closure walk finds the same 3, and no leaf outside `Flat/`. Each has **one** `sorryAx` occurrence, and none is synthetic: each is an explicit tagged `sorry`, not an elaboration error.

| leaf | module : lines (decl, `sorry`) | tag |
|---|---|---|
| `loxo_elementary_misner` | Loxodromic 2270–2339 (2285, 2339) | `[10.M]` |
| `Cla.exists_nonempty_isSpacelikeLipschitz_succ` | Cla/CompactComplete 1272–1281 (1277, 1281) | `bthm:cauclo, compact ⇒ complete, smoothing, d ≥ 1` |
| `Cla.maximal_of_isFiniteCover` | Cla/CoverMGH 617–623 (620, 623) | `bthm:cauclo, finding 2` |

Their obstructions, condensed from each tag's text:

- **`[10.M]`** is the Misner identification, l.3302–3330. The steps before it are proved: Γ₁ of finite index fixing `u₀`, `b ≡ 0`, and the second null direction `u₁` fixed by all of `L(Γ₁)` through `Lox.fix_second_null` (sorry-free, `Lox/SecondNullFix`). What remains:
  - a two-null-vector frame;
  - the normal form on Γ₁;
  - Bieberbach for the euclidean model of Γ₁;
  - `Ω(S̃) = Ω^±({(u₀,s₀),(u₁,s₁)})`;
  - `restrictGroup Γ' = misnerGroup L`.
- **Smoothing** means a nonempty compact spacelike-Lipschitz `H` in dimension `d + 1 ≥ 1`. Connectedness, lemma K and `d = 0` are proved.
  - Two routes were refused as circular: the cosmological time, and a Γ-invariant max of hyperboloids.
  - What is missing is an intrinsic envelope of ε-hyperboloids on `M`, its locality, and its compactness.
- **Finding 2** is the descent of a Cauchy extension of a finite cover to `M`. It goes through the Galois core, the Cauchy development and `int D(Σ)`.

**Per theorem** (shortest paths are from `check2`):

- **`barbot_A₀`: 1 leaf.**
  - `loxo_elementary_misner`, via `barbot_A₀ → caseOutput → caseOutput_misner → loxo_elementary_misner`.
- **`barbot_A`: 1 leaf, the same one,** via `barbot_A → barbot_A₀ → …`.
  - The three `[11.i]` leaves of the previous snapshot are not reached.
  - `amgh_of_isMisnerSpacetime`, `amgh_of_isCHCentralExtension` and `exists_absMax_unipotent_ltp` are all sorry-free.
- **`barbot_B`: 3 leaves.**
  - `loxo_elementary_misner`, via `barbot_A₀`.
  - `Cla.exists_nonempty_isSpacelikeLipschitz_succ`, via `barbot_B → isCauchyComplete_of_cauchyCompact → Cla.isCauchyComplete_of_isCompact_cauchy → Cla.exists_isSpacelikeLipschitz_of_isCompact_cauchy → …`.
  - `Cla.maximal_of_isFiniteCover`, via `barbot_B → cauclo_from_embedding → Cla.mgh_cauchyCompact_of_isFiniteCover → Cla.mgh_of_isFiniteCover → …`.
- **`barbot_B_geroch`: the same 3 leaves,** one step longer through `barbot_B`. `flatGerochGH` and everything in `Geroch/` add none.
- **`barbot_B_zero_geroch`: the same 3 leaves,** via `barbot_B_zero → barbot_B_of_externals → barbot_B → …`.

**Syntactic versus logical at `d = 0`.** `#print axioms` is syntactic. In the source, two of the three leaves are reached only through a `succ` branch of a `cases d`:

- `loxo_elementary_misner` is reached only in `caseOutput`'s `| succ d' =>` (Classification:529–531). The `| zero =>` branch refutes the loxodromic case with `not_isHyperbolic_zero`.
- `exists_nonempty_isSpacelikeLipschitz_succ` is reached only in `exists_isSpacelikeLipschitz_of_isCompact_cauchy`'s `| succ d =>` (Cla/CompactComplete:1297). `d = 0` is closed there by a point.

So at `d = 0`, `barbot_A₀` and `barbot_A` are logically sorry-free, and `barbot_B_zero_geroch` logically rests on `Cla.maximal_of_isFiniteCover` alone. That lemma's path (`cauclo_from_embedding:2653 → mgh_cauchyCompact_of_isFiniteCover → mgh_of_isFiniteCover`) has no dimension split. Making this visible to `#print axioms` would need `d = 0` restatements, which have not been written.

**Altogether there are 3 distinct sorry leaves: 1 in Loxodromic, 1 in Cla/CompactComplete and 1 in Cla/CoverMGH.** Classification, Nonloxodromic, TitsNull, GerochFlat, TheoremBInputs, `Lox/*`, `Nonlox/*`, `Geroch/*` and the other `Cla/*` files have none.

### Since the previous snapshot (11:06Z, 12 leaves)

`collectAxioms` is clean on every one of these:

- **Closed:**
  - `exists_finiteCover_tameEmbedding`
  - `nonloxodromic_parabolic_convex`
  - `nonloxodromic_parabolic`
  - `nonloxodromic_elliptic` (`[9.E]`)
  - `exists_commute_screenRot_of_discrete` (TitsNull)
  - `loxo_generic_centralExtension` (`[10.G]`)
  - `bprop_LU_discrete`
  - `amgh_of_isMisnerSpacetime`
  - `amgh_of_isCHCentralExtension`
  - `exists_absMax_unipotent_ltp`
  - `isLocallyCauchyTwoSided_image`
  - `caseOutput_nonloxodromic`
  - `absMax_of_cauchyCompact_of_mgh`
  - `Cla.false_of_cauchyCompact_of_fixed_pair` (closed in the working tree only, by the untracked `G9Pair` and `G9PairLin`)
  - `Cla.exists_modelB_cover_of_isLTPOver_cauchyCompact`
  - `titsVirtuallyAbelianNull`, now sorry-free for **every** `d`
- **No `sorry` in their own body, but they inherit one:**
  - `isCauchyComplete_of_cauchyCompact` inherits the smoothing leaf.
  - `cauclo_from_embedding` and `Cla.mgh_cauchyCompact_of_isFiniteCover` inherit finding 2.
  - `caseOutput` and `caseOutput_misner` inherit `[10.M]`.
- **Still open:** `[10.M]`, which has moved forward by one step (`Lox.fix_second_null`).
- **New leaves:** the two `Cla/` leaves. They are the residue of the old Classification leaves `isCauchyComplete_of_cauchyCompact` and `cauclo_from_embedding`.

## Named external hypotheses in the statements

The constants of each statement were extracted mechanically from its type.

| theorem | named externals in its statement |
|---|---|
| `barbot_A₀`, `barbot_A` | `BarbotExternals d` only |
| `barbot_B` | `BarbotExternals d`, `SelbergLemma (Minkowski d)`, `∀ N : FlatSpacetime.{0} d, GH N → FlatLemmaKData N` |
| `barbot_B_geroch` | `BarbotExternals d`, `SelbergLemma (Minkowski d)` (`hK` discharged) |
| `barbot_B_zero_geroch` | **none** |
| the 6 gx exports | none |

**One internal lemma changed its statement (working tree).** `loxo_elementary_misner` now takes `hBieb : ∀ k ≤ d' + 1 + 1, BieberbachI (EuclideanSpace ℝ (Fin k))`. This follows the master ruling of 2026-11-01: the conclusion implies Bieberbach I.

- `hBieb` is consumed by `Lox.fix_second_null (hBieb d' _)` (Loxodromic:2331).
- `caseOutput` supplies it as `hE.bieberbach`, at `d = d' + 1`, so its bound `k ≤ d + 1` matches `BarbotExternals.bieberbach` exactly.
- This is the "one call site in Classification" (lines 497, 502, 531). No top-level statement gains a hypothesis.

## Where each external is defined, and whether a non-vacuity witness exists

Every witness named here is sorry-free under `collectAxioms`.

| external | defined | non-vacuity witness |
|---|---|---|
| `BarbotExternals d` (structure: `benoist` k ≤ d, `bieberbach` k ≤ d+1, `auslander` k ≤ d, `unipotent` k ≤ d) | Classification:310 | `barbotExternals_zero` (Classification:325), for d = 0 only. Joint witness for Theorem A: `barbot_A_hypotheses_zero` (Classification:586). **For d ≥ 1 there is none**: the bundle is consistent only on the literature. |
| ↳ `BenoistNoLox` | Externals:526 | `benoistNoLox_zero`. Not trivially true: `not_benoist_conclusion_stdBoost` (Externals:584). |
| ↳ `BieberbachI E` | Bieberbach:685 | `bieberbachI_of_finrank_le_one`, `bieberbachI_euclideanSpace_fin_one`, `bieberbachI_of_finite`. Not trivially true: `not_isDiscreteEucl_euclTranslations` (Bieberbach:620). |
| ↳ `AuslanderCarriereDalbo` | Externals:276 | `auslanderCarriereDalbo_zero` (Externals:296) |
| ↳ `MaxUnipotentSubspace` | Externals:315 | `maxUnipotentSubspace_zero`. Not trivially true: `not_maxUnipotent_conclusion_top` (Externals:370). |
| `SelbergLemma V` | Externals:825 | `selbergLemma_real`. **New:** `selbergLemma_minkowski_zero : SelbergLemma (Minkowski 0)` (TheoremBInputs:316), by transport (`selbergLemma_of_linearEquiv` :307, `selbergLemma_of_injective_hom` :296). Monotone downward: `Lox.selbergLemma_minkowski_of_le` (Lox/SelbergMono:90). **For d ≥ 1 there is none** (Selberg in `GL_{n≥2}(ℝ)` is not in mathlib). Not trivially true: `not_selberg_conclusion_torsion` (Externals:917). |
| `FlatLemmaKData N` | Classification:340 | Pointwise: `flatLemmaKData_minkowskiSpace` (:351), `flatLemmaKData_torusSpace`, `CauchyCompact.flatLemmaKData` (TheoremBInputs:272), `flatLemmaKData_of_barbotGH`. **The universal form `∀ N, GH N → FlatLemmaKData N` that `barbot_B` takes is now a theorem in every d**: `flatLemmaKData_of_flatGerochGH flatGerochGH` (TheoremBInputs:246, GerochFlat:130), or `forall_flatLemmaKData_iff.2 flatGerochGH` as used in `barbot_B_geroch`. There is no standalone named theorem for the universal form. |
| `FlatGerochGH d` (`∀ N, GH N → BarbotGH N`) | TheoremBInputs:238 | **PROVED (DEC-65)**: `flatGerochGH` (GerochFlat:130), sorry-free, universe-polymorphic, every d. It goes through `flatAdmissibleMeasures` (GerochFlat:121, `FlatAdmissibleMeasures` TheoremBInputs:254) and `flatGerochGH_of_admissible` (ETT's `geroch_i_imp_iii`). Both are clean. |
| `LimitSetMinimal` | Externals:647 | `limitSetMinimal_zero`; not trivially true: `not_limitSet_conclusion_stdBoostL` (Externals:792). **It appears in no main statement and in none of the 11 closures.** |
| `AbelianPairAsPrinted` | Externals:995 | **In none of the 11 closures.** |
| `TitsVirtuallyAbelianNull` | Nonloxodromic:1711 | **Not a hypothesis (DEC-50), and now proved outright**: `titsVirtuallyAbelianNull : ∀ d` (TitsNull:1565) is sorry-free for every d, so it is no longer "sorry through TitsNull" as in the previous snapshot. It is in the closures of the five A/B theorems as a proved lemma, consumed by `caseOutput_nonloxodromic`. |

**Externals in the closures.**

- `barbot_A₀` and `barbot_A`: `BarbotExternals` and its 4 components, plus `TitsVirtuallyAbelianNull` (proved).
- `barbot_B`: the same, plus `SelbergLemma` and `FlatLemmaKData`.
- `barbot_B_geroch` and `barbot_B_zero_geroch`: the same as `barbot_B`, plus `FlatGerochGH`, `FlatAdmissibleMeasures` and `BarbotGH`. All three are discharged by proved theorems.
- The gx exports: none.

## Vacuity caveats

- **Theorem A (`barbot_A₀`, `barbot_A`).**
  - The hypotheses are jointly satisfiable at d = 0 by `barbot_A_hypotheses_zero`: the bundle, plus GH and Cauchy-completeness of 𝐌¹.
  - In every d, the spacetime hypotheses hold for `minkowskiSpace d` (`gh_minkowskiSpace` FlatSpacetime:737, `isCauchyComplete_minkowskiSpace` CauchyComplete:840).
  - So the only obstruction for d ≥ 1 is `BarbotExternals d`, which has no witness.
- **`barbot_B`.**
  - **`hK` is no longer a vacuity risk.** Its universal form is the theorem `flatLemmaKData_of_flatGerochGH flatGerochGH` in every d. It is consumed by the proved `absMax_of_cauchyCompact_of_mgh` and `Cla.mgh_cauchyCompact_of_isFiniteCover`.
  - The hypothesis set **is shown jointly satisfiable at d = 0** by `barbot_B_hypotheses_satisfiable` (TheoremBInputs:376), which is sorry-free. It gives `BarbotExternals 0`, `SelbergLemma (Minkowski 0)`, and `torusSpace 0` (`FlatSpacetime.{0}`, Examples:1000) being GH, Cauchy-compact and MGH and carrying lemma K's data. Take `u := 0`.
  - In every d, `torusSpace d` satisfies GH, Cauchy-compact and MGH (`gh_torusSpace`, `cauchyCompact_torusSpace`, `mgh_torusSpace`).
  - For d ≥ 1, `BarbotExternals d` and `SelbergLemma (Minkowski d)` have no witness.
  - **`hSel` is now genuinely consumed.** It goes through `cauclo_from_embedding` into G9's Selberg step (`Cla.exists_modelB_cover_of_isLTPOver_cauchyCompact` → `exists_torusProduct_cover_of_fg` → `exists_finiteIndex_torsionFree_linOf`, Cla/G9:1805). This was not true in the previous snapshot, where `hSel` reached only a sorried lemma.
  - The binder in `cauclo_from_embedding` is still spelled `_hSel` (Classification:2607), which now wrongly suggests it is unused. This is cosmetic.
- **`barbot_B_geroch`** takes `hE`, `hSel`, and `M` GH, Cauchy-compact and MGH.
  - **Its hypothesis set is shown satisfiable at d = 0.** The witnesses are `barbotExternals_zero`, `selbergLemma_minkowski_zero` and `M := torusSpace 0` (with `gh_torusSpace`, `cauchyCompact_torusSpace`, `mgh_torusSpace`). These are exactly the components of `barbot_B_hypotheses_satisfiable` minus the lemma-K data that `barbot_B_geroch` no longer takes.
  - No single theorem packages the set under `barbot_B_geroch`'s own name.
  - For d ≥ 1 the spacetime part is satisfiable (`torusSpace d`), and the two bundles are the only gap.
- **`barbot_B_zero_geroch`** has no named external. Its hypotheses are satisfied by `torusSpace 0`, so it is non-vacuous outright. Its remaining debt is the three leaves syntactically, and `Cla.maximal_of_isFiniteCover` logically.
- **`FlatGerochGH`, read correctly.** Under Barbot's own GH (l.498–507), this statement is a tautology. What `flatGerochGH` proves is ETT's GH (causal + compact diamonds) ⇒ a Cauchy surface. That is the real content, and it is sorry-free.

## Findings for the master session (docstring contract, kb/0006)

`Classification.lean`'s docstrings are **stale** against this measurement. The affected spots are the module docstring at l.25–28, l.174–179 and l.190–200, and `cauclo_from_embedding`'s docstring at l.2598–2606. They say:

- Theorem A rests on **two** leaves, `loxo_elementary_misner` and `bprop_LU_discrete`. Measured: **one**. `bprop_LU_discrete` is clean.
- Theorem B rests on **five**, including `Cla.exists_isSpacelikeLipschitz_of_isCompact_cauchy` and `Cla.false_of_cauchyCompact_of_fixed_pair`. Measured: **three**.
  - `false_of_cauchyCompact_of_fixed_pair` is clean in the working tree.
  - The smoothing leaf is `Cla.exists_nonempty_isSpacelikeLipschitz_succ` (CompactComplete:1277). `exists_isSpacelikeLipschitz_of_isCompact_cauchy` (:1289) is its sorry-free-bodied consumer, not a leaf.
- L11 `Cla.G9` has "one `sorry`". G9's own docstring (l.102) correctly says "No `sorry`".

Classification belongs to another agent in this run, apart from the one call site, so I report this here rather than editing it. The SCOPE sections of `Loxodromic` ("Sorries (1)", l.174), `Cla/CompactComplete` (l.45) and `Cla/CoverMGH` (l.63) agree with the measurement.