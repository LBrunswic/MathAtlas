<!-- Snapshot 2026-11-01 11:06Z by a read-only dependency audit (#print axioms + closure walk). Regenerate after each round. -->
# Barbot dependency report — node1, 2026-11-01 ~11:10 UTC

**Consistency of the view.** I snapshotted `scaffold/CausalScaffold/Flat/` (with `Lox/` and `Nonlox/`) to `/tmp/barbot-deps/snap/` at 11:06. All 4 edited modules (Classification, Loxodromic, Nonloxodromic, TitsNull) have source md5 equal to the snapshot. Every olean is newer than its source: the oleans were built 10:53, and the sources were last touched between 07:42 and 10:45. The olean md5s were the same before and after the runs. The declaration ranges the oleans report match the snapshot's line numbers exactly, so the oleans and the snapshot describe the same code.

**Out of scope.** `Flat/Lox/*` (9 files) and `Flat/Nonlox/*` (8 files, no oleans yet) are **not imported** by Classification, Loxodromic, Nonloxodromic or TitsNull. They do not reach any theorem below. `Flat/Cla/` does not exist.

**Method.** Toolchain v4.31.0, mathlib v4.31.0. The files are `check.lean`, `check2.lean` and `check3.lean`, with outputs in `*.out`, and `tags.py`. The traversal runs over `Environment`: it walks each declaration's type and value through `Expr.getUsedConstants` over the full closure (30k–59k constants). A declaration counts as a "sorry leaf" when its own type or value mentions `sorryAx` directly. Tags are read from `SORRY(...)` in the snapshot over the declaration range the olean reports. Each leaf contains exactly one `sorry` term.

## `#print axioms`

| theorem | sorryAx |
|---|---|
| `barbot_A₀` | **yes** |
| `barbot_A` | **yes** |
| `barbot_B` | **yes** |
| `equality_of_absMax` | no (propext, choice, Quot.sound only) |
| `range_eq_omegaS_of_absMax` | no |
| `uniformization_injective` | no |
| `uniformization_image` | no |
| `uniformization_properlyDiscontinuous` | no |
| `uniformization` | no |

The six exports to the gx side (the two equality theorems and the four uniformization theorems) are **sorry-free**, have **no named external hypotheses**, and no external predicate appears anywhere in their dependency closure.

## Sorry leaves

There are 6 shared leaves. They are the leaves of `barbot_A₀`, and `barbot_A` and `barbot_B` inherit all of them:

| leaf | module : lines | tag |
|---|---|---|
| `exists_finiteCover_tameEmbedding` | Classification 463–473 | `bthm:caucomp, finite cover` |
| `nonloxodromic_parabolic_convex` | Classification 360–375 | `[9.P]–[9.A], convexity` |
| `nonloxodromic_elliptic` | Nonloxodromic 2586–2599 | `[9.E]` |
| `exists_commute_screenRot_of_discrete` | TitsNull 568–576 | `TitsVirtuallyAbelianNull/Auslander` (reached through `titsVirtuallyAbelianNull`, which `caseOutput` uses; the `d ≤ 2` variant is sorry-free) |
| `loxo_elementary_misner` | Loxodromic 2154–2177 | `[10.M]` |
| `loxo_generic_centralExtension` | Loxodromic 2522–2535 | `[10.G]` |

**barbot_A₀:** 6 leaves, exactly the shared ones.

**barbot_A:** 9 leaves, the 6 shared ones plus:

| leaf | module : lines | tag |
|---|---|---|
| `amgh_of_isMisnerSpacetime` | Classification 1938–1955 | `[11.i], Misner, Cauchy-completeness` |
| `amgh_of_isCHCentralExtension` | Classification 2296–2312 | `[11.i], family (b), Cauchy-completeness` |
| `exists_absMax_unipotent_ltp` | Classification 2314–2324 | `[11.i] unipotent, G1 + G3` |

(`amgh_of_isTranslationSpacetime` is sorry-free.)

**barbot_B:** 9 leaves, the 6 shared ones plus:

| leaf | module : lines | tag |
|---|---|---|
| `isCauchyComplete_of_cauchyCompact` | Classification 2424–2429 | `bthm:cauclo, compact ⇒ complete` |
| `cauclo_from_embedding` | Classification 2435–2447 | `bthm:cauclo, G9` |
| `isLocallyCauchyTwoSided_image` | Classification 2374–2380 | `clomax, lemma K input` (reached through `absMax_of_cauchyCompact_of_mgh`) |

`barbot_B` does **not** depend on the three `[11.i]` leaves of `barbot_A`, because it goes through `barbot_A₀` and not through `barbot_A`.

Altogether there are **12 distinct sorry leaves**: 8 in Classification, 2 in Loxodromic, 1 in Nonloxodromic and 1 in TitsNull.

## Named external hypotheses in the statements

The constants in each statement were extracted mechanically from its type:

| theorem | named externals in its statement |
|---|---|
| `barbot_A₀`, `barbot_A` | `BarbotExternals d` only |
| `barbot_B` | `BarbotExternals d`, `SelbergLemma (Minkowski d)`, `∀ N : FlatSpacetime.{0} d, GH N → FlatLemmaKData N` |
| the 6 gx exports | none (only `IsDevelopingPair`, `IsCausal`, `DevelopsCC`, the loxodromic hypothesis, and for the equality theorems `IsQuotientOf`/`GH`/`P B`/`AbsMax`, which are ordinary hypotheses) |

## Where each external is defined, and whether a non-vacuity witness exists

All the witnesses named below are sorry-free under `#print axioms`.

| external | defined | non-vacuity witness |
|---|---|---|
| `BarbotExternals d` (structure: `benoist`, `bieberbach` (k ≤ d+1), `auslander`, `unipotent`, each ∀ k ≤ d) | Classification:253 | `barbotExternals_zero` (d = 0 only). The joint witness is `barbot_A_hypotheses_zero` (bundle + GH + Cauchy-complete for 𝐌¹). For d ≥ 1 there is none: the bundle is consistent only on the literature. |
| ↳ `BenoistNoLox` | Externals:526 | `benoistNoLox_zero`; not-trivially-true: `not_benoist_conclusion_stdBoost` (Externals:584) |
| ↳ `BieberbachI E` | Bieberbach:685 | `bieberbachI_of_finrank_le_one`, `bieberbachI_euclideanSpace_fin_one`, `bieberbachI_of_finite`; not-trivially-true: `not_isDiscreteEucl_euclTranslations` (Bieberbach:620) |
| ↳ `AuslanderCarriereDalbo` | Externals:276 | `auslanderCarriereDalbo_zero` |
| ↳ `MaxUnipotentSubspace` | Externals:315 | `maxUnipotentSubspace_zero`; not-trivially-true: `not_maxUnipotent_conclusion_top` (Externals:370) |
| `SelbergLemma V` | Externals:825 | **only `selbergLemma_real : SelbergLemma ℝ`**. There is no witness for `SelbergLemma (Minkowski d)` at any d. `Minkowski d := ℝ × EuclideanSpace ℝ (Fin d)` (Causal/Minkowski.lean:72), so even d = 0 needs a transport that has not been written. Not-trivially-true: `not_selberg_conclusion_torsion` (Externals:917). |
| `FlatLemmaKData N` | Classification:281 | `flatLemmaKData_minkowskiSpace` covers **one spacetime only**. No theorem proves the universally quantified form `∀ N, GH N → FlatLemmaKData N` that `barbot_B` takes, at any d. Its `flow` field is noted as a tagged sorry for general flat spacetimes (Splitting.lean). |
| `LimitSetMinimal` | Externals:647 | `limitSetMinimal_zero`, `not_limitSet_conclusion_stdBoostL`. **It appears in no main statement and in none of the 9 closures.** |
| `TitsVirtuallyAbelianNull` | Nonloxodromic:1678 | **Not a hypothesis anymore (DEC-50)**: it is proved internally by `titsVirtuallyAbelianNull` (∀ d, sorry through the TitsNull leaf above), which is sorry-free for d ≤ 2 (`titsVirtuallyAbelianNull_of_le_two`), with `titsVirtuallyAbelianNull_zero` as witness. It is in the closures of `barbot_A₀`, `barbot_A` and `barbot_B`. |

**Externals in the closures.** For `barbot_A₀` and `barbot_A`: `BarbotExternals` and its 4 components, plus `TitsVirtuallyAbelianNull`. For `barbot_B`: the same, plus `SelbergLemma` and `FlatLemmaKData`. For the gx exports: none.

**Vacuity caveat for `barbot_B`.** Theorem A's hypotheses are shown jointly satisfiable at d = 0. **Theorem B's are not shown satisfiable at any d**: no `SelbergLemma (Minkowski d)` witness exists, and no witness of `∀ N, GH N → FlatLemmaKData N` exists. Also, `hSel` reaches only the sorry'd `cauclo_from_embedding`, whose argument is `_hSel` and so unused. `hK` is consumed by the proved `absMax_of_cauchyCompact_of_mgh`.
