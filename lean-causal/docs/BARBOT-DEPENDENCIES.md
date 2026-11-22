<!-- Snapshot 2026-11-02 08:55Z–09:04Z by a read-only dependency audit (#print axioms + closure walk). Regenerate after each round. -->
# Barbot and CBG dependency report — node1, 2026-11-02 ~09:05 UTC

**HEAD `167852c`.** The Lean content audited is the same at `70b7662`, where the audit started, and at `167852c`, where it ended. The four commits in between (`a995237`, `a7f3306`, `ad29f7c`, `167852c`) touch only `lean-gx/` and `registers/` (DEC-74…78). The last commit that touched `lean-causal/Causal`, `lean-causal/scaffold` or `Causal.lean` is `f84b69e` (DEC-64). Against HEAD, `lean-causal/` has no modified tracked file. Its only untracked file is `campaign/CURATION-DRAFT.toml`, which is not Lean.

**Consistency of the view.**
- **No file moved during the audit.** At 08:55:49Z I recorded the md5 of all 153 `.lean` sources under `Causal/` and `scaffold/` and of all 154 oleans. I took them again at 09:04:04Z, after all runs, and they were identical.
- **The build is current.** `lake build --no-build Causal CausalScaffold` printed "All targets up-to-date (3677 jobs)" and wrote nothing.
  - 26 ETT sources (`Causal/Causality.lean` …) have an mtime newer than their olean. Their mtime is 07:03, from the Dropbox sync. Lake compares hashes, not mtimes, so these are not stale.
- **`python3 scripts/sorry_count.py`:**
  - strict: **0 `sorry` in 147 files**;
  - scaffold: 5 in 5 files (`CompactCauchy` 1, `GerochEquiv` 1, `MinkowskiMeasure` 1, `SubExtension` 2).

**Scope.** The environment is `import Causal` plus `import CausalScaffold`: 152 modules that contribute constants, 147 strict and 5 scaffold, and 10,588 of our constants.
- **Barbot.** All of `Causal/Flat/` is strict: 89 modules.
  - 31 at the top level;
  - `Lox/` 25, `Nonlox/` 10, `Cla/` 19, `Geroch/` 4.
- **CBG.** `Causal/CBG/` (11 modules) and `Causal/Flat/CBG{,Compact,Germ,Slice}` are strict.
- **Scaffold.** On the Barbot side, the only item is `CausalScaffold.CompactCauchy`, the bare lemma K.

**Method.**
- **Toolchain.** Lean v4.31.0, mathlib `fabf563a`. Every run was `taskset -c 0-11 lake env lean`.
- **Files.** All are in `/tmp/barbot-deps4/`:
  - `check.lean` / `check.out`: for each root, `Lean.collectAxioms`, the transitive closure, its leaves, its statement constants, its `Prop` binders and the modules it reaches. Also a scan of all 10,588 constants for `sorryAx` users and `axiom` declarations, a reverse scan for users of the bare lemma K and for strict→scaffold edges, and a scan for witnesses (theorems whose conclusion is an external predicate).
  - `check2.lean` / `check2.out`: `collectAxioms` on the not-trivially-true witnesses and the CBG instances, plus a scan for any theorem that concludes `¬ <external>`.
  - `check3.lean` / `check3.out`: `collectAxioms` on the three former leaves and their consumers.
  - `src-md5-{before,after}.txt` and `olean-md5-{before,after}.txt`.
- **The walk.** It runs over `Environment`. For each declaration it follows the type and the value (opaque values included) through `Expr.getUsedConstants`, over the full transitive closure.
- **Sorry leaves.** A sorry leaf is a declaration whose own type or value mentions `sorryAx`.
- **Roots, 23:**
  - Theorem A: `barbot_A₀`, `barbot_A`;
  - Theorem B: `barbot_B`, `barbot_B_geroch`, `barbot_B_zero_geroch`, `barbot_B_zero`, `barbot_B_of_externals`;
  - CBG: `Causal.CBG.cbg`, `cbg_of_hasTimeFunctions`, `flat_cbg`, `flat_cbg_gh`, `flat_cbg_of`, `flat_cbg_gh_of`;
  - the gx exports: `equality_of_absMax`, `range_eq_omegaS_of_absMax`, the four `uniformization_*`, `flatGerochGH`;
  - lemma K: the proved forms `isCauchySurface_of_isLocallyCauchyTwoSided` and `…_of_pushUp`, and the bare `isCauchySurface_of_isLocallyCauchy`.

## `#print axioms` (via `Lean.collectAxioms`)

| root | module : decl line | closure | axioms |
|---|---|---|---|
| `Causal.Flat.barbot_A₀` | Flat/Classification:598 | 69,563 | `propext`, `Classical.choice`, `Quot.sound` |
| `Causal.Flat.barbot_A` | Flat/Classification:2528 | 70,533 | same |
| `Causal.Flat.barbot_B` | Flat/Classification:2693 | 71,080 | same |
| `Causal.Flat.barbot_B_geroch` | Flat/GerochFlat:136 | 71,288 | same |
| `Causal.Flat.barbot_B_zero_geroch` | Flat/GerochFlat:147 | 71,455 | same |
| `Causal.Flat.barbot_B_zero` | Flat/TheoremBInputs:358 | 71,257 | same |
| `Causal.Flat.barbot_B_of_externals` | Flat/TheoremBInputs:337 | 71,092 | same |
| `Causal.CBG.cbg` | CBG/Maximal:1093 | 15,869 | same |
| `Causal.CBG.cbg_of_hasTimeFunctions` | CBG/Maximal:1103 | 15,871 | same |
| `Causal.CBG.flat_cbg` | Flat/CBG:875 | 53,916 | same |
| `Causal.CBG.flat_cbg_gh` | Flat/CBG:887 | 53,946 | same |
| `Causal.CBG.flat_cbg_of` / `flat_cbg_gh_of` | Flat/CBG:843 / 860 | 53,777 / 53,807 | same |
| `Causal.Flat.equality_of_absMax` | Flat/Classification:2717 | 30,126 | same |
| `Causal.Flat.range_eq_omegaS_of_absMax` | Flat/Classification:2764 | 33,201 | same |
| `Causal.Flat.uniformization_injective` | Flat/Loxodromic:2122 | 33,137 | same |
| `Causal.Flat.uniformization_image` | Flat/Loxodromic:2129 | 35,888 | same |
| `Causal.Flat.uniformization_properlyDiscontinuous` | Flat/Loxodromic:2141 | 37,691 | same |
| `Causal.Flat.uniformization` | Flat/Loxodromic:2156 | 37,706 | same |
| `Causal.Flat.flatGerochGH` | Flat/GerochFlat:130 | 52,590 | same |
| `Causal.Causality.isCauchySurface_of_isLocallyCauchyTwoSided` (lemma K, proved) | CompactCauchy:733–788 | 17,652 | same |
| `…isLocallyCauchyTwoSided_of_pushUp` | LemmaKBare:480–493 | 17,822 | same |
| `Causal.Causality.isCauchySurface_of_isLocallyCauchy` (**bare lemma K, scaffold**) | CausalScaffold/CompactCauchy:55 | 5,206 | **`sorryAx`** |

**22 of the 23 roots are axiom-clean.** The exception is the bare lemma K, which is a scaffold stub tagged `SORRY(DEC-44)` by design.

None of the 152 modules declares an `axiom`. No closure contains a constant from a `CausalScaffold` module, except the bare lemma K's closure, which contains the stub itself. No strict declaration uses a scaffold constant, and nothing uses the bare lemma K.

## Sorry leaves

**There are no sorry leaves in any Barbot, CBG or gx-export closure.** Each closure was walked in full, and none contains a declaration that mentions `sorryAx`.

The whole environment has exactly **5** `sorryAx` users. All five are in the scaffold, and none is in any of the 22 clean closures.

| declaration | module : range | paper | reached by |
|---|---|---|---|
| `Causal.Causality.isCauchySurface_of_isLocallyCauchy` | CausalScaffold/CompactCauchy 46–60 | DEC-44, bare lemma K (Barbot side) | nothing (no user in the environment) |
| `Causal.Causality.geroch_iii_imp_i` | CausalScaffold/GerochEquiv 69–75 | ETT | none of the roots |
| `Causal.minkowski_exists_measure` | CausalScaffold/MinkowskiMeasure 71–78 | ETT (its statement is proved in strict as `minkowski_frontier_null_measure`, DEC-65) | none of the roots |
| `Causal.IsCauchyEmbedding.exists_mem_image_inf` | CausalScaffold/SubExtension 77–86 | ETT, `lem:C_ext_connexe` (DEC-73 remainder) | none of the roots |
| `Causal.cauchy_pgcd` | CausalScaffold/SubExtension 116–124 | ETT, `prop:Cauchy_pgcd` (DEC-73 remainder) | none of the roots |

**Since the previous snapshot** (2026-11-01 22:05Z, working tree over `c3d4f89`, 3 leaves), all three leaves are now clean under `collectAxioms` (`check3`):

| former leaf | where it is now | consumers, also clean |
|---|---|---|
| `[10.M]` `loxo_elementary_misner` | Loxodromic:3212 | `caseOutput_misner` (Classification:518), `caseOutput` (:544); it still carries `hBieb`, supplied by `BarbotExternals.bieberbach` |
| smoothing, `Cla.exists_nonempty_isSpacelikeLipschitz_succ` | Cla/CompactComplete:1310 | `isCauchyComplete_of_cauchyCompact` (Classification:2616) |
| finding 2, `Cla.maximal_of_isFiniteCover` | Cla/CoverMGH:624 | it goes through `Cla.cover_maximal_of_isFiniteCover` (Cla/CoverMax:763), and is consumed by `Cla.mgh_cauchyCompact_of_isFiniteCover` (:648) and `cauclo_from_embedding` (Classification:2632) |

The previous report's "syntactic versus logical at `d = 0`" caveat is therefore **moot**: there is no `sorry` left to route around.

**Module reach**, from `check` MODS:

- **`barbot_A₀`:** 79 of our modules: 23 top-level `Flat`, 22 of the 25 `Lox/`, 10 `Nonlox/` and 3 `Cla/` (`FiniteCover`, `LTPConvex`, `TameNested`).
- **`barbot_A`:** 84 modules. Adds `Cla.LTPEnlarge`, `RegularComplete`, `UnipComplete` and `UnipEnvelope`.
- **`barbot_B`:** 97 modules.
  - 17 of the 19 `Cla/`; all except `LTPEnlarge` and `UnipEnvelope`. These include `CoverMax` and `SmoothCap`/`SmoothCone`/`SmoothGlue`.
  - `Geroch.Reach`.
  - `Causal.CompactCauchy`, the proved lemma K.
- **`barbot_B_geroch` and `barbot_B_zero_geroch`:** 107 modules. Add all 4 `Geroch/` and `GerochFlat`.
- **The CBG roots:**
  - `cbg` and `cbg_of_hasTimeFunctions`: 30 modules, 10 of them in `Causal.CBG`, and no `Flat` module.
  - `flat_cbg` and `flat_cbg_gh`: 64–65 modules (`Flat/CBG*`, the 4 `Geroch/`), and no `Lox/`, `Nonlox/` or `Cla/`.
- **The gx exports:** 21–38 modules, among 7–15 top-level `Flat` modules, plus `Geroch/` for `flatGerochGH`. They reach no `Lox/`, `Nonlox/` or `Cla/`.
- **Reached by no root:** `Flat/Abel`, `Flat/Laoucapulse`, `Lox.LevelComplete`, `Lox.QuotientComplete` and `Lox.SelbergMono`. All five are imported by `Causal.lean` and sorry-free.

## Named external hypotheses carried by each theorem

"Named external" means a cited theorem of the literature that enters as a hypothesis under DEC-36 and kb/0012. **These are NOT proved, by design, and a sorry-free `#print axioms` does not discharge them.** Theorems A and B are formalized *conditionally on them*, and are marked under DEC-72 with the externals disclosed.

| theorem | named externals in its statement (`Prop` binders, read mechanically) | other hypotheses |
|---|---|---|
| `barbot_A₀`, `barbot_A` | **`hE : BarbotExternals d`** | `GH M`, `IsCauchyComplete d M` |
| `barbot_B` | **`hE : BarbotExternals d`**, **`hSel : SelbergLemma (Minkowski d)`**, `hK : ∀ N : FlatSpacetime.{0} d, GH N → FlatLemmaKData N` | `GH M`, `CauchyCompact M`, `MGH M` |
| `barbot_B_of_externals` | **`hE`**, **`hSel`**, `hGer : FlatGerochGH d` | same |
| `barbot_B_geroch` | **`hE`**, **`hSel`** (`hK` discharged by `flatGerochGH`) | same |
| `barbot_B_zero` | `hGer : FlatGerochGH 0` only (the externals are discharged at `d = 0`) | same |
| `barbot_B_zero_geroch` | **none** | same, at `d = 0` |
| `cbg`, `flat_cbg`, `flat_cbg_gh`, `flat_cbg_of`, `flat_cbg_gh_of` | **none** | see CBG below |
| `equality_of_absMax`, `range_eq_omegaS_of_absMax`, `uniformization_*`, `flatGerochGH` | **none** | ordinary geometric hypotheses (`IsDevelopingPair`, `DevelopsCC`, `IsCausal`, `IsQuotientOf`, `GH B`, `P B`, `AbsMax P M`, `∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)`, `[T2Space M]`) |

The `BarbotExternals d` structure (Classification:336) has four components, each a cited theorem:

| component | bound | cited result |
|---|---|---|
| `benoist` | `k ≤ d` | Benoist, Prop 9.1 |
| `bieberbach` | `k ≤ d + 1` | Bieberbach I, §5 |
| `auslander` | `k ≤ d` | Auslander–Carrière–Dal'bo, 5.1 |
| `unipotent` | `k ≤ d` | Carrière–Dal'bo's maximal unipotent subspace, 5.2 |

**Predicates in the closures.** These include the predicates that are proved rather than assumed.

- **`barbot_A₀` and `barbot_A`:**
  - `BarbotExternals` and its four components, all **assumed**;
  - `TitsVirtuallyAbelianNull`, which is **proved**: `titsVirtuallyAbelianNull` holds for every `d` (TitsNull:1565, DEC-50) and is consumed in `caseOutput`. It is not a hypothesis.
- **`barbot_B`:** adds `SelbergLemma`, which is **assumed**, and `FlatLemmaKData`, which is assumed as `hK`.
- **`barbot_B_geroch` and `barbot_B_zero_geroch`:** add `FlatGerochGH`, `FlatAdmissibleMeasures` and `BarbotGH`. All three are **proved**: `flatGerochGH`, `flatAdmissibleMeasures`, and the GH⇒BarbotGH route.
- **Never reached:** `LimitSetMinimal` and `AbelianPairAsPrinted` are in none of the 23 closures.
- **No carried external is refuted.** No theorem concludes `¬` of a DEC-36 external carried by any root (`check2` refute scan). The paper's printed `AbelianPairAsPrinted`, used by no root, is refuted for d ≥ 2 (`not_abelianPairAsPrinted`).

## Where each external is defined, and its non-vacuity witnesses

Every witness listed here is sorry-free under `collectAxioms`.

| external | defined | witnesses (satisfiable) | not trivially true |
|---|---|---|---|
| `BarbotExternals d` | Classification:336 | `barbotExternals_zero` (:351), **`d = 0` only**. Downward monotone: `BarbotExternals.mono` (:342). **There is no witness for `d ≥ 1`.** | through its components |
| ↳ `BenoistNoLox` | Externals:526 | `benoistNoLox_zero` (:593) | `not_benoist_conclusion_stdBoost` (:584) |
| ↳ `BieberbachI E` | Bieberbach:685 | `bieberbachI_of_finrank_le_one` (:764), `bieberbachI_euclideanSpace_fin_one` (:768), `bieberbachI_of_finite` (:728). So `ℝ⁰` and `ℝ¹` are covered, which is exactly the `k ≤ 0 + 1` bound at `d = 0`. | `not_isDiscreteEucl_euclTranslations` (:620) |
| ↳ `AuslanderCarriereDalbo` | Externals:276 | `auslanderCarriereDalbo_zero` (:296) | — (no `not_*` witness; `DiscreteTopology Γ` is read in `isomTopology`) |
| ↳ `MaxUnipotentSubspace` | Externals:315 | `maxUnipotentSubspace_zero` (:333) | `not_maxUnipotent_conclusion_top` (:370) |
| `SelbergLemma V` | Externals:825 | `selbergLemma_real` (:872); `selbergLemma_minkowski_zero` (TheoremBInputs:319), by transport (`selbergLemma_of_linearEquiv` :309, `selbergLemma_of_injective_hom` :298). Downward monotone: `Lox.selbergLemma_minkowski_of_le` (Lox/SelbergMono:90). **There is no witness for `Minkowski d`, `d ≥ 1`**, because Selberg in `GL_{n ≥ 2}(ℝ)` is not in mathlib. | `not_selberg_conclusion_torsion` (:917) |
| `FlatLemmaKData N` | Classification:366 | Pointwise: `flatLemmaKData_minkowskiSpace` (:377), `flatLemmaKData_torusSpace` (TheoremBInputs:373), `CauchyCompact.flatLemmaKData` (:275), `flatLemmaKData_of_barbotGH` (:217). **The universal form taken by `hK` is a theorem in every `d`**: `flatLemmaKData_of_flatGerochGH flatGerochGH` (:249), or `forall_flatLemmaKData_iff.2 flatGerochGH` (:244). | — |
| `FlatGerochGH d` | TheoremBInputs:241 | **Proved (DEC-65)**: `flatGerochGH` (GerochFlat:130) for every `d`, universe-polymorphic, through `flatAdmissibleMeasures` (:121) and `flatGerochGH_of_admissible` (TheoremBInputs:265). | — |
| `TitsVirtuallyAbelianNull d` | Nonloxodromic:1711 | **Proved, not a hypothesis**: `titsVirtuallyAbelianNull` (TitsNull:1565) for every `d`. | — |
| `LimitSetMinimal` | Externals:647 | `limitSetMinimal_zero` (:709) | `not_limitSet_conclusion_stdBoostL` (:792). **Used by no root.** |
| `AbelianPairAsPrinted` | Externals:995 | — | **Refuted** by `not_abelianPairAsPrinted` (:1004) whenever `d` has two distinct indices (that is, `d ≥ 2`): it is the paper's printed form, recorded as false. **Used by no root.** |

## The CBG side

- **`Causal.CBG.cbg`** is parametric over an abstract `𝔊 : Geometry`, a structure whose fields are the framework's sheaf and gluing laws plus the round-2 `timeFunction` field. This structure is a *framework*, not a named external.
  - Its other hypotheses are `T2Space`, `ConnectedSpace`, `SecondCountableTopology`, GH, and a Cauchy surface.
  - **Instantiated sorry-free** by `flatGeometry d` (Flat/CBG:824) and by `CBG.ofLocalModelNoBTZ` (CBG/FromModel:2947).
  - In `cbg_of_hasTimeFunctions`, the extra `Geometry.HasTimeFunctions` is redundant: every geometry satisfies it, and for the flat model it is `flatGeometryOf_hasTimeFunctions` (Flat/CBG:833).
- **`flat_cbg`** has **no named external**. Its hypotheses are T2, connected, the `Minkowski d`-charted `HasGroupoid` structure, GH, and a Cauchy surface `S`.
  - `flat_cbg_gh` drops `S`, which it obtains from `flatGerochGH`.
  - `flat_cbg_of` and `flat_cbg_gh_of` take the model fields `hJ₁ hJ₂ hA3f hA3p hA4f hA4p` explicitly. Each is discharged by a sorry-free theorem: `flat_isCompact_Jplus_inter_Jminus` (:506), `flat_isCompact_Jminus_inter_Jplus` (:513), and `flatModelOf_germExtFuture` / `germExtPast` / `sliceFuture` / `slicePast` (:760–782). `flat_cbg` and `flat_cbg_gh` are those instances.
  - The hypotheses are satisfied by `𝐌ⁿ`: `gh_minkowskiSpace` (FlatSpacetime:737) and `barbotGH_minkowskiSpace` (:743). No theorem packages them under `flat_cbg`'s name.
- **Lemma K.**
  - **Proved form.** `isCauchySurface_of_isLocallyCauchyTwoSided` (CompactCauchy) and `…_of_pushUp` (LemmaKBare) are sorry-free, and their hypothesis sets are witnessed on the timelike line by `Causal.timelikeLine_lemmaK_hypotheses` (CompactCauchy:845), `timelikeLine_lemmaKBare_hypotheses` and `timelikeLine_lemmaKBare_twoSided_hypotheses`. All three are clean.
  - **Bare form.** The DEC-44 bare form is the only open Barbot-side item: one `SORRY(DEC-44)`, open in ETT generality and possibly false. **Nothing depends on it.**

## Vacuity caveats

- **"Sorry-free" is not "unconditional."** For `d ≥ 1`, Theorems A and B (`barbot_A₀`, `barbot_A`, `barbot_B`, `barbot_B_geroch`) are proved **relative to unproved cited theorems**:
  - `BarbotExternals d` (Benoist, Bieberbach I in `ℝ^{k ≥ 2}`, Auslander–Carrière–Dal'bo, Carrière–Dal'bo);
  - for B, also `SelbergLemma (Minkowski d)`.

  No witness exists in Lean for any `d ≥ 1`, and none can until those theorems are formalized. Their consistency there rests on the literature alone. The DEC-72 marks are marks *under disclosed externals*, and they must not be read as closing the externals.
- **Theorem A.**
  - **At `d = 0` it is jointly satisfiable and unconditional.** `barbot_A_hypotheses_zero` (Classification:612) gives `BarbotExternals 0`, `GH` and Cauchy-completeness of `𝐌¹`.
  - **In every `d` the spacetime hypotheses hold**, for `minkowskiSpace d` (`gh_minkowskiSpace` FlatSpacetime:737, `isCauchyComplete_minkowskiSpace` CauchyComplete:840). So the only gap for `d ≥ 1` is the bundle.
- **Theorem B.**
  - `barbot_B_hypotheses_satisfiable` (TheoremBInputs:379) gives:
    - `BarbotExternals 0` and `SelbergLemma (Minkowski 0)`;
    - for **every** `d`, the static torus `torusSpace d` (Examples:1000) is GH, Cauchy-compact and MGH, and carries `FlatLemmaKData` (`gh_torusSpace` :1063, `cauchyCompact_torusSpace` :1066, `mgh_torusSpace` TheoremBInputs:368, `flatLemmaKData_torusSpace` :373).
  - `hK` is a theorem in every `d`.
  - **So at `d = 0` the set is jointly satisfiable. For `d ≥ 1` the spacetime part is satisfiable, and `hE` and `hSel` are the only gap.**
  - `barbot_B_geroch` has no packaged witness under its own name. Its set is exactly `barbot_B_hypotheses_satisfiable` without `FlatLemmaKData`.
- **`barbot_B_zero_geroch` carries no named external** and is non-vacuous outright: `torusSpace 0` satisfies it.
  - Read the dimension correctly. `d = 0` is Barbot's `n = 1`: 1-dimensional `𝐌¹` and its quotients. In this degenerate dimension the Misner (loxodromic) and unipotent families are `False` by definition (`IsMisnerFamily 0 _ = False`, `IsUnipotentFamily 0 _ = False`, Classification:299–306), and `not_isHyperbolic_zero` (:534) refutes the loxodromic case.
  - So the only *unconditional* forms of A and B are those in dimension 1. They do not certify the classification in any physically meaningful dimension without the externals.
- **`FlatGerochGH`, read correctly.** Under Barbot's own GH (l.498–507: GH := has a Cauchy surface), the statement would be a tautology. What `flatGerochGH` proves is that ETT's GH (causal plus compact diamonds) implies a Cauchy surface. That is the real content, and it is proved sorry-free (DEC-65).
- **The gx exports carry no named external** and are sorry-free.
  - For the non-loxodromic shape, the developing-pair hypotheses are inhabited by `developsCC_minkowski` (Develop:2384).
  - This audit found no packaged witness for the loxodromic hypothesis `∃ γ ∈ ρ.range, IsLoxodromic (linOf γ)` of `uniformization_image`, `uniformization_properlyDiscontinuous` and `uniformization`. This is a documentation gap, not a named-external one.
  - DEC-75 has gx proving its 2+1 loxodromic element itself, rather than taking it from `BenoistNoLox`.
- **`cbg`** is non-vacuous through `flatGeometry d`. **`flat_cbg`** is non-vacuous through `𝐌ⁿ`.

## Findings for the master session (docstring contract, kb/0006)

These docstrings contradict this measurement. They belong to strict files, so I report them here rather than editing them.

- **`Flat/GerochFlat.lean` is stale on `sorry`:**
  - module docstring l.12–13: "Theorem B … still rests on `barbot_B`'s own upstream `sorry`s";
  - SCOPE l.60–62: "`barbot_B_geroch` still inherits `barbot_B`'s upstream `sorry`s (Classification / Cla / Loxodromic …)";
  - the docstrings of `barbot_B_geroch` (l.133–135, "Unmarked: rests on `barbot_B`'s upstream `sorry`s") and `barbot_B_zero_geroch` (l.144–146).

  Measured: both are axiom-clean. `barbot_B_zero_geroch` is now an unconditional theorem at `d = 0`.
- **`Flat/Nonloxodromic.lean` l.35 and l.219** still say `titsVirtuallyAbelianNull` holds "up to one tagged `sorry`". TitsNull's own SCOPE (l.131) says "Sorries (0)", and `collectAxioms` agrees.
- **`Flat/AchronalDomains.lean` l.94** says `Flat/Isometries`' trichotomy "is a `sorry` there". Strict has 0 `sorry`, and `lorentz_trichotomy` is proved (Isometries l.47, l.71).
- **Cosmetic.** `cauclo_from_embedding`'s binder `_hSel` (Classification:2632) is consumed at l.2673. Likewise `_hBieb` at l.451 is passed on at l.464. The underscore wrongly suggests the binder is unused. TheoremBInputs l.76 already calls it "a leftover name".
- **In agreement with the measurement:**
  - the SCOPE and declaration docstrings of `Classification` (A/B "sorry-free under the named externals; marked under DEC-72", l.112 checklist);
  - `TheoremBInputs` l.1–12;
  - `Cla/CoverMax`;
  - `CausalScaffold/CompactCauchy` ("Nothing may depend on it, and no declaration does").

## Summary

1. HEAD `167852c` (Lean content = `f84b69e`); no file moved during the audit (md5 before/after identical); `lake build --no-build` reports everything up to date; strict `sorry_count` = 0 in 147 files.
2. 22 of the 23 roots are axiom-clean (`propext`, `Classical.choice`, `Quot.sound`): Theorems A (`barbot_A₀`, `barbot_A`), B (`barbot_B`, `_geroch`, `_zero_geroch`, `_zero`, `_of_externals`), CBG (`cbg`, `flat_cbg` and their variants), the gx exports, `flatGerochGH`, and the proved lemma K.
3. There are no sorry leaves in any closure. The previous 3 leaves (`[10.M]`, the smoothing step, finding 2) are closed, so the `d = 0` routing caveat is moot.
4. The environment has 5 `sorryAx` users, all in the scaffold, and none is reached by any root. The only Barbot-side one is the bare lemma K `CausalScaffold.CompactCauchy` (`SORRY(DEC-44)`), and nothing uses it.
5. There are no `axiom` declarations, no strict→scaffold edges, and no theorem refutes a carried external (only the unused printed `AbelianPairAsPrinted`, d ≥ 2).
6. Named externals NOT proved (DEC-36): `BarbotExternals d` (Benoist, Bieberbach I, Auslander–Carrière–Dal'bo, Carrière–Dal'bo) on A and B, plus `SelbergLemma (Minkowski d)` on B. Sorry-free does not mean unconditional.
7. Proved, not assumed: `TitsVirtuallyAbelianNull` (all `d`), `FlatGerochGH` / `flatGerochGH` (all `d`, DEC-65), and B's `hK` (via `flatLemmaKData_of_flatGerochGH`). `LimitSetMinimal` and `AbelianPairAsPrinted` are used by nothing, and the latter is refuted for `d ≥ 2`.
8. Witnesses exist at `d = 0` only: `barbotExternals_zero`, `barbot_A_hypotheses_zero`, `selbergLemma_minkowski_zero`, `barbot_B_hypotheses_satisfiable` (torus in all `d`). For `d ≥ 1` the bundles have no Lean witness, and their consistency rests on the literature.
9. The unconditional forms, `barbot_B_zero_geroch` and A at `d = 0`, live in dimension 1 (`𝐌¹`), where the Misner and unipotent families are `False`. CBG, `flat_cbg` and the gx exports carry no named external.
10. Stale docstrings to fix (master): `GerochFlat` (module l.12–13, SCOPE l.60–62, `barbot_B_geroch` / `barbot_B_zero_geroch`); `Nonloxodromic` l.35, l.219; `AchronalDomains` l.94. Cosmetic: `_hSel` and `_hBieb`. There is also no packaged witness for the uniformization loxodromic hypothesis.
