# lean-causal — the Lean library of *Topological spacetimes (I)*

The formalization of `papers/ett`: a strict library `Causal` and a scaffold library
`CausalScaffold`, Lean `v4.31.0`, mathlib `fabf563a` (the hub's pin, `hub.toml`).

    python3 ../tools/dropbox_ignore.py   # once, BEFORE any build: .lake must never sync
    lake exe cache get                   # mathlib from ~/.cache/mathlib, no download
    lake build Causal.Generated          # one module — the iteration loop
    make check                           # strict build, scaffold build, sorry count, axiom sweep

**This directory is a provisional home.** The hub's plan puts every project in the one package
under `lean/`. Until GFNBoundsLean is absorbed in-tree (WP-8, OQ-1) `lean/` is a read-only
submodule, so the library is grown here in the layout it will have there: graduation is
`git mv lean-causal/Causal lean/Causal` and
`git mv lean-causal/scaffold/CausalScaffold lean/scaffold/CausalScaffold`, and
`papers/ett/ledger/ledger.toml`'s `[lean] root` goes back to `../../../lean` (OQ-11).

## The two libraries

| library | where | rule |
|---|---|---|
| `Causal` | `Causal/` | strict: `warningAsError`, so a `sorry`, an unused variable or a deprecation fails the build |
| `CausalScaffold` | `scaffold/CausalScaffold/` | `sorry` permitted and tagged; never imported by `Causal`. A module is here either because a proof is missing or because it rests on a **reading of the paper awaiting the author's ruling** — each module says which. The layer of the curves graduated on 2026-09-27 (DEC-6); the scaffold holds the campaign's files (`docs/CAMPAIGN.md`) until they graduate; today (2026-11-20) the modules resting on a `sorry` (`GerochEquiv`, `SubExtension`), on one (`SingularGeroch`), the Barbot campaign's bare Lemma K (`CompactCauchy`) and its open second-countable form (`LemmaKSCOpen`, DEC-93), and the conjectured Geroch repair (`GerochCauchy`, OQ-32); `MinkowskiMeasure` graduated on 2026-11-20; the rest of the Barbot campaign graduated on 2026-11-02, `GXSingular` and the sorry-free part of `SubExtension` the same day (DEC-73), then the CBG work (`CBG.*`, `Flat.CBG*`), then the sorry-free part of `SingularGeroch` (DEC-78) |

## Modules

| module | certifies | note |
|---|---|---|
| `Causal.Causality` | `defi:causalite`, `def:precausality` | the structures; `J^±`, `I^±`; time reversal `dual` |
| `Causal.Properties` | `defi:causalement_plat`, `defi:pushup`, `def:diamonds`, `def:causally_compact`, `def:alexandrov_topology`, `def:causal_spacetime`, `def:tarentin_spacetime`, `def:strongly_tarentin_point`, `def:globally_hyperbolic` | strong causality in two forms, causal openness one- and two-sided (OQ-8, OQ-9) |
| `Causal.StrongCausality` | `rem:topological_spacetime_strongly_causal`, `prop:FZenon_injectif` | `prop:tarentin_topological_spacetime_causality` under two-sided causal openness |
| `Causal.GlobalHyperbolicity` | `prop:relation_fermee`, `prop:GH_Jferme` | `prop:GH_fortement_causal` with the full diamond, or under causal openness |
| `Causal.Reachable` | `defi:futur_continue`, `rem:suite_croissante`, `lem:K_facile`, `lem:passe_coherent`, `prop:tarentin_fort_K`, `prop:K_plongement_ordre` and the two "obviously holds" remarks | `K^±`, the relative interior |
| `Causal.Generated` | `lem:union_causalite`, `def:precausality_generated_notation_lemma`, `def:topological_space_causality_absolutely`, `lem:precausalite_engendre_minimale`, `theo:causalite_engendre` | the Baire hypothesis is not used (OQ-10) |
| `Causal.Local` | — | a causality given on an open subset extends to the space |
| `Causal.Minimal` | `prop:topological_spacetime_absolutely_minimal`, `rem:absolutely_minimal_topological_spacetime`, `lem:cup_cap`, `rem:same_notation_one_proves` | |
| `Causal.Subdivision` | — | the Lebesgue-number step |
| `Causal.Lines` | `rem:droites_pas_plates` | the three lines of `ex:causalities_lines`; the timelike line satisfies the hypotheses of the library |
| `Causal.Measure` | `defi:mesure_dieckmann`, `rem:mesure_bord`, `prop:cont_ext_cont` | |
| `Causal.Curves` | `def:causal_chronological_curve` | causal and chronal curves, as ruled by DEC-6 (OQ-7) |
| `Causal.ArcConnected` | `def:causal_arc_connectedness`, `def:local_causal_arc_connectedness`, `rem:cac_local`, `prop:cac_engendre`, `cor:causalement_connexe_minimal`, `lem:precausalite_restriction_minimale`, `lem:pushup_local`, `lem:restriction_convexe` | causal arc-connectedness |
| `Causal.LinesCurves` | — | the timelike line is causally arc-connected |
| `Causal.TransparentLine` | `cexemple:point_transparent` | `rem:minimalite_non_hereditaire` partial (OQ-15) |
| `Causal.Galileo` | — | `rem:galileo_spacetime_not_strongly` partial: needs n ≥ 1 |
| `Causal.LinesReachable` | — | `rem:K_neq_I`, `rem:K_plongement_hypotheses` partial: counterexamples on lines |
| `Causal.PushUp` | — | the order-topological cores of `lem:J_int`, `lem:cup_cap_sing`, `prop:K_calcul`, `prop:K_monotone`, `cor:K_ordre_Sigma`; model facts as hypotheses (kb/0012) |
| `Causal.MeasureRemarks` | — | `rem:K_borelien`, `rem:mesure_unilaterale_ptr` partial |
| `Causal.MeasureSum` | — | countable weighted sums of regular measures |
| `Causal.MeasureLocal` | `prop:mesure_dieckmann_topo` | admissibility is local for causally convex covers |
| `Causal.Pushout` | `defi:ppcm` | `rem:non_separe_cas` partial (OQ-14); the Hausdorff criterion of a gluing |
| `Causal.Morphism` | `defi:categorie_C`, `def:category_topological_spacetimes`, `defi:fonction_temps` | strong and weak morphisms (DEC-10, DEC-12); `ex:open_subset` partial (OQ-13) |
| `Causal.PushoutCausal` | — | the causality of a gluing |
| `Causal.Chains` | — | causal chains, maximal chains, causal connectedness and completeness, as written (OQ-17) |
| `Causal.Inextensible` | — | strict extension and inextensibility, two- and one-sided (DEC-11, DEC-13) |
| `Causal.Cauchy` | `def:cauchy_surface`, `def:cauchy_time_function` | Cauchy surfaces (DEC-14) and Cauchy time functions |
| `Causal.Geroch` | — | `theo:geroch` (i)⇒(ii) and (ii)⇒(iii), (ii) strict (DEC-15); the Gaussian witness on the timelike line |
| `Causal.MinkowskiMeasure` | — | `prop:mesure_dieckmann_Lorentz` on `ℝ^{1,n}` (instance; marks no label), from `Causal.Flat.minkowski_frontier_null_measure` (DEC-65); graduated 2026-11-20 |
| `Causal.GluingHausdorff` | — | ETT programme, layer 1 (`programme/roadmap.toml` T-abs-gluing-hausdorff; no paper label): a gluing along open embeddings, two spaces or a `CBG.FamilyGlueData`, is Hausdorff iff there are no corresponding boundary points (Sbierski 1309.7591 Def 3.5, Thms 2.7–2.8); Chruściel's "H is closed" refuted as topology (`not_isClosed_nonHausdorffLeft_expGluing`), the pair form and a compact form proved; graduated 2026-11-20 |
| `Causal.NestedCausalities` | — | ETT programme, layer 1 (T-abs-nested-causalities; no paper label): two nested causalities on one space; wider GH ⇒ narrower GH iff the narrower diamonds are closed (bare form refuted by `cutLine 0`), nested domains of dependence, and the causal skeleton of Eperon–Reall–Sbierski 1802.03020 Lemmas 4.70, 4.72, Thms 4.77, 4.82 with the layer-3 inputs as named hypotheses; nothing marked; graduated 2026-11-20 |
| `Causal.LocateExtension` | — | ETT programme, layer 1 (T-abs-locate-extension; no paper label): a chronal curve leaves an open set iff `I^±(O) ⊄ O`, sharp form through a boundary point with a chronal neighbour; the target's form of Sbierski 1507.00601 Lemma 2.17 / Grant–Kunzinger–Sämann Lemma 3.8 is refuted (`not_exists_leaving_bare`, the isolated line), true with the localisation hypothesis `HasChronalNeighbour`; one-sided witness `closedHalfLine`; graduated 2026-11-20 |
| `Causal.LadderLocal` | — | ETT programme, layer 1 (T-abs-ladder-local-defs): the ladder's inline side conditions named (`LocallyPushUp`, `LocallyCausallyOpen(Future)`, `ChronalNeighbours`, `NoCausalEndpoint`, `OneSidedBoundary`), the witnesses restated with them, `GloballyHyperbolic.isCausal`, `globallyHyperbolic_iff`; graduated 2026-11-20 |
| `Causal.Ladder.Basic`, `.Rules`, `.Test` | — | the `causal_ladder` tactic (T-tac-ladder-core): an aesop rule set of safe forward rules; `Rules` and `Test` are generated by `python3 tools/ladder.py emit-lean` from `programme/ladder.toml` (never edit by hand); ETT layer only, guarded in `Test` |
| `Causal.CompactMinimal`, `Causal.CurveComponents`, `Causal.DependenceDomain` | — | model-free lemmas hoisted out of model-importing modules (T-abs-hoist-model-free, kb/0047), same full names and statements: `exists_minimal_of_isCompact(_on)` (Sbierski Lemma 3.9), the section `Relative` of `CBG.CausalConvex` (`curveOn_of_rel_imp`, `inextensible_ordConnectedComponent_of_le`), `Flat.dependenceDomain`; ETT layer, usable by layer-1 modules; 2026-11-20 |
| `Causal.GXStructure` | — | (G,X)-manifolds over a maximal atlas (DEC-16); `prop:GX_espace_temps_topo` partial (OQ-18) |
| `Causal.Static` | — | static spacetimes ℝ × X over a geodesic metric space, with the curve-defined causality of `defi:causal_Ealpha`: absolutely minimal, push-up, tarentin, strongly causal, globally hyperbolic, `J = cl I` |
| `Causal.Minkowski` | — | Minkowski space `ℝ^{1,n}`; DEC-15's counterexample and the absence of maximal chains as theorems |
| `Causal.Model.Cone`, `Causal.Model.Massive` | — | the flat cone `C_α` (a proper geodesic metric space) and `E_α = ℝ × C_α`, `α > 0`: the model facts of Section 3.1 for `α > 0`; `E_{2π} ≅` Minkowski |
| `Causal.SingularFlat` | — | singular flat spacetimes, with the model facts as named hypotheses (`SingularFlatAxioms`, kb/0012): `lem:past_BTZ`, `cor:K_injectif`, `prop:K_densite_sing`, `cor:K_ordre`, `lem:cup_cap_BTZ` (DEC-19) |
| `Causal.CauchyExtension`, `Causal.CauchyDiamond` | — | Cauchy embeddings and extensions, abstractly (DEC-17); `lem:image_diamant`, `lem:passe_pgcd`, `lem:Sigma_separe` |
| `Causal.ChainsCurves` | `def:causally_connected` | causal connectedness by inextensible curves (DEC-20) |
| `Causal.ChainsOrder` | `def:causally_complete`, `rem:causal_completeness_slightly_weaker` | causal completeness by maximal chains of `(M, ≤)` (DEC-21, DEC-22) |
| `Causal.CompactCauchy` | — | Lemma K's proved form `isCauchySurface_of_isLocallyCauchyTwoSided` (DEC-44, a splitting and two-sidedness named); the bare form is `CausalScaffold.CompactCauchy`. Barbot campaign (`docs/BARBOT.md`), graduated 2026-11-02 |
| `Causal.CurvesExtend` | — | every causal curve lies on an inextensible one, when there is a time function |
| `Causal.Splitting` | — | the splitting `M ≅ S × ℝ` along a Cauchy surface from a causal flow; `set_option backward.isDefEq.respectTransparency false` on one lemma (SCOPE) |
| `Causal.LemmaKBare` | — | Lemma K without a splitting, where curves extend, `C` has push-up and `Z^± = M` |
| `Causal.LemmaK`, `Causal.LemmaKSC`, `Causal.LemmaKSCLocal`, `Causal.LemmaKLocal`, `Causal.LemmaKReduction`, `Causal.LemmaKObstruction` | — | Lemma K of record (DEC-93): `isCauchySurface_of_isLocallyCauchy_of_causallyOpen`, second countable and causally open |
| `Causal.LevinUtility` | — | Levin's theorem for closed preorders: a continuous time function in second countable spacetimes, discharging `CurvesExtend` |
| `Causal.Port.GXBasic`, `Causal.Port.UniversalCover`, `Causal.Port.Developing` | — | `(G,X)`-structures, the universal cover and the developing theorem, ported from gx (WP-32a) |
| `Causal.Flat.Form`, `Causal.Flat.Isometries`, `Causal.Flat.IsomCausal`, `Causal.Flat.Achronal`, `Causal.Flat.AchronalDomains` | — | Minkowski space `𝐌ⁿ = Minkowski d` (`n = d + 1`), `Isom(𝐌ⁿ)`, Barbot §6–7 |
| `Causal.Flat.Penrose` | `bcor:closeregular`, `bdef:regular_domain`, `blem:closecool`, `blem:fermons`, `blem:fermonsbis` | the Penrose boundary and the regular convex domains |
| `Causal.Flat.FlatSpacetime`, `Causal.Flat.Quotient`, `Causal.Flat.Examples`, `Causal.Flat.TwistedProduct`, `Causal.Flat.Developing`, `Causal.Flat.Develop`, `Causal.Flat.InducedLength`, `Causal.Flat.LipschitzGraph` | — | flat spacetimes, quotients, the elementary models, linear twisted products, the developing map, Barbot §8 from (CC′), the induced length |
| `Causal.Flat.CauchyComplete` | `bprop:project`, `bcor:quoiso` | Cauchy-completeness and the bridge to (CC′) |
| `Causal.Flat.Bieberbach`, `Causal.Flat.Externals`, `Causal.Flat.Cosmological`, `Causal.Flat.SecondCountable`, `Causal.Flat.Abel`, `Causal.Flat.Laoucapulse` | — | Bieberbach's elementary part, Barbot's external results as named `Prop`s, the cosmological time, second countability, `bcor:abel` (false as printed, repaired), Prop 4.2 in its strongest true reading |
| `Causal.Flat.Nonloxodromic` and `Causal.Flat.Nonlox.*` (10) | `bprop:extension` | Barbot §9, the nonloxodromic case; `maxHeartbeats` on one theorem each in `UnipotentLTP`, `UnipotentUpToFrame` (SCOPE) |
| `Causal.Flat.Loxodromic`, `Causal.Flat.TitsNull` and `Causal.Flat.Lox.*` (26) | — | Barbot §10, the loxodromic case; `maxHeartbeats` in `Loxodromic`, `Lox.SecondNullFix` (SCOPE) |
| `Causal.Flat.Classification` and `Causal.Flat.Cla.*` (19) | `bthm:caucomp`, `bthm:cauclo` | Barbot §11, Theorems A and B, stated under the named externals; `maxHeartbeats` in `Cla.G9Pair` (SCOPE) |
| `Causal.Flat.BarbotUnconditional` | — | Theorems A and B with every external discharged: `barbot_A_unconditional`, `barbot_B_unconditional` (with lemma K's data), `barbot_B_geroch_unconditional` (DEC-121) |
| `Causal.Flat.Bieberbach{Proof,Zassenhaus,Abelian,MinSet,Effective}` | — | Bieberbach I, `bieberbachI` (DEC-110) |
| `Causal.Flat.Gromov{Base,Bounded,Unbounded,Proof}` | — | Gromov's classification on ℍᵈ in place of Benoist: `benoistNoLox`, `bprop_sanloxo_proved` (DEC-111) |
| `Causal.Flat.Selberg{Base,Matrix,Residue,Torsion,Proof}` | — | Selberg's lemma for every finite-dimensional real `V`, `selbergLemma` (DEC-115) |
| `Causal.Flat.ACD{Hall,Null,Loxodromic,Reduction,Proof}`, `Causal.Flat.MaxUnip{Fitting,Cocycle,Hirsch,Proof}` | — | Auslander–Carrière–Dal'bo and the maximal unipotent subspace for `Isom(𝐌ⁿ)`: `auslanderCarriereDalbo`, `maxUnipotentSubspace` (DEC-121) |
| `Causal.Flat.AffACD{Base,Local,Triang,Proof}`, `Causal.Flat.AffUnip{Fitting,Cocycle,Proof}` | `bthm:ausl`, `bthm:unip` | the same in the printed `Aff(n, ℝ)` generality: `affAuslanderCarriereDalbo`, `affMaxUnipotent` (DEC-123) |
| `Causal.Flat.TheoremBInputs`, `Causal.Flat.GerochFlat`, `Causal.Flat.Geroch.*` (4), `Causal.Flat.CBGCompact` | — | Theorem B's inputs (lemma K's data, Selberg), admissible measures on every GH flat spacetime, compactness of `J^∓(p) ∩ Σ` |
| `Causal.SubExtension` | — | common sub- and over-extensions, abstractly: the sorry-free part of the former scaffold file (DEC-73, 2026-11-02): `IsRigid`, `CommonSubExtension`, `CommonOverExtension`, `IsPgcdCandidate`, `pgcdOpens`/`pgcdMap`, the kink/timelike-line witnesses, `c_ext_connexe_of_isCauchySurfaceOn` |
| `Causal.GXSingular` | — (OQ-19) | `prop:GX_sing_espace_temps_topo` for abstracted model spaces; graduated from the scaffold (DEC-73, 2026-11-02) |
| `Causal.SingularGeroch` | — | singular flat spacetimes and Geroch's theorem, abstractly: the sorry-free part of the former scaffold file (DEC-78, 2026-11-02): `SingularFlatSpacetime`, `VecteurFlow`, `ModelMeasures`, `mesure_admissible` (`prop:mesure_admissible`), `geroch_hypotheses` (`rem:singular_flat_spacetime_therefore`, DEC-18), `geroch_sing_i_imp_ii`, `geroch_sing_i_imp_iii`, `geroch_sing_split` (`theo:geroch_sing` in part), `cupCapBTZAsPrinted_of_globallyHyperbolic` (`lem:cup_cap_BTZ`, DEC-19), the timelike-line witnesses |
| `CausalScaffold.GerochEquiv` | — | `theo:geroch`, the equivalence; one `sorry`, the cited (iii)⇒(i) |
| `CausalScaffold.SingularGeroch` | — | the remainder of the DEC-78 split: `geroch_sing_of_stronglyCausal` (`theo:geroch_sing`, the equivalence, DEC-18) and its witness `timelikeLine_geroch_sing`; rests on `GerochEquiv`; imports `Causal.SingularGeroch` |
| `CausalScaffold.LemmaKSCOpen` | — | the bare Lemma K with second countability, without causal openness; one `sorry`, an open generalisation not owed (DEC-93) |
| `CausalScaffold.SubExtension` | — | the remainder of the DEC-73 split: `exists_mem_image_inf`, `isCauchySurfaceOn_inf`, `c_ext_connexe` (`lem:C_ext_connexe`) and `cauchy_pgcd` (`prop:Cauchy_pgcd`); two `sorry`s; imports `Causal.SubExtension` |
| `CausalScaffold.CompactCauchy` | — | the bare DEC-44 form of Lemma K, `isCauchySurface_of_isLocallyCauchy`; one `sorry`, nothing depends on it (Barbot) |
| `Causal.CBG.*` (11), `Causal.Flat.CBG`, `.Flat.CBGGerm`, `.Flat.CBGSlice` | — | the Barbot campaign's CBG work (`docs/CBG-DESIGN.md`), sorry-free since interface round 4; graduated from the scaffold 2026-11-02. No label marked; A3/A4 at BTZ points are explicit hypotheses of `Geometry.ofLocalModelOfBTZ` (gx's, for `E₀`) |

What each label's status is, which declarations carry it and what formalizing found in the paper
is in `papers/ett/ledger/LEDGER.md`, generated from the sources and from
`papers/ett/certificate/curation.toml`.

## Conventions

* **The module docstring is a contract** (the GFN library's `kb/entries/0004`): title; the labels
  certified, in the form ``**`label`**`` the ledger reads, with their line in
  `papers/ett/legacy/labeled/ETT.tex`; the paper's own sentences in a block quote; a hypothesis
  checklist (`✓ carried`, `⚠ weakened`, `⚠ strengthened`); `## SCOPE (disclosed)`; `Provenance:`.
  A label proved under a reading or a hypothesis the paper does not have is written **without**
  the mark, and is `partial` in the ledger.
* **Everything is indexed by an open set.** `C.le U x y`, `C.Jplus U A`, `C.Kplus U A`: the
  spacetime `M` is `U = ⊤`. A property of the open subset `W` seen as a spacetime is `…On W`.
  No subtype of `M` appears in a statement.
* **Past from future.** A statement about the past is the statement about the future of
  `C.dual`; every property has its `dual_…` lemma.
* **Weakest sufficient hypotheses.** A theorem asks for the separation and countability it uses,
  not for "second countable Hausdorff"; the checklist says what was dropped.
