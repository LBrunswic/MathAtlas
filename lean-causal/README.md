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
| `Causal.CorrespondingPoints`, `Causal.CorrespondingSpacelike` | — | the model-free cores of `Causal.CBG.Corresponding` and `Causal.CBG.NoCorresponding` hoisted into the ETT layer (T-abs-hoist-cbg-cores, kb/0062), same full names: K⁻ and causal convexity, `CBG.Corresponds`/`IsCorrPair`/`KSide`, `lem:corresponding_K`, Sbierski Lemma 3.11 and Lemma 3.9's core; 2026-11-21 |
| `Causal.CauchyDual`; `Causal.Model.CurvesExtendModels`, `Causal.Model.InjectiveMinkowski` | — | the time-function layer made ETT-layer (T-abs-hoist-time-function, kb/0065): `dual_isCauchySurfaceOn` out of `Causal.Splitting`; the static/Minkowski instances of `Causal.CurvesExtend` and `Causal.CBG.Injective` moved to model modules, same names; `Causality.HasTimeFunction` now in `Causal.CurvesExtend`, with `HasTimeFunction.isCausal` and `.curvesExtend`; 2026-11-21 |
| `Causal.NestedConverse` | — | ETT programme, layer 1 (T-abs-nested-converse): curve nesting gives ≤-nesting when the narrower causality is causally arc-connected (`CurveNestedOn.leNested_of_causallyArcConnected`), not bare (`not_leNested_of_curveNested_bare`, the pointed line), `CurveNestedOn.trans`; the rational line (`rationalLine`, kb/0069); 2026-11-21 |
| `Causal.NestedTransfer` | — | ETT programme, layer 1 (T-abs-nested-transfer): strong causality, its open form and a time function pass to the narrower causality; tarentin does not (`spacelikeLine_separates_tarentin`, the first model proved GH and not tarentin) and passes to the wider one; 2026-11-21 |
| `Causal.SbierskiProp37` | — | ETT programme, layer 1 (T-abs-sbierski-prop-3-7): Sbierski 1309.7591 Prop 3.7 (i) ⇒ (ii) without A3 (`CBG.sbierski_prop_3_7_i_imp_ii`); the whole equivalence at regular points under causal arc-connectedness; (iii) fails at BTZ points; `mghdprop:EquivCha` not marked (OQ in the register); 2026-11-21 |
| `Causal.ChronalNeighbourBridge` | — | ETT programme, layer 1 (T-abs-chronal-neighbour-bridge): `ChronalNeighbours` ⇒ `HasChronalNeighbour` everywhere ⇒ … with three strictly different strengths (`NonemptyChronalCones`, `HasChronalNeighbourEverywhere`), equal under arc-connectedness or absolute minimality on T1; the leaving theorems restated; sharpness models `globalLine`, `sierpinskiCausality`; 2026-11-21 |
| `Causal.PushUpNotOpen` | — | ETT programme, layer 1 (T-abs-pushup-not-open): the jump line on ℝ, push-up and two-sided locally causally open but not causally open in the future: absolute minimality cannot be dropped from `prop:topological_spacetime_absolutely_minimal` (in the library's reading of `defi:causalite`); 2026-11-21 |
| `Causal.GateLineLocal` | — | ETT programme, layer 1 (T-abs-gateline-local): the gated line is causally open in the future and not in the past, so the printed J⁺-only `def:causally_open_spacetime_open` is strictly weaker than DEC-8's two-sided reading (in the library's reading of `defi:causalite`; OQ in the register); locally push-up and not push-up; 2026-11-21 |
| `Causal.Dec8MinimalWitness` | — | ETT programme, layer 1 (T-abs-dec8-minimal-witness): the half-lit line on ℝ, absolutely minimal on every open, causally arc-connected, GH, causally open in the future and not in the past: the printed J⁺-only `def:causally_open_spacetime_open` is strictly weaker than DEC-8's two-sided reading in either reading of `defi:causalite`; 2026-11-21 |
| `Causal.PushUpOfMinimalLocal` | — | ETT programme, layer 1 (T-abs-pushup-of-minimal-local): on a T1 space absolute minimality and local push-up give push-up (`AbsolutelyMinimal.pushUp_of_locallyPushUp`), weakening `lem:pushup_local`'s arc-connectedness; local = global for push-up (T1) and causal openness under absolute minimality; T1 and local push-up cannot be dropped (the vee, `halfChronoLine`); 2026-11-21 |
| `Causal.ChronalTarentin` | — | ETT programme, layer 1 (T-abs-chronal-neighbours-tarentin): chronal neighbours give tarentin with no separation axiom (`ChronalNeighbours.tarentin`); so does `Z⁺ = Z⁻ = M` (`tarentin_of_Zplus_Zminus`, via `Iplus_inter_Iminus_subset_openDiamond`), strictly weaker (`globalLine_separates_Z`); neither is necessary (`lightlikeLine_separates_Z`); the globally chronological line is tarentin and not absolutely minimal (`globalLine_separates_tarentin`); 2026-11-21 |
| `Causal.CausallyPlainLocZ` | — | ETT programme, layer 1 (T-abs-hoist-plain-locz; no paper label): the causal-plainness criterion hoisted out of the E₀ ports, same full names: `E0LM.LocZplus`, `LocZminus`, `LocTarentin`, `LocNoPast`, `LocPastIn`, `rel_of_causallyConvex`, `locZplus_of`, `locZminus_of`, `locTarentin_of`, `Causality.causallyPlain_of_locZ` (push-up, local `Z⁺`, local `Z⁻` off a set with empty interior); new edge `PushUp.causallyPlain_of_chronalNeighbours` (`push_up ∧ chronal_neighbours ⇒ causally_plain`); 2026-11-21 |
| `Causal.SingularFlatPlain` | — | beside `Causal.SingularFlat` (model layer, no `Causal.Port.*`; T-abs-hoist-plain-locz): `SingularFlatAxioms.causallyPlain` (a strongly causal singular flat spacetime is causally plain), `BTZAxioms.Jminus_diff_nonempty`, `Kminus_ne_Iminus`, `K_neq_I`, moved out of `Causal.Port.E0ModelRows`, same names; 2026-11-21 |
| `Causal.Model.FlatTimeCylinder` | — | ETT programme, layer 3, model flat-gx (T-loc-flat-time-cylinder; no paper label): the flat time cylinder `ℤe₀\𝐌ⁿ` (`Causal.Flat.TimeCylinder d`, causality `timeCylinder d`), T2, second countable, connected, with curves_extend, absolutely_minimal, causally_arc_connected, push_up, tarentin, chronal_neighbours, causally_open and causally_plain, `≪_M` total (not causal), and for `d ≥ 1` not causally compact (`timeCylinder_separates`); for `d = 0` the timelike circle, causally compact and not causal (`timeCylinder_zero_separates`); 2026-11-21 |
| `Causal.Model.QuasilinearOneSided` | — | ETT programme, layer 3, model quasilinear (T-loc-quasilinear-one-sided): Eperon–Reall–Sbierski 1802.03020 Lemma 4.86 on ℝ × E, (4.87) read as the slope-δ cone (`slopeCone`, the static cone transported along (t, x) ↦ (t, δx)) curve-nested in C on U₁, either orientation, S ⊆ {t = 0} a Cauchy surface of U₁: (4.83) in the identity chart with a 1/δ-Lipschitz graph (`ers_lemma_4_86`), hence `OneSidedBoundary U₁ (closure S)` (`ers_lemma_4_86_oneSidedBoundary`) and Thm 4.82 with it (`ers_theorem_4_82_of_slopeCone`); GH and the openness of S not used; model-free: the maximal piece of a time-parametrised curve is inextensible (`Causality.inextensible_connectedComponentIn`); witness the Minkowski slab; the paper's labels not marked (readings); 2026-11-21 |
| `Causal.RationalLineExtras` | — | ETT programme, layer 1 (T-abs-rational-line-extras): the rational line's other ladder facts: a time function (the identity), strongly causal in the open form (intervals are causally convex), absolutely minimal on every open set for every cover; not locally causally open in the future (`causal_ladder`: absolute minimality and ¬ causally open in the future), not tarentin (no diamond has interior), not causally plain, no chronal neighbours, not causally compact (`J(p, q) = ℚ ∩ [p, q]` for rationals `p`, `q`); conjoined in `rationalLine_separates`, valid in either reading of `defi:causalite`; 2026-11-21 |
| `Causal.LevinTimeFunction` | — | ETT programme, layer 1 (T-abs-hoist-levin; no paper label): Levin's theorem for closed preorders (namespace `Causal.Levin`: order normality, order Urysohn, `exists_utility`), local and σ-compactness from global hyperbolicity and tarentin (`weaklyLocallyCompactSpace_of_globallyHyperbolic`, `locallyCompactSpace_of_globallyHyperbolic`, `sigmaCompactSpace_of_globallyHyperbolic`), `exists_timeFunction_of_secondCountable`, `curvesExtend_of_secondCountable`, `exists_inextensible_of_secondCountable`, moved out of `Causal.LevinUtility`, `Causal.LemmaKSC`, `Causal.LemmaKObstruction` with the same names; new edge `GloballyHyperbolic.hasTimeFunction` (`globally_hyperbolic ∧ tarentin ⇒ time_function`, T2, second countable); 2026-11-21 |
| `Causal.ErsUniqueness` | — | ETT programme, layer 1 (T-abs-ers-thm-4-64): the causal skeleton of Eperon–Reall–Sbierski 1802.03020 Thm 4.64 on one background (`ers_theorem_4_64`: the maximal common development as a union, a spacelike boundary point, the restart as the named hypothesis `SliceRestart`, shared with `ers_theorem_4_82`), Rem 4.67, Cors 4.68, 4.69, 4.71, 4.73; layer-3 inputs named; nothing marked; graduated 2026-11-20 |
| `Causal.CausalIsoInvariance` | — | ETT programme, layer 1 (T-abs-causal-iso-invariance): causal isomorphisms (`IsCausalIso`, the strict `ChartIso` for a global chart, `isCausalIso_iff_chartIso`) transport causality, GH, Cauchy surfaces, every causality-sort ladder property and time functions; a function strictly increasing along ≤ makes a causality causal; an ETT time function does not (`exists_isTimeFunction_not_isCausal`); graduated 2026-11-20 |
| `Causal.Model.EAlphaCauchy` | — | ETT programme, layer 3, model E_α (T-loc-ealpha-cauchy): `massive α` is globally hyperbolic with every slice `{t = t₀}` a Cauchy surface; its regular part (the axis removed) has no Cauchy surface in the library's sense and is not GH; `J⁻` of an axis point on a slice is a disc; the ladder properties instantiated for `massive α` and the 3+1 `cosmicString α`; graduated 2026-11-20 |
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
| `Causal.LevinUtility` | — | Lemma K's characterisations in second countable spacetimes without `CurvesExtend` (`isCauchySurface_iff_local_of_secondCountable`, `isCauchySurface_iff_isOpen_strictJplus_of_secondCountable`); Levin's theorem itself is in `Causal.LevinTimeFunction` |
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
