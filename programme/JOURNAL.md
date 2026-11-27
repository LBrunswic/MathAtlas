# The /ett-programme journal

One entry per iteration, appended by the loop (`.claude/skills/ett-programme/SKILL.md`).

## 2026-11-20 19:35 · wave of 5 · T-lad-seed-check, T-pkg-sbierski-mghd, T-pkg-ers-predictability, T-abs-gluing-hausdorff, T-abs-nested-causalities
- T-lad-seed-check (ladder): the 7 seeded edges and the consequence read against their witnesses' signatures; `from` corrected on 2 edges (tarentin), a localisation `under` on 3, the consequence split (J⁺ and J⁻); 3 implications and 9 consequences added; checked by `ladder.py check`. emit-lean NOT run: Rules.lean imports Causal.Ladder.Basic (T-tac-ladder-core creates it), and emit-lean would make conditional edges aesop safe rules; recorded in T-tac-ladder-core. The keeper proposes T-lad-local-nodes (LocallyPushUp, LocallyCausallyOpenFuture, chronal neighbours) and T-lad-gh-causal (GH ⇒ causal without tarentin; a causally_compact node), and four ladder.py changes (closure that skips localisation `under`, namespace resolution, conjunctive `at`, label check): for the planner
- T-pkg-sbierski-mghd (package): papers/sbierski-mghd, 19 statements, 20 edges; two texgraph gaps fixed with tests (proof titles through secondary labels; digits in env names), story_lint accepts hyphenated slugs; no other ledger moved
- T-pkg-ers-predictability (package): papers/ers-predictability, 32 statements, 34 edges
- T-abs-gluing-hausdorff (abstract, layer 1): Causal.GluingHausdorff; assertions 1–2 marked, assertion 3 false as topology (Chruściel's "H is closed"), true forms proved; Sbierski's uniqueness and openness of C not topology; audit major (REPORT: a pdftotext artefact read as a typo in Sbierski) → minor (round 2); OQ-40
- T-abs-nested-causalities (abstract, layer 1): Causal.NestedCausalities, nothing marked; wider GH ⇒ narrower GH iff narrower diamonds closed; nested domains under InextensibleNestedOn; ERS19 4.70/4.72/4.77/4.82 with named layer-3 inputs; audit major (REPORT: a claimed gap in ERS 4.70 that (4.62) excludes) → minor (round 2); OQ-41
- ladder: 12/110 pairs classified (7 only under a localisation hypothesis), 10 checked edges, 10 consequences
- binders: 0 binder(s) (T-bind-sbierski-mghd and T-bind-ers-predictability now unblocked, planner-owned)
- gates: lean-causal ✓ (208 strict files, 0 sorry), ladder ✓, binder ✓, roadmaps ✓, tests ✓; hub: papers-check red on papers/egf and papers/syracuse only, their ledgers stale under /atlas-team's in-flight closers in lean-egf and lean-syracuse (paths it holds; not reverted), gate-tests red through papers-check; nothing of this wave red
- commits: 685b84a 377fd99 6148937 89d49b8 b070c95 b03614f ca07081 c4d6baf
- shared checkout: /atlas-team's push 2e8c12e carried the first three; lean-causal handed back to it for T-ett-deux-pushup-graduate
- next: a planning run (rule 2: two papers set up since the planner last ran; the binder targets and the keeper's proposals); then wave: T-tac-ladder-core, T-abs-locate-extension, T-pub-blueprint, T-loc-ealpha-cauchy

## 2026-11-20 20:05 · plan · programme-planner (rule 2: two papers set up)
- T-bind-sbierski-mghd (binder): 19 rows bound; layer 1 in Lean 15 (Causal.CBG, Causal.GluingHausdorff), layer 3 in Lean 0 (smooth-vacuum all targets; flat-gx entries are Lean names); A1/A3/A4 and local uniqueness in open_localisation pending ladder nodes. Findings: Lean's CBG starts from a GH spacetime, Sbierski from initial data (Thm 2.6 needed: T-abs-cbg-initial-data); Lean proves Prop 3.7 (ii) from A3, Sbierski A3 from 3.7 (ii) (T-abs-sbierski-prop-3-7); in the causal CBG setting uniqueness of the corresponding point and openness of C are proved, which bears on OQ-40; model-free CBG theorems sit in model-importing modules
- T-bind-ers-predictability (binder): 28 of 32 rows bound; layer 1 in Lean 7, layer 3 in Lean 1. Findings: ERS Thm 4.64 (used by 7 rows) not in Lean beyond Step 2; §3's non-uniqueness is a developing-map phenomenon (T-abs-ers-etale-mghd); the OQ-41 readings recorded as taken
- roadmap 18 → 45 targets: 7 ladder (2 blocked on OQ-40/OQ-41), 1 tooling (T-tool-ladder-py, master), 9 layer 1, 10 layer 3 and package; T-pkg-smooth-lorentz needs-ruling (where smooth Lorentzian metrics live in Lean), and eight smooth-vacuum/quasilinear targets wait on it; T-tac-ladder-core now fixes emit-lean first
- planner's readings, not recorded as OQ (no target has taken them yet; the closer will report them): Sbierski's "initial data" as a fixed Cauchy surface plus the class of its developments closed under common sub-developments (T-abs-cbg-initial-data); ERS §3 computational rows bound with `ett` = the layer-1 theorem they feed
- ladder: 12/110 pairs, 10 checked edges, 10 consequences (unchanged)
- binders: ers-predictability 28 rows bound, layer 1 in Lean 7, layer 3 in Lean 1; sbierski-mghd 19 rows bound, layer 1 in Lean 15, layer 3 in Lean 0
- gates: ladder ✓, binder ✓, roadmaps ✓, tests ✓; hub: papers-check red on bbs, benzecri, egf, gx, syracuse, yamabe only, ledgers stale under /atlas-team's six in-flight closers in lean-gx, lean-benzecri, lean-egf, lean-syracuse, lean-yamabe (its paths, not reverted); gate-tests red through papers-check; lean-causal papers green
- commits: 400e67c 8d905eb c149d7f
- next: wave: T-tac-ladder-core, T-abs-locate-extension, T-abs-ladder-local-defs (lean-causal ×3), T-pub-blueprint, T-lad-cbg-geometry-nodes — the lean-causal three after /atlas-team's T-ett-deux-pushup-graduate frees lean-causal

## 2026-11-20 21:27 · wave of 5 · T-lad-cbg-geometry-nodes, T-tac-ladder-core, T-abs-locate-extension, T-abs-ladder-local-defs, T-pub-blueprint
- shared cap with /atlas-team: started with keeper + publisher while /atlas-team held lean-causal for T-ett-deux-pushup-graduate, topped up with one lean-causal closer per slot it freed (3 → 4 → 5 targets)
- T-lad-cbg-geometry-nodes (ladder): rigid, germ_extension, cauchy_slice (a new sort `geometry`), curves_extend, time_function; 2 implications, 3 counterexamples on the gated line (GH, causal, curves extend, yet not absolutely minimal: the CBG's A2 absolute minimality is a genuine localisation hypothesis), 13 consequences, 8 open entries; header corrected for the new emit-lean
- T-tac-ladder-core (tactic): causal_ladder = aesop safe forward rules; emit-lean emits only unconditional, causality-sort, ETT-layer edges (4 rules; 7 skipped for `under`, 1 for the layer rule), writes Test.lean (5 derived, 132 not derived, a layer guard); audit minor; at integration the vacuous test fixed (mutation-checked) and the "never unfolded" docstring corrected
- T-abs-locate-extension (abstract, layer 1): Causal.LocateExtension; the target's statement FALSE (isolatedLine), sharp characterisation marked, true form with HasChronalNeighbour, non-dense form under tarentin + plain + arc-connected, closedHalfLine one-sided witness; audit minor; duplicate lightlikeLine_tarentin removed at graduation; OQ-51
- T-abs-ladder-local-defs (abstract, layer 1): Causal.LadderLocal; the ladder's inline side conditions named, witnesses restated, GloballyHyperbolic.isCausal without tarentin; all marked; audit minor; OQ-52. The auditor's sharper separating example for the keeper: on ℝ with ≪ empty and ≤ the diagonal plus 0 ≤ 1, push-up holds but J⁺((−1,1)) = (−1,1] is not open, so push-up alone does not give causal openness (a `fails` entry candidate)
- T-pub-blueprint (publish): reports/blueprint, three views, two builds byte-identical, 0 page errors
- ladder: 16 properties (13 causality, 3 geometry), 12 checked implications, 3 counterexamples, 23 consequences; 27 of 240 pairs classified (27 of 162 within a sort)
- binders: ers-predictability 28 rows bound, layer 1 in Lean 7, layer 3 in Lean 1; sbierski-mghd 19 rows bound, layer 1 in Lean 15, layer 3 in Lean 0
- gates: lean-causal ✓ (214 strict files, 0 sorry), ladder ✓, binder ✓, roadmaps ✓, tests ✓, blueprint ✓, hub make -k check ALL GREEN
- commits: 6411f34 9f5cfce 1fcbea8 2328498 3e48e55 7594ae2 8b5cf06 1e3bfcf
- for the planner: the keeper's proposals (Lean one-liners HasTimeFunction.isCausal/.curvesExtend once HasTimeFunction is hoisted; gateLine_hasTimeFunction, gateLine_tarentin; the flat time cylinder for curves_extend ⇏ is_causal; ladder.py reading `sort`, `fails` with a list); the tactic's limits (no reasoning across C.dual); HasChronalNeighbour ↔ ChronalNeighbours bridge lemma; the push-up ⇏ causally-open example above
- next: wave: T-lad-nested-nodes (keeper), T-abs-hoist-model-free (closer, exclusive in lean-causal)

## 2026-11-20 22:28 · wave of 2 · T-abs-hoist-model-free, T-lad-nested-nodes
- T-abs-hoist-model-free (abstract, exclusive in lean-causal): Causal.CompactMinimal, Causal.CurveComponents, Causal.DependenceDomain hold the four model-free lemmas of kb/0047 under their old full names; NestedCausalities' duplicates removed (dependenceDomainOn kept as an abbrev); audit clean (every constant compared against a build of HEAD); ETT-layer strict modules 44 → 47 of 217; kb/0047 rewritten. Note for the planner: `_on` was not more general than `_of_le`; `Flat.dependenceDomain` keeps its Flat namespace (a Causality-namespace alias is the author's call); `futureExtensible_of_final_on`, `not_futureExtensible_of_component_on` now have no users
- T-lad-nested-nodes (ladder): le_nested, curve_nested of a new sort `pair`; le_nested ⇒ curve_nested checked, the converse open; 10 consequences; curve_nested covers 8 ERS binder rows. Keeper proposals for the planner: CurveNestedOn.leNested_of_causallyArcConnected (converse), not_leNested_of_curveNested_bare (pointedLine in spacelikeLine), T-abs-nested-transfer (SC, SCO, HasTimeFunction pass to the narrower causality; tarentin does not), a `[[transfer]]` schema in ladder.py; binder rows 4.72/4.73 can move curves_extend to `localisation`, and the binders' [[proposed]] entries for le_nested, curve_nested, cauchy_slice, curves_extend are stale
- ladder: 18 properties (13 causality, 3 geometry, 2 pair), 13 checked implications, 3 counterexamples, 33 consequences; 29 of 306 pairs classified (29 of 164 within a sort); emit-lean: 4 rules, 9 checked edges skipped
- binders: ers-predictability 28 rows bound, layer 1 in Lean 7, layer 3 in Lean 1; sbierski-mghd 19 rows bound, layer 1 in Lean 15, layer 3 in Lean 0
- gates: lean-causal ✓ (217 strict files, 0 sorry), ladder ✓, binder ✓, roadmaps ✓, tests ✓, blueprint ✓, hub make -k check ALL GREEN (the gate-tests red /atlas-team saw at 23:05 was the un-emitted ladder of this wave, fixed by c02c8c8)
- commits: 02b43b6 c02c8c8 72c0fbc ab9f54c
- next: wave: T-abs-cbg-initial-data, T-abs-sbierski-prop-3-7, T-abs-ers-thm-4-64 (lean-causal ×3) — shared with /atlas-team's three ready lean-causal closers, which have waited on this wave's exclusivity

## 2026-11-20 23:45 · wave of 3 · T-abs-ers-thm-4-64, T-loc-ealpha-cauchy, T-abs-causal-iso-invariance
- shared cap: one lean-causal closer first (agreed split), topped up as /atlas-team's wave 6 freed slots; T-abs-cbg-initial-data swapped out at dispatch (it needs Causal.CBG.cbg, model-importing: a layer-1 module cannot use it before T-abs-hoist-cbg-cores; same for T-abs-sbierski-prop-3-7)
- T-abs-ers-thm-4-64 (abstract, layer 1): Causal.ErsUniqueness; ERS Thm 4.64 skeleton + Rem 4.67, Cors 4.68, 4.69, 4.71, 4.73, nothing marked; SliceRestart = 4.82's hstep; one extra named hypothesis FrontierStaysIn (no roadmap row owns it yet: T-loc-quasilinear-slice is the natural owner); audit minor → clean (round 2: non-degenerate witness, narrowed FollowsSolution); OQ-57
- T-loc-ealpha-cauchy (localisation, layer 3, E_α): Causal.Model.EAlphaCauchy; GH + every slice Cauchy with the axis, no Cauchy surface (library sense) and not GH without it, J⁻ of axis points; the 3+1 cosmic string too; ladder side conditions instantiated for massive α; audit minor; OQ-58
- T-abs-causal-iso-invariance (abstract, layer 1): Causal.CausalIsoInvariance; IsCausalIso ≡ global ChartIso (bridge added at the audit), transport of causality, GH, Cauchy, the ladder, time functions; an ETT time function does not give IsCausal (doubledLine); audit minor
- ladder: unchanged this wave (18 properties, 13 implications, 3 counterexamples, 33 consequences; 29/306); emit-lean byte-identical
- binders: unchanged (ers-predictability 28 rows, layer 1 in Lean 7, layer 3 in Lean 1; sbierski-mghd 19 rows, layer 1 in Lean 15, layer 3 in Lean 0) — stale against today's modules
- gates: lean-causal ✓ (220 strict files, 0 sorry), ladder ✓, binder ✓, roadmaps ✓, tests ✓, blueprint ✓, hub make -k check ALL GREEN
- commits: 56ccff0 80260b0 39dc3c1 e8e594a 1df3386
- for the planner: rebind both binders to the new Lean (Causal.ErsUniqueness rows 4.64–4.73, CausalIsoInvariance rows 3.27–3.39, EAlphaCauchy, GluingHausdorff, LocateExtension, LadderLocal, the hoisted modules); make T-abs-cbg-initial-data and T-abs-sbierski-prop-3-7 depend on T-abs-hoist-cbg-cores; give FrontierStaysIn an owner; the keeper's proposals (edge time_function ⇒ is_causal via isCausal_of_exists_timeFunction, curve_nested ⇒ le_nested under arc-connectedness, nested transfers, push-up ⇏ causally open, HasChronalNeighbour ↔ ChronalNeighbours bridge, a [[transfer]] schema); the duplicated withLp lemmas; inextensible_Iio_of_tendsto_not_mem to hoist
- next: a planning run (rule 2 in spirit: the wave tool offers two layer-1 targets that cannot meet the layer rule, and both binders lag seven new modules); lean-causal left to /atlas-team meanwhile

## 2026-11-21 00:16 · plan · programme-planner (binders stale; layer-1 rule through depends)
- binders rebound to the Lean of 2026-11-20: ers-predictability 28 rows bound, layer 1 in Lean 7 → 17, layer 3 in Lean 1 → 0 (row 4.79 now needs a quasilinear curve_nested entry); sbierski-mghd 19 rows, layer 1 in Lean 15, layer 3 in Lean 0 (GluingHausdorff, CompactMinimal, CurveComponents cited; Lemma 3.9 uses no A3)
- roadmap 45 → 64 targets: 22 added from the waves' findings (keeper edges, tactic across C.dual, hoists, ERS 4.79–4.80, nested converse/transfer, chronal-neighbour bridge, push-up ⇏ causally open, gated-line witnesses, flat time cylinder, E_α tidy, FrontierStaysIn's owner, binder targets); T-abs-cbg-initial-data and T-abs-sbierski-prop-3-7 back to planned behind T-abs-hoist-cbg-cores (ready, exclusive) and T-abs-hoist-cbg-geometry (needs-ruling: may layer 1 import Causal.SingularFlat, the CBG Geometry's A2 field?); T-abs-dependence-domain-home needs-ruling (Flat.dependenceDomain's namespace)
- master: T-loc-quasilinear-slice blocked on OQ-57 (planner's proposal); T-lad-local-nodes confirmed ready (OQ-52 (a) concerns only the one-sided names); OQ-40's blocks column names T-lad-programme-properties, now T-lad-gluing-nodes (noted, the register row is not edited)
- gates: binder ✓, roadmap ✓ (64 targets), ladder ✓, tests ✓, blueprint ✓, hub make -k check ALL GREEN
- commits: 957faa9 8ef112a
- next: wave: T-lad-local-nodes (keeper), T-abs-hoist-cbg-cores (closer, exclusive in lean-causal, while /atlas-team plans)

## 2026-11-21 00:44 · wave of 2 · T-abs-hoist-cbg-cores, T-lad-local-nodes
- T-abs-hoist-cbg-cores (abstract, exclusive in lean-causal, during /atlas-team's planner run): Causal.CorrespondingPoints, Causal.CorrespondingSpacelike hold the model-free cores of Causal.CBG.Corresponding/NoCorresponding under their old names; audit clean (85 constants changed module only, against a rebuild of HEAD); ETT-layer modules 49 → 51 of 224; ett curation's extra_lean_files and the Sbierski binder's references updated; kb/0043 corrected, kb 0062, 0063. Left: correspondingSet, correspondingExt (model-free, unlisted)
- T-lad-local-nodes (ladder): locally_push_up, locally_causally_open(_future), chronal_neighbours as nodes; the four conditional edges restated with the side condition in `from`; lightlike-line counterexamples; seven [[open]] entries for the pairs the old closure overstated; causal_ladder 4 → 12 rules, Test 23 derived / 235 not derived
- keeper's finding for the planner (argued, not in Lean): the gated line looks causally open in the future but not in the past, which would make the printed J⁺-only causal openness strictly weaker than DEC-8's two-sided reading; proposals T-abs-gateline-local, a widened T-abs-pushup-not-open, deux_pushup's [[fails]] (61/462 with all three, simulated, no contradiction)
- ladder: 22 properties, 17 checked implications, 8 counterexamples, 33 consequences; 44 of 462 pairs (44 of 280 within a sort); only 2 pairs through a conditional (T1) edge
- binders: ers-predictability 28 rows bound, layer 1 in Lean 17, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 15, layer 3 in Lean 0
- gates: lean-causal ✓ (224 strict files, 0 sorry), ladder ✓, binder ✓, roadmaps ✓, tests ✓, hub make -k check ALL GREEN; blueprint: two builds identical, 0 page errors, but its smoke check "click an implication" FAILS (committed in 9c4ebef before it was caught): the new conjunctive edges are drawn through ∧ junctions; a publisher fix follows
- commits: e4df4d0 947f841 d6832d4 9c4ebef
- next: the blueprint smoke fix (publisher); then wave: T-lad-gh-causal (keeper), T-abs-hoist-time-function (closer, exclusive in lean-causal) — lean-causal goes back to /atlas-team first (its two closers have waited)

## 2026-11-21 01:08 · wave of 3 · blueprint fix, T-lad-gh-causal, T-lad-time-function-causal
- blueprint (publisher, T-pub-blueprint maintenance): the smoke failure of 9c4ebef fixed — the click band of an arrow was 2–6 px on screen after fitting and the check clicked bounding-box centres; now a constant 14 px band (22 on touch), nearest line wins, hover lights a whole implication; the smoke clicks every segment, beside it, overlaps and junctions, and fails on the old page
- T-lad-gh-causal and T-lad-time-function-causal (ladder, one commit): causally_compact node; GH ⇔ is_causal ∧ causally_compact as three checked edges (no tarentin); time_function ⇒ is_causal (isCausal_of_exists_timeFunction); half-plane counterexamples (… ⇏ causally_compact, ⇏ GH); 7 consequences; the time_function node's comment corrected (ETT's IsTimeFunction is not stronger). The time_function ⇒ is_causal rule is emitted but inert until HasTimeFunction is hoisted
- emit/rebuild of Causal.Ladder.Rules/Test waited for /atlas-team's T-ett-e0-model-rows to free lean-causal (its gate-tests red meanwhile was this loop's in-flight ladder, recorded as such on both sides)
- keeper's proposals for the planner: doubledLine_causallyCompact (settles causally_compact ⇏ is_causal, GH, SC, SCO, time_function), gateLine_not_pushUp, spacelikeLine_not_tarentin (first GH non-tarentin model), lightlike-line ⇏ causally_plain entries (~9 pairs, witnesses exist), emitted() skipping formless properties, a single halfPlane witness; /atlas-team's: E0ModelRows' model-free theorems (causallyPlain_of_locZ, SingularFlatAxioms.causallyPlain — evidence for OQ-16, rem:pas_plat —, BTZAxioms.K_neq_I) to hoist (its kb 0061, 0064)
- ladder: 23 properties, 21 checked implications, 18 counterexamples, 40 consequences; 85 of 506 pairs classified; causal_ladder 16 rules, Test 26 derived / 265 not derived
- binders: unchanged (ers 28 rows, layer 1 in Lean 17; sbierski 19 rows, layer 1 in Lean 15)
- gates: lean-causal ✓ (Rules/Test built), ladder ✓, binder ✓, roadmaps ✓, tests ✓, blueprint ✓ (every smoke check); hub: papers-check red on benzecri and egf only — /atlas-team's in-flight closers (it holds lean-benzecri, lean-egf, papers/benzecri, papers/egf), gate-tests red through it; nothing of this wave red
- commits: 7985e8b 6a0018d 9f24800 105daa1
- next: wave: T-abs-hoist-time-function (closer, exclusive in lean-causal) — /atlas-team's exclusive T-ett-gxsingular-dec25 also waits for lean-causal: alternate

## 2026-11-21 01:51 · wave of 1 (+ ladder follow-up) · T-abs-hoist-time-function
- T-abs-hoist-time-function (abstract, exclusive in lean-causal, agreed with /atlas-team): Causal.CurvesExtend, Causal.CBG.Injective (Sbierski Lemma 3.3), Causal.CBG.CausalConvex and the new Causal.CauchyDual are ETT-layer; HasTimeFunction lives in Causal.CurvesExtend with the wrappers HasTimeFunction.isCausal and .curvesExtend; the static/Minkowski instances in Causal.Model.CurvesExtendModels and Causal.Model.InjectiveMinkowski; audit clean (11 constants changed module only; the private-name artefact explained); ETT-layer 51/225 → 55/228; stale docstrings fixed at integration; kb 0065, 0066
- ladder follow-up (keeper): the time_function edges now use the wrappers; causal_ladder 17 rules; time_function's examples present and derived (28 derived, 297 not derived); a negative control showed the old witnesses fail
- ladder: 23 properties, 21 checked implications, 18 counterexamples, 40 consequences; 85 of 506 pairs
- binders: unchanged (ers 28 rows, layer 1 in Lean 17; sbierski 19 rows, layer 1 in Lean 15)
- gates: lean-causal ✓ (228 strict files, 0 sorry), ladder ✓, binder ✓, roadmaps ✓, tests ✓, blueprint ✓, hub make -k check ALL GREEN; /tmp/check-lean-causal.log left for /atlas-team's sweep refresh
- commits: 7eff58c 645b01e 37df062 68957f2
- next: lean-causal to /atlas-team's exclusive T-ett-gxsingular-dec25; then a wave of up to 3 lean-causal closers from the ready p4 targets (nested-converse, nested-transfer, chronal-neighbour-bridge, pushup-not-open, quasilinear-one-sided); a planner pass is due soon (proposals since 00:20: doubled-line compactness, gated-line local facts and the DEC-8 finding, spacelike-line non-tarentin, E0ModelRows hoist candidates, SingularFlatAxioms.causallyPlain for OQ-16)

## 2026-11-21 02:14 · plan · programme-planner (backlog since 00:20; lean-causal held by /atlas-team)
- roadmap 64 → 68 targets: T-lad-plain-separations (keeper, ready), T-abs-gateline-local (ready; the possible DEC-8 finding: an OQ row is the master's to write only if the closer confirms it), T-abs-doubled-line-compact (ready), T-abs-hoist-plain-locz (ready; SingularFlatAxioms.causallyPlain is evidence for OQ-16 and rem:pas_plat, recorded in evidence only)
- now ready: T-abs-sbierski-prop-3-7, T-abs-gateline-witnesses, T-abs-hoist-cbg-gluing (exclusive; + correspondingSet, correspondingExt), T-tool-ladder-py (master; + emitted() skipping formless properties); T-abs-hoist-cbg-geometry stays needs-ruling with a refined question (Causal.CBG.cbg reaches only Causal.SingularFlat, through Geometry)
- binders rebound to the new layering (notes and headers); counts unchanged (ers 28 rows, layer 1 in Lean 17; sbierski 19, layer 1 in Lean 15)
- planner's findings: pushUp_of_causallyPlain_of_absolutelyMinimal (DeuxPushup, ETT-layer, T1) is an implication the ladder lacks (in T-lad-plain-separations); push_up ∧ chronal_neighbours ⇒ causally_plain argued, to be checked by T-abs-hoist-plain-locz; ett curation's extra_lean_files (:496, :867, :1223) will need the hoisted files
- commits: 98dafcf
- next: T-lad-plain-separations (keeper) now; T-tool-ladder-py (master) after it (both touch the ladder's checks); the three lean-causal closers (T-abs-sbierski-prop-3-7, T-abs-nested-converse, T-abs-nested-transfer) when /atlas-team frees lean-causal

## 2026-11-21 03:46 · wave of 5 · T-lad-plain-separations, T-tool-ladder-py, T-abs-nested-converse, T-abs-nested-transfer, T-abs-sbierski-prop-3-7
- T-lad-plain-separations (ladder): 7 counterexamples (lightlike line; deuxPushup, valid in the no-gluing reading only, cf. OQ-39), edge absolutely_minimal ∧ causally_plain ⇒ push_up (T1); 98 of 506 pairs; emitted with HEAD's tool while T-tool-ladder-py was in flight
- T-tool-ladder-py (tooling, master, delegated and verified): standing hypotheses, sorts, list `from` in [[fails]], conjunctive `at`, [[transfer]], namespace-exact names, labels checked, formless-edge skip; same classification on the current ladder (98 classified within one sort, 192 cross-sort ill-typed); 20-breakage fixture registered in selftest (every gate bites); 68 programme tests. For the keeper: migrate the four `under`s to `standing` (3 more rules: 20; Levin's edge stays skipped, LevinUtility imports a model); update ladder-keeper.md and the ladder header. For the publisher: build.py breaks on a list `from` in [[fails]] or a non-ambient `space`, shows implied-standing as unknown, does not read [[transfer]]
- T-abs-nested-converse (layer 1): Causal.NestedConverse; converse under arc-connectedness, bare counterexample (pointed line), trans; the rational line; audit clean
- T-abs-nested-transfer (layer 1): Causal.NestedTransfer; SC, SCO, time function to the narrower; tarentin not (spacelike line: first model proved GH and not tarentin), to the wider; audit minor (fixed at graduation)
- T-abs-sbierski-prop-3-7 (layer 1): Causal.SbierskiProp37; (i) ⇒ (ii) without A3 — the circularity the binder found is broken; the equivalence at regular points under arc-connectedness; (iii) fails at BTZ points; label unmarked; audit minor (fixed); OQ-65
- ladder: 23 properties, 22 checked implications, 25 counterexamples, 40 consequences; 98 of 314 pairs within one sort (192 ill-typed); causal_ladder 17 rules; keeper proposals pending (nested-converse 12 pairs, nested-transfer 14 pairs, the lightlike-line SC/time-function facts)
- binders: unchanged this wave (ers 28 rows, layer 1 in Lean 17; sbierski 19 rows, layer 1 in Lean 15) — the Sbierski Prop 3.7 row now has Lean
- gates: lean-causal ✓ (234 strict files, 0 sorry), ladder ✓, binder ✓, roadmaps ✓, full tests ✓, selftest ✓ (ladder fixture bites), blueprint ✓, hub make -k check ALL GREEN
- commits: 1e997bc 5185566 8044439 f868749 48d1cf0 e177ac8 6084e8e
- next: keeper pass (the standing migration + the nested/transfer [[fails]] and [[transfer]] entries); then wave: T-abs-chronal-neighbour-bridge, T-abs-pushup-not-open, T-abs-gateline-local (lean-causal ×3); publisher: build.py for the new ladder fields

## 2026-11-21 04:22 · wave of 4 · T-lad-classify-core, T-abs-chronal-neighbour-bridge, T-abs-pushup-not-open, T-abs-gateline-local
- T-lad-classify-core (ladder): every causality-sort pair classified (14 implied, 103 fails, 189 open with notes; 312 of 314 within a sort); `standing` migration; 7 [[transfer]] entries; causal_ladder 20 rules (Test 36 derived). The keeper asks the author to update `.claude/agents/ladder-keeper.md` for the new reading (an agent definition: not edited by the loop). Its target list for the planner: timelike-line-top (49 pairs), doubled line widened (45), flat time cylinder widened (44), Galileo ladder facts (40), gated-line extras (36), jump-line extras (28), rational-line extras (27), ChronalNeighbours.tarentin (a new edge), a Levin wrapper concluding HasTimeFunction, and tool proposals (backward reading of conjunctive edges in counterexample(), conditional transfers, premise-free Level-B facts)
- T-abs-chronal-neighbour-bridge (layer 1): three strictly ordered chronology strengths; equal under arc-connectedness or absolute minimality on T1; leaving theorems restated; globalLine, sierpinskiCausality; audit minor
- T-abs-pushup-not-open (layer 1): the jump line; ETT.tex:698 needs absolute minimality (no-gluing reading); audit minor (docstring qualifier added)
- T-abs-gateline-local (layer 1): the gated line causally open in the future and not in the past — the DEC-8 finding, holding in the no-gluing reading (the gated line is not absolutely minimal); audit minor (reading disclosed, SCOPE corrected); OQ-67, with an auditor's sketch of an absolutely minimal witness for the planner
- ladder: 23 properties, 22 implications, 35 counterexamples, 42 consequences, 7 transfers; 312 of 314 classified within a sort
- binders: unchanged (ers 28 rows, layer 1 in Lean 17; sbierski 19 rows, layer 1 in Lean 15)
- gates: lean-causal ✓ (237 strict files, 0 sorry), ladder ✓, binder ✓, roadmaps ✓, full tests ✓, selftest ✓; blueprint NOT rebuilt this wave: its build.py reads the ladder differently from the new tool ("1 violation"); the publisher is adapting it (reports/blueprint, in progress)
- commits: 52b8b45 b9bc26d 1cbb750 d41b625 6c0d59e 96488c6
- next: the blueprint fix (publisher, running); a planner pass for the keeper's model targets and the absolutely minimal DEC-8 witness; then lean-causal waves

## 2026-11-21 04:49 · plan + blueprint fix · programme-planner, publisher
- blueprint (publisher): reads the ladder only through tools/ladder.py; the "1 violation" was build.py's own TypeError on a list-valued [[fails]] from; new views for standing, space, transfers, open notes; `make check` gains an `agree` step (the page's ladder line equals the tool's); 0 page errors
- planning run: roadmap 68 → 79 targets. Finding: 43 of the 193 [[open]] entries are already settled by merged Lean (jump line, gated line, isolated/global lines) — T-lad-record-lines (keeper, ready); 89 more would be settled by absolutely minimal witnesses alone (T-lad-record-minimal), the rest in the no-gluing reading only (T-lad-record-no-gluing). Ready layer-1 targets: T-abs-dec8-minimal-witness (the OQ-67 auditor's sketch), T-abs-pushup-of-minimal-local (a T1 edge; if it holds, under gluing local and global push-up/causal openness coincide — a finding for OQ-67 (b)), T-abs-chronal-neighbours-tarentin, T-abs-hoist-levin (exclusive), T-abs-rational-line-extras, T-abs-timelike-line-top and T-abs-galileo-ladder (no-gluing; Galileo would be evidence for OQ-18). Binders: mghdprop:EquivCha on Causal.SbierskiProp37 (sbierski layer 1 in Lean 15 → 16); mghdlem:ExtendIso's A3 entry no longer circular
- commits: 3d20bce 763932c
- next: wave: T-lad-record-lines (keeper), T-abs-dec8-minimal-witness, T-abs-pushup-of-minimal-local (lean-causal ×2, within the shared cap with /atlas-team's 3 closers); then T-abs-hoist-plain-locz

## 2026-11-21 05:22 · wave of 3 · T-lad-record-lines, T-abs-dec8-minimal-witness, T-abs-pushup-of-minimal-local
- T-lad-record-lines (ladder): wave 10's separations recorded — 14 [[fails]] (gated, jump, isolated, global lines), the 43 [[open]] entries they settle removed, each separation's reading noted; Causal/Ladder/Test.lean re-emitted (43 comments, rules unchanged); checked by ladder.py
- T-abs-dec8-minimal-witness (layer 1): the half-lit line, absolutely minimal, causally arc-connected, GH, causally open in the future and not in the past — the printed J⁺-only causal openness is strictly weaker than DEC-8's in either reading of defi:causalite; ≪ empty, not tarentin; audit minor (paper attribution narrowed to ETT.tex:745–746 and OQ-9/DEC-8); OQ-69, kb/0074
- T-abs-pushup-of-minimal-local (layer 1): on T1, absolutely minimal ∧ locally push-up ⇒ push-up, a strict weakening of lem:pushup_local's hypothesis (rationalLine); local = global for push-up (T1) and causal openness under absolute minimality; T0 (vee) and the local hypothesis (halfChronoLine) both needed; audit minor (proof line numbers corrected); OQ-70, kb/0075
- ladder: 312/314 pairs classified within a sort, 22 implications, 49 counterexamples, 42 consequences, 7 transfers
- binders: ers-predictability 28 rows bound, layer 1 in Lean 17; sbierski-mghd 19 rows bound, layer 1 in Lean 16
- gates: lean-causal ✓ (239 strict files, 0 sorry), ladder ✓, binder ✓, roadmaps ✓, test_programme + test_roadmap ✓, blueprint check ✓ (0 page errors, agree), hub: all gates green
- journal: the headers of the twelve entries since 2026-11-20 19:35 were estimated times, each later than the commit that wrote it; set to those commit times
- commits: a45528d 175fb94 4e06808 87e2475 6975f3f
- next: wave: T-abs-hoist-plain-locz, T-abs-chronal-neighbours-tarentin, T-loc-quasilinear-one-sided (lean-causal ×3); the keeper has new material (the half-lit and half-chrono lines' separations, the T1 edge absolutely_minimal ∧ locally_push_up ⇒ push_up) for T-lad-record-minimal or a new keeper target

## 2026-11-21 05:56 · wave of 2 · T-abs-chronal-neighbours-tarentin, T-abs-hoist-plain-locz
- T-abs-chronal-neighbours-tarentin (layer 1): chronal_neighbours ⇒ tarentin with no separation axiom (Causal.ChronalTarentin); Z⁺ = Z⁻ = M already suffices, strictly weaker, not necessary (global and lightlike lines); isolated-line and global-line separations; audit minor (a REPORT sentence about the gluing reading fits tarentin → causally_arc_connected only); kb/0076. The target's evidence clause "the lightlike line has neither" was wrong: it is tarentin (ladder.toml already says so)
- T-abs-hoist-plain-locz (layer 1, hoist): the plainness criterion in the ETT layer (Causal.CausallyPlainLocZ), the SingularFlat/BTZ lemmas beside Causal.SingularFlat (Causal.SingularFlatPlain), 16 constants moved module only, none changed; new edge push_up ∧ chronal_neighbours ⇒ causally_plain; audit minor (the ledger-lookup effect overstated); ett curation rem:K_neq_I lists the new file (applied while the wave ran, so the working tree's ett ledger stayed green); kb/0077, kb 0061 and 0064 updated
- tools: tools/ledger.py decl_line resolves a curated decl by its last name component (BTZAxioms.K_neq_I passes against E0.K_neq_I); /atlas-team takes the fix (its planner, a master target)
- for the author: tarentin_of_Zplus_Zminus is the abstract step from rem:lorentz_tarentin (ETT.tex:783–784) to rem:tarentin_exemples' "Lorentzian manifolds are tarentin" (l.689), given there without proof; no OQ row (no reading in question)
- ladder: unchanged this wave, 312/314 pairs classified within a sort, 22 implications, 49 counterexamples, 42 consequences, 7 transfers; three new edges wait for T-lad-record-minimal (which also waits on T-abs-rational-line-extras, T-loc-flat-time-cylinder, T-abs-hoist-levin)
- binders: ers-predictability 28 rows bound, layer 1 in Lean 17; sbierski-mghd 19 rows bound, layer 1 in Lean 16
- gates: lean-causal ✓ (242 root imports, 0 strict sorry), ladder ✓, binder ✓, roadmaps ✓, test_programme + test_roadmap ✓, blueprint check ✓; hub: papers-check red on papers/benzecri (ledger.json differs from a rebuild) and gate-tests red through test_no_model_in_gates, both from /atlas-team's leased in-flight lean-benzecri scaffold files (T-bz-c2-cas-affin, T-bz-c2-developpement), not this loop's
- times: journal headers are UTC
- commits: ff0fd2f e278e3a 45809f9 b2e1e10
- next: wave: T-loc-quasilinear-one-sided, T-loc-flat-time-cylinder (lean-causal ×2, beside /atlas-team's 4); then T-abs-maximal-zorn, T-abs-rational-line-extras, T-abs-hoist-levin (exclusive), and T-lad-record-minimal

## 2026-11-21 06:50 · wave of 3 · T-loc-flat-time-cylinder, T-loc-quasilinear-one-sided, T-abs-rational-line-extras
- T-loc-flat-time-cylinder (layer 3, flat-gx): ℤe₀\𝐌ⁿ with every local ladder property and causal plainness, ≪ total, not causally compact for d ≥ 1 and compact for d = 0 (the timelike circle); absolutely minimal on every open set, so either reading; audit minor (the proposed [[fails]] entries' space = [] would misfire: record them with no space key); kb/0078. Flat model modules reach GXBasic/UniversalCover/Developing through Causal.Flat.Developing: the "no Port" rule for a model module reads as direct imports
- T-loc-quasilinear-one-sided (layer 3, quasilinear): ERS Lemma 4.86 with GH, S open/connected and S ⊆ U₁ unused, (4.83) as a 1/δ-Lipschitz graph, OneSidedBoundary, Thm 4.82 plugged with no restatement; labels unmarked on readings (OQ-73); audit minor, two docstring readings corrected by the master before graduation; binder 4.82/4.86: the lemma cited in open_reason, not under entries proving other nodes; kb/0081
- T-abs-rational-line-extras (layer 1): time function, open strong causality, ¬ locally causally open (one causal_ladder call), ¬ tarentin, ¬ plain, no chronal neighbours, ¬ causally compact; absolutely minimal on every open set; audit minor (README row's diamond formula restricted to rationals); kb/0079, kb/0080. The target's evidence "J_⊤(p, q) ⊆ ℚ" is ⊆ ℚ ∪ {p}
- curation: ett lem:corresponding_K lists Causal/CBG/NoCorresponding.lean, the one false short-name resolution in this loop's ledgers found by /atlas-team's planner, ahead of its tools/ledger.py fix (T-ledger-decl-fullname)
- for the author: OQ-73 (Lemma 4.86's readings (a) (4.87) as a curve-nested slope cone, (b) (4.83) on a cylinder chart; the typo at ghd_02_19.tex:1168)
- ladder: unchanged, 312/314 within a sort, 22 implications, 49 counterexamples, 42 consequences, 7 transfers; waiting for T-lad-record-minimal (now only on T-abs-hoist-levin): 3 edges, the cylinder's, the circle's and the rational line's [[fails]]
- binders: ers-predictability 28 rows bound, layer 1 in Lean 17; sbierski-mghd 19 rows bound, layer 1 in Lean 16
- gates: lean-causal ✓, ladder ✓, binder ✓, roadmaps ✓, test_programme + test_roadmap ✓, blueprint ✓, hub: all gates green
- commits: eeec2ae b50f7be 9bda56f 4d90fb7 dd78b53
- next: T-abs-hoist-levin (exclusive in lean-causal), then T-lad-record-minimal (keeper); after them, T-abs-maximal-zorn, T-abs-ers-unions, T-abs-ers-mughd

## 2026-11-21 07:36 · wave of 1 · T-abs-hoist-levin
- T-abs-hoist-levin (layer 1, hoist, exclusive in lean-causal): Levin's theorem in the ETT layer (Causal.LevinTimeFunction), 38 constants moved module only, no type or proof term changed; the duplicate locallyCompactSpace_of_globallyHyperbolic (two modules, one root: Lean merges equal-typed duplicates) is one copy; new wrapper GloballyHyperbolic.hasTimeFunction; audit minor (a test count misreported). The ladder edge globally_hyperbolic ∧ tarentin ⇒ time_function switched to the wrapper by the master in the same commit (otherwise test_programme's staleness check fails): causal_ladder 20 → 21 rules, Test 38 derived / 309 not derived; kb 0082, 0083 (pitfalls), kb/0065 updated
- tools: /atlas-team's T-ledger-decl-fullname landed (7314b34): ledger check resolves curated decls by full name; this loop's four ledgers pass, after 4d90fb7's curation
- ladder: 312/314 within a sort, 22 implications (one more checked edge emitted as a rule), 49 counterexamples, 42 consequences, 7 transfers
- binders: ers-predictability 28 rows bound, layer 1 in Lean 17; sbierski-mghd 19 rows bound, layer 1 in Lean 16
- gates: lean-causal ✓, ladder ✓, binder ✓, roadmaps ✓, test_programme + test_roadmap ✓, blueprint ✓, hub: all gates green
- commits: ad07121 4ccc6b5 c71956d
- next: T-lad-record-minimal (keeper; its last dependency is done): the three new edges, the cylinder's, circle's and rational line's [[fails]], the 16 settled [[open]] entries; beside it lean-causal closers T-abs-maximal-zorn, T-abs-ers-unions, T-abs-ers-mughd

## 2026-11-21 08:37 · wave of 1 + 3 · T-abs-hoist-levin (journal above), T-lad-record-minimal, T-abs-ers-unions, T-abs-ers-mughd
- T-lad-record-minimal (ladder): three new checked edges (AbsolutelyMinimal.pushUp_of_locallyPushUp under T1, ChronalNeighbours.tarentin, PushUp.causallyPlain_of_chronalNeighbours); 16 new and 6 re-pointed [[fails]] (half-lit, half-chrono, rational, cylinder, circle, global, lightlike lines), no space keys; 99 [[open]] settled (planner's 73 + 26 from witnesses it did not simulate); the vee (T0) kept out of the matrix because the tool counts every [[fails]] whatever its space; causal_ladder 21 → 24 rules, Test 42 derived / 310 not derived
- T-abs-ers-unions (layer 1): ERS Prop 4.63 (GH form without Geroch, inside a causally arc-connected curves-extending U₁) and Thm 4.75 (Thm 4.64 run per component), both unmarked (OQ-77); audit minor, eight findings fixed in docstrings and REPORT (two declaration docstrings by the master); binder rows 4.63, 4.64, 4.67, 4.75 rebound; kb 0084–0086
- T-abs-ers-mughd (layer 1): Remark 4.78 under subluminality, Thms 4.79 (MUGHD) and 4.80 (m-MGHD), all unmarked (OQ-78); audit 1 major (a false claim about UGHD overlaps in the account of the paper), fixed by the closer; audit 2 minor (one sentence corrected by the master); binder rows 4.78, 4.79, 4.80, Cor 4.73 rebound; kb 0087–0089
- for the author: OQ-77 (ERS 4.63/4.75 readings, paper findings at :843 and :1021), OQ-78 (ERS 4.78–4.80 readings (1)–(4), the record form of Remark 4.78, paper findings at :1061, :1063, :1072)
- ladder: 312/314 within a sort (245 fails, 51 open, 16 implied), 25 implications, 65 counterexamples, 42 consequences, 7 transfers
- binders: ers-predictability 28 rows bound, layer 1 in Lean 21 (17 before); sbierski-mghd 19 rows bound, layer 1 in Lean 16
- for the planner: the keeper's list (halfLightLine.dual, 4 pairs either reading; T-lad-record-no-gluing now 7 pairs; T-abs-doubled-line-compact settles no ladder pair any more; a space-aware refuted()/matrix with the vee as fixture; OQ-69's tarentin witness; the X → curves_extend and → time_function pairs); the ERS ledger has never carried Lean anchors (the binder holds the mapping), so its rows read "not yet formalised" where the binder shows layer 1 in Lean; T-loc-quasilinear-slice/-frontier are scoped to U₁ ∩ U₂ while Thm 4.75 wants them in a component; Causality.inextensible_connectedComponentIn is a hoist candidate
- gates: lean-causal ✓, ladder ✓, binder ✓, roadmaps ✓ (with /atlas-team's new stale_blockers rule), test_programme + test_roadmap ✓, blueprint ✓, hub: all gates green
- commits: 5f558c5 109bb64 c4e9d26 31ecdcd 462865d
- next: a planning run (programme-planner, alone) on the list above; then wave: T-abs-maximal-zorn, T-abs-gateline-witnesses, T-abs-timelike-line-top

## 2026-11-21 10:02 · plan + wave of 5 · planning run, T-tool-ladder-space, T-cur-ers-layer1, T-abs-halflit-dual-separates, T-abs-one-way-membrane, T-abs-maximal-zorn
- planning run (programme-planner, alone): 79 → 90 targets; T-abs-doubled-line-compact dropped (settles none of the 51 open pairs); the keeper's list, the ERS ledger anchors, the quasilinear restart scope and a hoist turned into targets (96e3a41)
- T-tool-ladder-space (master): refuted() and matrix count only counterexamples on ETT's spacetimes; a pair refuted only off them is fails-off, not classified, an [[open]] entry for it legal; check line gains ", R refuted off the ambient only" (0 today); fixture fails-off-contradiction; the publisher renders the class and fixed the fails view, which would have shown an off-ambient counterexample as a refutation
- T-cur-ers-layer1 (master): the ERS ledger shows its 21 rows with layer 1 in Lean as partial, unmarked (14 B, 7 D), 22 with Remark 3.56; binder and curation are two copies of one mapping, mirrored
- T-abs-halflit-dual-separates (layer 1): halflit.dual, either reading, 4 open pairs; audit minor (a quote restored, line citations replaced, by the master); kb 0090–0091
- T-abs-one-way-membrane (layer 1): OQ-69 answered YES in either reading, the one-way membrane on ℝ^{1+1} built in the ETT layer by hand; for prop:tarentin_topological_spacetime_causality no counterexample, but its printed proof's J⁻ step (:746) needs DEC-8's two-sided openness; audit minor (REPORT wordings); kb 0092–0093; OQ-80
- T-abs-maximal-zorn (layer 1): Chruściel Thm 2.2 abstractly (existence without rigidity, each hypothesis needed) and ERS Remark 3.56 on a fixed background; audit minor (three docstrings corrected by the master); binder row 3.56 rebound, curation mirrored; kb 0094–0097; OQ-81
- for the author: OQ-80 (may OQ-69 be closed as answered; is the J⁺-only form of the proposition worth a target), OQ-81 (Remark 3.56's readings; "infinitely many" proved nowhere in ERS)
- ladder: unchanged this wave (25 implications, 65 counterexamples; 245 fails, 51 open, 16 implied); waiting for the keeper: halflit.dual (4 pairs), the membrane (6 pairs, 2 shared), the vee (now recordable)
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22; sbierski-mghd 19 rows bound, layer 1 in Lean 16
- shared checkout: a third loop, egf, now holds tools/roadmap.py, tools/selftest.py, tests/test_roadmap.py, lean-egf, papers/egf; the shared caps now span three loops
- gates: lean-causal ✓, ladder ✓, binder ✓, roadmaps ✓, test_programme + test_roadmap ✓, blueprint ✓, hub: all gates green
- commits: 96e3a41 027db7a 599b0b0 570511d 57f8b4f 0dae971 1ebcbc4 1a0e3df
- next: T-lad-record-dual-vee (keeper); lean-causal back to /atlas-team's three ETT closers

## 2026-11-21 10:15 · wave of 2 · T-lad-record-dual-vee, T-cur-sbierski-layer1
- T-lad-record-dual-vee (ladder): the time-reversed half-lit line's two [[fails]] (either reading), 4 open pairs settled; the vee recorded with space = ["T0"] (no space, or T1, contradicts the T1 edge: T0 is the boundary), 0 pairs fails-off since both pairs it refutes are refuted on the ambient; the T1 of absolutely_minimal ∧ locally_push_up ⇒ push_up is now an entry, not a comment; Test.lean re-emitted (4 comments) and built in a window with no lake build running (the agreed pgrep check; /atlas-team's three ETT closers were working), Rules.lean unchanged
- T-cur-sbierski-layer1 (master): the Sbierski ledger reads 19 of 19 rows Lean-stated, partial, unmarked (3 B: OQ-40, OQ-65; 16 D)
- ladder: 25 implications, 68 counterexamples, 42 consequences; 249 fails, 47 open, 16 implied, 0 fails-off
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22; sbierski-mghd 19 rows bound, layer 1 in Lean 16
- gates: ladder ✓, binder ✓, roadmaps ✓, test_programme ✓, Causal.Ladder.Test built ✓, blueprint ✓; lean-causal package gate not run (/atlas-team's closers have unfinished scaffold files in it; this wave changed only generated comments there); hub: papers-check red on papers/egf (ledger.json differs from a rebuild) and gate-tests red through test_no_model_in_gates, both from the egf loop's leased in-flight work, not this loop's
- for the planner: the one-way membrane settles 4 more pairs (tarentin → causally_open, causally_open_future and their local forms) independently of T-abs-gh-without-tarentin
- commits: 39c3e41 39be167 2b1b77d c2327ec
- next: lean-causal is /atlas-team's (three ETT closers); this loop's next work outside it: T-tool-ladder-py-2 (master) if ready, else a quiet hold until lean-causal frees

## 2026-11-21 10:37 · wave of 1 · T-pub-progress
- T-pub-progress (publisher): reports/programme/2026-11-21/report.pdf, 8 pages, every number generated (164 macros, 14 tables) from a git archive of the pinned commit 963b755 by reports/programme/numbers.py, so the shared checkout's working tree never enters it; the ladder's history from each commit's own tool, not from the journal (whose ladder lines do not parse reliably); open questions by their first clause; make check: identical numbers and PDF across two builds, no undefined reference, no legacy prose
- not delivered to the author through the session (no project thread to place a file): it is committed at reports/programme/2026-11-21/report.pdf
- gates: the report's make check ✓, roadmaps ✓, blueprint ✓
- commits: df6ba3a (+ roadmap)
- next: lean-causal is /atlas-team's; T-tool-ladder-py-2 (master, settles no pair today) or a hold until lean-causal frees for T-abs-gh-without-tarentin and T-lad-record-separators

## 2026-11-21 11:37 · wave of 4 · T-tool-ladder-py-2, T-abs-hoist-inextensible-piece, T-abs-one-way-membrane-chronal, T-abs-gh-without-tarentin
- T-tool-ladder-py-2 (master): counterexamples read backwards through conjunctive edges (no further pair settled; no contradiction the forward reading misses), conditional transfers kept out of the contradiction check, premise-free [[fact]]s; the fact `rigid` (every Level-B local model is rigid, Causal.CBG.eqOn_of_liftPropOn) classifies germ_extension, cauchy_slice → rigid: 314 of 314 pairs within a sort; the publisher's blueprint explains backward lacks from the tool's own results and shows facts; fact_edges added after the publisher found needed_standing ignored facts (bce2a8d)
- T-abs-hoist-inextensible-piece (layer 1, hoist): Causal.InextensiblePiece, 5 constants moved, none changed over 14899; audit minor
- T-abs-one-way-membrane-chronal (layer 1): the membrane with a chronology, chronal neighbours without push-up in either reading, 7 chronal_neighbours pairs; audit minor; kb 0111–0112
- T-abs-gh-without-tarentin (layer 1): the fork (GH, strongly causal, no time function) and the loop fan (GH, time function, not strongly causal), 8 pairs; prop:GH_fortement_causal, prop:GH_Jferme and Levin's edge sharp in tarentin (evidence, for the ETT ledger's notes); audit minor; kb 0113–0115
- ladder: 25 implications, 68 counterexamples, 1 fact; 314/314 within a sort (249 fails, 47 open, 18 implied); the keeper has 7 + 8 + the membrane's 4 tarentin pairs to record
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22; sbierski-mghd 19 rows bound, layer 1 in Lean 16
- gates: lean-causal ✓, ladder ✓, binder ✓, roadmaps ✓, tests ✓, selftest ✓, blueprint ✓; hub: papers-check green, gate-tests red once through test_no_model_in_gates while the egf loop rebuilt its leased lean-egf and papers/egf (green when rerun alone), not this loop's
- commits: bce2a8d ebcb66e cf4703e 28b4b95 e26b042 a400fd3
- next: T-lad-record-separators (keeper): the membrane, the chronal membrane, the fork and the loop fan

## 2026-11-21 11:57 · wave of 1 · T-lad-record-separators
- T-lad-record-separators (ladder, with the chronal membrane added to its scope by the master): 6 [[fails]] (one-way membrane and reversal, chronal membrane and reversal, the fork, the loop fan), all either reading; 19 [[open]] pairs settled (3 only through the tool's backward reading); entries the tool infers, or that move no pair, left out and named; Levin's edge, prop:GH_fortement_causal and prop:GH_Jferme noted sharp in tarentin; Test.lean re-emitted and built in a pgrep-clear window, Rules unchanged
- ladder: 25 implications, 74 counterexamples, 1 fact; 314/314 within a sort: 268 fails, 28 open (24 causality-sort, 4 geometry), 18 implied; refuted causality-sort pairs either reading 239, no-gluing only 28
- the 28 open pairs, by what they want: 16 X → curves_extend (T-abs-curves-extend-second-countable, a [[fact]] if proved); 4 causally_plain → (local) causal openness (no target: a plain, absolutely minimal, non-open model, necessarily push-up without chronal neighbours); causally_plain → locally_push_up (no-gluing only possible); chronal_neighbours → absolutely_minimal, causally_arc_connected (Galileo, T-lad-record-no-gluing, now only these 2); strongly_causal → strongly_causal_open (no model); 4 geometry pairs (the BTZ residuals)
- gates: ladder ✓, tests ✓, Causal.Ladder.Test built ✓, blueprint ✓; hub: papers-check red on papers/egf (the egf loop's in-flight ledger), not this loop's
- commits: a4e55ff ec86412 597acf7
- next: a planning run on the keeper's three proposals (T-abs-plain-not-open, T-abs-chronal-not-arc-connected, T-abs-sc-not-sco) and the shrunk no-gluing targets

## 2026-11-21 13:16 · plan + wave of 3 · planning run, T-abs-omega-one-constant, T-abs-chronal-not-arc-connected, T-abs-plain-not-open
- planning run (programme-planner, alone): 90 → 97 targets (4fa42e2); every open ladder pair has a target except strongly_causal → strongly_causal_open and the 4 geometry pairs; two targets dropped (they settled nothing any more)
- T-abs-omega-one-constant (layer 1, pure topology): continuous maps from ω₁ (and any well order of uncountable cofinality) into a T1 second countable space are eventually constant, each hypothesis sharp; audit minor (T0Space Prop IS a Mathlib instance under LowerUpperTopology; the curves target's step (2b) needs two right-excess steps per stage so the excess is never a single point); kb 0124–0126
- T-abs-chronal-not-arc-connected (layer 1): the rational-jump plane, absolutely minimal (rational subdivision) with chronal neighbours and not causally arc-connected; audit clean; kb 0127–0128
- T-abs-plain-not-open (layer 1): the notched plane, causally plain, push-up, GH, absolutely minimal, not causally open even locally; audit minor; kb 0129–0132
- ladder: unchanged this wave (74 counterexamples; 268 fails, 28 open); the keeper's next record (T-lad-record-plain-chronal) settles 5 pairs, leaving 23
- gates: lean-causal ✓, ladder ✓, binder ✓, tests ✓, blueprint ✓; hub: papers-check red on papers/egf and gate-tests through it, the egf loop's in-flight ledger, not this loop's
- commits: 4fa42e2 6e2337f c4616a5 0311ea4 94d85eb 7174f61
- next: T-lad-record-plain-chronal (keeper); T-abs-curves-extend-second-countable becomes ready-able (its ω₁ lemma done)

## 2026-11-21 14:32 · wave of 3 · T-lad-record-plain-chronal, T-abs-curves-extend-second-countable, T-lad-record-curves-fact
- T-lad-record-plain-chronal (ladder): the notched plane and the rational-jump plane, 5 pairs, either reading; the notched plane is the only counterexample to causally_plain ∧ causally_open_future ⇒ causally_open, the jump plane the only one to chronal_neighbours ∧ causally_open ⇒ push_up (Lemma K's edge does not reverse)
- T-abs-curves-extend-second-countable (layer 1): CurvesExtendOn W for every open W of every T1, second countable space, any causality, no other hypothesis (Causal.CurvesExtendSecondCountable: Zorn on towers of tail-free curves; direct limits at countable cofinality; the ω₁ lemma at uncountable cofinality with the audit's two right-excess steps; maximal ⇒ inextensible by trimming). The library's Inextensible (DEC-11/DEC-13) unchanged and audited as not trivialising the statement; the two strict docstrings that said the library does not prove it amended; audit minor; kb 0142–0145. The lean-causal package gate's scaffold step failed only on /atlas-team's in-flight CausalScaffold.MeasuresE0 (its sorries are permitted, its build was mid-edit); the strict build and the audit step were run alone and passed
- T-lad-record-curves-fact (ladder): [[fact]] curves_extend (T1, second_countable), the 16 X → curves_extend pairs implied; two Cauchy consequences; emit-lean's comment for a fact-implied pair corrected (tools/ladder.py)
- ladder: 25 implications, 78 counterexamples, 44 consequences, 2 facts; 314/314 within a sort: 34 implied, 273 fails, 7 open — chronal_neighbours → absolutely_minimal and causally_plain → locally_push_up (no-gluing reading only, targets T-abs-galileo-ladder and T-abs-plain-not-locally-pushup ready), strongly_causal → strongly_causal_open (no model), 4 geometry pairs (gx's BTZ residuals)
- consequences for the library (the audit and keeper): about 90 CurvesExtend(On) named hypotheses in 19 modules (Lemma K's hext among them) are now dischargeable on T1 second countable spaces; the CBG geometry fields A2 and B3 are redundant; on a T1 second countable space no point has a vacuous chart (LemmaKObstruction)
- from /atlas-team (for the planner/keeper): SFALocalE0.causallyPlain (every E₀-manifold is causally plain: evidence for OQ-16) and SFALocalE0.e0_topTotal_separates
- gates: lean-causal strict ✓ (scaffold step: /atlas-team's in-flight file), ladder ✓, tests ✓, selftest ✓, blueprint ✓, hub: all gates green
- commits: 7852b54 7923138 71b5cc7 47ead98 f59dee6
- next: T-bind-curves-extend (binders: curves_extend is now discharged at layer 1 on every ETT spacetime), T-abs-galileo-ladder, T-abs-plain-not-locally-pushup; a planner pass for the dischargeable hypotheses (ERS 4.72, c_ext_connexe) and the CBG fields

## 2026-11-21 16:44 · wave of 2 interrupted · T-abs-ers-4-72-second-countable, T-abs-c-ext-connexe-second-countable — the loop stops
- both closers stopped on an API error, the account's weekly limit (resets 2026-11-27 09:00 UTC); no REPORT.json was written. Their partial files are parked OUTSIDE the repository, so that no unheld file sits in the shared checkout: /home/maxbrain/ett-programme-wip/2026-11-21/ErsSecondCountable.lean (built alone, 3121 jobs, per the closer's last message) and CExtConnexeSecondCountable.lean (statements typecheck, proofs unfinished). Both targets are back to `ready`. To resume: copy the files back to lean-causal/scaffold/CausalScaffold/, re-take their leases, and continue the closers (their transcripts are saved) or dispatch fresh ones
- state at the stop: 106 targets; ladder 314/314 within a sort, 34 implied, 273 fails, 7 open; binders ers-predictability layer 1 in Lean 22, sbierski-mghd 16; open questions for the author OQ-69/80, 70, 73, 77, 78, 81, 86
- next when the limit resets: wave 22 again (the two targets above), then T-abs-ers-4-64-second-countable, T-abs-c-ext-connexe-cauchy, T-abs-galileo-ladder, T-abs-plain-not-locally-pushup; T-loc-cbg-curves-default waits on telling gx

## 2026-11-22 19:40 · wave of 3 · T-abs-ers-4-72-second-countable, T-abs-c-ext-connexe-second-countable, T-tac-ladder-dual
- rulings: the author's walk-through (DEC-147–206, d1c40af) landed during this iteration's set-up. It ruled the OQs of 8 blocked programme targets (OQ-40, 41, 51, 52, 57, 58) and the questions of the 3 needs-ruling ones (DEC-147, 197, 198). All 11 were moved to `planned`, the DEC prepended to their evidence, for the planner to rescope: each ruling reshapes its target, e.g. DEC-166 (b) makes OneSidedBoundary no node, and DEC-162 puts layer 3 in DEC-147's new Lorentzian package (f2a7833)
- T-abs-ers-4-72-second-countable (abstract, layer 1): resumed from the file parked on 2026-11-21. Causal.ErsSecondCountable proves InextensibleThrough W, SplitBy W S and IsAcausalOn W S on every T1, second countable space. ERS 4.72 (and _isConnected), 4.73, isUniqueDevelopment, 4.79 and 4.80 lose hmext and their through-hypotheses, each exactly its original less those binders, and 4.73 also holds from S Cauchy in a causally arc-connected U₁. Nothing marked. Audit minor, applied: ERS's curve at :983 is timelike and starts at x, while the Lean curve is an inextensible causal curve through x, which is all the proof uses. So the closer's REPORT note (9) ("ERS's curve needs no Lorentzian input") overstates. hsplit is discharged only where S is Cauchy in W for the same causality (kb 0218). kb 0218–0219
- T-abs-c-ext-connexe-second-countable (abstract, layer 1): resumed from the parked file. Its proofs were already closed; the closer removed two accidental certification marks and a twin of a model-reaching lemma. Causal.CExtConnexeSecondCountable: a Cauchy embedding is an open embedding (instances on N suffice). lem:C_ext_connexe's lemmas, Lemma 3.3, Thm 3.4's union, lem:image_diamant and lem:passe_pgcd hold without hDext, hext, hcover, and c_ext_connexe_of_connectedSpace_of_secondCountable has no named hypothesis left. sigma_separe follows from a Cauchy surface of a causally arc-connected M (narrower than the library's form, which the row keeps). Witness gateArc : ℝ → ]-1, 1[ is a Cauchy embedding that is not onto. Nothing marked. Audit minor, applied in the docstring. kb 0220–0222
- T-tac-ladder-dual (tactic): Causal.Ladder.Dual has 38 forward rules over the 18 causality-sort nodes. A transport fires only where C.dual is already in sight, by an aesop rule pattern. One-sided nodes are not transported (DEC-163); the time_function and curves_extend duals are re-proved locally. Causal.Ladder.DualTest has 425 examples, generated by its campaign script. Test.lean is unchanged with Dual imported. Written as new modules: an edit to Basic.lean would have rebuilt ErsMughd under the running ERS closer. Audit minor, applied: the termination argument is restated, since the pair rules do create a reversal; the depth limit can stop single goals with nested reversals in a large context; the replay is 0.2–0.6 s slower. kb 0223–0225
- ladder: unchanged, 23 properties, 25 implications, 78 counterexamples, 44 consequences; 314/314 within a sort: 34 implied, 273 fails, 7 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0
- gates: lean-causal ✓ (strict and scaffold, axiom sweep with Dual imported), ladder ✓, binder ✓, both roadmaps ✓ (/atlas-team repaired its own five blocked-on-ruled rows during the wave), tests.test_programme + test_roadmap ✓ (88), blueprint check ✓ (0 page errors). Hub: lib-check NOT RUN, because lean/ is held by /atlas-team mid-absorption (DEC-157) and a second lake build there would collide with it. The other hub gates ran. papers-check is red on barbot, ers-predictability, ett, sbierski-mghd: their ledgers' commit stamps are stale after this wave's lean-causal commits, and /atlas-team holds those ledgers. egf is red too, the egf loop's. gate-tests is red only through that papers-check. Nothing reverted
- pending for the master, blocked by /atlas-team's leases: (1) rebuild the ett, barbot, ers-predictability and sbierski-mghd ledgers; (2) curate the new declarations onto the partial rows: ERS 4.72/4.73/4.79/4.80 (papers/ers-predictability, with its ledger) and Sbierski welldefined, IsoDiffeo, ExMCGHD; the ETT rows are /atlas-team's; (3) an OQ row: may c_ext_connexe_of_connectedSpace_of_secondCountable anchor lem:C_ext_connexe? That reads singular flat spacetimes as T2, second countable topological spacetimes (ETT.tex:255, DEC-93) and 𝕄≥0-morphisms as IsEMorphism, and would lift the row's T-ett-cbg-e0 blocker (registers/DECISIONS.md held); (4) the lean-causal README rows of Causal.ErsSecondCountable and Causal.CExtConnexeSecondCountable (README held)
- for the planner: absorb DEC-147–206 into the programme roadmap. Chiefly: DEC-167, gluing in defi:causalite (a library refactor; absolutely_minimal becomes automatic, and the no-gluing-only targets T-abs-galileo-ladder and T-abs-plain-not-locally-pushup need re-reading); DEC-163/164/166 (a) (renames to the future base); DEC-159/160 (new ladder localisation properties); DEC-168 (prove plainness per model); DEC-172 (an open-problem ladder target); DEC-190 (the curves_extend consequence); DEC-197/198; DEC-147 (the Lorentzian package). Then rescope the 11 planned targets. T-abs-ers-4-64-second-countable's dependency is now done. The tactician proposes: raise causal_ladder's maxRuleApplicationDepth and maxSafePrefixRuleApplications in Basic.lean; have emit-lean import Dual into Rules.lean (no cycle); add a ladder `dual` field so emit-lean generates the dual rules; hoist dual_hasTimeFunction and CurvesExtend.dual into the ETT layer; shorten HalfLitDual, NotchedPlane, OneWayMembrane(Chronal) with the dual rules
- commits: f2a7833 3999b32 65646df df620bf 4515d20
- next: a planning run (programme-planner, alone) on the rulings; `wave` alone would pick T-abs-hoist-cbg-gluing

## 2026-11-22 20:55 · planning run · the author's walk-through absorbed; wave 23's pending integration done
- planning run (programme-planner, alone): 106 → 137 targets (bd8e2a0). Ready by owner: closer 14, keeper 6, planner 3, tactician 1, master 1; 1 needs-ruling (T-loc-lipschitz-plain: where Lipschitz metrics live).
  - The 11 ruled targets: 8 ready, 3 planned on new dependencies.
  - DEC-167's refactor is split into four steps: inventories (T-abs-gluing-generic, T-abs-gluing-models, ready), the master's design (lean-causal/docs/GLUING-DESIGN.md), then retype and the field switch, both exclusive.
  - Dropped: T-abs-galileo-ladder, T-abs-plain-not-locally-pushup and T-lad-record-no-gluing (their objects are no causalities under gluing); T-abs-hoist-cbg-gluing (subsumed by DEC-197); T-loc-cbg-curves-default (folded into T-abs-hoist-cbg-geometry, DEC-190).
  - T-loc-e0-plain recorded done at 5bcad0b (SFALocalE0.causallyPlain, DEC-168).
  - The planner simulated gluing on the ladder (no contradiction): implied 34 → 56, fails 273 → 250, open 7 → 5, and 3 pairs reopen (causally_compact, globally_hyperbolic, causally_plain → causally_arc_connected).
- wave 23's pending integration, now that /atlas-team released the paths:
  - curation: ERS rows 4.72, 4.73, 4.74, 4.79, 4.80 and Sbierski rows welldefined, IsoDiffeo, ExMCGHD carry the new second countable forms; all stay partial, no badge moved.
  - ledgers ett, barbot, ers-predictability, sbierski-mghd rebuilt; papers-check green.
  - lean-causal README rows for the three new modules.
  - Order matters: commit README edits to a Lean root BEFORE its ledgers, since any commit into the root moves their stamp.
- readings for the master's OQ rows, not yet written (registers/DECISIONS.md is held by /atlas-team):
  - (a) may c_ext_connexe_of_connectedSpace_of_secondCountable anchor lem:C_ext_connexe? This reads singular flat spacetimes as T2, second countable topological spacetimes (ETT.tex:255, DEC-93) and 𝕄≥0-morphisms as IsEMorphism.
  - (b) DEC-167's field: hereditary (every open set) or on M only? It blocks T-abs-gluing-design.
  - (c) DEC-167's non-minimal objects (gated line, deuxPushup, kb/0073): restate them for precausalities, or retire them?
  - (d) DEC-197: does SingularFlatAxioms become a ladder node, or do the consequences CBG consumes become the localisation properties?
  - (e) DEC-190 "dropped everywhere": do binder rows drop curves_extend now or once a form exists? Second countable forms beside the originals, or replacing them? Are CBG's A2/B3 curvesExtend fields removed?
  - (f) DEC-161 (b): is InextensibleNestedOn the nesting of record, with no no_causal_endpoint node?
  - (g) DEC-163 / OQ-80: does the J⁺-only form of prop:tarentin's (ii) ⇒ (i) deserve a target?
  - (h) DEC-168: where do Lipschitz metrics live?
  - (i) DEC-147: the package's name (lean-lorentz is a placeholder).
- ladder: unchanged, 314/314 within a sort: 34 implied, 273 fails, 7 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0
- gates: both roadmaps ✓, ladder ✓, binder ✓, tests ✓ (88), blueprint check ✓, papers-check ✓
- commits: bd8e2a0 89fea72 18da097 0657708 and the 18da097 restamp
- next: wave T-abs-gluing-generic, T-abs-gluing-models, T-abs-ers-4-64-second-countable (closers, lean-causal), T-lad-nested-inextensible (keeper), T-pkg-smooth-lorentz (master: the package set-up waits on its name, reading (i))

## 2026-11-22 23:10 · wave of 4 · T-abs-gluing-generic, T-abs-gluing-models, T-abs-ers-4-64-second-countable, T-lad-nested-inextensible
- before the wave: OQ-94–100 written (4b23217), the planner's readings; its reading of DEC-161 (b) not asked again (ruled: InextensibleNestedOn is the nesting). T-pkg-smooth-lorentz blocked on OQ-100 (the package's name)
- T-lad-nested-inextensible (ladder): inextensible_nested is a pair-sort node; no_causal_endpoint stays a definition. New [[fails]] le_nested ⇏ inextensible_nested (cutLine 1). Its witness is indirect: not_isCauchySurface_of_nested_bare, with the one-line step through IsCauchySurfaceOn.of_nested written out and compiled. Kept `checked`; a direct witness is the keeper's proposal 1. Two argued pair-sort [[open]] notes, six consequences, emit-lean unaffected (7b16a43)
- T-abs-ers-4-64-second-countable (abstract, layer 1): Causal.Ers464SecondCountable, beside the originals. Two kinds of form: `_secondCountable` (hext and through-hypotheses discharged) and `_of_isCauchySurfaceOn_secondCountable` (hacausal/hsplit traded, siblings). They cover Prop 4.63, Thm 4.64 and its variants, Rem 4.67, Cors 4.68, 4.69, 4.71, Lemma 4.70, Thm 4.82 and ErsUnions §1; 27 pairs compared binder by binder. Audit minor, applied in the docstring. kb 0226–0229 (c178342). Eight ERS rows curated, all partial
- T-abs-gluing-models (abstract): Causal.GluingModels inventories 75 concrete causalities in both gluing forms. 47 glue hereditarily, 28 do not, 17 of them refuted here first. The transparent-point line is the concrete object separating the forms. ModelScaffold stays in the scaffold (it imports CausalScaffold.GerochCauchy). Audit minor (b107106). The REPORT stays as written beside AUDIT-1, whose corrections are: withoutChronology transparentLine separates the forms too; topEnlarge/topTotal need T1 and two unrelated points; two citations; the def row is not "partial"; bowtie/fan were known non-local
- T-abs-gluing-generic (abstract, layer 1): Causal.GluingGeneric gives, construction by construction, which gluing form each preserves (24 rows). The M-only form fails exactly where an open piece becomes a space of its own. lem:precausalite_engendre_minimale holds in hereditary form from hereditary pieces. (G,X) is hereditary and unique; ofRelation glues iff its relations are diagonal. Audit minor, applied (cbbff41). kb 0230–0237 across the two gluing targets
- findings for the author, as OQ rows NOT YET WRITTEN (registers/DECISIONS.md held by /atlas-team, which has meanwhile used OQ-101 itself):
  - (1) ex:open_subset's first sentence (ETT.tex:260): its uniqueness still fails under gluing in either form, `Causal.openSubset_not_unique_of_absolutelyMinimal` (timeline restriction vs the diagonal causality, both hereditary; DEC-10/12's strong morphism). The cause is the morphism's direction, and the diagonal is OQ-13's witness. So DEC-167's "holds as printed" does not cover it, while the second sentence does hold. Which reading: reflects the relations / greatest, the local-isomorphism reading, or other?
  - (2) ex:causalities_lines item 4, Galileo's spacetime (ETT.tex:272–274), is not absolutely minimal for n ≥ 1 (`Causal.GluingModels.galileoOn_not_minimal`), so it is no causality under DEC-167, and rem:galileo_spacetime_not_strongly (l.670) is about a precausality. Is it meant with the causality its small opens generate, as a precausality (OQ-96), or retired?
- for the planner and /atlas-team:
  - puncturedPlane (the witness of hypothesis_a_needed, rem:K_plongement_hypotheses) is not absolutely minimal: T-abs-gluing-retype must restate it.
  - Many ETT rows rest on non-minimal witnesses (GluingModels' REPORT lists them).
  - Under the M-only field, existence at ex:open_subset l.262 is open in general (a target?).
  - The hereditary reading of lem:precausalite_engendre_minimale's "absolutely minimal on U_i" goes with OQ-95.
  - The keeper's proposals: a direct cutLine witness; pointedLine is no causality under gluing, so its [[fails]] curve_nested → le_nested should be re-pointed to rationalLine_separates_curveNested (Causal/NestedConverse.lean:413), and the argued [[open]] inextensible_nested → le_nested re-argued; a sub-arc form of exists_inextensible_of_t1_secondCountable; InextensibleNestedOn.refl/trans/dual.
  - The ETT rows of the gluing inventories are /atlas-team's to curate.
- ladder: 24 properties, 25 implications, 79 counterexamples, 50 consequences; 318/318 within a sort: 34 implied, 275 fails, 9 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓, hub `make -k check` all green (lib-check ran: lean/ is in-tree and unheld; its regenerated docs restored)
- commits: 4b23217 7b16a43 c178342 b107106 cbbff41 eda30f7 a377a7e
- next: wave T-tac-ladder-integration (tactician, exclusive in lean-causal) and T-lad-one-sided-node (keeper); write the two OQ rows when registers/DECISIONS.md is free

## 2026-11-23 01:00 · wave of 2 · T-tac-ladder-integration, T-lad-one-sided-node
- T-tac-ladder-integration (tactic, exclusive in lean-causal). causal_ladder now runs at depth 60 and Rules.lean imports Causal.Ladder.Dual, so every user reasons across C.dual. emit-lean emits checked causality-sort [[fact]]s as safe apply rules under their standing (plus forward rules when an edge reads them), and skips a witness module that imports Rules, as a cycle. Test.lean has 376 examples, every negative failing by exhaustion. tests: LadderEmitFacts; mutate.py 11 mutants, all red. lake build Causal: 8870 jobs (1735598).
  - PARTIAL: curves_extend's rule is not shipped. Causal.CurvesExtendSecondCountable imports Rules through MaximalZorn → ErsMughd. Test.lean tests the rule locally; kb/0221 rewritten.
  - The fix is the tactician's proposal 1: split Causal.AbstractDev (MaximalZorn.lean:122–746) into its own module, probe kept at campaign/T-tac-ladder-integration/scratch/AbstractZornProbe.lean. CExtConnexeSecondCountable, Remarks.SingularRowsK and SingularCauchy then need explicit imports. A target for the planner.
  - Audit minor. kb 0221/0223/0225 updated, 0238 added. 23 scratch probes kept outside the repository (~/ett-programme-wip/2026-11-22/T-tac-ladder-integration-scratch).
- T-lad-one-sided-node (ladder): one_sided_boundary is an edge hypothesis only (DEC-166 (b)). It appears as the consequence ERS Thm 4.82 at is_causal, with OneSidedBoundary in `under`. Header: DEC-166 (a)'s rename changes no ladder id. The pointed-line [[fails]] is flagged for re-pointing under DEC-167 (0ea179a).
- T-abs-hoist-cbg-geometry blocked on OQ-97: its field list is OQ-97's question, and the A2/B3 fields OQ-98 (c)'s.
- OQ rows still NOT WRITTEN (registers/DECISIONS.md held by /atlas-team all iteration): ex:open_subset's first uniqueness under gluing, and Galileo item 4 (journal 2026-11-22 23:10)
- for the planner:
  - the AbstractDev split (above);
  - the keeper's stale comment at programme/ladder.toml:483 ("a fact is none");
  - T-bind-ers-rulings: binder rows ThmNotBlocking and PropertyTimelike can point at the new consequence;
  - three binder targets ready and planner-owned (T-bind-ealpha-entries, T-bind-curves-corollaries, T-bind-sbierski-rulings), for a planning iteration.
- ladder: 24 properties, 25 implications, 79 counterexamples, 51 consequences; 318/318 within a sort: 34 implied, 275 fails, 9 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓, hub `make -k check` all green (lean/ docs restored)
- commits: 0ea179a 1735598 d9bbc32 78ef09e and the block
- next: wave T-lad-ers-restart-nodes (keeper), T-abs-gluing-compact-def, T-loc-ealpha-plain, T-abs-c-ext-connexe-cauchy (closers)

## 2026-11-23 04:30 · wave of 4 · T-lad-ers-restart-nodes, T-abs-gluing-compact-def, T-loc-ealpha-plain, T-abs-c-ext-connexe-cauchy
- T-lad-ers-restart-nodes (ladder): slice_restart and frontier_stays_in are edge hypotheses, not nodes; neither has a parameter-free form. 19 ERS §4 consequences (51 → 70) name them in `under`, with the second countable forms as witnesses (when they only drop binders) or as second entries (when they trade). Fact comment refreshed; matrix unchanged (e8f35dd)
- T-abs-gluing-compact-def (layer 1, pure topology): Causal.Gluing.CorrespondingCompact, Iff.rfl to the old inline hypothesis, with its pointwise and proper-map forms. DEC-160's compact and pair forms are stated against it. Witnesses: the exponential and shear gluings, the line with two origins. Audit minor, applied (5eed9ff). Two findings:
  - ETT.tex:2303–2304 (proof of prop:Cauchy_point_min): "c_n is entirely contained in C_1" is false as topology from prop:C_connexe alone (expGluing_not_subset_correspondingLeft) and true under the property. This sharpens the ledger's prop:C_connexe finding; the row's anchor takes another route and stays partial.
  - A continuous extension at corresponding points does not give the property, so "A3 ⇒ compactness" is not topology.
- T-loc-ealpha-plain (layer 3, E_α): every static spacetime over a geodesic metric space is causally plain. E_α is the 3+1 cosmic string of record, with 2+1 massive (every α) as corollary, plus regular parts, Minkowski and the half-plane (bf17b0b). Audit minor, in the REPORT. Its prop:K_calcul finding (l.1565 rests on prop:tarentin_fort_K, which assumes plainness, never proved for E_α or E≥0-manifolds in ETT.tex) needs more than one sentence for E≥0-manifolds: E₀'s plainness and theo:causalite_engendre's plainness clause, or the ledger's push-up repair.
- T-abs-c-ext-connexe-cauchy (layer 1): the sub-arc form of the curves theorem; trimming keeps inextensibility; inextensible_nested ⇒ curve_nested on T1, second countable spaces (curveNestedOn_of_t1_secondCountable, for the keeper's [[open]] entry). lem:C_ext_connexe's middle step: a Cauchy surface Cauchy in A and in B is Cauchy in A ⊓ B, without hDac/hDext. Nothing marked (OQ-94). Audit minor, applied (5d58a2f). Finding: ETT.tex:1940–1941's step is true but unargued; its "so" is circular, not backwards (audit).
- OQ rows STILL NOT WRITTEN (registers/DECISIONS.md held by /atlas-team the whole iteration): ex:open_subset's first uniqueness under gluing; Galileo item 4 (2026-11-22 23:10)
- for the planner:
  - the keeper's [[open]] inextensible_nested → curve_nested can become [[implies]] (standing T1, second_countable);
  - isCauchySurfaceOn_inf_of_secondCountable is a candidate consequence at is_causal;
  - the scaffold sorry exists_mem_image_inf (CausalScaffold.SubExtension:83) now has a second countable form: retire or restate it?
  - the keeper's proposals: an edge-hypothesis schema table (T-tool-ladder-edge-hypotheses); T-abs-ers-4-75-cauchy-form; witnesses for the 4.68/4.69/4.71/4.82 forms; T-lad-record-curves-corollaries' remaining entries;
  - CorrespondingCompact's ladder node (X side, Y side, or both: only both make the gluing's non-Hausdorff points closed) is T-lad-gluing-nodes';
  - three planner binder targets ready.
- ladder: 24 properties, 25 implications, 79 counterexamples, 70 consequences; 318/318 within a sort: 34 implied, 275 fails, 9 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓. Hub: papers-check red on papers/yamabe only (prop:nonpositive names Yamabe.Mfd.Reads.prop_nonpositive_csc, not yet in its files), /atlas-team's in-flight lean-yamabe, which it holds whole; gate-tests red through it. Not this loop's; nothing reverted. lean/ docs restored
- commits: e8f35dd bf17b0b 5eed9ff 5d58a2f a8d6840 3ebe20f
- next: wave T-lad-record-curves-corollaries (keeper), T-abs-hoist-lemma-k (closer, exclusive); a planning iteration soon for the accumulated proposals and the three binder targets

## 2026-11-23 07:00 · wave of 2 · T-abs-hoist-lemma-k, T-lad-record-curves-corollaries
- T-abs-hoist-lemma-k (abstract, exclusive refactor): the Lemma K family is ETT-layer.
  - Nine declarations moved verbatim with the same full names: LemmaKBare's static/E_α section and LemmaKSCLocal's Minkowski corollary went to the new model module Causal.Model.LemmaKModels; CurvesExtend.dual went to Causal.CauchyExtension.
  - LemmaKBare also dropped Causal.Splitting, which reached Flat.IsomCausal. model_path shows only the shortest chain (kb/0247).
  - ETT layer: 99/315 → 107/316 modules. 17191 constants; only the nine changed module, all hashes identical. lean-gx needs no edit at its bump. Audit minor (9287e1a).
  - Stale prose fixed at integration (LadderLocal, Ladder/Dual, SFAManifolds, kb/0181, three BARBOT docs, the ett curation note of def:singular_spacetime, the ladder's Lemma K comment); README row; kb 0246–0248.
- T-lad-record-curves-corollaries (ladder): 4.72 and 4.70 take their second countable witnesses (their `under` loses curves_extend and the through-clause); lem:C_ext_connexe takes the abstract second countable form (OQ-94 open). Two new consequences: eq_of_mem_image_inter at curves_extend, the Cauchy-in-A ⊓ B lemma at is_causal. New pair-sort edge inextensible_nested ⇒ curve_nested (T1, second_countable); its [[open]] entry is removed. DEC-190 recorded. Rules.lean re-emitted (one `-- skipped` comment) (b6c8212)
- ladder: 24 properties, 26 implications, 79 counterexamples, 72 consequences; 318/318 within a sort: 35 implied, 275 fails, 8 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0
- gates: lean-causal ✓ (after the docstring edits and emit-lean), ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓. Hub: papers-check red on papers/perforated only (ledger stale), /atlas-team's in-flight lean-yamabe and papers/perforated/ledger, both held by it; gate-tests red through it. Not this loop's; lean/ docs restored
- OQ rows still NOT WRITTEN (registers/DECISIONS.md held by /atlas-team): ex:open_subset's first uniqueness; Galileo item 4
- for the planner:
  - the duplicates curvesExtend_dual_iff and PushUp.causallyOpen_of_chronalNeighbours can now cite their originals;
  - DEC-190's CurvesExtend binders of the Lemma K family can now be dropped in ETT-layer modules (T-abs-curves-free-lemma-k);
  - inextensible_nested → le_nested stays open (the pointed line is no causality under gluing; T-lad-gluing-reading);
  - Prop 4.63 goes to T-lad-development-nodes.
- commits: 9287e1a b6c8212 4ea14ad 964abd2
- next: wave T-lad-record-rulings (keeper), T-abs-one-sided-future-base (closer, exclusive, DEC-166 (a)); then a planning iteration for the accumulated proposals and the three binder targets

## 2026-11-23 08:40 · wave of 2 · T-lad-record-rulings, T-abs-one-sided-future-base
- registers: OQ-107 (ex:open_subset's first uniqueness under gluing) and OQ-108 (Galileo's spacetime under gluing) written; DECISIONS.md was free at last (87ef5e2)
- T-lad-record-rulings (ladder). DEC-163: causally_open_future and causally_open are both nodes of record. A naming rule for comments; each edge and consequence names the openness node its witness takes. The one-way membrane is the separating edge of record; the gated line's entry is kept, commented as no-gluing only. New consequence prop:tarentin_topological_spacetime_causality (ii)⇒(i) at causally_open; whether the future form suffices is OQ-99. DEC-164: the T1 edge absolutely_minimal ∧ locally_push_up ⇒ push_up is labelled as lem:pushup_local's statement of record. Matrix unchanged (a02c4e4)
- T-abs-one-sided-future-base (abstract, exclusive refactor, DEC-166 (a)). ChronalFutureNeighbours and NoFutureEndpoint are the bases; ChronalPastNeighbours and NoPastEndpoint are their duals, each rfl-equal to its HEAD body. ChronalNeighbours and NoCausalEndpoint keep their meaning and order. 18 declarations added, 4 proofs changed, no statement changed (405 `#check @` byte-identical). Audit minor (1cef44b). kb/0053 and two README rows updated; kb 0249–0252, incl. the pitfall that `tools/ladder.py emit-lean --help` RUNS emit-lean (a tool fix for the planner)
- ladder: 24 properties, 26 implications, 79 counterexamples, 73 consequences; 318/318 within a sort: 35 implied, 275 fails, 8 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓, hub `make -k check` all green (lean/ docs restored)
- for the keeper's next pass: move the ladder comments citing ChronalPastNeighbours / NoPastEndpoint to the future names (programme/ladder.toml 273–286, 612–616, 637–640, 1686–1692; the stale LadderLocal line references at :266, :288, :2416, :2427)
- roadmap: 81 done, 36 planned, 9 ready (closer 5, planner 3, keeper 1), 2 blocked, 1 needs-ruling. The planner's three ready binder targets and the accumulated proposals (journal 2026-11-22 23:10 to this entry) wait for a planning run. Rule 2 calls one when fewer than two abstract/localisation targets are ready.
- commits: 87ef5e2 a02c4e4 1cef44b c09c5d1 ee549f9
- next: wave T-lad-has-chronal-neighbour (keeper), T-abs-hoist-dual-cover (closer, exclusive)

## 2026-11-23 10:30 · wave of 2 · T-abs-hoist-dual-cover, T-lad-has-chronal-neighbour
- T-abs-hoist-dual-cover (abstract, exclusive refactor):
  - dual_hasTimeFunction moved to Causal.CurvesExtend, after `end Causal`, so it keeps its universe variable.
  - lem:Sigma_separe's model-free steps (cover_of_t1_secondCountable and six more, with their witness) moved to the new ETT-layer Causal.CauchySeparation.
  - Two proofs re-pointed, no statement changed; 17209 constants, 9 changed module, 2 changed value. ETT layer 107/316 → 108/317. Audit minor (a295191).
  - At integration: CurvesExtend's earlier lines kept at HEAD's numbers, so six citations elsewhere stay exact; CauchySeparation's checklist names step (3)'s hchr; lem:Sigma_separe's curation lists the new file (the ett ledger check needed it); the CExtConnexeSecondCountable line references in programme/ +1; README rows; kb 0091/0244/0248 updated, 0253–0256 (0255 corrected: a universe rename shows in levelParams and the type hash, not in `#check @`).
- T-lad-has-chronal-neighbour (ladder, DEC-159): node has_chronal_neighbour (HasChronalNeighbourEverywhere, the everywhere form), with the edge chronal_neighbours ⇒ it.
  - Counterexamples: the lightlike line, the closed half-line, the notched plane and the global line (no-gluing). The notched-plane derivation was compiled by the master in a scratch file.
  - 36 new pairs: 2 implied, 34 refuted, 0 open. Eight consequences, including Lemma 2.17's ladder form and its boundary form (an edge hypothesis).
  - Comments moved to the one-sided future base. emit-lean: Rules imports ChronalNeighbourBridge, 25 edge rules (5117a6d).
- ladder: 25 properties, 27 implications, 83 counterexamples, 81 consequences; 354/354 within a sort: 37 implied, 309 fails, 8 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓, hub `make -k check` all green
- for the planner, the keeper's proposals:
  - T-abs-chronal-neighbour-conjoined: one-line conjoined witnesses for the notched plane and the global line;
  - E₀'s SingularFlatAxioms.hasChronalNeighbourEverywhere, layer 3 for BTZ, DEC-159's case;
  - a dual rule for the node (Causal.Ladder.Dual);
  - sigma_separe_of_nonemptyChronalCones as a consequence;
  - T-lad-gluing-reading now removes 21 non-minimal entries.
  Also the hoist's twin Jplus_inter_Jminus_eq / IsAcausal.Jplus_inter_Jminus (both cited, kept, kb/0256).
- commits: a295191 5117a6d 8756c67 c180669
- next: wave T-abs-curves-free-cauchy, T-loc-ealpha-tidy, T-abs-sc-open-without-tarentin (closers). Afterwards fewer than two abstract/localisation targets are ready (T-abs-dependence-domain-home, exclusive, stays), so a planning run comes next: the three binder targets and the proposals since 2026-11-22 23:10

## 2026-11-23 12:20 · wave of 2 · T-abs-curves-free-cauchy, T-abs-sc-open-without-tarentin
- T-loc-ealpha-tidy was left out of the wave although `wave` picked it: it moves a lemma into the strict upstream Causal.InextensiblePiece, which would rebuild under the other closers. So it is exclusive in effect; the planner should mark it `exclusive = true`.
- T-abs-curves-free-cauchy (layer 1, DEC-190): Causal.CurvesFreeCauchy.{CompactCauchy, CausalConvex, Basic}, 19 second countable forms beside the originals, each exactly its original less the curve binder. An elaborated scan found 45 curve binders; 26 already had a form elsewhere, all 26 verified by the audit. The ETT-layer binders still without a form are now in the Lemma K modules, ErsUnions/ErsMughd and Ladder.Dual only. Audit minor (d21912b); kb 0259–0260
- T-abs-sc-open-without-tarentin (layer 1): StronglyCausal.stronglyCausalOpen_of_causallyOpen gives strong causality plus two-sided causal openness ⇒ the open form, without tarentin. Weaker hull forms; the two readings of strong causality agree on causally open spacetimes. A counterexample to strongly_causal → strongly_causal_open is not causally open even at M. The future half alone does not open the hull (the one-way membrane), so whether causally_open_future suffices stays open. Witnesses: the timelike, spacelike and isolated lines (isolatedLine_stronglyCausal, new). Audit minor, applied (364ec2d); kb 0257–0258
- for the keeper:
  - the edge [strongly_causal, tarentin, causally_open] → strongly_causal_open can drop tarentin (new witness, standing []; no pair moves);
  - the "M = J⁺(Σ) ∪ J⁻(Σ)" consequence (programme/ladder.toml ~3085) can take IsCauchySurface.cover_of_t1_secondCountable;
  - the isolated line's [[fails]] can gain strongly_causal, strongly_causal_open, causally_open.
- ladder: unchanged, 354/354 within a sort: 37 implied, 309 fails, 8 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓. Hub: papers-check red on papers/bbs only (ledger stale), /atlas-team's in-flight lean-gx/scaffold/GXScaffold/BBS, which it holds. Not this loop's
- commits: 364ec2d d21912b 1cec96b 51d84ae
- next: a PLANNING RUN (programme-planner, alone). The ready closers are down to T-loc-ealpha-tidy and the exclusive T-abs-dependence-domain-home; the three planner-owned binder targets are ready (rule 2's binder clause in spirit); and the proposals since 2026-11-22 23:10 wait. The run takes those: the keeper edits above, emit-lean's argument handling, T-abs-chronal-neighbour-conjoined, E₀'s has_chronal_neighbour, the AbstractDev split for the curves_extend rule, the duplicates to merge, ealpha-tidy's exclusivity, and T-lad-gluing-reading's 21 entries.

## 2026-11-23 14:10 · planning run · waves 24–30's proposals folded in; the three binder targets done
- planning run (programme-planner, alone): 137 → 154 targets (03c1fa0); ready 5 → 20 (closer 10, planner 4, keeper 2, tactician 2, master 2); 2 needs-ruling, 2 blocked
  - 17 new targets: the keeper's ladder edits, the emit-lean argument fix (kb/0252), the edge-hypothesis table (tool + ladder + binders), the AbstractDev split so curves_extend's fact rule ships, the dual rule for has_chronal_neighbour, six layer-1 targets (direct cutLine witness, conjoined chronal witnesses, InextensibleNestedOn basics, ERS 4.75's Cauchy form and witnesses, ErsUnions' curve binders, the model-stranded duplicates), E₀'s has_chronal_neighbour (layer 3, DEC-159's BTZ case), and T-abs-scaffold-c-ext-connexe (needs-ruling)
  - promoted: T-lad-record-sc-open-edge, T-abs-curves-free-lemma-k, T-bind-ers-rulings, T-pkg-sbierski-schwarzschild; T-loc-ealpha-tidy made exclusive
  - every target that stays planned names its OQ (OQ-95/96/97/100/108) or its reason
- binders (cd2d694):
  - T-bind-curves-corollaries (DEC-190): the ERS rows 4.72/4.73/4.74/4.79/4.80 and the Sbierski rows welldefined/IsoDiffeo/ExMCGHD bound to the second countable forms; curves_extend left their localisation. Cor 3.2 / Thm 3.4's CBG assembly still reads the A2 field (OQ-98 (c), T-bind-cbg-hoist).
  - T-bind-ealpha-entries (DEC-188): E_α entries of record (the 3+1 cosmic string) on five Sbierski rows; none on ERS, whose localisation is g(u) and m on ℝ^{d+1}.
  - T-bind-sbierski-rulings (DEC-165): Prop 3.7 recorded; the regularity of p is owed per model.
  - A curation mirror: welldefined's decls gain isCauchySurfaceOn_inf_of_secondCountable (bd55874).
- reading for the author, as a needs-ruling target (not an OQ row): T-abs-scaffold-c-ext-connexe. The scaffold sorry IsCauchyEmbedding.exists_mem_image_inf (CausalScaffold.SubExtension:83) is proved on second countable spaces (exists_mem_image_inf_of_secondCountable). (a) Retire it with isCauchySurfaceOn_inf and c_ext_connexe and re-point the ett row; (b) restate it with second countability and close it; or (c) keep it as the open general statement? It goes with OQ-94.
- for /atlas-team: lem:C_ext_connexe's curation names the three scaffold declarations, and its finding "exists_mem_image_inf neither proved nor refuted" is stale for second countable N. Pending its findings from the gluing inventories: ETT rows on non-minimal witnesses; ETT.tex:2303–2304; prop:K_calcul's plainness gap; ETT.tex:1940–1941.
- ladder unchanged (354/354: 37 implied, 309 fails, 8 open); binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0
- gates: both roadmaps ✓, ladder ✓, binder ✓, tests ✓, blueprint ✓, papers-check ✓
- commits: cd2d694 03c1fa0 bd55874
- next: wave T-tool-ladder-emit-args (master), T-pkg-sbierski-schwarzschild (master), T-lad-record-cauchy-separation (keeper), T-tac-dual-has-chronal-neighbour (tactician), T-abs-curves-free-lemma-k, T-abs-cutline-inextensible-direct (closers)

## 2026-11-23 16:50 · wave of 5 · T-tool-ladder-emit-args, T-pkg-sbierski-schwarzschild, T-lad-record-cauchy-separation, T-abs-curves-free-lemma-k, T-abs-cutline-inextensible-direct
- held out of the wave though `wave` picked it: T-tac-dual-has-chronal-neighbour. It edits Causal/Ladder/Dual.lean, which Rules.lean imports, so about 30 strict modules would rebuild under the closers. Exclusive in effect; the planner should mark it `exclusive = true`.
- T-tool-ladder-emit-args (master, tooling): tools/ladder.py refuses an argument a subcommand does not take (exit 2), and -h/--help prints the usage, both before reading or writing anything. emit-lean --dry-run reports what would change. tests: LadderArgs, mutation-checked against the old main (df1fb2d)
- T-pkg-sbierski-schwarzschild (master, set-up): papers/sbierski-schwarzschild from the arXiv 1507.00601 v2 e-print, fetched today as data only. 30 statement environments carry schw-prefixed labels that reuse the author's names. Ledger on lean-causal, with the two introduction theorem* as twins of MainThm and DiamFinite; curation header; a three-fragment reading map; papers-check green (1eb6189). Its binder target T-bind-sbierski-schwarzschild is now ready.
- T-lad-record-cauchy-separation (ladder): the cover consequence takes IsCauchySurface.cover_of_t1_secondCountable; four lem:Sigma_separe consequences (IsAcausal.Jplus_inter_Jminus, sigma_separe_of_isOpen, sigma_separe_of_nonemptyChronalCones, sigma_separe_of_t1_secondCountable). Matrix unchanged (697178b)
- T-abs-cutline-inextensible-direct (layer 1): Causal.cutLine_separates_inextensibleNested is the direct witness for le_nested ⇏ inextensible_nested. At the audit's finding the master added the timelike line's gluing as conjuncts, so the witness stands under DEC-167 in either form. Audit minor, applied (895ccd8)
- T-abs-curves-free-lemma-k (layer 1, DEC-190): Causal.CurvesFreeLemmaK.*, 24 forms (with 7 already existing, all 31 curve theorems of the Lemma K family). One form is disclosed as a twin of CurvesFreeCauchy's. The remaining ETT-layer curve binders are in ErsUnions/ErsMughd and Ladder.Dual only. Audit minor (c37eba0)
  - Correction to the closer's keeper note (2): the two-sided Lemma K form is NOT subsumed by the lemma of record, which needs full CausallyOpen. It is subsumed by isCauchySurface_of_isLocallyCauchy_of_isOpen_Jplus_of_secondCountable (Causal/LemmaKSCLocal.lean:94), more general than the lemma of record.
- ladder: 25 properties, 27 implications, 83 counterexamples, 85 consequences; 354/354 within a sort: 37 implied, 309 fails, 8 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓ (86), blueprint ✓, hub `make -k check` all green
- commits: df1fb2d 1eb6189 697178b 895ccd8 c37eba0 24f0b57 88cfc89
- next: a PLANNING RUN (rule 2: a paper was set up), alone. It runs T-bind-sbierski-schwarzschild (planner-owned) and marks T-tac-dual-has-chronal-neighbour exclusive. Then the wave T-lad-record-sc-open-edge, T-abs-inextensible-nested-basics, T-abs-ers-4-75-cauchy-form, and the tactician alone.

## 2026-11-23 18:30 · planning run · the Schwarzschild binder; 154 → 171 targets
- T-bind-sbierski-schwarzschild (planner): papers/sbierski-schwarzschild/certificate/binder.toml, 30 rows bound, layer 1 in Lean 11 (d788814).
  - Lemma 2.17 is bound to the locating theorems with has_chronal_neighbour (DEC-159) and causally_arc_connected. These are properties of the extension M̃, so Sbierski's own layer 3 is the C⁰ class.
  - The metric rows (timelike and spacelike diameters) have no layer-1 statement.
  - future_one_connected and locally_strongly_causal are proposed as nodes.
  - Finding: Prop 6.5 prints (M_ext, g_ext) for the interior.
- planning (89a44cf): 17 new targets. They cover the causal skeleton of C⁰-inextendibility at layer 1 (T-abs-schw-causal-lemmas and T-abs-timelike-homotopy ready), its ladder nodes, and the layer-3 entries for C⁰ metrics (T-loc-c0-metric-causality, needs-ruling: where C⁰ Lorentzian metrics live), Minkowski and Schwarzschild. T-tac-dual-has-chronal-neighbour is now exclusive; T-tool-ladder-edge-hypotheses and T-bind-curves-ers-4-64 are ready.
- registers: the binder's readings as OQ-114 (Sbierski's Cauchy hypersurfaces, timelike curves, vs ETT's, causal curves, DEC-14) and OQ-115 (M̃ time-oriented by construction, the double-cover lift cited) (220fb62); R1 is the needs-ruling question of T-loc-c0-metric-causality
- ladder unchanged (354/354); binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0; sbierski-schwarzschild 30 rows bound, layer 1 in Lean 11, layer 3 in Lean 0
- gates: both roadmaps ✓, binder ✓ (3), tests ✓, blueprint ✓ (three binders), papers-check ✓
- commits: 220fb62 d788814 89a44cf 1d1c7d5
- next: wave T-tool-ladder-edge-hypotheses (master), T-lad-record-sc-open-edge (keeper), T-tac-dual-has-chronal-neighbour (tactician, exclusive in lean-causal)

## 2026-11-23 20:40 · wave of 3 · T-tool-ladder-edge-hypotheses, T-lad-record-sc-open-edge, T-tac-dual-has-chronal-neighbour
- T-tool-ladder-edge-hypotheses (master, tooling): a new ladder table [[edge_hypothesis]] (id, lean, what; label, reads, note) for the localisation hypotheses the rulings keep out of the nodes.
  - check: required keys, duplicate ids, no [[property]] id, the Lean name resolves.
  - matrix, emit-lean and the check line ignore it (the blueprint's ladder line is unchanged). tools/binder.py accepts its ids as localisation, open_localisation and proves ids.
  - Tests LadderEdgeHypotheses and BinderEdgeHypotheses; two fixture breakages (5654963). The keeper fills the table (T-lad-edge-hypotheses).
- T-tac-dual-has-chronal-neighbour (tactic, exclusive): Dual.lean's rule pair for has_chronal_neighbour; curvesExtend_dual_iff is a one-liner. DualTest 425 → 470, every negative failing by exhaustion. dual_closure.py now reads its edges off the shipped Rules.lean and guards against a missing pair. Audit clean (3653b3d); kb 0264, 0248 updated
- T-lad-record-sc-open-edge (ladder): the edge strongly_causal ∧ causally_open ⇒ strongly_causal_open (StronglyCausal.stronglyCausalOpen_of_causallyOpen) replaces the tarentin form. The isolated line's two [[fails]] gain strongly_causal, strongly_causal_open, causally_open. The [[open]] note is sharpened: the causally_open_future form is open too. Matrix unchanged.
  - emit-lean run by the master after the tactician: Rules imports Causal.SCOpenWithoutTarentin and swaps the rule; Test 5 derived rewritten, 3 negatives gone; DualTest regenerated against it (791b0aa)
  - for the planner, the keeper's T-abs-sc-open-hoist: SCOpenWithoutTarentin's model-free half into a lighter module, since Rules.lean now pulls in OneWayMembrane and NestedTransfer
- ladder: 25 properties, 27 implications, 83 counterexamples, 85 consequences; 354/354 within a sort: 37 implied, 309 fails, 8 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0; sbierski-schwarzschild 30 rows bound, layer 1 in Lean 11, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓. Hub: papers-check red on papers/perforated only (ledger stale), /atlas-team's in-flight lean-yamabe scaffold (it holds T-perf-* in lean-yamabe); gate-tests red through it. Not this loop's
- commits: 5654963 3653b3d 791b0aa 848b3ac 078b37e
- next: wave T-abs-inextensible-nested-basics, T-abs-ers-4-75-cauchy-form, T-abs-schw-causal-lemmas (closers)

## 2026-11-23 05:22 · wave of 3 · T-abs-ers-4-75-cauchy-form, T-abs-schw-causal-lemmas, T-abs-inextensible-nested-basics
- clock: this heading said 23:30. The headings from 2026-11-23 08:40 to 20:40 ran ahead of the clock; their commits are at 2026-11-23 00:04–04:10 UTC (git log -- programme/JOURNAL.md). From here on, headings are UTC from `date -u`.
- T-abs-ers-4-75-cauchy-form (abstract, layer 1): Causal.Ers475CauchyForm, ERS Thm 4.75 with "GHD" read "S Cauchy" (DEC-162) on a T2, second countable background, beside the originals.
  - IsCauchyLocalDevelopment (IsLocalDevelopment less acausal and split); ers_theorem_4_75_secondCountable and _eqOn_, at least as strong as the originals there; the 4.63/4.64 siblings with hacausal and hsplit traded for S Cauchy; IsCauchySurfaceOn.of_inter_eq. No causal arc-connectedness asked.
  - Audit minor (the 4.63 checklist row), applied (ee6ad88); kb/0218 refined, kb 0265–0266.
- T-abs-schw-causal-lemmas (abstract, layer 1): Causal.SchwCausalLemmas, Sbierski 1507.00601 §2 for any causality: Prop 2.7 (schw_prop_2_7), Def 2.14 (ChronallySeparatedOn, schw_def_2_14_iff), Lemma 2.17's leaving curve (exists_leaving_futureInextensible_of_isOpenEmbedding; Hausdorff is needed in futureInextensible_of_leaving only, witnessed by forkPoint_leaving_futureExtensible) and not_continuousExtension_preimage.
  - Audit minor (a line reference, two checklist rows), applied (873469e); kb 0267–0270.
  - The closer's binder notes for schwthm:Exterior and schwthm:Inex are inaccurate (not applied; the binder is the planner's).
- T-abs-inextensible-nested-basics (abstract, layer 1): Causal.InextensibleNestedBasics. InextensibleNestedOn.refl, .trans, .dual (and dual_inextensibleNestedOn_iff) take no hypothesis, since Inextensible carries CausalCurveIn.
  - Monotonicity in the open set is refuted in Lean (not_inextensibleNestedOn_mono) on Causal.CoarsePoint. That space is not T1, and every precausality on it is absolutely minimal on every open set (so either form of DEC-167 holds).
  - Sufficient condition: mono_of_inextensible (through Inextensible.restrict).
  - A Hausdorff circle refutation is argued, not in Lean. With both causalities causal on a T2, second countable space the question is open.
  - Audit minor (six wording items: the circle's relations written out, "nonempty W", kb/0142, the REPORT's package and 'why'), applied (a4ce20a); kb 0271–0272.
- ladder: 25 properties, 27 implications, 83 counterexamples, 85 consequences; 354/354 within a sort: 37 implied, 309 fails, 8 open (unchanged; the keeper records the new lemmas in T-lad-record-direct-witnesses)
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0; sbierski-schwarzschild 30 rows bound, layer 1 in Lean 11, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓ (106), blueprint ✓, hub: all gates green, no new red
- commits: ee6ad88 873469e a4ce20a 8c2dab5
- proposals for the planner:
  - Ers464SecondCountable's trade forms may not need harc either (the 4.75 route did not).
  - IsCauchySurfaceOn.of_inter_eq has a model-stranded twin to hoist.
  - T-abs-sc-open-hoist (kb from wave 32).
  - The isolated line's full form.
  - The Schwarzschild binder rows can now name SchwCausalLemmas' declarations, and ers-predictability's can name the Ers475 forms.
  - Monotonicity of inextensible_nested with both causalities causal, as a ladder [[open]] note or a target, and whether to put the T2 circle in Lean.
- next: wave T-abs-timelike-homotopy, T-loc-e0-has-chronal-neighbour, T-abs-chronal-neighbour-conjoined (closers, lean-causal)

## 2026-11-23 06:01 · wave of 3 · T-abs-timelike-homotopy, T-loc-e0-has-chronal-neighbour, T-abs-chronal-neighbour-conjoined
- T-abs-timelike-homotopy (abstract, layer 1): Causal.TimelikeHomotopy, Sbierski 1507.00601 Def 2.13 with timelike curves read as chronal curves.
  - Definitions: ChronalHomotopyOn (jointly continuous on [0,1]², chronal slices, fixed endpoints), ChronallyHomotopicOn, FutureOneConnectedOn, FutureOneConnected.
  - An equivalence on chronal curves; two-sided (dual_futureOneConnectedOn); invariant under IsCausalIso and ChartIso; reads only ≪.
  - The timelike line is future one-connected on every open set, non-trivially.
  - Row schwdef:timelike_homotopic_fixed_endpoints: proposed anchor FutureOneConnectedOn, partial (an incomparable class of curves under C0), unmarked.
  - Audit minor, applied (9448424); kb 0273–0274.
- T-abs-chronal-neighbour-conjoined (abstract, layer 1): Causal.ChronalNeighbourConjoined.
  - ChronalPast/FutureNeighbours.hasChronalNeighbourEverywhere.
  - notchedCausality_separates_hasChronalNeighbour (and its dual), with every recorded conjunct plus the node, hereditary minimality and the one-sided pair.
  - globalLine_separates_hasChronalNeighbour (with Tarentin; no gluing only); two bare forms.
  - The re-pointings were simulated in memory: no pair changes.
  - Audit minor, applied (c72ff51); kb 0276.
- T-loc-e0-has-chronal-neighbour (localisation, layer 3, E_0): Causal.Model.E0ChronalNeighbour.
  - HasChronalNeighbourEverywhere (the future disjunct, from mem_Zplus) for every SingularFlatAxioms causality, for E₀, for every causality with isomorphic DEC-25 charts (SFALocal; no minimality, separation or countability) and for E₀-manifolds.
  - exists_leaving applied with no restatement.
  - I⁻(p) ≠ ∅ ↔ p ∉ sing₀, so with a BTZ point the past and two-sided notions fail; E0.chronalFutureNeighbours holds.
  - Audit minor, applied (524cc76); kb 0275.
- Sbierski 1507.00601 findings, all verified by the audit; none in a register yet (the planner's T-cur-schw-layer1 or the binder's notes):
  - Thm 3.1 Step 2.1 (:572–579): the printed homotopy Γ(t,s) = (σ_{λ(t)} * λ|[t,1])(s) splits at s = 1/2. Its slices at t = 0 and at t = 1 are constant on half of [0, 1], so they are not timelike (Def 2.1, 2.13). The interior slices are fine. Fix: split at s = t, Γ(t,s) = σ_{λ(t)}(s/t) for s ≤ t and λ(s) for s ≥ t, with Γ(0,·) = λ.
  - :876 writes γᵢ(0), γᵢ(1) where γᵢ(t₀), γᵢ(t₁) are meant, and the homotopy is over [0,1]×[t₀,t₁].
  - :1623 writes γ(x₀⁻) where γ(y₀⁻) is meant.
- ladder: 25 properties, 27 implications, 83 counterexamples, 85 consequences; 354/354 within a sort: 37 implied, 309 fails, 8 open (unchanged)
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0; sbierski-schwarzschild 30 rows bound, layer 1 in Lean 11, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓, hub: all gates green, no new red
- commits: 9448424 c72ff51 524cc76 5a456e6
- proposals for the planner:
  - T-lad-record-direct-witnesses has every input in Lean now and can be made ready:
    - the cut line's direct witness;
    - the conjoined notched-plane and global-line witnesses (ladder :2545, :1910 required; :1884, :1891, :2372, :2397 optional);
    - InextensibleNestedOn.refl/trans/dual;
    - E0.hasChronalNeighbourEverywhere.
  - T-lad-c0-extension-nodes: future_one_connected has its Lean form (FutureOneConnected), a fact (timelikeLine_futureOneConnected) and dual transport (dual_futureOneConnected). locally_strongly_causal still waits on T-abs-diamond-confinement.
  - T-loc-minkowski-future-one-connected: its evidence quotes the printed Step 2.1 formula as the homotopy to formalise; use the s = t split.
  - Stranded: ChartIso.chronalCurveOn_image, chronalCurveOn_symm_image and chartImage_subset_target belong in Causal.GXStructure. The symm form duplicates Causal.Flat.curveOn_chart_symm (for T-abs-merge-stranded-duplicates).
  - Model-free homes (the E₀ closer's proposals): Causality.hasChronalNeighbourEverywhere_of_forall_mem_Zplus in ChronalNeighbourBridge, and E0LM.LocZplus.chronalFutureNeighbours in CausallyPlainLocZ.
  - inextensible_nested's monotonicity with both causalities causal (wave 33) as an [[open]] note or a target.
- next: rule 3 gives T-loc-ealpha-tidy alone (exclusive in lean-causal). Two planner targets are ready (T-bind-curves-ers-4-64, T-bind-ers-rulings), and the proposals above wait for the planner.

## 2026-11-23 06:41 · wave of 1 · T-loc-ealpha-tidy (exclusive)
- T-loc-ealpha-tidy (localisation, layer 3, E_α; exclusive, with the whole lean-causal package leased): Causal.Model.EAlphaCauchy is split. No statement of record changed and full names are unchanged.
  - Causality.inextensible_Iio_of_tendsto_not_mem is now in the ETT-layer Causal.InextensiblePiece (which gains no import).
  - The 24 static ℝ × X declarations are now in the new Causal.Model.StaticCauchy, which does not import Massive.
  - The withLp duplicates are replaced by mathlib's, and the unused Causal.CBG.Pgcd import is dropped (closure 47 → 37 modules).
  - New: Causal.halfPlane_separates (Causal.Model.HalfPlaneLadder).
  - Before/after constant dump: 68 constants changed module; the only proof-term change is properSpace_withLpTwo's. `lake build Causal` and `CausalScaffold` are green.
  - Audit minor (two docstrings, the README row, EAlphaPlain's reference), applied (6d471fa); kb 0055, 0056, 0066 updated; kb 0277.
  - emit-lean --dry-run: Rules and Test unchanged. The ett curation needs no change: rem:galileo_spacetime_not_strongly's declarations stay in EAlphaCauchy.
- For the keeper:
  - ladder.toml:1361–1363 still points to EAlphaCauchy.lean; the four lemmas are now at StaticCauchy.lean :109, :129, :132, :135.
  - :1366 ("no one Lean statement conjoins the two halves") is now false.
  - The nine half-plane entries (:1336–1358 and :1369–1397) can be re-pointed to Causal.halfPlane_separates. This joins T-lad-record-direct-witnesses' re-pointings.
- For the planner: papers/sbierski-mghd/certificate/binder.toml:71 and :76 cite the old EAlphaCauchy ranges (now :107–164 and :434–455).
- ladder: 25 properties, 27 implications, 83 counterexamples, 85 consequences; 354/354 within a sort: 37 implied, 309 fails, 8 open (unchanged)
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0; sbierski-schwarzschild 30 rows bound, layer 1 in Lean 11, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓. Hub: papers-check red on papers/gx and papers/yamabe only. Both are /atlas-team's in flight: gx's ledger (06:31) predates its lean-gx commit 4cdca6c (06:39), and yamabe has the CorYamabe scaffold it holds. Not this loop's.
- commits: 6d471fa 42baea6
- next: rule 3 gives T-tac-curves-fact-rule (tactician, lean-causal). A planning run is due soon: the proposals of waves 33–35, T-lad-record-direct-witnesses to make ready, and two ready planner targets.

## 2026-11-23 07:18 · wave of 1 · T-tac-curves-fact-rule (exclusive)
- T-tac-curves-fact-rule (tactic; exclusive, with the whole lean-causal package leased): curves_extend's [[fact]] is now a causal_ladder rule.
  - The split: Causal.AbstractDev (Chruściel's abstract-development Zorn block) moved byte for byte out of MaximalZorn into its own ETT-layer module importing Mathlib only. CurvesExtendSecondCountable now imports it instead of MaximalZorn, so it no longer reaches Causal.Ladder.Rules. Constant dump: 17602 before and after, 102 changed module, nothing else.
  - The master ran emit-lean. Rules.lean imports CurvesExtendSecondCountable and carries curvesExtend_of_t1_secondCountable as a safe apply rule (standing T1, second countable).
  - Test.lean's local registration is retired: 71 derived, 355 not derived. DualTest unchanged; mutate.py: 11/11 mutants killed.
  - ersrem:note_two_ghds_constructed's extra_lean_files gains AbstractDev. kb/0221 rewritten; Basic.lean, a ladder.py comment and a test docstring updated.
  - New constraint: no module in CurvesExtendSecondCountable's 31-module closure may use causal_ladder.
  - Audit minor, applied (7a62073).
- For the keeper: ladder.toml:618–640 (the curves_extend fact's comment) is stale. It still says the rule is skipped as a cycle and registered in Test, and :633–634 calls the time_function edge "the one CausalLadder rule for curves_extend". This goes with T-lad-record-direct-witnesses.
- For /atlas-team: reports/atlas/lean/edges-ers-predictability.json still gives MaximalZorn line numbers (e.g. ersMor_hypotheses :906 → :239), and facts-lean-causal.json gives Causal.MaximalZorn for the AbstractDev declarations, until the next `make -C reports/atlas`.
- ladder: 25 properties, 27 implications, 83 counterexamples, 85 consequences; 354/354 within a sort: 37 implied, 309 fails, 8 open (unchanged); Rules: 25 edge rules, 1 fact rule
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0; sbierski-schwarzschild 30 rows bound, layer 1 in Lean 11, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓. Hub: papers-check red on papers/gx and papers/bbs, and gate-tests red through them. Both are /atlas-team's in flight: their ledgers (06:31) predate its lean-gx commit 4cdca6c (06:39) and its BBS scaffold edits, and lean-gx pins lean-causal by git commit. Not this loop's.
- commits: 7a62073 4f8816e
- next: rule 3 gives T-abs-dependence-domain-home (closer, lean-causal). The planner backlog grows: waves 33–36's proposals, T-lad-record-direct-witnesses to make ready, and two ready planner targets.

## 2026-11-23 08:11 · wave of 1 · T-abs-dependence-domain-home (exclusive)
- 07:22: one iteration stopped at its preconditions. lean-gx/kb/INDEX.md and kb entries 0102–0104 were changed and held by no live loop (written 06:57, during /atlas-team's BBS wave). /atlas-team committed them at 07:45 (a42c925), and this iteration started at 07:43 on a clean tree.
- T-abs-dependence-domain-home (abstract, layer 1; exclusive, with the whole lean-causal package leased): DEC-198's rename.
  - Causal.Flat.dependenceDomain and its four lemmas are now in Causal.Causality, source unchanged but for the namespace.
  - The old names are @[deprecated] theorem/abbrev wrappers: the ledger and ladder scanners find these, which they would not find for an `alias`.
  - dependenceDomainOn is an abbrev of C.dependenceDomain W S. The two userless lemmas are kept (no deletion ruled).
  - 64 uses re-pointed; no deprecation warning left.
  - Constant dump with the old names substituted back: 17602 → 17607 (+5 wrappers), every pair matching.
  - Audit minor (kb/0047's sentence on rw and the abbrev), applied (bc2d546); kb 0278.
- For the keeper: ladder.toml:3681 and :3773 name Causal.Flat.dependenceDomain in comments (now Causal.Causality.dependenceDomain).
- Possibly for the author: Causal.Causality now has two names for one notion, dependenceDomainOn and dependenceDomain, with three duplicate lemma pairs. Deprecating dependenceDomainOn would be a further rename, and needs a ruling; not raised as an OQ yet.
- ladder: 25 properties, 27 implications, 83 counterexamples, 85 consequences; 354/354 within a sort: 37 implied, 309 fails, 8 open (unchanged)
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0; sbierski-schwarzschild 30 rows bound, layer 1 in Lean 11, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓, hub: all gates green, no new red
- commits: bc2d546 17a2031
- next: rule 3 gives T-abs-curves-free-ers-unions (closer). After it, one ready abstract target is left, so a planning run follows (rule 2).

## 2026-11-23 08:40 · wave of 1 · T-abs-curves-free-ers-unions
- T-abs-curves-free-ers-unions (abstract, layer 1): closed on the report, with nothing left to form and no module written.
  - The scan (kb/0259) over the 123 ETT-layer modules finds that the 10 CurvesExtend(On) binders of ErsUnions (7) and ErsMughd (3) are all covered: by Ers464SecondCountable (six exact, Rem 4.67's GH form stronger) and by ErsSecondCountable (three stronger, hthrough dropped too).
  - Across the strict library, 90 binders in 18 modules each have a covering second countable form. The auditor checked all 90 with the kernel. The scaffold's SubExtension keeps two, on statements resting on a sorry.
  - The target's premise (kb/0260's list) was stale.
  - Audit minor (a quote's source, and "the ETT layer" read as the strict library), applied (16b1d10); kb/0260 and kb/0262 updated.
- For the planner: only 2 of the 10 covering forms are instantiated on the timelike line. A witness-only follow-up (the union-lemma forms, 4.79/4.80) is cheap (kb/0011).
- ladder: 25 properties, 27 implications, 83 counterexamples, 85 consequences; 354/354 within a sort: 37 implied, 309 fails, 8 open (unchanged)
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0; sbierski-schwarzschild 30 rows bound, layer 1 in Lean 11, layer 3 in Lean 0
- gates: ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓, hub: all gates green, no new red (no Lean changed)
- commits: 16b1d10 ac8c0be
- next: a PLANNING RUN (rule 2: only one ready abstract target, T-abs-merge-stranded-duplicates). It folds in waves 33–38's proposals, makes T-lad-record-direct-witnesses ready, and runs the two ready planner targets (T-bind-curves-ers-4-64, T-bind-ers-rulings).

## 2026-11-23 09:12 · planning run · waves 33–38's proposals folded in; 171 → 181 targets
- Planner targets applied (886c471, set done):
  - T-bind-curves-ers-4-64: ERS rows 4.63, 4.64, 4.67, 4.68–4.71 name the Ers464SecondCountable forms (4.63 also Ers475CauchyForm's), and curves_extend leaves the binder (DEC-190).
  - T-bind-ers-rulings: DEC-161, DEC-162 and DEC-166 (b) are recorded as ruled. inextensible_nested is in rows 4.70, 4.71, 4.77, 4.79, 4.80; one_sided_boundary is cited at 4.82 and 4.86.
  - The Schwarzschild binder names SchwCausalLemmas, TimelikeHomotopy and the chronal-neighbour lemmas, with layer 1 in Lean 11 → 14. The 1507.00601 findings (Step 2.1, :876, :1623, :798, Prop 6.5) are recorded in it.
  - The sbierski-mghd static ranges are re-pointed.
- Targets (171 → 181):
  - Added, ready: T-lad-future-one-connected-node, T-lad-record-ers-cauchy-forms, T-abs-ers-4-64-without-arc, T-abs-ers-sc-witnesses, T-abs-isolated-line-conjoined, T-abs-hoist-stranded-homes (exclusive), T-abs-sc-open-hoist (exclusive; emit-lean after).
  - Added, planned: T-abs-not-future-one-connected, T-abs-inextensible-nested-mono, T-bind-schw-future-one-connected.
  - Planned → ready: T-lad-record-direct-witnesses (scope extended: the half-plane's nine entries, the stale comments, inextensible_nested's monotonicity), T-lad-edge-hypotheses, T-abs-diamond-confinement, T-abs-ers-witnesses, T-loc-minkowski-future-one-connected (the s = t split, not the printed homotopy), T-cur-schw-layer1.
  - T-lad-c0-extension-nodes is rescoped to locally_strongly_causal.
  - T-abs-merge-stranded-duplicates also takes the Cauchy-surface congruence twins.
  - Adding the future_one_connected node will drop the classified pairs below 354/354 until T-abs-not-future-one-connected gives a separation.
- registers: OQ-127 (dependenceDomainOn beside DEC-198's Causality.dependenceDomain; no target blocked) (79145f8)
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0; sbierski-schwarzschild 30 rows bound, layer 1 in Lean 14, layer 3 in Lean 0
- gates: binder ✓, both roadmaps ✓, tests ✓, blueprint ✓, hub: all gates green, no new red
- commits: 79145f8 886c471
- next: T-lad-record-direct-witnesses (keeper) and T-cur-schw-layer1 (master), with lean-causal closers from T-abs-diamond-confinement, T-abs-ers-4-64-without-arc and T-loc-minkowski-future-one-connected. /atlas-team has a closer in lean-causal (T-ett-geroch-iii-i), so at most two of the three fit under MAX_PER_PACKAGE.

## 2026-11-27 17:14 · wave of 5 · T-abs-strong-causality-lifts, T-lad-record-direct-witnesses, T-abs-diamond-confinement, T-abs-ers-4-64-without-arc, T-cur-schw-layer1
- 2026-11-23 09:14 and 09:35: two iterations stopped at their preconditions. lean-causal/scaffold/CausalScaffold/GerochIIIImpI.lean (/atlas-team's T-ett-geroch-iii-i) was outside every lease, so the loop stopped (two iterations without a commit). The author restarted it on 2026-11-27, on a clean tree. Since then: DEC-208–212, of which DEC-211/212 set the seven-package architecture, "plan now, move later", so nothing moves yet. The author's commit be6ff7f added 4 targets on the tamifying topology (171 + 10 → 185).
- T-abs-strong-causality-lifts (abstract, layer 1): the author's lifting statement of 2026-11-24.
  - Proved with M̃ causally arc-connected (stronglyCausal_lift; with tarentin, topology = Alexandrov), with the open form, the weak-morphism variant and the general form (stronglyCausal_of_lift: monotone maps and connected diamonds).
  - The printed form (curves to curves only) does not hold in either reading of DEC-167: not_stronglyCausal_lift_of_curves on symmRationalLine. That causality is absolutely minimal on every open set, its causal curves are constant, and it is not strongly causal.
  - The proof's step assumes ≤ of M̃ realised by causal curves. The intended instance satisfies this (DEC-33): a misprint of the hypothesis, not a gap. → OQ-145.
  - Audit minor (the refutation holds), applied (df08a2b5); kb 0293.
- T-abs-diamond-confinement (abstract, layer 1): Sbierski's homotopy confinement (i), diamond identification (ii) and the localisation LocallyStronglyCausal (iii), for any causality and with no separation axiom in (i).
  - The compact closures need only a locally compact R₁ space.
  - Paper: implicit steps only (:621 needs γ̃(−s₁) ≪ γ̃(0), from :491; Hausdorffness from :228; the tube lemma).
  - Audit minor (the equation is (3.2); the quote is at :1625), applied (db0e8e7f); kb 0291.
- T-abs-ers-4-64-without-arc (abstract, layer 1): ten `…_noArc` forms, each a trade form less harc with an identical conclusion: 4.64 ×3, 4.67, 4.68 ×2, 4.69, 4.71, 4.73, m-GHD.
  - No step uses the acausality of S in U₁. No paper finding.
  - Witnesses include densCausality, which is not causally arc-connected.
  - Audit minor, applied (959b867b); kb 0292; kb/0265's follow-up closed.
- T-lad-record-direct-witnesses (ladder): 16 [[fails]] re-pointed (cut line, notched plane ×3, global line ×3, half-plane ×9), and four consequences at inextensible_nested.
  - Non-monotonicity in the open set is recorded as a note: it joins a node to itself, so no pair can carry it.
  - E₀ is added to has_chronal_neighbour's layer 3, and the stale comments are rewritten.
  - Matrix identical, emit-lean not needed (552aa09f).
- T-cur-schw-layer1 (master): the Schwarzschild curation. 11 rows carry their layer-1 Lean, partial and unmarked: bucket D, or B for Def 2.12 (OQ-114). Thm 3.1 carries the Step 2.1 finding.
  - not_continuousExtension_preimage is kept out of decls: restate would read it as a refutation.
  - The intro's theorem* (MainThm's twin) is curated with its twin's Lean, so that build and curation agree. This paper is the only one with twins; tools/ledger_curate.py resets a twin's copied fields, and a tool fix would be the better cure.
  - Ledger: 12 of 30 statements Lean-stated (d89f204c).
- For the planner:
  - add harc forms of the lifting theorems and one refutation with gluing and continuity inside (the lifting audit);
  - Q4: T-loc-btz-tamifying-initial and T-loc-ealpha-tamifying-alexandrov must prove that ≤ is realised by curves for btzCylCausality and Ẽ_α;
  - locally_strongly_causal now has its Lean (T-lad-c0-extension-nodes can be made ready), with separation candidates the loop fan (in a module away from Rules) and the flat time cylinder;
  - binder rows 4.64, 4.68, 4.69, 4.71, 4.73 can drop causally_arc_connected once the trade forms' fate is decided (kb/0226);
  - the binder's schwlem:NormalForm note cites "(3.3)" for (3.2);
  - the DiamondConfinement anchors for the Schwarzschild rows (REPORT paper_rows).
- ladder: 25 properties, 27 implications, 83 counterexamples, 89 consequences; 354/354 within a sort: 37 implied, 309 fails, 8 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0; sbierski-schwarzschild 30 rows bound, layer 1 in Lean 14, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓, hub: all gates green, no new red
- commits: d89f204c 552aa09f 959b867b db0e8e7f df08a2b5 042cbeb8
- next: T-lad-record-ers-cauchy-forms (keeper), T-loc-minkowski-future-one-connected, T-abs-ers-witnesses, T-abs-ers-sc-witnesses (closers, lean-causal)

## 2026-11-27 18:17 · wave of 4 · T-lad-record-ers-cauchy-forms, T-loc-minkowski-future-one-connected, T-abs-ers-witnesses, T-abs-ers-sc-witnesses
- 17:17: one iteration stopped at its preconditions. lean-gx/scaffold/GXScaffold/BTZ/SectorAtlas.lean (/atlas-team's T-btz-blunt-vertical-ray) was outside every lease. It was committed by 17:38.
- T-lad-record-ers-cauchy-forms (ladder): three consequences added, with no causally_arc_connected: ERS Prop 4.63 and Thm 4.75 in the S Cauchy reading, and Rem 4.67's first sentence without harc.
  - Thm 4.64 and Cors 4.68, 4.69, 4.71, 4.73 are re-pointed to the stronger `_noArc` witnesses (4.64/4.68/4.69 at [GH, tarentin], no longer with causally_arc_connected).
  - The densCausality separation [GH, tarentin] ⇏ causally_arc_connected is noted, not recorded: no declaration conjoins it.
  - Matrix identical (b315ee6b).
- T-loc-minkowski-future-one-connected (localisation, layer 3, minkowski): minkowski_futureOneConnected for every n, on every convex open, and time-reversed.
  - Chronal curves of an open set of ℝ^{1,n} are exactly the continuous ≪-increasing maps.
  - Step 2.1 is proved, and so is the split at s = t.
  - The printed homotopy (:575–579) is refuted for every λ in ℝ^{1,n}. This is a proof-level defect; Step 2.1 stands.
  - Audit minor, applied (3247324f); kb 0295.
- T-abs-ers-witnesses (abstract, layer 1): every form of Cors 4.68, 4.69, 4.71 and Thm 4.82 has a timelike-line witness.
  - 4.68's Lean forms do not ask u₂ a development, so a disconnected U₂ gives a line witness. In the paper's reading 4.68 has no instance on ℝ (proved), nor with one flat causality on 1+1 Minkowski (argued).
  - 4.82's hstep is never exercised by a witness, and given the rest it is equivalent to the conclusion.
  - Audit minor, applied (913bbbf2).
- T-abs-ers-sc-witnesses (abstract, layer 1): the four union lemmas on a two-point S in a disconnected B with an infinite family of pieces; 4.79, 4.80 and the m-GHD's uniqueness (and its `_noArc` form).
  - The duplicate tarentinOn now cites ErsWitnesses'.
  - Audit minor, applied (77f00e76); kb 0294.
- For the keeper:
  - ladder.toml:2982–2985 says the 4.68 and 4.82 forms have no witness;
  - future_one_connected's node (T-lad-future-one-connected-node) can name minkowski_futureOneConnected;
  - 4.82's hstep shape (a form whose restart ranges over every region, so that a witness can exercise it?);
  - T-abs-dens-separates as a Lean target, for the densCausality [[fails]].
- For the planner:
  - binder papers/ers-predictability:308 (4.68 "no line witness") is stale;
  - the roadmap evidence of T-abs-ers-witnesses at :1724 suggests "Minkowski 1+1", which cannot work;
  - a paper-faithful 4.68 witness needs a non-flat causality or two causalities (layer 3);
  - the Schwarzschild binder's minkowski entry of Thm 3.1 can name minkowski_futureOneConnected and minkowski_chronallyHomotopicOn_segment;
  - non-convex opens of Minkowski (ℝ^{1,2} minus the time axis, argued not future one-connected) are a candidate for T-abs-not-future-one-connected.
- ladder: 25 properties, 27 implications, 83 counterexamples, 92 consequences; 354/354 within a sort: 37 implied, 309 fails, 8 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0; sbierski-schwarzschild 30 rows bound, layer 1 in Lean 14, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓, hub: all gates green, no new red
- commits: b315ee6b 913bbbf2 77f00e76 3247324f f17577d4
- next: T-lad-edge-hypotheses (keeper) and T-abs-isolated-line-conjoined (closer); then the three exclusive hoists, one at a time

## 2026-11-27 18:42 · wave of 2 · T-lad-edge-hypotheses, T-abs-isolated-line-conjoined
- T-lad-edge-hypotheses (ladder): the [[edge_hypothesis]] table has its five entries, each with its Lean body in `what`:
  - slice_restart (SliceRestart), frontier_stays_in (FrontierStaysIn), local_uniqueness (LocalUniqueness, fixed background; the CBG shape noted), one_sided_boundary (OneSidedBoundary);
  - chronal_neighbour_at_boundary (HasChronalNeighbour at every frontier point, DEC-159; not the node).
  - The first four match the ERS binder's [[proposed]] ids.
  - 26 consequences name them in `under` (23 ERS §4, 3 Lemma 2.17). Matrix identical (1b8e26a1).
  - Flagged: T-lad-development-nodes' planned node local_uniqueness (data form) would clash with this id. sbierski-mghd's binder lists local_uniqueness (data form) in open_localisation, which now resolves to the fixed-background edge hypothesis.
  - The keeper ran one read-only `git diff --stat`, against its rule; it changed nothing.
- T-abs-isolated-line-conjoined (abstract, layer 1): isolatedLine_separates decides all 19 causality-sort nodes on ℝ with no hypothesis.
  - New to the library: the isolated line is causally compact and globally hyperbolic, with a time function. Every diamond is [p, q], ∅ or {0}. It is still not tarentin: an either-reading witness of GH ∧ plain ∧ causally open ⇏ tarentin.
  - One witness for its two [[fails]] entries; re-pointing simulated, no pair moves.
  - Audit minor, applied (166420a2); kb 0296.
- For the keeper:
  - re-point ladder.toml:1805 (→ tarentin) and :2029 (→ has_chronal_neighbour) to Causal.isolatedLine_separates;
  - the comment at ≈ :2530–2534 credits nothing new for strong causality (in Lean since 364ec2d3, 791b0aa4); only causally_compact, globally_hyperbolic and time_function are new;
  - future_one_connected's node can name minkowski_futureOneConnected (T-lad-future-one-connected-node, next);
  - the stale "4.68 and 4.82 forms have no witness" at ≈ :2982–2985.
- ladder: 25 properties, 27 implications, 83 counterexamples, 92 consequences, 5 edge hypotheses; 354/354 within a sort: 37 implied, 309 fails, 8 open
- binders: ers-predictability 28 rows bound, layer 1 in Lean 22, layer 3 in Lean 0; sbierski-mghd 19 rows bound, layer 1 in Lean 16, layer 3 in Lean 0; sbierski-schwarzschild 30 rows bound, layer 1 in Lean 14, layer 3 in Lean 0
- gates: lean-causal ✓, ladder ✓, binder ✓, both roadmaps ✓, tests ✓, blueprint ✓, hub: all gates green, no new red
- commits: 1b8e26a1 166420a2 120d93a8
- next: T-lad-future-one-connected-node (keeper) with T-abs-merge-stranded-duplicates (closer, exclusive in lean-causal). After those, only two exclusive hoists remain ready, and the proposals of waves 39–41 wait for a planning run.
