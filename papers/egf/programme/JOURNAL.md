# EGF programme journal

One entry per `/egf-programme` iteration, newest last (format in `.claude/skills/egf-programme/SKILL.md` § 6).

## 2026-11-21 · set-up (DEC-141)
- the programme was created from the author's instruction of 2026-11-21 ("Build a team following
  the model of ETT dedicated to fully formalize and correct the EGF paper"); its charter is
  `README.md`, its rulings DEC-141
- roadmap: 20 targets seeded (`T-egf-universality` and `T-egf-families` continue here; their hub
  blocks leave with `T-egf-hub-handover`, since /atlas-team held the hub roadmap during set-up);
  corrections: 28 entries seeded from the ledger's findings (9 found, 19 proved)
- v2 working copy put under git (`~/Dropbox/ErgodicGFN arXiv/source`, first commit = camera-ready + stars)
- next: the planner alone (`T-egf-plan-wave-1`), then the wave `T-egf-adopt-dec141`,
  `T-egf-inflow-nonsingular`, `T-egf-universality`, `T-egf-repro-scaffold`

## 2026-11-21 · plan + adoption · T-egf-plan-wave-1, T-egf-adopt-dec141
- T-egf-plan-wave-1 (planner, alone by rule 2): 20 → 30 targets, 28 → 37 corrections. The Lean targets are cut to one closer each with disjoint labels (T-egf-inflow-nonsingular narrowed to theo:backward_policy; T-egf-loss now after it); new T-egf-universality-ergodic (C-29: with a finite invariant λ̂ ~ λ, ε-universality holds iff the policy is ergodic, so the mixing clause of Theorems B.1 and 3.4 can go), T-egf-mixing-criteria (C-30), T-egf-families-sphere (Bourgain–Gamburd is about SU(d), C-32), tori-minimal, sphere-dense-ergodic, spectral-gap-so3, and four correct batches; the repro targets are pinned to main.tex lines and figure files; C-29 to C-37 found
- T-egf-adopt-dec141 (master, beside the planner): 13 entries adopted under DEC-141 after reading each anchor against its corrected text (C-1, C-4, C-7, C-8, C-9, C-11 to C-16, C-19, C-27); the master wrote the missing `corrected` texts of C-4, C-14, C-15, C-16, C-19, completed C-4's anchor, and narrowed C-8's `printed` to the appendix (the planner's catch). cor:pinsker_negative_control and theo:backward_policy closed in their corrected forms (curation as T-ett-ruled-rows; docstring marks in EGF/SamplingCorollaries.lean:13 and EGF/BackwardPolicy.lean:11)
- held: C-18 (its anchor IsUniversalFamily is the printed exact definition; the ε-form is T-egf-universality), C-21, C-22, C-25 (OQ-47: the repair and the statement of B.1 presume λ̂ = λ), C-23 (a strengthening of a true statement: not a correction the standing ruling covers), C-26 (OQ-48)
- corrections: 18 found, 6 proved, 13 adopted, 0 applied, 0 reviewed
- ledger: 9/16 rows closed (bucket A), from 7
- v2: 4e74ce4 camera-ready (untouched); repro: not yet created (T-egf-repro-scaffold ready)
- gates: lean-egf ✓, corrections ✓, roadmaps ✓ (egf and hub), test_corrections + test_roadmap ✓, v2 build not needed, hub: all gates green
- commits: decb391 e2a70e3 a809fb1 6f95db0 (+ this) (hub)
- lease note: `lease.py drop` has no per-path form; dropping the ledger sub-lease released the base lease too, retaken at once
- T-egf-hub-handover not run: /atlas-team holds `roadmap` (its wave in lean-causal)
- asks: none new (OQ-47, OQ-48 stay open). For the author: C-23 (state Theorem B.1 under its weaker hypotheses in v2?) and C-29 (if T-egf-universality-ergodic proves it, the follow-up's "Universality then does need mixing", GFNCertified body/04_universality.tex, is contradicted too)
- next: wave of 5 — T-egf-inflow-nonsingular, T-egf-universality, T-egf-universality-ergodic (three closers in lean-egf), T-egf-repro-scaffold (experimenter), T-egf-hub-handover (master, when /atlas-team frees `roadmap`)

## 2026-11-21 · wave of 3 · T-egf-inflow-nonsingular, T-egf-universality, T-egf-repro-scaffold
- T-egf-inflow-nonsingular (close): F_in ≪ λ from the diffeomorphism decomposition as soon as the moves are nonsingular, on any measurable space, no inverse, no Jacobian (EGF.inflow_ac_of_map_ac, EGF.InflowAC.of_map_ac); sharp criterion, nonsingularity necessary for positive weights; f_in for σ-finite λ (needed: counterexample in AUDIT-1); main.tex:735-737 as printed with |J| = 1 for measure-preserving moves, the setting of every experiment; graduated as EGF/InflowNonsingular.lean; audit minor (fixed at graduation); C-6 proved and adopted
- T-egf-universality (close): def:universal_family and theo:universality closed in their corrected forms (EGF.IsUniversalFamilyEps, EGF.universality: ε-universality, outflows paired with π* dense in the non-negative cone); the printed "dense in L²" is unsatisfiable, the exact Definition 3.2 does not follow (Bool counterexample), the all-outflows reading is false, so the paired form is of record under the standing ruling (no OQ); graduated as EGF/UniversalFamily.lean; audit minor (fixed at graduation); C-18, C-20 adopted
- T-egf-repro-scaffold (repro): LBrunswic/egf-reproduction (private) at 06796fe; env egf (torch 2.11.0+cu128, CUDA visible); guard, six configs with their [unpinned] tables; make smoke 44 tests in 4 s, rerun by the master on node1 ✓; no GPU run yet
- master: the typos C-10 (its text now the λ-Jacobian of C-8), C-17, C-24, C-37 adopted; seven targets promoted to ready
- corrections: 12 found, 5 proved, 20 adopted, 0 applied, 0 reviewed
- ledger: 11/16 rows closed (bucket A), from 9
- v2: 4e74ce4 camera-ready (untouched); repro: 06796fe scaffold, smoke ✓
- gates: lean-egf ✓ (745 declarations, 9 modules), corrections ✓, roadmaps ✓, test_corrections + test_roadmap ✓, hub: papers-check red on papers/ett only (def:singular_spacetime: three Causal declarations not in their listed files), from /atlas-team's leased in-flight graduation (lean-causal/Causal/MaximalAEAtlasIso.lean, papers/ett); not this loop's, not reverted
- commits: c176df4 a2f6878 da18069 404b90b 59b7904 31af44f (+ this) (hub) · 06796fe (repro)
- for the planner: the experimenter's unpinned list (F_init, b and R weights, LR, lengths, batches, the RL map count, the filter split, the torus seam of raw-coordinate inputs); a possible finding: Algorithm 1's backward stop (l.400) uses δf_init/f_in where (f_init + δf_init)/f_in is expected; the squared weak-FM form (l.407) is sign-blind
- asks: none new (OQ-47, OQ-48 open; they now hold C-21, C-22, C-23, C-25 and C-26, and with them T-egf-correct-universality and T-egf-correct-defs)
- next: wave of 4 at the shared cap — T-egf-universality-ergodic, T-egf-loss (closers in lean-egf), T-egf-repro-torus-il (experimenter, the first GPU run), T-egf-correct-backward (corrector, the first v2 batch); T-egf-mixing-criteria and the hub handover when slots and /atlas-team's lease free

## 2026-11-21 · wave of 3 · T-egf-universality-ergodic, T-egf-loss, T-egf-repro-torus-il (active)
- T-egf-loss (close): Eq. (15) with the negative part controls the sampling error for b ≥ 1 + ‖dλ/dν_train‖_∞ (b > 0 is not enough); the KL decomposition of l.418 holds in the direction KL(κ ‖ κ̂/κ̂(𝒮)) and is false as printed even with both sides finite; Corollary 3.10 holds for that divergence; Algorithm 1's factors lie in (0, 1] with the corrected sign; graduated as EGF/Loss.lean; audit minor (fixed at graduation); C-2, C-3, C-5 adopted (C-5 now kind false), C-35 proved and held (OQ-84)
- T-egf-universality-ergodic (close): Theorem B.1 under ergodicity alone, for a finite invariant λ̂ ~ λ, with necessity needing no invariant measure (EGF.universal_iff_ergodic); universal non-mixing witnesses (circle translation, swap; their non-mixing is T-egf-mixing-criteria's); graduated as EGF/UniversalityErgodic.lean; audit minor (fixed at graduation); C-29 proved, held (OQ-85: a strengthening of a true theorem, not covered by the standing ruling)
- T-egf-repro-torus-il (repro): the first GPU run, still running (budget ≈ 4 GPU-hours); stays active into the next iteration
- the l.400 finding of T-egf-loss is a reading by its audit (what the backward buffer holds): OQ-83, not a correction
- the stale olean of EGF.UniversalFamily (the master's docstring edits of the last iteration, made after that iteration's lean-egf gate, comment-only) was rebuilt by this iteration's gate: green
- corrections: 7 found, 7 proved, 23 adopted, 0 applied, 0 reviewed
- ledger: 11/16 rows closed (bucket A); cor:pinsker_negative_control and theo:universality_true gain the new declarations and findings
- v2: 4e74ce4 camera-ready (untouched); repro: 06796fe (torus IL in progress)
- gates: lean-egf ✓ (988 declarations, 11 modules), corrections ✓, roadmaps ✓, registers ✓, test_corrections + test_roadmap ✓, hub: all gates green
- commits: bb7232d a664a93 9442319 1125a79 ca6f3cf afab43f (+ this) (hub)
- asks: OQ-83 (Algorithm 1's backward buffer, l.400), OQ-84 (which weak-FM term is of record, C-35), OQ-85 (adopt the strengthenings C-23, C-29 of Theorem B.1 in v2?); OQ-47, OQ-48 still open
- next: resume T-egf-repro-torus-il; top up with T-egf-families, T-egf-families-sphere, T-egf-mixing-criteria (closers) and T-egf-correct-sign (corrector, the first v2 batch) at the shared cap; T-egf-hub-handover when /atlas-team frees `roadmap`

## 2026-11-21 · wave of 4 (topped up) · T-egf-correct-sign, T-egf-correct-backward, T-egf-correct-sampling, T-egf-families; T-egf-repro-torus-il (active)
- T-egf-correct-sign (correct): C-1 to C-5 applied to v2 (abe4bc8): δf_init the negative part through Eq. (15), Corollary 3.10, Algorithm 1 and the normalization identity, the KL decomposition in its true direction; CHECK-1 minor (C-3 qualified to f_out > 0 / f_in > 0, C-5's +∞ case anchored and H(κ) assumed finite, one clause reworded; fixed by the master before the v2 commit); C-35 and OQ-83's f_init not applied
- T-egf-correct-backward (correct): C-6 to C-10 applied to v2 (e90ff4b): F_in ≪ λ derived from nonsingular moves, Appendix A's setting and the λ-Jacobian, a.e. weights with setwise uniqueness, the proof's notation and \end{proof}; CHECK-1 minor (σ-finite for finite; anchors; the Riemannian examples recorded as resting on unformalized standard facts)
- T-egf-correct-sampling (correct): C-11 to C-17 applied to v2 (256b365): TV with ½, termination proved, τ ∈ ℕ_{≥1} ∪ {∞} with the sampler's randomized stopping stated as Lean's instance, the stopping probability's version, the δF_init = 0 case, Corollary 3.9's proof, two typos; CHECK-1 major (C-13 claimed a larger class of stopping rules than Lean's sampler, C-14 a version-independence beyond the anchors, τ's range made termination vacuous): the master amended C-13 and C-14 to the Lean, one fix round, CHECK-2 minor
- T-egf-families (close): Bekka–Guivarc'h's Theorem 5 as a faithful named Prop, universality from ergodicity of the generated group, the printed Theorem 3.5 refuted by the constant model (C-31) and vacuous at d = 1; AUDIT-1 major fixed in one round (families as images of a model); AUDIT-2 still major on prose only (a false aperiodicity claim): not graduated, back to ready with the findings; committed in the scaffold (aeae8df)
- T-egf-repro-torus-il (repro): the first GPU run, still running; stays active
- master: gate-tests turned red with the register's progress (test_errata_lists_only_applied_entries assumed nothing applied): the test now checks the rule independent of the register's state (6b1c386); the hub gate run chained after the unit tests had read a stale log: rerun on its own, green
- corrections: 7 found, 7 proved, 6 adopted, 17 applied, 0 reviewed
- ledger: 11/16 rows closed (bucket A), unchanged (theo:universality_tori and theo:spectral_gap_tori wait for T-egf-families)
- v2: 256b365 EGF-C11..C17 (three batches: abe4bc8, e90ff4b, 256b365); repro: 06796fe (torus IL in progress)
- gates: corrections ✓, roadmaps ✓, test_corrections + test_roadmap ✓, v2 build ✓ (20 pages, no undefined reference), hub: all gates green
- commits: 04be17f f14b447 f3e71f6 aeae8df 9f46c26 6b1c386 (+ roadmap, this) (hub) · abe4bc8 e90ff4b 256b365 (v2)
- for the planner: new typo entries (|J| at l.229, `\delta_{Φ⁻¹(u))}` at l.773, "for any measurable X" at l.758, a stray comma under Appendix A's heading, `$\Finit$and` at l.163, (π*, f_out*) at v1 l.320 and l.846); C-30's and C-28 (a)'s aperiodicity sentences over-state; a found entry for l.400 (OQ-83); the experimenter's unpinned list
- asks: OQ-83, OQ-84, OQ-85 (new today), OQ-47, OQ-48 open
- next: T-egf-families (prose fix + third audit), T-egf-families-sphere, T-egf-mixing-criteria (closers), T-egf-correct-figures (corrector), the torus GPU run; a planning run soon for the typo entries

## 2026-11-21 · wave of 5 (topped up) · T-egf-families, T-egf-families-sphere, T-egf-mixing-criteria, T-egf-correct-figures; T-egf-repro-torus-il — stopped by the API usage limit
- T-egf-families (close): prose fix round 2 by the same closer; AUDIT-3 minor (three wordings, fixed at graduation); graduated as EGF/TorusFamilies.lean; theo:universality_tori partial (corrected form, C-28/C-31 wait for their sphere halves), theo:spectral_gap_tori a cited named Prop (Troyanov pattern)
- T-egf-mixing-criteria (close): the swap refutes l.273-274 in the gloss reading; in the operator reading l.273 lacks only the invariance of λ; the corrected criterion with exponential decay; C-29's non-mixing witnesses; OQ-47's alternative reading needs λ̂ σ-finite; AUDIT-1 minor (fixed in one round); graduated as EGF/MixingCriteria.lean; C-30 proved and adopted (its text now names λπ = λ)
- T-egf-correct-figures (correct): C-37 applied to v2 (97419c7): unique figure labels (the body's reference printed an appendix figure), Appendix E's ablations on ℝ², the two-spirals subcaption; CHECK-1 minor (the register said Appendix F)
- T-egf-families-sphere (close): closed by its closer (0 sorry; Bourgain–Gamburd as a named Prop with witnesses, the SO(2) refutation of l.830-833 (C-32), universality from ergodicity, a new l.307 finding), but its AUDIT-1 was cut off by the API usage limit: not graduated, committed in the scaffold (d0889b1), back to ready
- T-egf-repro-torus-il (repro): the experimenter ran 9 arms (15 runs) on the GPU and was cut off by the limit before its report; the master committed the collected results as partial and pushed (LBrunswic/egf-reproduction 6485f1a); back to ready
- the API usage limit (weekly; resets 2026-11-27 09:00 UTC) stopped both running agents: no agent can be dispatched before then, so the loop stops here
- corrections: 6 found, 7 proved, 6 adopted, 18 applied, 0 reviewed
- ledger: 11/16 rows closed (bucket A); theo:universality_tori partial (B), theo:spectral_gap_tori cited (C)
- v2: 97419c7 EGF-C37 (four batches: abe4bc8, e90ff4b, 256b365, 97419c7); repro: 6485f1a (torus IL partial)
- gates: lean-egf ✓ (1230 declarations, 13 modules), corrections ✓, roadmaps ✓, test_corrections + test_roadmap ✓, v2 build ✓, hub: all gates green
- commits: adca9aa b529fb3 f402610 06bf337 d0889b1 77054e8 ed5f89c (+ this) (hub) · 97419c7 (v2) · 6485f1a (repro)
- for the planner (first thing after the reset): split T-egf-correct-universality into the adopted entries (C-18, C-19, C-20, C-24) and those on OQ-47/OQ-85 (C-21, C-22, C-23, C-25), and T-egf-correct-defs (C-27 adopted, C-26 on OQ-48); a batch for C-30 (adopted); new typo entries (|J| at l.229, l.758, l.773, a stray comma, `$\Finit$and` at l.163, (π*, f_out*) at v1 l.320 and l.846, the two-spirals main caption, the depth-ablation caption, "lest stable", "2 hidden layer", "2spirals", "ie"); a found entry for l.400 (OQ-83); C-28 (a)'s aperiodicity wording; the reproduction config that copied "Appendix F"; kb entries proposed by the torus, sphere and mixing closers (in their REPORT.json) not yet written
- asks: OQ-83, OQ-84, OQ-85, OQ-47, OQ-48 open; the four v2 commits are ready for the author's review (git diff camera-ready..HEAD in ~/Dropbox/ErgodicGFN arXiv/source)
- next (after 2026-11-27 09:00 UTC): re-audit T-egf-families-sphere and graduate it; resume T-egf-repro-torus-il's report; a planning run; T-egf-hub-handover when /atlas-team frees `roadmap`

## 2026-11-22 · the author's rulings (no wave: agents unavailable until 2026-11-27 09:00 UTC)
- asked in the session at the author's request ("Raise OQ here"); recorded as DEC-142 to DEC-146, OQ-83, OQ-84, OQ-85, OQ-47, OQ-48 set RULED
- DEC-142 (OQ-83): reversed-sampler paths; l.400 corrected to (1 + (f_init + δf_init)/f_in)⁻¹ — needs a new corrections entry (anchor EGF.reverse_cont_ae_eq_backwardFactor)
- DEC-143 (OQ-84): Eq. (15)'s form everywhere — C-35 (proved) becomes adoptable
- DEC-144 (OQ-85): B.1 and 3.4 restated under ergodicity — C-29 (proved) becomes adoptable; C-23 (weaker mixing) superseded; the proof of B.1 in v2 must follow the ergodic route, which C-21 and C-22 (repairs of the printed proof) bear on: for the planner
- DEC-145 (OQ-47): the L²(λ) reading — C-21, C-22, C-25 no longer wait on a reading (check each against DEC-144)
- DEC-146 (OQ-48): def:egf with measure ergodicity of the generated group — T-egf-def-egf moved blocked → planned for re-scoping; C-26 to be re-written
- next (after the reset): adoption under DEC-142 to DEC-146 (master), then a planning run: the batches T-egf-correct-universality, -ergodicity, -defs re-cut to the rulings, a new entry and batch for l.400, T-egf-def-egf re-scoped

## 2026-11-22 · master only (adoption; agents unavailable until 2026-11-27 09:00 UTC)
- adoption under the new rulings: C-35 (DEC-143), C-29 (DEC-144; its anchors now include the non-mixing witnesses), C-25 (DEC-145; corrected text written by the master: Definition 3.3 names λ)
- held for the planner: C-21, C-22 (repairs of the printed B.1 route, which DEC-144 replaces), C-23 (superseded by C-29), C-26 (def:egf, DEC-146: measure ergodicity, not yet in Lean), and a new entry for l.400 (DEC-142)
- curation: theo:universality_true, def:summably_mixing, def:egf cite the rulings
- corrections: 6 found, 4 proved, 9 adopted, 18 applied, 0 reviewed
- ledger: 11/16 rows closed (bucket A)
- gates: corrections ✓, roadmaps ✓, registers ✓, tests ✓, hub: all gates green
- idle otherwise: every remaining target needs an agent (closer, auditor, corrector, checker, planner, experimenter), and none can run before the usage limit resets; the loop stops
- next (after the reset): a planning run (re-cut the universality, ergodicity and defs batches to DEC-142 to DEC-146; the l.400 entry; T-egf-def-egf), the re-audit of T-egf-families-sphere, the torus repro report

## 2026-11-22 12:04 · wave of 3 · T-egf-hub-handover, T-egf-families-sphere, T-egf-repro-torus-il
- agents run again this session; the usage limit noted on 2026-11-21 did not block dispatch
- T-egf-hub-handover (master): the hub roadmap's T-egf-families and T-egf-universality blocks removed (they live here); OQ-50 RULED (DEC-141); hub roadmap and registers checks green
- T-egf-families-sphere (close, resumed at the audit): AUDIT-1 minor (four points: SCOPE's import sentence, the anonymous SU(d) instances, C-32's unanchored d = 3 sentence, the l.307 quote), fixed at graduation by the master (instances named, sentence and quote fixed; the interrupted audit's probes removed); graduated as EGF/SphereFamilies.lean; theo:universality_sphere partial (B), theo:spectral_gap_sphere a cited named Prop (C); BourgainGamburdTheorem1 checked against the PDF of arXiv:1108.6264v1
- corrections: C-31 proved on both halves and adopted under DEC-141; C-28 stays found (the cat-map form is T-egf-tori-minimal, the density form for d ≥ 2 is T-egf-sphere-dense-ergodic), with the new l.307 finding (density omitted, EGF.not_universality_sphere_identity) recorded on it for its batch; C-32 stays found (its d = 3 sentence waits on T-egf-spectral-gap-so3, or on a text quoting it as cited)
- T-egf-repro-torus-il (repro, resumed at the report): REPORT.md written (325e7a6, pushed, private), 10 arms × 3 seeds, a DDPM 3x32 baseline, exact TV/KL on T², the App. D filter scan. Checkerboard 4x128 reproduced only with a periodic input encoding the paper does not state; the 3x32 star and two spirals of Fig. toyimg not reproduced; the advantage over DDPM reversed at 3x32; the printed sign does not train; only Eq. (15)'s form (C-35) keeps δ near zero; Corollary 3.10's bound vacuous. Checked: the result files exist, make smoke passes, every entry point calls scripts/guard.py. Flags: three short CPU trial runs overlapped a GPU job (one-job rule); tests/test_guard.py's import-order check narrowed to scripts importing egf_repro
- corrections: 5 found, 4 proved, 10 adopted, 18 applied, 0 reviewed
- ledger: 11/16 rows closed (bucket A); B 3, C 2 (every row now curated)
- v2: 97419c7 EGF-C37 (unchanged this wave); repro: 325e7a6 torus IL report
- gates: lean-egf ✓ (1510 declarations, 14 modules), corrections ✓, roadmaps ✓, test_corrections + test_roadmap ✓, v2 unchanged, hub: all gates green
- commits: 8ac31ca 95a2e50 ccff08b 0766cd6 58ceab9 2dfc692 (+ this) (hub) · none (v2) · f6020b2 27733af 325e7a6 (repro)
- asks: none open for EGF; the four v2 commits still await the author's review (git diff camera-ready..HEAD in ~/Dropbox/ErgodicGFN arXiv/source)
- next: `wave` gives T-egf-repro-rl alone (only experimenters are ready, one at a time); a planning run follows once fewer than two are ready: re-cut the universality, ergodicity, defs and families batches to DEC-142 to DEC-146 and C-31's adoption, the l.400 entry (DEC-142), C-26 re-written (DEC-146), T-egf-def-egf re-scoped, the closers T-egf-tori-minimal and T-egf-sphere-dense-ergodic made ready

## 2026-11-22 17:30 · wave of 1 · T-egf-repro-rl
- T-egf-repro-rl (repro): reproduced in LBrunswic/egf-reproduction 811da29 (pushed, private; REPORT.md generated from the CSVs): 48 runs (4 losses × the two move readings of C-34 × raw and periodic encodings × 3 seeds, the pre-registered values) and two 100000-step checks, about 5.1 GPU-hours. The stability claim reproduces qualitatively (L^div without R blows up, L^stable_2 stays bounded, R holds both down), and so does the density panel; the curve magnitudes do not (the stable flow 42-493× smaller, E τ of the blown-up flow ≥ 1.8e4 against 245, the regularized curves, the start near 20-35). Finding for T-egf-repro-report: the paper's regularized stable curve (F_out(S) ≈ 0.13, E τ ≈ 4.9) is not a flow-matching flow if F_init is uniform of mass 1 (F_out(S) ≥ 1/2 and E τ ≤ F_out(S) + 1); F_init is not stated. Deviations disclosed: the evaluation sampler's cap raised from 200 to 20000 steps before any run; the periodic encoding and the long-horizon check added. Checked: the result files exist, make smoke passes, every run went through scripts/guard.py, no job overlapped a GPU run
- master: the hub gate first failed on papers-check (egf): the ledger of ccff08b stamped lean-egf at d0889b1 because it was built before the graduation commit 95a2e50; rebuilt and committed (5cf78d5, stamp only). From now on the ledger is rebuilt after the target's commit, as § 5 orders
- corrections: 5 found, 4 proved, 10 adopted, 18 applied, 0 reviewed (unchanged)
- ledger: 11/16 rows closed (bucket A)
- v2: 97419c7 EGF-C37 (unchanged); repro: 811da29 RL checkerboard
- gates: corrections ✓, roadmaps ✓, test_corrections + test_roadmap ✓, lean-egf untouched, v2 unchanged, hub: all gates green (after 5cf78d5)
- commits: 5cf78d5 291aaa3 951502e (+ this) (hub) · none (v2) · a69083b 544794e 6ed2f65 811da29 (repro)
- asks: none open for EGF; the v2 commits still await the author's review
- next: `wave` gives T-egf-repro-sphere alone; after it fewer than two targets are ready and the planning run follows (the batches re-cut to DEC-142 to DEC-146 and C-31's adoption, the l.400 entry, C-26, T-egf-def-egf, the closers T-egf-tori-minimal and T-egf-sphere-dense-ergodic, the RL finding for the experiments batch)

## 2026-11-22 18:03 · planning run (rule 2: one target ready)
- correction to the 17:30 entry: with only T-egf-repro-sphere ready, rule 2 (plan) applied before rule 3, so this iteration planned instead of dispatching the sphere reproduction
- egf-planner: the batches re-cut to DEC-142 to DEC-146 (e0e11df). Ready now: closers T-egf-tori-minimal, T-egf-sphere-dense-ergodic, T-egf-def-egf (re-scoped to DEC-146); correctors T-egf-correct-universality, -algorithm (C-35, C-38), -typos (C-40 to C-43), -captions (C-44, C-45, C-47), -spelling (C-48); experimenters T-egf-repro-sphere, -ablations; master T-egf-kb-families, T-egf-corrections-superseded. Planned: -ergodicity (after -universality), -defs (after T-egf-def-egf), -families, -experiments, -repro-report, the SO(3) stretch, the v2 package
- corrections: 17 found, 4 proved, 10 adopted, 18 applied, 0 reviewed (49 entries; new C-38 to C-49)
- master actions owed before the batches they feed (the planner's list): C-35's batch to T-egf-correct-algorithm; C-38 proved and adopted (DEC-142); C-39 and C-21 adopted (DEC-144) and C-29's series sentence amended to the λ-invariant form, before -ergodicity; C-22, C-23 (and C-24, which C-39 replaces) to superseded once T-egf-corrections-superseded lands; C-26 after T-egf-def-egf; C-32 and C-33 adopted (DEC-141); the typo entries C-40 to C-45, C-47, C-48 proved and adopted (DEC-141); register hygiene (C-27's line, C-37's 'Appendix F', C-30's aperiodicity wording)
- genuine readings: none. Facts only the author can supply, wanted before the experiments batch: l.440's move count (12 or 20; the RL conclusions do not depend on it); whether Table nll's EGF row is filtered, and with what floor; whether the depth ablation (l.1003) is on R² (C-46 waits on this); optionally F_init and the weight of R in the RL experiment
- gates: corrections ✓, roadmaps ✓, test_corrections + test_roadmap ✓ (nothing else changed)
- commits: e0e11df (+ this) (hub)
- next: adoption by the master (the list above), then a wave of closers (tori-minimal, sphere-dense-ergodic, def-egf), one corrector (-universality first, or -algorithm), one experimenter (repro-sphere), the master's kb target

## 2026-11-22 18:54 · wave of 6 · T-egf-kb-families, T-egf-corrections-superseded, T-egf-correct-universality, T-egf-tori-minimal, T-egf-sphere-dense-ergodic, T-egf-def-egf
- rulings: the author's DEC-147 to DEC-206 (d1c40af) touch EGF only through DEC-187 (the spectral-gap theorems as named Props: what T-egf-families and -sphere did) and DEC-157 (OQ-1: absorb GFNBoundsLean in-tree; until the absorption lands, lean-egf keeps porting by copying); no egf target moved
- adoption (master): C-38 (DEC-142), C-39 (DEC-144, DEC-141); C-35's batch to T-egf-correct-algorithm; C-24 held out of the universality batch; C-21's batch to -ergodicity, C-22 and C-23 out of any batch
- T-egf-kb-families (master): kb 0020-0025 written from the three closers' proposals (bf20b2a)
- T-egf-corrections-superseded (master): `superseded_by` in tools/corrections.py (rules, closed(), errata, status), five breakages, two tests; C-22, C-23, C-24 superseded; ROOT resolved with realpath (through the ~/LeanArticles symlink the fixture's unbroken copy failed, so the fixture proved nothing); selftest: every gate bites (37e8781)
- T-egf-correct-universality (correct): C-18, C-19, C-20, C-25 applied (v2 a1ddcb0); CHECK-1 major (the Expressivity sentence, v1 l.238, still claimed exact flow matching; no entry covered it), the master extended C-18 to l.238 (ε and probability, qualified by Theorem 3.4's richness), one fix round, CHECK-2 minor (C-18's added_hypotheses, fixed in the register)
- T-egf-tori-minimal (close): AUDIT-1 minor (six wordings: the 'minimal four' finding reworded, the l.149 finding qualified by C-29, docstring quotes and tags, the 'printed theorem is false' citation), graduated as EGF/ToriMinimal.lean; the stretch landed (every SL_d(ℤ), d ≥ 2)
- T-egf-sphere-dense-ergodic (close): AUDIT-1 minor (the d ≥ 1 reading tagged, the witness's entries), graduated as EGF/SphereDense.lean; universality from density in SO(d+1) for every d ≥ 1, rational dense generators on 𝕊²
- T-egf-def-egf (close): AUDIT-1 minor (one REPORT sentence inverted), graduated as EGF/DefEGF.lean; def:egf marked in DEC-146's form (EGF.IsEGFErgodic); the auditor judges the nonsingular field an honest abstraction and the design settled by DEC-146, not a reading
- corrections: 11 found, 3 proved, 13 adopted, 22 applied, 0 reviewed; 3 superseded (C-26 under DEC-146; C-28 under DEC-141, DEC-144, DEC-187, with d ≥ 1 for spheres; C-32 and C-49 under DEC-141; C-33 under DEC-141)
- ledger: 12/16 rows closed (bucket A; def:egf closed); theo:universality_tori and theo:universality_sphere partial (B): corrected forms of record and proved, no strict module marks them yet
- v2: a1ddcb0 EGF-C18,C19,C20,C25; repro: 811da29 (unchanged)
- gates: lean-egf ✓ (1827 declarations, 17 modules), corrections ✓ (fixture ✓), roadmaps ✓, test_corrections + test_roadmap ✓, selftest ✓, v2 build ✓; hub: papers-check red on papers/ett, barbot, ers-predictability, sbierski-mghd (stale ledgers after the ETT loop's lean-causal commits 3999b32, 65646df; its wave, not reverted) and so gate-tests (test_no_model_in_gates runs the whole gate); egf's own red (def:egf's IsGroupErgodic outside its listed files) fixed in f599124
- commits: bf20b2a 37e8781 da524d6 0f51317 f7db95a 91479a6 ffa1ad7 f599124 fa7e506 1a3d4f8 (+ this) (hub) · a1ddcb0 (v2)
- asks: none open; the five v2 batches await the author's review (git diff camera-ready..HEAD)
- for the planner: an audited step marking theo:universality_tori and theo:universality_sphere in their corrected forms of record (C-28, C-31, C-49 adopted); T-egf-correct-defs (C-26, C-27 adopted) and -families (C-28, C-31, C-32, C-33, C-49 adopted) can be made ready (-families after -ergodicity, per its dependency); -ergodicity after this batch: C-21 (anchors, basis, added hypotheses) and C-29's series sentence to the λ-invariant form before it runs; new entries: v2 l.693 cites 'the proof of Theorem 3.4' (B.1's is meant; ergodicity batch), the typo 'a family of generative flow family' (l.250), the pair order (f_out*, π*) vs (π*, f_out*); kb proposals of the three new REPORTs (tori 5, sphere-dense 4, def-egf 5); the tori auditor's optional universality_tori_one_of_mem; the def-egf auditor's optional full-support witness (the cat map) for the converse direction
- next: `wave` gives T-egf-correct-algorithm (C-35, C-38) and T-egf-repro-sphere

## 2026-11-22 19:14 · wave of 2 · T-egf-correct-algorithm; T-egf-repro-sphere (continues)
- adoption (master): C-21 (DEC-141, DEC-144; anchored on the λ-invariant mixing criteria); C-29's series sentence narrowed to 'when λ itself is invariant' (the only case with a convergent series; the theorem DEC-144 rules is unchanged); T-egf-correct-ergodicity (C-21, C-29, C-30, C-39) and -defs (C-26, C-27) made ready, every entry adopted and the dependencies done (9f631d2)
- T-egf-correct-algorithm (correct): C-35, C-38 applied (v2 487763f); CHECK-1 minor (no fix round): the backward factor written with f̂_init, defined in the buffer sentence just above (the literal form widened an overfull box to 46pt; the checker confirms the meaning); register updated to the applied text
- T-egf-repro-sphere (repro): running on the GPU; stays active, resumed by the next iteration
- corrections: 11 found, 2 proved, 12 adopted, 24 applied, 0 reviewed; 3 superseded
- ledger: 12/16 rows closed (bucket A), unchanged
- v2: 487763f EGF-C35,C38 (six batches since camera-ready); repro: 811da29 (sphere in progress)
- gates: corrections ✓, roadmaps ✓, v2 build ✓ (no undefined reference after the final pass); lean-egf untouched
- commits: 9f631d2 52e756d (+ the roadmap status and this) (hub) · 487763f (v2)
- for the planner (CHECK-1 of the algorithm batch): l.386's 'b > 0' against the control's b condition (an optional C-35 round 2), which ν_train the b condition refers to and the estimator's missing sum over trajectories (a typo entry), the bound the b condition buys (an optional strengthening), and a found entry for the experiments batch: which loss form, b placement and backward factor the reported runs used (facts from T-egf-repro-report)
- next: resume T-egf-repro-sphere and top up: `wave` gives the next corrector (T-egf-correct-ergodicity)

## 2026-11-22 21:00 · wave of 2 (topped up) · T-egf-correct-ergodicity; T-egf-repro-sphere (continues)
- rulings: DEC-207 (the hub's public mirror LBrunswic/MathAtlas) concerns the hub, not v2 or the reproduction repository, which stay private; no egf target moved
- T-egf-correct-ergodicity (correct): C-29, C-39, C-21, C-30 applied (v2 0ff8347). CHECK-1 major: C-21's remark claimed the lifted partial sums work for L² densities (false for unbounded ones: the resampling kernel and F_term = (3/4)x^{-1/4}λ); the lead-in to Theorem 3.4 (l.261) and the Cesàro contrast (l.271) still announced the old hypothesis; the Discussion (l.664) described the replaced proof. The master extended C-21 (bounded densities, general ones after truncation), C-29 (l.261, l.271) and C-39 (l.664) in the register and dropped the unchecked Conze citation as C-30's adopted text does (main.bbl regenerated); one fix round; CHECK-2 minor. v2 is now 21 pages (the main body still ends on page 9)
- T-egf-correct-families made ready (C-28, C-31, C-32, C-33, C-49 adopted; its last dependency was -ergodicity)
- T-egf-repro-sphere (repro): still running (code at 4d5b197: the DEC-142 backward factor, the four NLL scorings, the main queue)
- corrections: 11 found, 2 proved, 8 adopted, 28 applied, 0 reviewed; 3 superseded
- ledger: 12/16 rows closed (bucket A), unchanged
- v2: 0ff8347 EGF-C29,C39,C21,C30 (seven batches since camera-ready); repro: 4d5b197 (sphere in progress)
- gates: corrections ✓, roadmaps ✓, v2 build ✓ (also from the tracked main.bbl alone); lean-egf untouched
- commits: 6064e77 cf0f61c (+ this) (hub) · 0ff8347 (v2)
- for the planner (CHECK-1/2): l.697-698's motivation and 'two transformations are sufficient' against the 'four' of l.149, l.306, l.321; l.702's spectral-gap sentence (C-30's criterion without λ invariant; 'spectral gap' no longer defined); a definition of a kernel's ergodicity (Walters' invariant sets); π*(x,A) against π*(s→Y); the visible equation-counter gap (39)→(46); l.701's 'summably mixing' against the remark's λ̂ = λ
- next: resume T-egf-repro-sphere and top up with the next corrector (`wave`: -defs or -families)

## 2026-11-22 20:35 · wave of 2 (topped up) · T-egf-correct-defs; T-egf-repro-sphere (continues)
- T-egf-correct-defs (correct): C-27, C-26 applied (v2 1fbdb0f): Definition 3.1 with a measurable policy summing to 1 and the generated group ergodic for λ (DEC-146); CHECK-1 minor, no fix round; register: C-27's printed line, its anchors without the topological EGF.IsEGF
- T-egf-repro-sphere (repro): still running
- corrections: 11 found, 2 proved, 6 adopted, 30 applied, 0 reviewed; 3 superseded
- v2: 1fbdb0f EGF-C27,C26 (eight batches since camera-ready)
- gates: corrections ✓, roadmaps ✓, v2 build ✓
- commits: f025740 5f52f56 (+ this) (hub) · 1fbdb0f (v2)
- for the planner (CHECK-1 of -defs): Appendix A's restatement of the definition (v1 l.731: without the two clauses, nonsingular one way); the Expressivity sentence's 'Ergodicity' (group vs kernel); kernel ergodicity undefined in v2 while zero weights are allowed (read in Definition 3.1's sense Theorem 3.4 fails: the identity move with weight 1); l.319's 'a continuous family of EGFs'; the 'ergodic measures ξ' of l.142, l.216
- next: top up with T-egf-correct-families

## 2026-11-22 21:00 · wave of 2 (topped up) · T-egf-correct-typos; T-egf-repro-sphere (continues)
- adoption (master): C-40 to C-43 (typos) under DEC-141 (579600d)
- T-egf-correct-typos (correct): C-40 to C-43 applied at eight sites (v2 f3a75ad); CHECK-1 minor (one marker at the end of a display row, harmless); each fix agrees with its Lean reading (EGF.coordJac, EGF.IsBackwardPolicy, EGF.GenerativeFlow)
- T-egf-repro-sphere (repro): still running
- corrections: 7 found, 2 proved, 6 adopted, 34 applied, 0 reviewed; 3 superseded
- v2: f3a75ad EGF-C40..C43 (nine batches since camera-ready)
- gates: corrections ✓, roadmaps ✓, v2 build ✓
- commits: 579600d c620586 3b42666 (+ this) (hub) · f3a75ad (v2)
- for the planner: l.759's 'for any $Y\subset\Statespace$' without 'measurable' (outside C-42's lines)
- next: top up with the next corrector (`wave`: -families or -captions)

## 2026-11-22 22:10 · wave of 2 (topped up) · T-egf-correct-families; T-egf-repro-sphere (continues)
- T-egf-correct-families (correct): C-28, C-31, C-32, C-33, C-49 applied (v2 a9c3b9d). CHECK-1 major: l.828 defined Q̄ as the algebraic real numbers, which made the newly quoted SU(d) theorem vacuous; B.3's lead-in still announced the spectral-gap route; l.821's free-group sentence was left unrestricted at d = 1 while l.293 now says d ≥ 2. The master extended C-32 (l.827-829: complex algebraic numbers, the lead-in on ergodicity) and C-28 (l.809, l.821, the l.818-820 conclusion; the S, T definition the corrector added to Theorem 3.5); one fix round; CHECK-2 minor
- T-egf-repro-sphere (repro): still running
- corrections: 7 found, 2 proved, 1 adopted, 39 applied, 0 reviewed; 3 superseded (left: the captions C-44, C-45, C-47; the spelling C-48; the experiments C-34, C-36, C-46)
- v2: a9c3b9d EGF-C28..C49 (ten batches since camera-ready)
- gates: corrections ✓, roadmaps ✓, v2 build ✓
- commits: 38fe786 29ed02e (+ this) (hub) · a9c3b9d (v2)
- for the planner (CHECK-1/2 of -families): proof text in Appendix B for the no-periodic-vector, T¹ and dense ⇒ ergodic routes (Lean: ergodic_torusAffine_of_noPeriodic, ergodicSMul_rotSphere); l.302's 'a continuous family of EGFs' (members at non-ergodic rotations are not EGFs); l.1022's 'theoretically minimal' (one move suffices); l.702's spectral-gap sentence; the leftover 'technical assumption' wording (l.293, l.307, l.836); l.888's sentence repeating the lead-in; and the audited marking of theo:universality_tori and theo:universality_sphere, whose corrected forms are now applied
- next: top up with T-egf-correct-captions

## 2026-11-22 21:30 · wave of 3 (topped up twice) · T-egf-correct-captions, T-egf-correct-spelling; T-egf-repro-sphere (continues)
- a pause at the start: lean-yamabe/scaffold/YamabeScaffold.lean and Rellich.lean were changed and unheld for about a minute (/atlas-team integrating T-yamabe-analysis); the tree check passed once it took the lease
- adoption (master): C-44, C-45, C-47 (2610b9b), C-48 (f535933) under DEC-141
- T-egf-correct-captions (correct): C-47, C-44, C-45 applied (v2 a261aa9); C-45's adopted 'in the second row' corrected in the register to 'in the second subfigure' after the corrector checked the panels; CHECK-1 minor
- T-egf-correct-spelling (correct): C-48 applied at nine sites (v2 49d6ed0); its l.828 site dropped (C-32 replaced the sentence); CHECK-1 clean
- T-egf-repro-sphere (repro): still running (earthquake arm; about an hour a run)
- corrections: 3 found, 2 proved, 1 adopted, 43 applied, 0 reviewed; 3 superseded (left: the experiments C-34, C-36, C-46)
- v2: 49d6ed0 EGF-C48 (twelve batches since camera-ready, eleven this session)
- gates: corrections ✓, roadmaps ✓, v2 build ✓
- commits: 2610b9b 7c943be 8c3342d f535933 e83a6fe a5445a1 (+ this) (hub) · a261aa9 49d6ed0 (v2)
- for the planner: '2 spirals' in subfigure b's subcaption, 'depths and width' in the star and 4-circles captions, 'their inverse' at v1 l.293, l.308 (l.440 is C-34's), v1 l.217 'be Riemannian manifold' (missing 'a')
- next: rule 2 (fewer than two ready: only T-egf-repro-ablations, behind the active sphere run): a planning run

## 2026-11-22 21:52 · planning run (rule 2: one target ready, behind the active sphere run)
- egf-planner (a824af0): the checkers' and correctors' minor findings of this session become C-50 to C-63; ready now: T-egf-kb-tori-sphere-def (master), T-egf-families-of-record (closer: the audited marking of theo:universality_tori and theo:universality_sphere), T-egf-correction-witnesses (closer), the corrector batches -notions (C-50 to C-52, C-56, C-57), -families-proofs (C-53 to C-55), -loss-hypotheses (C-58, C-59), -wording (C-60 to C-62), and T-egf-repro-ablations; -experiments gains C-63; T-egf-repro-sphere untouched (active)
- corrections: 63 entries (17 found, 2 proved, 1 adopted, 43 applied; 3 superseded)
- genuine readings: none. Choices noted for the master: C-56's 'one move on T^d, d ≥ 2, suffices' (a strengthening, drop it if DEC-144 does not cover it); stating the bound b ≥ 1 + N buys would add a result (an OQ on OQ-85's precedent, not part of C-58); the equation-counter gap is layout
- questions of fact for the author (the experiments batch): the l.440 move count and which SL₂(ℤ) elements; whether Table nll's EGF row is filtered, with what floor, k chosen on which split; whether the depth ablation l.1003 is on ℝ²; F_init on T² and S² and R's weight; the loss form, b, the backward factor and the training values of the reported T² runs; what l.713's '30 times smaller' compares (measured 2.0-2.5); l.496's six moves and the Moser Flow timing; the S, T of Theorem 3.5's minimal four moves
- gates: corrections ✓, roadmaps ✓, test_corrections + test_roadmap ✓
- next: the wave: T-egf-kb-tori-sphere-def, T-egf-families-of-record, T-egf-correction-witnesses, T-egf-correct-notions (adopt C-50 with C-52 first), with T-egf-repro-sphere continuing

## 2026-11-22 23:20 · wave of 5 (topped up) · T-egf-kb-tori-sphere-def, T-egf-families-of-record, T-egf-correction-witnesses, T-egf-correct-notions, T-egf-correct-families-proofs; T-egf-repro-sphere (continues)
- adoption (master): C-50, C-51, C-52, C-56, C-57 (de0e8e3), C-53, C-54, C-55 (f30e138) under DEC-141, DEC-144; C-58 proved (its witnesses graduated)
- T-egf-kb-tori-sphere-def (master): kb 0026-0033 (21c863b)
- T-egf-families-of-record (close): AUDIT-1 minor, both marks stand; graduated as EGF/FamiliesOfRecord.lean: theo:universality_tori and theo:universality_sphere marked in their corrected forms of record (C-28, C-31, C-49, C-54); C-56's move counts. New result, confirmed by the auditor: ¬(ii) gives ergodicity directly (EGF.isGroupErgodic_of_not_bgConditionII), so Bekka–Guivarc'h's Theorem 5 is not needed for Theorem 3.5 (recorded on C-28)
- T-egf-correction-witnesses (close): AUDIT-1 minor (wording, fixed at graduation); graduated as EGF/CorrectionWitnesses.lean: the zero-weight EGF refuting C-29's Theorem 3.4 in Definition 3.1's sense (C-50), the cat map (C-26), SwapM without a floor (C-58), universal non-mixing translations in every dimension (C-29, C-56)
- T-egf-correct-notions (correct): C-50, C-51, C-52, C-56, C-57 applied (v2 0e3320c); CHECK-1 minor, a short round by the master on its finding 1 (with C-50's definition 'an ergodic policy suffices' would be false: the convention sentence), CHECK-2 clean
- T-egf-correct-families-proofs (correct): C-53, C-54, C-55 applied (v2 01f6112); CHECK-1 minor
- T-egf-repro-sphere (repro): still running
- corrections: 8 found, 3 proved, 1 adopted, 51 applied, 0 reviewed; 3 superseded (left: C-58, C-59 loss hypotheses; C-60 to C-62 wording; C-34, C-36, C-46, C-63 experiments)
- ledger: 14/16 rows closed (bucket A); theo:spectral_gap_tori and theo:spectral_gap_sphere cited named Props (C)
- v2: 01f6112 EGF-C53,C54,C55 (fifteen batches since camera-ready); repro: 4d5b197 (sphere in progress)
- gates: lean-egf ✓ (1962 declarations, 19 modules), corrections ✓, roadmaps ✓, test_corrections + test_roadmap ✓, v2 build ✓; hub: red only on papers/yamabe (prop:nonpositive's Yamabe.Mfd.Reads.prop_nonpositive_csc not in its files: /atlas-team's lean-yamabe work in progress) and so gate-tests; egf green
- commits: de0e8e3 21c863b f79a58a f30e138 370d142 65396f7 b7245fa 55cd571 241f97e b565611 ca56ca3 (+ this) (hub) · 0e3320c 01f6112 (v2)
- for the planner: a strengthening entry if v2 should say Bekka–Guivarc'h's Theorem 5 is not needed for Theorem 3.5; l.919's dense-subgroup fact without its setting; l.901 'invariant' for 'almost invariant'; 'parameterized family of EGF(s)' at v1 l.238, l.277; C-51's 'satisfying (2)'; C-56's 'ask of the moves only'
- next: the next corrector (`wave`: -loss-hypotheses or -wording), the sphere reproduction continuing

## 2026-11-22 23:35 · wave of 2 (topped up twice) · T-egf-correct-loss-hypotheses, T-egf-correct-wording; T-egf-repro-sphere (continues)
- correction to the previous entry: its heading's time is 22:38, not 23:20
- adoption (master): C-58, C-59 (2b13668), C-60, C-61, C-62 (53e0408) under DEC-141 (C-58 also DEC-143)
- T-egf-correct-loss-hypotheses (correct): C-58, C-59 applied (v2 6a9c510); CHECK-1 minor
- T-egf-correct-wording (correct): C-60, C-61, C-62 applied (v2 225d9a9); CHECK-1 minor
- T-egf-repro-sphere (repro): still running (volcano seeds)
- corrections: 4 found (C-34, C-36, C-46, C-63: the experiments batch), 2 proved and 1 adopted (superseded), 56 applied, 0 reviewed
- ledger: 14/16 rows closed (bucket A), unchanged
- v2: 225d9a9 EGF-C60,C61,C62 (seventeen batches since camera-ready)
- gates: corrections ✓, roadmaps ✓, v2 build ✓
- commits: 2b13668 8dd4a7b 8da07f8 53e0408 1d84b61 579bbeb (+ this) (hub) · 6a9c510 225d9a9 (v2)
- for the planner (CHECK-1 of -loss-hypotheses and -wording): ν_train a probability on states at l.366; 'B trajectories in each of the two buffers' at l.392; t_max's font; v1 l.192's pair (F_out*, π*); v1 l.375 'as follow'; optional '4 circles', 'spin wheel', l.778 and l.872 'with λ̂ = λ'; and from earlier: Bekka–Guivarc'h's Theorem 5 not needed for Theorem 3.5 (a strengthening), l.919's dense-subgroup setting, l.901 'almost invariant', 'parameterized family of EGF(s)' at l.238, l.277, C-51's 'satisfying (2)', C-56's 'ask of the moves only'
- next: rule 2 (one target ready, behind the active sphere run): a short planning run
