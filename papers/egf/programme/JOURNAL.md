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
