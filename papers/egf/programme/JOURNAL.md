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
