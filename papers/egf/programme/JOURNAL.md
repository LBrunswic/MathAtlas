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
