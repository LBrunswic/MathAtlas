# The EGF programme

*Ergodic Generative Flows* (Brunswic, Clemente, Yang, Sigal, Rasouli, Li; ICML 2025; arXiv
2505.03561) is to be **fully formalized and corrected** (the author, 2026-11-21, DEC-141). The
programme runs as its own loop, `/egf-programme`, modelled on the ETT programme, beside
`/atlas-team` and `/ett-programme` in the same checkout (leases, `tools/lease.py`; lease name `egf`).

## Three deliverables

1. **The Lean.** Every statement of the paper certified in `lean-egf/` (strict library `EGF`), in
   its printed form when it is true and in its corrected form when it is not, with the printed form
   kept as a Prop beside its refutation (kb 0022 of lean-causal). The ledger
   (`papers/egf/ledger/`) counts the closure.
2. **The corrected paper.** The arXiv v2 working copy, `~/Dropbox/ErgodicGFN arXiv/source/`
   (outside the hub: DEC-4 and `legacy/` are untouched), its own git repository with the
   camera-ready (plus the equal-contribution stars) as its first commit. Every correction is a
   reviewable commit tied to an entry of the corrections register. The author reviews the whole
   diff before anything goes to arXiv; the loop never uploads.
3. **The reproduction.** A private repository, `LBrunswic/egf-reproduction`, cloned at
   `node1:~/egf-reproduction`: a PyTorch reimplementation of the paper's own experiments (the
   code behind the final experiments is lost), run on node1's GPU only. Baseline numbers stay
   cited from their papers. GPU work never runs on hyperlolipop.

## The standing ruling (DEC-141)

When Lean refutes a printed statement, or it cannot be proved as printed, the programme adopts
**the smallest correction proved sufficient**: the strongest true form, with the fewest added
hypotheses, each added hypothesis named. It is applied to the v2 working copy; the author reviews
the applied diff. Genuine readings, where the paper is not wrong but ambiguous between two
mathematically different statements, still go to the author as OQ rows: OQ-47 and OQ-48 stay open.

DEC-141 also rules:
- OQ-49 (probability measures);
- OQ-50 (ε-universality);
- OQ-55 (nonsingular moves, the Jacobian relative to λ);
- OQ-60 (total variation with ½, randomized stopping);
- OQ-66 (δf_init is the negative part);
- the families: the cited spectral-gap theorems are faithful named Props.

**F_in domination** (the author's words): "the F_in domination in the context of the paper is a
straightforward consequence of the diffeomorphism decomposition of the policy". Its form of record
is nonsingularity:

  F_out π = Σᵢ (Φᵢ)#(αᵢ F_out) ≪ Σᵢ (Φᵢ)#λ ≪ λ   as soon as (Φᵢ)#λ ≪ λ for every i,

which holds for diffeomorphisms and a smooth volume, Haar measure on tori and isometries of the
sphere. The follow-up's Lean (GFNBounds) has the ingredients (`IsEGFPolicy.bind_withDensity`,
`Family.bind_withDensity_ac`, `inflowAC_of_bind_ac`). The chaining is `T-egf-inflow-nonsingular`.

## The story it rests on (`papers/egf/STORY.md`)

| fragment | what | anchors |
|---|---|---|
| S-egf-1 | Ergodicity buys universality | `EGF.main_universality` |
| S-egf-2 | Two concrete universal families (tori, spheres) | T-egf-families |
| S-egf-3 | The sampling error is controlled by the losses | `EGF.main_quantitative_sampling`, Corollaries 3.9 and 3.10 |
| S-egf-4 | The backward policy is explicit | `EGF.backward_policy` |

## The programme's objects

| file | what | kept by |
|---|---|---|
| `roadmap.toml` | the targets: `close` (Lean, lean-egf), `correct` (one batch of corrections applied to v2), `repro` (one experiment), `tooling` (planning, adoption, packaging) | egf-planner; statuses by the loop; `tools/roadmap.py --file papers/egf/programme/roadmap.toml` |
| `corrections.toml` | **the corrections register**: every finding, its refutation, its corrected form and anchor, its status `found → proved → adopted → applied → reviewed` | egf-planner adds `found` entries; the master moves statuses (`tools/corrections.py set`); `tools/corrections.py check` is the gate |
| `JOURNAL.md` | one entry per `/egf-programme` iteration | the loop |

## The team

| role | who | writes |
|---|---|---|
| master | `/egf-programme` (`.claude/skills/egf-programme/SKILL.md`) | graduation, curation, statuses, OQ rows (never DEC rows), commits in the hub, v2 and the reproduction repository |
| planner | `egf-planner` | `roadmap.toml`, new `found` entries of `corrections.toml` |
| closer, auditor | `target-closer`, `target-auditor` (shared with the other loops) | `lean-egf/scaffold/**`, `lean-egf/campaign/<id>/` |
| corrector | `paper-corrector` | `~/Dropbox/ErgodicGFN arXiv/source/main.tex` only, `adopted` entries only |
| checker | `tex-lean-checker` | its `CHECK-n.json` only (read-only otherwise) |
| experimenter | `egf-experimenter` | `node1:~/egf-reproduction` only, node1 only |

## What "done" means

- Every ledger row of `papers/egf` closed in bucket A (its printed or its adopted corrected form).
- Every corrections entry `applied`, apart from those waiting on an open reading. The v2 package
  is built (`T-egf-v2-package`), with its "Changes from v1" appendix generated by
  `tools/corrections.py errata`.
- The reproduction report is in the reproduction repository.

The author's review of the v2 diff then moves entries to `reviewed`, and the upload is the
author's.
